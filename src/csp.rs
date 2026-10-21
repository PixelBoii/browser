use reqwest::header::{HeaderMap, CONTENT_SECURITY_POLICY};
use url::{Origin, Url};

/// The `connect-src` restrictions from every `Content-Security-Policy`
/// header on a document (falling back to `default-src` per policy).
/// An empty policy restricts nothing.
#[derive(Clone, Debug)]
pub(crate) struct ContentSecurityPolicy {
    connect_sources: Vec<Vec<Source>>,
    origin: Origin,
}

#[derive(Clone, Debug)]
enum Source {
    Wildcard,
    Self_,
    Never,
    Scheme(String),
    Host(HostSource),
}

#[derive(Clone, Debug)]
struct HostSource {
    scheme: String,
    host: Host,
    port: Port,
    path: String,
}

#[derive(Clone, Debug)]
enum Host {
    Any,
    Exact(String),
    Subdomain(String),
}

#[derive(Clone, Debug)]
enum Port {
    Default,
    Any,
    Explicit(u16),
}

impl Default for ContentSecurityPolicy {
    fn default() -> Self {
        Self {
            connect_sources: Vec::new(),
            origin: Origin::new_opaque(),
        }
    }
}

impl ContentSecurityPolicy {
    pub fn from_headers(headers: &HeaderMap, origin: Origin) -> Self {
        let origin_scheme = match &origin {
            Origin::Tuple(scheme, _, _) => scheme.clone(),
            Origin::Opaque(_) => String::new(),
        };
        let mut connect_sources = Vec::new();
        for header in headers.get_all(CONTENT_SECURITY_POLICY) {
            let Ok(value) = header.to_str() else { continue };
            // Comma-separated policies each restrict independently.
            for policy in value.split(',') {
                let mut connect = None;
                let mut default = None;
                for directive in policy.split(';') {
                    let mut tokens = directive.split_ascii_whitespace();
                    let Some(name) = tokens.next() else { continue };
                    let slot = if name.eq_ignore_ascii_case("connect-src") {
                        &mut connect
                    } else if name.eq_ignore_ascii_case("default-src") {
                        &mut default
                    } else {
                        continue;
                    };
                    // Only the first occurrence of a directive counts.
                    if slot.is_none() {
                        *slot = Some(
                            tokens
                                .map(|token| parse_source(token, &origin_scheme))
                                .collect(),
                        );
                    }
                }
                if let Some(sources) = connect.or(default) {
                    connect_sources.push(sources);
                }
            }
        }
        Self {
            connect_sources,
            origin,
        }
    }

    /// Every policy must allow the URL for the connection to proceed.
    pub fn allows_connect(&self, url: Url, redirect_count: u32) -> bool {
        self.connect_sources.iter().all(|sources| {
            sources
                .iter()
                .any(|source| source.matches(self, &url, redirect_count))
        })
    }

    fn origin_scheme(&self) -> &str {
        match &self.origin {
            Origin::Tuple(scheme, _, _) => scheme,
            Origin::Opaque(_) => "",
        }
    }

    fn matches_self(&self, url: &Url) -> bool {
        if url.scheme() == "blob" {
            return false;
        }
        if self.origin == url.origin() {
            return true;
        }
        let (
            Origin::Tuple(scheme, host, port),
            Origin::Tuple(target_scheme, target_host, target_port),
        ) = (&self.origin, url.origin())
        else {
            return false;
        };
        if host != &target_host {
            return false;
        }
        // An omitted target port means the scheme's default port.
        let port_matches =
            *port == target_port || (Some(*port) == default_port(scheme) && url.port().is_none());
        let scheme_matches = matches!(target_scheme.as_str(), "https" | "wss")
            || (scheme == "http" && matches!(target_scheme.as_str(), "http" | "ws"));
        port_matches && scheme_matches
    }
}

impl Source {
    fn matches(&self, policy: &ContentSecurityPolicy, url: &Url, redirect_count: u32) -> bool {
        match self {
            Source::Wildcard => {
                matches!(url.scheme(), "http" | "https") || url.scheme() == policy.origin_scheme()
            }
            Source::Self_ => policy.matches_self(url),
            Source::Never => false,
            Source::Scheme(scheme) => scheme_matches(scheme, url.scheme()),
            Source::Host(source) => source.matches(url, redirect_count),
        }
    }
}

impl HostSource {
    fn matches(&self, url: &Url, redirect_count: u32) -> bool {
        if !scheme_matches(&self.scheme, url.scheme()) {
            return false;
        }
        let Some(target_host) = url.host_str() else {
            return false;
        };
        self.host.matches(target_host)
            && self.port.matches(url)
            && (redirect_count > 0 || path_matches(&self.path, url.path()))
    }
}

impl Host {
    fn matches(&self, target: &str) -> bool {
        match self {
            Host::Any => true,
            Host::Exact(host) => host.eq_ignore_ascii_case(target),
            Host::Subdomain(host) => target.to_ascii_lowercase().ends_with(&format!(".{host}")),
        }
    }
}

impl Port {
    fn matches(&self, url: &Url) -> bool {
        match self {
            Port::Default => url.port().is_none(),
            Port::Any => true,
            Port::Explicit(port) => Some(*port) == url.port_or_known_default(),
        }
    }
}

fn parse_source(token: &str, origin_scheme: &str) -> Source {
    if token == "*" {
        return Source::Wildcard;
    }
    if token.eq_ignore_ascii_case("'self'") {
        return Source::Self_;
    }
    // Other keywords such as 'none' never match a connection.
    if token.starts_with('\'') {
        return Source::Never;
    }
    // Scheme source, e.g. `https:` or `wss:`.
    if let Some(scheme) = token.strip_suffix(':') {
        return Source::Scheme(scheme.to_ascii_lowercase());
    }
    parse_host_source(token, origin_scheme)
}

// Host source: `[scheme://]host[:port][/path]`, host may be `*` or `*.example.com`.
fn parse_host_source(token: &str, origin_scheme: &str) -> Source {
    let (scheme, rest) = token.split_once("://").unwrap_or((origin_scheme, token));
    let (authority, path) = match rest.find('/') {
        Some(index) => rest.split_at(index),
        None => (rest, ""),
    };
    if path.contains(['?', '#']) {
        return Source::Never;
    }
    let (host, port) = match authority.rsplit_once(':') {
        Some((host, port)) => (host, Some(port)),
        None => (authority, None),
    };
    let port = match port {
        None => Port::Default,
        Some("*") => Port::Any,
        Some(port) if port.bytes().all(|b| b.is_ascii_digit()) && !port.is_empty() => {
            match port.parse() {
                Ok(port) => Port::Explicit(port),
                Err(_) => return Source::Never,
            }
        }
        Some(_) => return Source::Never,
    };
    let host = if host == "*" {
        Host::Any
    } else if let Some(domain) = host.strip_prefix("*.") {
        if !is_valid_host(domain) {
            return Source::Never;
        }
        Host::Subdomain(domain.to_ascii_lowercase())
    } else {
        if !is_valid_host(host) {
            return Source::Never;
        }
        Host::Exact(host.to_ascii_lowercase())
    };
    Source::Host(HostSource {
        scheme: scheme.to_ascii_lowercase(),
        host,
        port,
        path: path.to_string(),
    })
}

fn is_valid_host(host: &str) -> bool {
    !host.is_empty()
        && host
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'-'))
}

fn scheme_matches(source: &str, target: &str) -> bool {
    source.eq_ignore_ascii_case(target)
        || (source.eq_ignore_ascii_case("http") && target == "https")
        || (source.eq_ignore_ascii_case("ws") && matches!(target, "wss" | "http" | "https"))
        || (source.eq_ignore_ascii_case("wss") && target == "https")
}

fn default_port(scheme: &str) -> Option<u16> {
    match scheme {
        "http" | "ws" => Some(80),
        "https" | "wss" => Some(443),
        "ftp" => Some(21),
        _ => None,
    }
}

fn path_matches(source: &str, target: &str) -> bool {
    if source.is_empty() {
        return true;
    }
    // A trailing `/` makes the source a prefix: `/api/` matches `/api/users`.
    // Without it, the whole path must match: `/api` does not match `/api/users`.
    let is_prefix = source.ends_with('/');
    let source = source.strip_suffix('/').unwrap_or(source);
    let source_parts: Vec<&str> = source.split('/').collect();
    let target_parts: Vec<&str> = target.split('/').collect();
    let length_matches = if is_prefix {
        source_parts.len() <= target_parts.len()
    } else {
        source_parts.len() == target_parts.len()
    };
    if !length_matches {
        return false;
    }
    source_parts
        .iter()
        .zip(&target_parts)
        .all(|(source_part, target_part)| {
            percent_encoding::percent_decode_str(source_part)
                .eq(percent_encoding::percent_decode_str(target_part))
        })
}
