use deno_core::error::{ModuleLoaderError};
use deno_core::futures::FutureExt;
use deno_core::{
    resolve_import, ModuleLoadOptions, ModuleLoadReferrer,
    ModuleLoadResponse, ModuleLoader, ModuleSource, ModuleSourceCode, ModuleSpecifier,
    ModuleType, RequestedModuleType, ResolutionKind,
};

pub struct HttpModuleLoader {
    client: reqwest::Client,
}

impl HttpModuleLoader {
    pub fn new() -> Self {
        Self {
            client: reqwest::Client::builder()
                .redirect(reqwest::redirect::Policy::limited(10))
                .build()
                .unwrap(),
        }
    }

    fn infer_module_type(
        specifier: &ModuleSpecifier,
        content_type: Option<&str>,
        requested: &RequestedModuleType,
    ) -> ModuleType {
        let path = specifier.path().to_ascii_lowercase();
        let ct = content_type
            .and_then(|s| s.split(';').next())
            .map(|s| s.trim().to_ascii_lowercase());

        // Keep this simple for now.
        if path.ends_with(".json") || ct.as_deref() == Some("application/json") {
            ModuleType::Json
        } else if path.ends_with(".wasm") || ct.as_deref() == Some("application/wasm") {
            ModuleType::Wasm
        } else {
            match requested {
                RequestedModuleType::Text => ModuleType::Text,
                RequestedModuleType::Bytes => ModuleType::Bytes,
                RequestedModuleType::Other(ty) => ModuleType::Other(ty.clone()),
                _ => ModuleType::JavaScript,
            }
        }
    }
}

impl ModuleLoader for HttpModuleLoader {
    fn resolve(
        &self,
        specifier: &str,
        referrer: &str,
        _kind: ResolutionKind,
    ) -> Result<ModuleSpecifier, ModuleLoaderError> {
        // Browser-like resolution for relative and absolute URL imports.
        resolve_import(specifier, referrer).map_err(ModuleLoaderError::from_err)
    }

    fn load(
        &self,
        module_specifier: &ModuleSpecifier,
        _maybe_referrer: Option<&ModuleLoadReferrer>,
        options: ModuleLoadOptions,
    ) -> ModuleLoadResponse {
        println!("Loading module {:?}", module_specifier);
        let client = self.client.clone();
        let requested = options.requested_module_type.clone();
        let requested_specifier = module_specifier.clone();

        let fut = async move {
            match requested_specifier.scheme() {
                "http" | "https" => {}
                other => {
                    return Err(ModuleLoaderError::generic(format!(
                        "Unsupported module scheme for network loader: {other}"
                    )));
                }
            }

            let response = client
                .get(requested_specifier.clone())
                .send()
                .await
                .map_err(|err| {
                    ModuleLoaderError::generic(format!(
                        "Failed to fetch module {requested_specifier}: {err}"
                    ))
                })?
                .error_for_status()
                .map_err(|err| {
                    ModuleLoaderError::generic(format!(
                        "Module request failed for {requested_specifier}: {err}"
                    ))
                })?;

            let final_specifier = response.url().clone();

            let content_type = response
                .headers()
                .get(reqwest::header::CONTENT_TYPE)
                .and_then(|v| v.to_str().ok())
                .map(|s| s.to_string());

            let module_type = HttpModuleLoader::infer_module_type(
                &final_specifier,
                content_type.as_deref(),
                &requested,
            );

            // Mirror deno_core's JSON behavior: JSON imports should be explicit.
            if module_type == ModuleType::Json
                && requested != RequestedModuleType::Json
            {
                return Err(ModuleLoaderError::type_error(
                    "Attempted to load JSON module without `with { type: \"json\" }`.",
                ));
            }

            let bytes = response.bytes().await.map_err(|err| {
                ModuleLoaderError::generic(format!(
                    "Failed to read module body for {final_specifier}: {err}"
                ))
            })?;

            Ok(ModuleSource::new_with_redirect(
                module_type,
                ModuleSourceCode::Bytes(bytes.to_vec().into_boxed_slice().into()),
                &requested_specifier,
                &final_specifier,
                None,
            ))
        }
        .boxed_local();

        ModuleLoadResponse::Async(fut)
    }
}
