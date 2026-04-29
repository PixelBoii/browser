use anyhow::Context;
use deno_core::{ToV8, v8};
use std::collections::{HashMap, VecDeque};
use std::convert::Infallible;

const SELF_CLOSING_TAGS: [&str; 6] = ["br", "input", "meta", "link", "img", "hr"];

#[derive(Debug, Clone, PartialEq)]
pub struct Element {
    pub tag: String,
    pub attributes: HashMap<String, String>,
    pub parent: Option<usize>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TextElement {
    pub text: String,
    pub parent: Option<usize>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CommentElement {
    pub comment: String,
    pub parent: Option<usize>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    Element(Element),
    Text(TextElement),
    Comment(CommentElement),
}

impl Node {
    pub fn get_parent(&self) -> Option<usize> {
        match self {
            Node::Element(element) => element.parent,
            Node::Text(element) => element.parent,
            Node::Comment(element) => element.parent,
        }
    }

    pub fn set_parent(&mut self, parent: Option<usize>) {
        match self {
            Node::Element(element) => element.parent = parent,
            Node::Text(element) => element.parent = parent,
            Node::Comment(element) => element.parent = parent,
        }
    }
}

fn set_object_prop<'a, 'i, T>(
    scope: &mut v8::PinScope<'a, 'i>,
    object: v8::Local<'a, v8::Object>,
    key: &str,
    value: T,
) where
    T: ToV8<'a, Error = Infallible>,
{
    let key = v8::String::new(scope, key).unwrap();
    let value = value.to_v8(scope).unwrap();
    object.set(scope, key.into(), value).unwrap();
}

impl<'a> ToV8<'a> for Element {
    type Error = Infallible;

    fn to_v8<'i>(
        self,
        scope: &mut v8::PinScope<'a, 'i>,
    ) -> Result<v8::Local<'a, v8::Value>, Self::Error> {
        let object = v8::Object::new(scope);
        let attributes = v8::Object::new(scope);

        set_object_prop(scope, object, "kind", "element");
        set_object_prop(scope, object, "tag", self.tag);
        set_object_prop(scope, object, "parent", self.parent);

        for (key, value) in self.attributes {
            set_object_prop(scope, attributes, &key, value);
        }

        let attrs_key = v8::String::new(scope, "attributes").unwrap();
        object
            .set(scope, attrs_key.into(), attributes.into())
            .unwrap();

        Ok(object.into())
    }
}

impl<'a> ToV8<'a> for TextElement {
    type Error = Infallible;

    fn to_v8<'i>(
        self,
        scope: &mut v8::PinScope<'a, 'i>,
    ) -> Result<v8::Local<'a, v8::Value>, Self::Error> {
        let object = v8::Object::new(scope);

        set_object_prop(scope, object, "kind", "text");
        set_object_prop(scope, object, "text", self.text);
        set_object_prop(scope, object, "parent", self.parent);

        Ok(object.into())
    }
}

impl<'a> ToV8<'a> for CommentElement {
    type Error = Infallible;

    fn to_v8<'i>(
        self,
        scope: &mut v8::PinScope<'a, 'i>,
    ) -> Result<v8::Local<'a, v8::Value>, Self::Error> {
        let object = v8::Object::new(scope);

        set_object_prop(scope, object, "kind", "comment");
        set_object_prop(scope, object, "comment", self.comment);
        set_object_prop(scope, object, "parent", self.parent);

        Ok(object.into())
    }
}

impl<'a> ToV8<'a> for Node {
    type Error = Infallible;

    fn to_v8<'i>(
        self,
        scope: &mut v8::PinScope<'a, 'i>,
    ) -> Result<v8::Local<'a, v8::Value>, Self::Error> {
        match self {
            Node::Element(element) => element.to_v8(scope),
            Node::Text(element) => element.to_v8(scope),
            Node::Comment(element) => element.to_v8(scope),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BuildPhase {
    Start,
    Tag,
    TagDone,
    AttributeName,
    AttributeValue,
    AttributeValueInside,
    Text,
    TagClosing,
    ScriptOpen,
    CommentOpen,
}

#[derive(Debug)]
pub struct HtmlParser {
    input: String,
    pub stage: BuildPhase,
    pub tag: String,
    value: String,
    pub nodes: Vec<Node>,
    pub traces: VecDeque<TraceItem>,
    node: Option<usize>,
}

#[derive(Debug)]
#[allow(dead_code)]
pub struct TraceItem {
    pub char: char,
    pub stage: BuildPhase,
    pub tag: String,
}

const UNIQUE_TAGS: [&str; 2] = ["script", "style"];

fn decode_html_entities(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    let mut rest = input;

    while let Some(amp_idx) = rest.find('&') {
        out.push_str(&rest[..amp_idx]);
        rest = &rest[amp_idx..];

        if let Some(stripped) = rest.strip_prefix("&amp;") {
            out.push('&');
            rest = stripped;
            continue;
        }

        if let Some(decoded) = decode_numeric_entity(rest) {
            out.push(decoded.0);
            rest = decoded.1;
            continue;
        }

        out.push('&');
        rest = &rest[1..];
    }

    out.push_str(rest);
    out
}

fn decode_numeric_entity(input: &str) -> Option<(char, &str)> {
    let after_prefix = input.strip_prefix("&#")?;
    let semicolon_idx = after_prefix.find(';')?;
    let entity_body = &after_prefix[..semicolon_idx];

    let codepoint = if let Some(hex) = entity_body
        .strip_prefix('x')
        .or_else(|| entity_body.strip_prefix('X'))
    {
        u32::from_str_radix(hex, 16).ok()?
    } else {
        entity_body.parse::<u32>().ok()?
    };

    let ch = char::from_u32(codepoint).unwrap_or('\u{FFFD}');
    let rest = &after_prefix[semicolon_idx + 1..];

    Some((ch, rest))
}

impl HtmlParser {
    pub fn new(input: String) -> Self {
        Self {
            input,
            tag: "".to_string(),
            value: "".to_string(),
            stage: BuildPhase::Start,
            nodes: vec![],
            traces: VecDeque::new(),
            node: None,
        }
    }

    fn curr_node(&mut self) -> anyhow::Result<&mut Node> {
        let node_idx = self.node.with_context(|| "Failed to get node (1)")?;
        let node = self
            .nodes
            .get_mut(node_idx)
            .with_context(|| "Failed to get node (2)")?;
        Ok(node)
    }

    fn curr_is_script(&mut self) -> bool {
        match self.curr_node() {
            Ok(Node::Element(element)) => UNIQUE_TAGS.contains(&element.tag.as_str()),
            _ => false,
        }
    }

    fn close_attribute(&mut self) -> anyhow::Result<()> {
        let tag = self.tag.clone();
        let value = decode_html_entities(&self.value);
        let node = self.curr_node()?;
        match node {
            Node::Element(element) => {
                element.attributes.insert(tag, value);
            }
            _ => {}
        }
        self.tag = "".to_string();
        self.value = "".to_string();
        Ok(())
    }

    fn create_node_from_state(&mut self) -> anyhow::Result<bool> {
        let node = match self.stage {
            BuildPhase::Text => Node::Text(TextElement {
                text: decode_html_entities(&self.tag),
                parent: self.node.clone(),
            }),
            _ => Node::Element(Element {
                tag: self.tag.trim().to_string(),
                attributes: HashMap::new(),
                parent: self.node.clone(),
            }),
        };
        self.node = Some(self.nodes.len());
        self.nodes.push(node);
        Ok(true)
    }

    fn create_comment_from_state(&mut self) -> anyhow::Result<bool> {
        let mut comment = self.tag.clone();
        comment = comment.strip_prefix("--").unwrap_or(&comment).to_string();
        comment = comment.strip_suffix("--").unwrap_or(&comment).to_string();
        let node = Node::Comment(CommentElement {
            comment,
            parent: self.node.clone(),
        });
        self.nodes.push(node);
        Ok(true)
    }

    fn self_close_if_appropiate(&mut self) {
        let curr_node = self.curr_node();
        if let Ok(curr) = curr_node {
            match curr {
                Node::Element(element) => {
                    if SELF_CLOSING_TAGS.contains(&element.tag.as_str()) {
                        self.node = curr.get_parent();
                    }
                }
                _ => {}
            }
        }
    }

    pub fn get_context(&self) -> String {
        let traces = self
            .traces
            .iter()
            .map(|t| format!("{:?}", t))
            .collect::<VecDeque<String>>();
        format!(
            "{} {:?} {}",
            self.tag,
            self.stage,
            Vec::from(traces).join("\n")
        )
    }

    pub fn parse(&mut self) -> anyhow::Result<()> {
        let input = self.input.clone();
        let chars = input.chars();
        for char in chars {
            if self.traces.len() >= 200 {
                self.traces.pop_back();
            }
            self.traces.push_front(TraceItem {
                char,
                tag: self.tag.clone(),
                stage: self.stage.clone(),
            });

            // If in a script we ignore most parsing logic and just keep adding to "tag" until we see </script>
            if self.stage == BuildPhase::ScriptOpen {
                self.tag.push(char);

                let suffix_target = UNIQUE_TAGS
                    .iter()
                    .map(|t| format!("</{}>", t))
                    .find(|t| self.tag.ends_with(t));
                if let Some(suffix) = suffix_target {
                    // Save script content as its own element
                    self.stage = BuildPhase::Text;
                    self.tag = self
                        .tag
                        .strip_suffix(&suffix)
                        .with_context(|| "Failed to strip tag suffix")?
                        .to_string();
                    self.create_node_from_state()?;
                    // Go up the tree twice, first up from the text, then up from the script tag
                    let curr_node = self.curr_node()?;
                    self.node = curr_node.get_parent();
                    let curr_node = self.curr_node()?;
                    self.node = curr_node.get_parent();
                    self.tag = "".to_string();
                    self.stage = BuildPhase::Start;
                }
                continue;
            }

            match char {
                '<' => match self.stage {
                    BuildPhase::Start => {
                        self.stage = BuildPhase::Tag;
                    }
                    BuildPhase::Text => {
                        self.create_node_from_state()?;
                        let curr_node = self.curr_node()?;
                        self.node = curr_node.get_parent();
                        self.stage = BuildPhase::Tag;
                        self.tag = "".to_string();
                    }
                    _ => {}
                },
                '/' => match self.stage {
                    BuildPhase::Tag => {
                        self.stage = BuildPhase::TagClosing;
                    }
                    BuildPhase::AttributeValueInside => {
                        self.value.push(char);
                    }
                    BuildPhase::Text => {
                        self.tag.push(char);
                    }
                    _ => {}
                },
                '>' => match self.stage {
                    BuildPhase::Tag => {
                        self.create_node_from_state()?;
                        self.self_close_if_appropiate();
                        if self.curr_is_script() {
                            self.stage = BuildPhase::ScriptOpen;
                        } else {
                            self.stage = BuildPhase::Start;
                        }
                        self.tag = "".to_string();
                    }
                    BuildPhase::TagDone => {
                        self.self_close_if_appropiate();
                        if self.curr_is_script() {
                            self.stage = BuildPhase::ScriptOpen;
                        } else {
                            self.stage = BuildPhase::Start;
                        }
                        self.tag = "".to_string();
                    }
                    BuildPhase::TagClosing => {
                        let curr_node = self.curr_node()?;
                        self.node = curr_node.get_parent();
                        self.stage = BuildPhase::Start;
                        self.tag = "".to_string();
                    }
                    BuildPhase::AttributeName | BuildPhase::AttributeValue => {
                        self.close_attribute()?;
                        self.self_close_if_appropiate();
                        if self.curr_is_script() {
                            self.stage = BuildPhase::ScriptOpen;
                        } else {
                            self.stage = BuildPhase::Start;
                        }
                        self.tag = "".to_string();
                        self.value = "".to_string();
                    }
                    BuildPhase::CommentOpen => {
                        self.create_comment_from_state()?;
                        self.stage = BuildPhase::Start;
                        self.tag.clear();
                    },
                    _ => {}
                },
                '=' => match self.stage {
                    BuildPhase::AttributeName => {
                        self.stage = BuildPhase::AttributeValue;
                    }
                    BuildPhase::AttributeValueInside => {
                        self.value.push(char);
                    }
                    _ => {}
                },
                ' ' | '\n' => match self.stage {
                    BuildPhase::Start => {
                        self.tag.push(char);
                    },
                    BuildPhase::Tag => {
                        self.create_node_from_state()?;

                        self.stage = BuildPhase::TagDone;
                        self.tag = "".to_string();
                    }
                    BuildPhase::Text => {
                        self.tag.push(char);
                    }
                    BuildPhase::AttributeValueInside => {
                        self.value.push(char);
                    }
                    BuildPhase::AttributeName => {
                        self.close_attribute()?;
                        self.stage = BuildPhase::TagDone;
                    }
                    _ => {}
                },
                _ => match self.stage {
                    BuildPhase::Start => {
                        self.stage = BuildPhase::Text;
                        self.tag.push(char);
                    }
                    BuildPhase::Tag => {
                        // If this is the first char after entering the tag, and it's a !
                        // that means this is actually a doctype/comment, so go into a separate stage
                        if self.tag.is_empty() && char == '!' {
                            self.stage = BuildPhase::CommentOpen;
                        } else {
                            self.tag.push(char);
                        }
                    }
                    BuildPhase::TagDone | BuildPhase::AttributeName => {
                        self.stage = BuildPhase::AttributeName;
                        self.tag.push(char);
                    }
                    BuildPhase::AttributeValue => {
                        if char == '"' {
                            self.stage = BuildPhase::AttributeValueInside;
                        } else {
                            self.value.push(char);
                        }
                    }
                    BuildPhase::AttributeValueInside => {
                        if char == '"' {
                            self.close_attribute()?;
                            self.stage = BuildPhase::TagDone;
                        } else {
                            self.value.push(char);
                        }
                    }
                    BuildPhase::Text | BuildPhase::CommentOpen => {
                        self.tag.push(char);
                    }
                    _ => {}
                },
            }
        }
        // If we're out of chars, and in the text phase, consider it done
        if self.stage == BuildPhase::Text {
            self.create_node_from_state()?;
        }
        Ok(())
    }
}
