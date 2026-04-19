use anyhow::Context;
use std::collections::{HashMap, VecDeque};

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
    parent: Option<usize>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    Element(Element),
    Text(TextElement),
}

impl Node {
    pub fn get_parent(&self) -> Option<usize> {
        match self {
            Node::Element(element) => element.parent,
            Node::Text(element) => element.parent,
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
}

#[derive(Debug)]
pub struct HtmlParser<'a> {
    input: &'a str,
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

impl<'a> HtmlParser<'a> {
    pub fn new(input: &'a str) -> Self {
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
        let value = self.value.clone();
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
            BuildPhase::Text => {
                Node::Text(TextElement {
                    text: self.tag.clone(),
                    parent: self.node.clone(),
                })
            },
            _ => Node::Element(Element {
                tag: self.tag.clone(),
                attributes: HashMap::new(),
                parent: self.node.clone(),
            }),
        };
        self.node = Some(self.nodes.len());
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
        let chars = self.input.chars();
        for char in chars {
            if self.traces.len() >= 1000 {
                self.traces.pop_front();
            }
            self.traces.push_back(TraceItem {
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
                    BuildPhase::AttributeValue => {
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
                ' ' => match self.stage {
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
                    _ => {}
                },
                _ => match self.stage {
                    BuildPhase::Start => {
                        // Don't count new lines as valid starts to text
                        if char == '\n' {
                            continue;
                        }
                        self.stage = BuildPhase::Text;
                        self.tag.push(char);
                    }
                    BuildPhase::Tag => {
                        self.tag.push(char);
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
                    BuildPhase::Text => {
                        self.tag.push(char);
                    }
                    _ => {}
                },
            }
        }
        Ok(())
    }
}
