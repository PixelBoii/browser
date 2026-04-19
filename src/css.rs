use anyhow::Result;

const IGNORED_CHARS: [char; 2] = ['\n', '\r'];

#[derive(Debug, Clone)]
pub enum ClassNamePart {
    Class(String),
    PseudoClass(String),
    Tag(String),
}

#[derive(Debug, Clone)]
pub struct ClassName {
    #[allow(dead_code)]
    pub name: Vec<String>,
    pub name_parts: Vec<Vec<ClassNamePart>>,
    parent: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct Property {
    pub property: String,
    pub value: String,
    pub parent: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct Variable {
    pub variable: String,
    pub value: String,
    pub parent: Option<usize>,
}

#[derive(Debug, Clone)]
pub enum Node {
    ClassName(ClassName),
    Variable(Variable),
    Property(Property),
}

impl Node {
    pub fn get_parent(&self) -> Option<usize> {
        match self {
            Node::ClassName(element) => element.parent,
            Node::Variable(element) => element.parent,
            Node::Property(element) => element.parent,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum CssBuildPhase {
    Start,
    ClassName,
    PropertyName,
    PropertyValue,
}

#[derive(Debug)]
pub struct CssParser<'a> {
    input: &'a str,
    stage: CssBuildPhase,
    label: String,
    value: String,
    pub nodes: Vec<Node>,
    node: Option<usize>,
}

impl<'a> CssParser<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            stage: CssBuildPhase::Start,
            label: String::new(),
            value: String::new(),
            nodes: vec![],
            node: None,
        }
    }

    pub fn new_inline(input: &'a str) -> Self {
        Self {
            input,
            stage: CssBuildPhase::PropertyName,
            label: String::new(),
            value: String::new(),
            nodes: vec![],
            node: None,
        }
    }

    fn create_class_name_from_state(&mut self) {
        let name: Vec<String> = self
            .label
            .split(",")
            .map(|l| l.trim().to_string())
            .collect();

        let name_parts: Vec<Vec<ClassNamePart>> = name.iter().map(|n| -> Vec<ClassNamePart> {
            let parts = n.split(" ");
            parts.map(|p| -> ClassNamePart {
                let mut chars = p.chars();
                match chars.nth(0).unwrap() {
                    '.' => ClassNamePart::Class(chars.as_str().to_string()),
                    ':' => ClassNamePart::PseudoClass(chars.as_str().to_string()),
                    // This isn't entirely correct, there are ID matchers among other things, but we don't support those yet
                    _ => ClassNamePart::Tag(p.to_string())
                }
            }).collect()
        }).collect();

        self.nodes.push(Node::ClassName(ClassName {
            name,
            name_parts,
            parent: self.node,
        }));
        self.node = Some(self.nodes.len() - 1);
        self.label.clear();
    }

    fn create_property_from_state(&mut self) {
        let cloned = self.value.clone();
        let mut value = cloned.as_str();
        value = value.trim();
        value = value.strip_prefix("'").unwrap_or(value);
        value = value.strip_suffix("'").unwrap_or(value);

        let name = self.label.clone().trim().to_string();

        if name.starts_with("--") {
            self.nodes.push(Node::Variable(Variable {
                variable: name,
                value: value.to_string(),
                parent: self.node,
            }));
        } else {
            self.nodes.push(Node::Property(Property {
                property: name,
                value: value.to_string(),
                parent: self.node,
            }));
        }

        self.label.clear();
        self.value.clear();
    }

    fn curr_node(&mut self) -> Option<&mut Node> {
        let node = self.nodes.get_mut(self.node?)?;
        Some(node)
    }

    fn curr_parent(&mut self) -> Option<usize> {
        self.curr_node()?.get_parent()
    }

    pub fn parse(&mut self) -> Result<()> {
        let chars = self.input.trim().chars();
        for char in chars {
            match char {
                '.' => {
                    match self.stage {
                        CssBuildPhase::Start | CssBuildPhase::ClassName => {
                            self.stage = CssBuildPhase::ClassName;
                            self.label.push(char);
                        }
                        _ => {}
                    };
                }
                ' ' => {
                    match self.stage {
                        CssBuildPhase::ClassName => {
                            self.label.push(char);
                        }
                        CssBuildPhase::PropertyValue => {
                            self.value.push(char);
                        }
                        _ => {}
                    };
                }
                '{' => {
                    match self.stage {
                        CssBuildPhase::ClassName => {
                            self.create_class_name_from_state();
                            self.stage = CssBuildPhase::PropertyName;
                        }
                        _ => {}
                    };
                }
                '}' => {
                    match self.stage {
                        CssBuildPhase::PropertyValue => {
                            self.create_property_from_state();
                            self.stage = CssBuildPhase::Start;
                            self.node = self.curr_parent();
                        }
                        CssBuildPhase::PropertyName => {
                            self.stage = CssBuildPhase::Start;
                            self.node = self.curr_parent();
                        }
                        _ => {}
                    };
                }
                ':' => {
                    match self.stage {
                        CssBuildPhase::Start | CssBuildPhase::ClassName => {
                            self.stage = CssBuildPhase::ClassName;
                            self.label.push(char);
                        }
                        CssBuildPhase::PropertyName => {
                            self.stage = CssBuildPhase::PropertyValue;
                        }
                        _ => {}
                    };
                }
                ';' => {
                    match self.stage {
                        CssBuildPhase::PropertyValue => {
                            self.create_property_from_state();
                            self.stage = CssBuildPhase::PropertyName;
                        }
                        _ => {}
                    };
                }
                _ => {
                    match self.stage {
                        CssBuildPhase::Start => {
                            self.stage = CssBuildPhase::ClassName;
                            if IGNORED_CHARS.contains(&char) {
                                continue;
                            }
                            self.label.push(char);
                        }
                        CssBuildPhase::ClassName | CssBuildPhase::PropertyName => {
                            if IGNORED_CHARS.contains(&char) {
                                continue;
                            }
                            self.label.push(char);
                        }
                        CssBuildPhase::PropertyValue => {
                            if IGNORED_CHARS.contains(&char) {
                                continue;
                            }
                            self.value.push(char);
                        }
                    };
                }
            };
        }

        // Flush at end if still needed
        if self.stage == CssBuildPhase::PropertyValue {
            self.create_property_from_state();
        }

        Ok(())
    }
}
