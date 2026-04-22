use anyhow::Result;

const IGNORED_CHARS: [char; 2] = ['\n', '\r'];

#[derive(Debug, Clone)]
pub enum ClassNamePart {
    Class(String),
    Id(String),
    PseudoClass(String),
    Tag(String),
}

#[derive(Debug, Clone)]
pub struct ClassName {
    #[allow(dead_code)]
    pub name: Vec<String>,
    pub name_parts: Vec<Vec<ClassNamePart>>,
    pub parent: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct MediaQuery {
    pub criterias: Vec<MediaQueryCriteria>,
    pub parent: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct MediaQueryCriteria {
    pub property: String,
    pub value: String,
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
    MediaQuery(MediaQuery),
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
            Node::MediaQuery(element) => element.parent,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum CssBuildPhase {
    Start,
    Specifier,
    MediaQuery,
}

#[derive(Debug)]
pub struct CssParser<'a> {
    input: &'a str,
    stage: CssBuildPhase,
    label: String,
    pub nodes: Vec<Node>,
    node: Option<usize>,
}

pub fn selector_to_parts(selector: &String) -> Vec<ClassNamePart> {
    let parts = selector.split(" ");
    parts.filter_map(|p| -> Option<ClassNamePart> {
        if p.is_empty() {
            return None;
        }
        let mut chars = p.chars();
        match chars.nth(0).unwrap() {
            '.' => Some(ClassNamePart::Class(chars.as_str().to_string())),
            '#' => Some(ClassNamePart::Id(chars.as_str().to_string())),
            ':' => Some(ClassNamePart::PseudoClass(chars.as_str().to_string())),
            // This isn't entirely correct, there are ID matchers among other things, but we don't support those yet
            _ => Some(ClassNamePart::Tag(p.to_string()))
        }
    }).collect()
}

impl<'a> CssParser<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            stage: CssBuildPhase::Start,
            label: String::new(),
            nodes: vec![],
            node: None,
        }
    }

    pub fn new_inline(input: &'a str) -> Self {
        Self {
            input,
            stage: CssBuildPhase::Specifier,
            label: String::new(),
            nodes: vec![],
            node: None,
        }
    }

    fn create_media_query_from_state(&mut self) {
        let mut name = self.label.trim().strip_prefix("media").unwrap_or(&self.label).trim();
        name = name.strip_prefix("(").unwrap_or(&name);
        name = name.strip_suffix(")").unwrap_or(&name);

        let criterias: Vec<MediaQueryCriteria> = name
            .split(",")
            .map(|l| {
                let trimmed = l.trim().to_string();
                let parts: Vec<&str> = trimmed.split(":").collect();
                if parts.len() == 2 {
                    MediaQueryCriteria {
                        property: parts[0].trim().to_string(),
                        value: parts[1].trim().to_string(),
                    }
                } else {
                    panic!();
                }
            })
            .collect();

        self.nodes.push(Node::MediaQuery(MediaQuery {
            criterias,
            parent: self.node,
        }));
        self.node = Some(self.nodes.len() - 1);
        self.label.clear();
    }

    fn create_class_name_from_state(&mut self) {
        let name: Vec<String> = self
            .label
            .split(",")
            .map(|l| l.trim().to_string())
            .collect();

        let name_parts: Vec<Vec<ClassNamePart>> = name.iter().map(|n| selector_to_parts(n)).collect();

        self.nodes.push(Node::ClassName(ClassName {
            name,
            name_parts,
            parent: self.node,
        }));
        self.node = Some(self.nodes.len() - 1);
        self.label.clear();
    }

    fn create_property_from_state(&mut self) {
        let parts: Vec<&str> = self.label.split(":").collect();
        if parts.len() != 2 {
            panic!("Failed to parse property: {}", self.label);
        }
        let mut value = parts[1];
        value = value.trim();
        value = value.strip_prefix("'").unwrap_or(value);
        value = value.strip_suffix("'").unwrap_or(value);

        let name = parts[0].trim().to_string();

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
    }

    fn create_specifier_from_state(&mut self) {
        if self.label.contains(":") {
            self.create_property_from_state();
            return;
        } else {
            // Ignore in the case of class name, but still clear state
            self.label.clear();
        }
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
                '@' => {
                    match self.stage {
                        CssBuildPhase::Start | CssBuildPhase::Specifier => {
                            self.stage = CssBuildPhase::MediaQuery;
                        }
                        _ => {
                            panic!("Got @ at unexpected stage: {:?}", self.stage);
                        }
                    }
                },
                '.' | '#' => {
                    match self.stage {
                        CssBuildPhase::Start | CssBuildPhase::Specifier => {
                            self.stage = CssBuildPhase::Specifier;
                            self.label.push(char);
                        }
                        _ => {}
                    };
                }
                ' ' => {
                    match self.stage {
                        CssBuildPhase::Specifier | CssBuildPhase::MediaQuery => {
                            self.label.push(char);
                        }
                        _ => {}
                    };
                }
                '{' => {
                    match self.stage {
                        CssBuildPhase::Specifier => {
                            self.create_class_name_from_state();
                            self.stage = CssBuildPhase::Specifier;
                        }
                        CssBuildPhase::MediaQuery => {
                            self.create_media_query_from_state();
                            self.stage = CssBuildPhase::Start;
                        }
                        _ => {}
                    };
                }
                '}' => {
                    match self.stage {
                        CssBuildPhase::Specifier => {
                            self.create_specifier_from_state();
                            self.stage = CssBuildPhase::Start;
                            self.node = self.curr_parent();
                        }
                        CssBuildPhase::Start => {
                            self.stage = CssBuildPhase::Start;
                            self.node = self.curr_parent();
                        }
                        _ => {}
                    };
                }
                ':' => {
                    match self.stage {
                        CssBuildPhase::Start | CssBuildPhase::Specifier => {
                            self.stage = CssBuildPhase::Specifier;
                            self.label.push(char);
                        }
                        CssBuildPhase::MediaQuery => {
                            self.label.push(char);
                        }
                    };
                }
                ';' => {
                    match self.stage {
                        CssBuildPhase::Specifier => {
                            self.create_property_from_state();
                        }
                        _ => {}
                    };
                }
                _ => {
                    match self.stage {
                        CssBuildPhase::Start => {
                            if IGNORED_CHARS.contains(&char) {
                                continue;
                            }
                            self.stage = CssBuildPhase::Specifier;
                            self.label.push(char);
                        }
                        CssBuildPhase::Specifier | CssBuildPhase::MediaQuery => {
                            if IGNORED_CHARS.contains(&char) {
                                continue;
                            }
                            self.label.push(char);
                        }
                    };
                }
            };
        }

        // Flush at end if still needed
        if self.stage == CssBuildPhase::Specifier {
            self.create_specifier_from_state();
        }

        Ok(())
    }
}
