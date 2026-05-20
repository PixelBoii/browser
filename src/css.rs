use anyhow::{Context, Result};

use crate::style::{
    GridTemplateColumns, StyleAlign, StyleBackground, StyleBorderStyle, StyleDisplay,
    StyleFlexDirection, StyleJustifyContent, StylePointerEvents, StylePosition, StyleSize,
    StyleZIndex, parse_property_value, split_ignoring_parentheses,
};

const IGNORED_CHARS: [char; 2] = ['\n', '\r'];

#[derive(Debug, Clone, PartialEq)]
pub enum ClassNamePartAttribute {
    KeyValue((String, String)),
    Key(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum PseudoClass {
    Root,
    Hover,
    Active,
    Focus,
    Before,
    After,
    Host,
    Has(Vec<ClassNamePart>),
    Not(Vec<ClassNamePart>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ClassNamePart {
    Class(String),
    Id(String),
    PseudoClass(PseudoClass),
    Attributes(Vec<ClassNamePartAttribute>),
    Tag(String),
    Combined(Vec<ClassNamePart>),
    ArrowRight,
    Ampersand,
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
pub enum MediaQueryCriteriaComparison {
    Is,
    MoreOrEqual,
    LessOrEqual,
}

#[derive(Debug, Clone)]
pub enum MediaQueryCriteriaValue {
    Px(f32),
    Rem(f32),
    String(String),
}

#[derive(Debug, Clone)]
pub struct MediaQueryCriteria {
    pub property: String,
    pub value: MediaQueryCriteriaValue,
    pub comparison: MediaQueryCriteriaComparison,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BorderSideValue {
    pub size: Option<StyleSize>,
    pub color: Option<StyleBackground>,
    pub style: Option<StyleBorderStyle>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StyleComplexBackground {
    pub background: StyleBackground,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Overflow {
    Hidden,
    Visible,
    Auto,
    Scroll,
    Clip,
}

impl Overflow {
    pub fn visible(&self) -> bool {
        *self == Overflow::Visible || *self == Overflow::Auto
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum VariableTemplatePart {
    Text(String),
    Var(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum PropertyValue {
    Raw(String),
    Size(StyleSize),
    Color(StyleBackground),
    Display(StyleDisplay),
    Position(StylePosition),
    Align(StyleAlign),
    Int(u32),
    JustifyContent(StyleJustifyContent),
    FlexDirection(StyleFlexDirection),
    Flex {
        grow: Option<u32>,
        shrink: Option<u32>,
        basis: Option<StyleSize>,
    },
    BorderStyle(StyleBorderStyle),
    BorderSide(BorderSideValue),
    CombinedSize((StyleSize, StyleSize, StyleSize, StyleSize)),
    CombinedColor(
        (
            StyleBackground,
            StyleBackground,
            StyleBackground,
            StyleBackground,
        ),
    ),
    VerticalCombinedSize((StyleSize, StyleSize)),
    HorizontalCombinedSize((StyleSize, StyleSize)),
    GridTemplateColumns(GridTemplateColumns),
    ComplexBackground(StyleComplexBackground),
    Overflow(Overflow),
    VariableTemplate(Vec<VariableTemplatePart>),
    ZIndex(StyleZIndex),
    PointerEvents(StylePointerEvents),
}

#[derive(Debug, Clone)]
pub struct Property {
    pub property: String,
    pub value: PropertyValue,
    pub parent: Option<usize>,
    pub important: bool,
}

#[derive(Debug, Clone)]
pub struct Variable {
    pub variable: String,
    pub value: PropertyValue,
    pub parent: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct Layer {
    pub name: String,
    pub parent: Option<usize>,
}

#[derive(Debug, Clone)]
pub struct PropertyDefinition {
    pub name: String,
    pub parent: Option<usize>,
}

#[derive(Debug, Clone)]
pub enum Node {
    MediaQuery(MediaQuery),
    Layer(Layer),
    ClassName(ClassName),
    Variable(Variable),
    Property(Property),
    PropertyDefinition(PropertyDefinition),
}

impl Node {
    pub fn get_parent(&self) -> Option<usize> {
        match self {
            Node::ClassName(element) => element.parent,
            Node::Variable(element) => element.parent,
            Node::Property(element) => element.parent,
            Node::MediaQuery(element) => element.parent,
            Node::Layer(element) => element.parent,
            Node::PropertyDefinition(element) => element.parent,
        }
    }

    pub fn set_parent(&mut self, parent: Option<usize>) {
        match self {
            Node::ClassName(element) => element.parent = parent,
            Node::Variable(element) => element.parent = parent,
            Node::Property(element) => element.parent = parent,
            Node::MediaQuery(element) => element.parent = parent,
            Node::Layer(element) => element.parent = parent,
            Node::PropertyDefinition(element) => element.parent = parent,
        }
    }

    pub fn offset_parent(&mut self, offset: usize) {
        if let Some(parent) = self.get_parent() {
            self.set_parent(Some(parent + offset));
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
    in_url: bool,
}

pub fn unquote(mut value: &str) -> &str {
    value = value.strip_prefix("'").unwrap_or(value);
    value = value.strip_suffix("'").unwrap_or(value);
    value = value.strip_prefix("\"").unwrap_or(value);
    value = value.strip_suffix("\"").unwrap_or(value);
    value
}

fn parse_selector_with_attributes(mut rest: &str) -> Option<ClassNamePart> {
    let mut attributes = vec![];
    while !rest.is_empty() {
        let Some(attribute_end) = rest.find(&"]") else {
            break;
        };
        let attribute = &rest[..attribute_end];
        rest = &rest[(attribute_end + 2).min(rest.len())..];

        let split: Vec<&str> = attribute.split("=").collect();
        if split.len() == 2 {
            let key = split[0];
            let mut value = split[1];
            value = unquote(value.trim());

            attributes.push(ClassNamePartAttribute::KeyValue((
                key.to_string(),
                value.to_string(),
            )));
        } else if split.len() == 1 {
            let key = split[0];
            attributes.push(ClassNamePartAttribute::Key(key.to_string()));
        }
    }

    Some(ClassNamePart::Attributes(attributes))
}

fn parse_pseudo_class(value: &str) -> Option<PseudoClass> {
    if let Some(stripped) = value.strip_prefix("not(") {
        if let Some(stripped) = stripped.strip_suffix(")") {
            return Some(PseudoClass::Not(selector_to_parts(&stripped.to_string())));
        }
    }
    if let Some(stripped) = value.strip_prefix("has(") {
        if let Some(stripped) = stripped.strip_suffix(")") {
            return Some(PseudoClass::Has(selector_to_parts(&stripped.to_string())));
        }
    }
    if value == "hover" {
        return Some(PseudoClass::Hover);
    }
    if value == "active" {
        return Some(PseudoClass::Active);
    }
    if value == "before" {
        return Some(PseudoClass::Before);
    }
    if value == "after" {
        return Some(PseudoClass::After);
    }
    if value == "focus" {
        return Some(PseudoClass::Focus);
    }
    if value == "host" {
        return Some(PseudoClass::Host);
    }
    if value == "root" {
        return Some(PseudoClass::Root);
    }
    None
}

pub fn selector_to_parts(selector: &String) -> Vec<ClassNamePart> {
    let nested_parts = split_ignoring_parentheses(selector.clone(), ' ', &['>']);
    nested_parts
        .into_iter()
        .filter_map(|p| -> Option<ClassNamePart> {
            if p.is_empty() {
                return None;
            }
            let mut conditions = vec![];
            let mut buffer = String::new();
            let new_statement = ['.', '#', '[', '>', ':'];
            let mut parentheses_depth = 0;
            let mut escaped = false;
            for char in p.chars() {
                if char == '(' {
                    parentheses_depth += 1;
                    buffer.push(char);
                    continue;
                }
                if char == ')' {
                    parentheses_depth -= 1;
                    buffer.push(char);
                    continue;
                }
                if char == '\\' && !escaped {
                    escaped = true;
                    continue;
                }
                if buffer.len() > 0
                    && new_statement.contains(&char)
                    && parentheses_depth == 0
                    && !escaped
                    && !(buffer == ":" && char == ':')
                {
                    conditions.push(buffer.clone());
                    buffer.clear();
                }
                buffer.push(char);
                if escaped {
                    escaped = false;
                }
            }
            if buffer.len() > 0 {
                conditions.push(buffer);
            }
            let mut parsed_conditions = vec![];
            for cond in conditions {
                let mut chars = cond.chars();
                let parsed = match chars.nth(0).unwrap() {
                    '.' => Some(ClassNamePart::Class(chars.as_str().to_string())),
                    '#' => Some(ClassNamePart::Id(chars.as_str().to_string())),
                    ':' => {
                        let pseudo_class =
                            chars.as_str().strip_prefix(':').unwrap_or(chars.as_str());
                        let parsed = parse_pseudo_class(pseudo_class);
                        match parsed {
                            Some(parsed) => Some(ClassNamePart::PseudoClass(parsed)),
                            None => {
                                println!("Failed to parse pseudo class: {}", chars.as_str());
                                // This intentionally returns the entire function
                                // If we fail to parse pseudo class, consider the whole class invalid
                                return None;
                            }
                        }
                    }
                    '[' => parse_selector_with_attributes(chars.as_str()),
                    '>' => Some(ClassNamePart::ArrowRight),
                    '&' => Some(ClassNamePart::Ampersand),
                    _ => Some(ClassNamePart::Tag(cond.clone())),
                };
                match parsed {
                    Some(parsed) => parsed_conditions.push(parsed),
                    None => println!("Failed to parse condition: {}", cond),
                };
            }
            if parsed_conditions.len() > 1 {
                Some(ClassNamePart::Combined(parsed_conditions))
            } else if parsed_conditions.len() == 1 {
                Some(parsed_conditions[0].clone())
            } else {
                None
            }
        })
        .collect()
}

const MEDIA_QUERY_SEPARATORS: [(MediaQueryCriteriaComparison, &str); 3] = [
    (MediaQueryCriteriaComparison::Is, ":"),
    (MediaQueryCriteriaComparison::MoreOrEqual, ">="),
    (MediaQueryCriteriaComparison::LessOrEqual, "<="),
];

pub fn parse_media_query_parts(name: &str) -> Vec<MediaQueryCriteria> {
    let criterias: Vec<MediaQueryCriteria> = name
        .split("and")
        .filter_map(|mut l| {
            l = l.strip_prefix("(").unwrap_or(&l);
            l = l.strip_suffix(")").unwrap_or(&l);
            let trimmed = l.trim().to_string();
            for (comparison, separator) in MEDIA_QUERY_SEPARATORS {
                let parts: Vec<&str> = trimmed.split(separator).collect();
                if parts.len() == 2 {
                    let mut value = MediaQueryCriteriaValue::String(parts[1].trim().to_string());
                    if let Some(inner) = parts[1].trim().strip_suffix("px") {
                        if let Ok(parsed) = inner.parse::<f32>() {
                            value = MediaQueryCriteriaValue::Px(parsed);
                        }
                    }
                    if let Some(inner) = parts[1].trim().strip_suffix("rem") {
                        if let Ok(parsed) = inner.parse::<f32>() {
                            value = MediaQueryCriteriaValue::Rem(parsed);
                        }
                    }

                    return Some(MediaQueryCriteria {
                        property: parts[0].trim().to_string(),
                        value,
                        comparison,
                    });
                }
            }
            println!("Invalid media query: {:?}", trimmed);
            return None;
        })
        .collect();
    criterias
}

impl<'a> CssParser<'a> {
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            stage: CssBuildPhase::Start,
            label: String::new(),
            nodes: vec![],
            node: None,
            in_url: false,
        }
    }

    pub fn new_inline(input: &'a str) -> Self {
        Self {
            input,
            stage: CssBuildPhase::Specifier,
            label: String::new(),
            nodes: vec![],
            node: None,
            in_url: false,
        }
    }

    fn create_media_query_from_state(&mut self) {
        if let Some(stripped) = self.label.trim().strip_prefix("@property") {
            self.nodes
                .push(Node::PropertyDefinition(PropertyDefinition {
                    name: stripped.trim().to_string(),
                    parent: self.node,
                }));
        } else if let Some(stripped) = self.label.trim().strip_prefix("@layer") {
            self.nodes.push(Node::Layer(Layer {
                name: stripped.trim().to_string(),
                parent: self.node,
            }));
        } else {
            let name = self
                .label
                .trim()
                .strip_prefix("@media")
                .unwrap_or(&self.label)
                .trim();

            let criterias = parse_media_query_parts(name);

            self.nodes.push(Node::MediaQuery(MediaQuery {
                criterias,
                parent: self.node,
            }));
        }
        self.node = Some(self.nodes.len() - 1);
        self.label.clear();
    }

    fn create_class_name_from_state(&mut self) {
        let name: Vec<String> = split_ignoring_parentheses(self.label.clone(), ',', &[])
            .into_iter()
            .map(|l| l.trim().to_string())
            .collect();

        let name_parts: Vec<Vec<ClassNamePart>> =
            name.iter().map(|n| selector_to_parts(n)).collect();

        self.nodes.push(Node::ClassName(ClassName {
            name,
            name_parts,
            parent: self.node,
        }));
        self.node = Some(self.nodes.len() - 1);
        self.label.clear();
    }

    fn create_property_from_state(&mut self) {
        let parts: (&str, &str) = self
            .label
            .split_once(":")
            .with_context(|| format!("Failed to parse property: {}", self.label))
            .unwrap();
        let mut value = parts.1;
        value = value.trim();
        value = value.strip_prefix("'").unwrap_or(value);
        value = value.strip_suffix("'").unwrap_or(value);

        let name = parts.0.trim().to_string();

        let parse_result = parse_property_value(name.clone(), value.to_string());

        match parse_result {
            Ok((parsed, important)) => {
                if name.starts_with("--") {
                    self.nodes.push(Node::Variable(Variable {
                        variable: name,
                        value: parsed,
                        parent: self.node,
                    }));
                } else {
                    self.nodes.push(Node::Property(Property {
                        property: name,
                        value: parsed,
                        parent: self.node,
                        important,
                    }));
                }
            }
            Err(err) => println!("Failed to parse property value: {}", err),
        };

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
                '@' => match self.stage {
                    CssBuildPhase::Start | CssBuildPhase::Specifier => {
                        self.label.push(char);
                        self.stage = CssBuildPhase::MediaQuery;
                    }
                    CssBuildPhase::MediaQuery => {
                        self.label.push(char);
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
                // TODO: Handle hover and other states here
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
                        CssBuildPhase::Specifier if !self.in_url => {
                            self.create_property_from_state();
                        }
                        CssBuildPhase::MediaQuery => {
                            self.label.push(char);
                        }
                        _ => {}
                    };
                }
                '(' => match self.stage {
                    CssBuildPhase::Specifier => {
                        self.label.push(char);
                        if self.label.ends_with("url(") {
                            self.in_url = true;
                        }
                    }
                    _ => {}
                },
                ')' => match self.stage {
                    CssBuildPhase::Specifier => {
                        self.in_url = false;
                        self.label.push(char);
                    }
                    _ => {}
                },
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
