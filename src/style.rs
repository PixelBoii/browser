use std::collections::HashMap;

use anyhow::{Context, Result, anyhow};

use crate::css::{ClassName, ClassNamePart, CssParser, Node, Property};
use crate::parser::{Element as HtmlElement, Node as HtmlNode};

#[derive(Debug, Clone, PartialEq)]
pub enum StyleCalcOperator {
    Plus,
    Minus,
    Divide,
    Multiply,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CalcExpression {
    Size(StyleSize),
    Operator(StyleCalcOperator),
}

#[derive(Debug, Clone, PartialEq)]
pub enum StyleSize {
    Auto,
    Px(i32),
    Percent(i32),
    Calc(Vec<CalcExpression>)
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StyleBackground {
    Transparent,
    Hex(u32),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StyleDisplay {
    None,
    Block,
    InlineBlock,
    Flex,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StyleJustifyContent {
    Auto,
    FlexStart,
    FlexEnd,
    Center,
    SpaceBetween,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StyleFlexDirection {
    Row,
    Column,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StylePosition {
    Static,
    Relative,
    Absolute,
    Fixed,
}

impl StylePosition {
    pub fn is_free(self) -> bool {
        self == StylePosition::Absolute || self == StylePosition::Fixed
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StyleAlign {
    Left,
    Center,
    Right,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Style {
    pub width: StyleSize,
    pub height: StyleSize,
    pub background: StyleBackground,
    pub display: StyleDisplay,
    pub flex_shrink: u32,
    pub flex_grow: u32,
    pub justify_content: StyleJustifyContent,
    pub align_items: StyleJustifyContent,
    pub flex_direction: StyleFlexDirection,
    pub gap: StyleSize,
    pub margin_left: StyleSize,
    pub margin_right: StyleSize,
    pub margin_top: StyleSize,
    pub margin_bottom: StyleSize,
    pub padding_left: StyleSize,
    pub padding_right: StyleSize,
    pub padding_top: StyleSize,
    pub padding_bottom: StyleSize,
    pub color: StyleBackground,
    pub min_height: StyleSize,
    pub max_height: StyleSize,
    pub min_width: StyleSize,
    pub max_width: StyleSize,
    pub position: StylePosition,
    pub left: StyleSize,
    pub right: StyleSize,
    pub top: StyleSize,
    pub bottom: StyleSize,
    pub text_align: StyleAlign,
    pub variables: HashMap<String, String>,
    pub font_size: StyleSize,
    pub align_self: StyleJustifyContent,
}

pub fn get_base_style(node: &HtmlNode, parent_style: Option<Style>) -> Style {
    Style {
        width: match node {
            HtmlNode::Element(element) => if let Some(width) = element.attributes.get(&"width".to_string()) {
                parse_style_size(width.clone()).unwrap()
            } else {
                match element.tag.as_str() {
                    "br" => StyleSize::Px(0),
                    "input" => StyleSize::Px(130),
                    _ => StyleSize::Auto,
                }
            },
            _ => StyleSize::Auto,
        },
        height: match node {
            HtmlNode::Element(element) => if let Some(height) = element.attributes.get(&"height".to_string()) {
                parse_style_size(height.clone()).unwrap()
            } else {
                match element.tag.as_str() {
                    "br" => StyleSize::Px(10),
                    "input" => StyleSize::Px(22),
                    _ => StyleSize::Auto,
                }
            },
            _ => StyleSize::Auto,
        },
        background: match node {
            HtmlNode::Element(element) => {
                if element.tag == "input" {
                    StyleBackground::Hex(0xDD_DD_DD)
                } else {
                    StyleBackground::Transparent
                }
            }
            HtmlNode::Text(_) => StyleBackground::Transparent,
        },
        display: match node {
            HtmlNode::Element(element) => match element.tag.as_str() {
                "head" | "script" | "style" => StyleDisplay::None,
                "button" | "input" => if element.attributes.get("type").is_some_and(|v| v == "hidden") {
                    StyleDisplay::None
                } else {
                    StyleDisplay::InlineBlock
                },
                _ => StyleDisplay::Block,
            },
            HtmlNode::Text(_) => StyleDisplay::Block,
        },
        flex_shrink: 1,
        flex_grow: 0,
        justify_content: StyleJustifyContent::FlexStart,
        align_items: StyleJustifyContent::FlexStart,
        flex_direction: StyleFlexDirection::Row,
        gap: StyleSize::Px(0),
        margin_left: StyleSize::Px(0),
        margin_right: StyleSize::Px(0),
        margin_top: StyleSize::Px(0),
        margin_bottom: StyleSize::Px(0),
        padding_left: StyleSize::Px(0),
        padding_right: StyleSize::Px(0),
        padding_top: StyleSize::Px(0),
        padding_bottom: StyleSize::Px(0),
        left: StyleSize::Auto,
        right: StyleSize::Auto,
        top: StyleSize::Auto,
        bottom: StyleSize::Auto,
        color: match node {
            HtmlNode::Element(element) => {
                parent_style.clone().and_then(|v| Some(v.color)).unwrap_or(if element.tag == "input" {
                    StyleBackground::Hex(0x00_00_00)
                } else {
                    StyleBackground::Transparent
                })
            }
            HtmlNode::Text(_) => StyleBackground::Hex(0xFF_FF_FF)
        },
        min_height: StyleSize::Auto,
        max_height: StyleSize::Auto,
        min_width: StyleSize::Auto,
        max_width: StyleSize::Auto,
        position: StylePosition::Static,
        text_align: parent_style.clone().and_then(|v| Some(v.text_align)).unwrap_or(StyleAlign::Left),
        variables: HashMap::new(),
        font_size: parent_style.clone().and_then(|v| Some(v.font_size)).unwrap_or(StyleSize::Px(16)),
        align_self: StyleJustifyContent::Auto,
    }
}

fn parse_combined_style_size(
    value: String,
) -> Result<(StyleSize, StyleSize, StyleSize, StyleSize)> {
    let values: Vec<StyleSize> = value
        .split(" ")
        .map(|s| parse_style_size(s.to_string()))
        .collect::<Result<Vec<StyleSize>>>()?;

    match values.len() {
        1 => Ok((
            values[0].clone(),
            values[0].clone(),
            values[0].clone(),
            values[0].clone(),
        )),
        2 => Ok((
            values[0].clone(),
            values[1].clone(),
            values[0].clone(),
            values[1].clone(),
        )),
        3 => Ok((
            values[0].clone(),
            values[1].clone(),
            values[2].clone(),
            values[1].clone(),
        )),
        4 => Ok((
            values[0].clone(),
            values[1].clone(),
            values[2].clone(),
            values[3].clone(),
        )),
        _ => Err(anyhow!("Failed to parse combined style size {}", value)),
    }
}

fn extract_operator(char: char) -> Option<CalcExpression> {
    if char == '+' {
        Some(CalcExpression::Operator(StyleCalcOperator::Plus))
    } else if char == '-' {
        Some(CalcExpression::Operator(StyleCalcOperator::Minus))
    } else if char == '/' {
        Some(CalcExpression::Operator(StyleCalcOperator::Divide))
    } else if char == '*' {
        Some(CalcExpression::Operator(StyleCalcOperator::Multiply))
    } else {
        None
    }
}

fn flush_calc_value(buffer: &mut String, parts: &mut Vec<CalcExpression>) -> Result<()> {
    if buffer.len() > 0 {
        let size = parse_style_size(buffer.clone())?;
        buffer.clear();
        parts.push(CalcExpression::Size(size));
    }
    Ok(())
}

fn parse_calc(value: &str) -> Result<StyleSize> {
    let mut parts: Vec<CalcExpression> = vec![];
    let mut buffer = String::new();
    // Remove whitespace
    let mut value = value.to_string();
    value.retain(|c| !c.is_whitespace());
    for char in value.chars() {
        if let Some(operator) = extract_operator(char) {
            flush_calc_value(&mut buffer, &mut parts)?;
            parts.push(operator);
        } else {
            buffer.push(char);
        }
    }
    flush_calc_value(&mut buffer, &mut parts)?;
    println!("{} {:?}", value, parts);
    Ok(StyleSize::Calc(parts))
}

fn parse_style_size(value: String) -> Result<StyleSize> {
    if value == "auto" {
        return Ok(StyleSize::Auto);
    }
    if let Some(value) = value.strip_prefix("calc(") {
        if let Some(value) = value.strip_suffix(")") {
            return parse_calc(value);
        }
    }
    if value.ends_with("%") {
        let percentage = value
            .strip_suffix("%")
            .with_context(|| "Failed to strip percentage")?
            .trim();
        return Ok(StyleSize::Percent(
            percentage
                .parse::<i32>()
                .ok()
                .with_context(|| format!("Failed to parse percentage \"{}\"", percentage))?,
        ));
    }
    // TODO: Better handle commas later
    if value.ends_with("px") && !value.contains(",") {
        let px = value
            .strip_suffix("px")
            .with_context(|| "Failed to strip px")?
            .trim();
        return Ok(StyleSize::Px(px.parse::<i32>().ok().with_context(
            || format!("Failed to parse px \"{}\"", px),
        )?));
    }
    if let Ok(parsed) = value.parse::<i32>() {
        return Ok(StyleSize::Px(parsed));
    }
    println!("Failed to parse style value \"{}\"", value);
    Ok(StyleSize::Auto)
}

fn get_inline_nodes(element: &HtmlElement) -> Result<Vec<Node>> {
    let style_str = element.attributes.get("style");
    match style_str {
        Some(style) => {
            let mut inline_parser = CssParser::new_inline(&style);
            inline_parser.parse()?;
            Ok(inline_parser.nodes)
        }
        None => Ok(vec![]),
    }
}

fn class_part_matches_element(
    element: &HtmlElement,
    element_classes: &Vec<&str>,
    part: &ClassNamePart,
) -> bool {
    match part {
        // Normal class matching
        ClassNamePart::Class(class) => element_classes.contains(&class.as_str()),
        ClassNamePart::PseudoClass(class) => {
            match class.as_str() {
                // No parent means it's a root element
                "root" => element.parent.is_none(),
                _ => false,
            }
        },
        // Tag matching, can be extended to IDs and more later on
        ClassNamePart::Tag(part) => {
            if *part == element.tag {
                return true;
            }

            // If it's a match but has more criteras, match those as well
            let prefix = format!("{}[", element.tag);
            let suffix = "]";
            if part.starts_with(&prefix) && part.ends_with(&suffix) {
                let stripped = part
                    .strip_prefix(&prefix)
                    .with_context(|| format!("Failed to parse {}", part))
                    .unwrap()
                    .strip_suffix(&suffix)
                    .with_context(|| format!("Failed to parse {}", part))
                    .unwrap();
                // We only support one = for now
                let split: Vec<&str> = stripped.split("=").collect();
                if split.len() == 2 {
                    let key = split[0];
                    let mut value = split[1];
                    value = value.trim();
                    value = value.strip_prefix("'").unwrap_or(value);
                    value = value.strip_suffix("'").unwrap_or(value);
                    value = value.strip_prefix("\"").unwrap_or(value);
                    value = value.strip_suffix("\"").unwrap_or(value);

                    if element.attributes.get(key).is_some_and(|x| x == value) {
                        return true;
                    }
                }
            }

            false
        }
    }
}

fn class_matches_element(
    element: &HtmlElement,
    element_classes: &Vec<&str>,
    class: &ClassName,
    node_idx: usize,
    partial_matches: &mut HashMap<(usize, usize), usize>,
) -> bool {
    for (part_group_idx, parts) in class.name_parts.iter().enumerate() {
        let key = (node_idx, part_group_idx);
        let ancestor_progress = partial_matches.get(&key).copied().unwrap_or(0);
        let mut descendant_progress = ancestor_progress;

        // A descendant selector can only advance one segment per DOM node. If the current element
        // matches the next expected selector part, it can either complete the selector or extend the
        // prefix that children inherit.
        if ancestor_progress < parts.len()
            && class_part_matches_element(element, element_classes, &parts[ancestor_progress])
        {
            if ancestor_progress == parts.len() - 1 {
                return true;
            }
            descendant_progress = descendant_progress.max(ancestor_progress + 1);
        }

        // A selector chain may also start over at the current node. This keeps `.a .b` working for
        // nested `.a` trees without making single-part selectors leak into descendants.
        // TODO: I don't think this is enough. I think we need to handle start-over mid progress too. But this seems like a good step in the right direction.
        if parts.len() > 1 && class_part_matches_element(element, element_classes, &parts[0]) {
            descendant_progress = descendant_progress.max(1);
        }

        if descendant_progress != ancestor_progress {
            partial_matches.insert(key, descendant_progress);
        }
    }
    false
}

fn get_class_nodes(element: &HtmlElement, nodes: &Vec<Node>, partial_matches: &mut HashMap<(usize, usize), usize>) -> Result<Vec<Node>> {
    let empty_str = "".to_string();
    let element_classes: Vec<&str> = element
        .attributes
        .get("class")
        .unwrap_or(&empty_str)
        .split(" ")
        .collect();
    let applicable_classes: Vec<usize> = nodes
        .iter()
        .enumerate()
        .filter(|(node_idx, n)| match n {
            Node::ClassName(class) => class_matches_element(element, &element_classes, class, *node_idx, partial_matches),
            _ => false,
        })
        .map(|(idx, _)| idx)
        .collect();

    let applicable_nodes: Vec<Node> = nodes
        .iter()
        .filter(|n| match n {
            Node::Property(property) => property
                .parent
                .is_some_and(|parent| applicable_classes.contains(&parent)),
            Node::Variable(variable) => variable
                .parent
                .is_some_and(|parent| applicable_classes.contains(&parent)),
            _ => false,
        })
        .cloned()
        .collect();

    Ok(applicable_nodes)
}

fn parse_color(value: String) -> Result<StyleBackground> {
    if value.starts_with("#") {
        let code_str = value
            .strip_prefix("#")
            .with_context(|| "Failed to strip hex hashtag")?;
        let parsed = u32::from_str_radix(code_str, 16)
            .ok()
            .with_context(|| "Failed to parse HEX")?;
        Ok(StyleBackground::Hex(parsed))
    } else if value == "transparent" || value == "none" {
        Ok(StyleBackground::Transparent)
    } else {
        println!("Failed to parse color \"{}\"", value);
        Ok(StyleBackground::Transparent)
    }
}

// Map variable references
pub fn resolve_node_variables<'a>(nodes: &'a mut Vec<Node>, variables: &mut HashMap<String, String>) -> Vec<&'a mut Property> {
    for node in nodes.iter() {
        match node {
            Node::Variable(variable) => {
                variables.insert(variable.variable.clone(), variable.value.clone());
            },
            _ => {},
        };
    }

    let properties = nodes.iter_mut().filter_map(|node| match node {
        Node::Property(property) => {
            if let Some(value) = property.value.strip_prefix("var(") {
                if let Some(value) = value.strip_suffix(")") {
                    let string: String = value.to_string();
                    property.value = variables.get(&string).unwrap_or(&string).clone();
                }
            }

            Some(property)
        },
        _ => None,
    }).collect();

    properties
}

pub fn parse_style(
    element: &HtmlElement,
    class_css_nodes: &Vec<Node>,
    parent_style: Option<Style>,
    parent_variables: &mut HashMap<String, String>,
    partial_matches: &mut HashMap<(usize, usize), usize>,
) -> Result<Style> {
    let mut style = get_base_style(&HtmlNode::Element(element.clone()), parent_style);
    let mut inline_nodes = get_inline_nodes(&element)?;
    let mut nodes = get_class_nodes(&element, &class_css_nodes, partial_matches)?;
    nodes.append(&mut inline_nodes);
    let properties = resolve_node_variables(&mut nodes, parent_variables);
    style.variables = parent_variables.clone();
    for property in properties {
        let value = property.value.clone();
        match property.property.as_str() {
            "width" => {
                if element.attributes.contains_key("width") {
                    continue;
                }
                style.width = parse_style_size(value)?;
            }
            "height" => {
                if element.attributes.contains_key("height") {
                    continue;
                }
                style.height = parse_style_size(value)?;
            }
            "min-height" => {
                style.min_height = parse_style_size(value)?;
            }
            "max-height" => {
                style.max_height = parse_style_size(value)?;
            }
            "min-width" => {
                style.min_width = parse_style_size(value)?;
            },
            "max-width" => {
                style.max_width = parse_style_size(value)?;
            }
            "gap" => {
                style.gap = parse_style_size(value)?;
            }
            "margin" => {
                let (top, right, bottom, left) = parse_combined_style_size(value)?;
                style.margin_top = top;
                style.margin_right = right;
                style.margin_bottom = bottom;
                style.margin_left = left;
            }
            "margin-left" => {
                style.margin_left = parse_style_size(value)?;
            }
            "margin-right" => {
                style.margin_right = parse_style_size(value)?;
            }
            "margin-top" => {
                style.margin_top = parse_style_size(value)?;
            }
            "margin-bottom" => {
                style.margin_bottom = parse_style_size(value)?;
            }
            "font-size" => {
                style.font_size = parse_style_size(value)?;
            }
            "left" => {
                style.left = parse_style_size(value)?;
            }
            "right" => {
                style.right = parse_style_size(value)?;
            }
            "top" => {
                style.top = parse_style_size(value)?;
            }
            "bottom" => {
                style.bottom = parse_style_size(value)?;
            }
            "padding" => {
                let (top, right, bottom, left) = parse_combined_style_size(value)?;
                style.padding_top = top;
                style.padding_right = right;
                style.padding_bottom = bottom;
                style.padding_left = left;
            }
            "padding-left" => {
                style.padding_left = parse_style_size(value)?;
            }
            "padding-right" => {
                style.padding_right = parse_style_size(value)?;
            }
            "padding-top" => {
                style.padding_top = parse_style_size(value)?;
            }
            "padding-bottom" => {
                style.padding_bottom = parse_style_size(value)?;
            }
            "background" | "background-color" => {
                style.background = parse_color(value)?;
            }
            "color" => {
                style.color = parse_color(value)?;
            }
            "display" => {
                style.display = match value.as_str().trim() {
                    "block" => StyleDisplay::Block,
                    "inline-block" => StyleDisplay::InlineBlock,
                    "flex" => StyleDisplay::Flex,
                    "none" => StyleDisplay::None,
                    _ => {
                        println!("Failed to parse style display \"{}\"", value);
                        StyleDisplay::Block
                    }
                };
            }
            "position" => {
                style.position = match value.as_str().trim() {
                    "static" => StylePosition::Static,
                    "relative" => StylePosition::Relative,
                    "absolute" => StylePosition::Absolute,
                    "fixed" => StylePosition::Fixed,
                    _ => {
                        println!("Failed to parse style position \"{}\"", value);
                        StylePosition::Static
                    }
                };
            }
            "text-align" => {
                style.text_align = match value.as_str().trim() {
                    "left" => StyleAlign::Left,
                    "center" => StyleAlign::Center,
                    "right" => StyleAlign::Right,
                    _ => {
                        println!("Failed to parse style text-align \"{}\"", value);
                        StyleAlign::Left
                    }
                };
            }
            "flex-shrink" => {
                style.flex_shrink = value.parse::<u32>()?;
            }
            "flex-grow" => {
                style.flex_grow = value.parse::<u32>()?;
            }
            "flex" => {
                let parts: Vec<&str> = value.split(" ").collect();
                // Flex-basis ignored for now
                match parts.len() {
                    1 => {
                        // If it can be parsed as a u32, it refers to grow
                        if let Ok(value) = parts[0].parse::<u32>() {
                            style.flex_grow = value;
                        }
                        // Otherwise it refers to the flex-basis, which we don't yet handle
                    },
                    2 => {
                        style.flex_grow = parts[0].parse::<u32>()?;
                        if let Ok(value) = parts[1].parse::<u32>() {
                            style.flex_shrink = value;
                        }
                        // Otherwise it refers to the flex-basis, which we don't yet handle
                    },
                    3 => {
                        style.flex_grow = parts[0].parse::<u32>()?;
                        style.flex_shrink = parts[1].parse::<u32>()?;
                    },
                    _ => {},
                }
            },
            "justify-content" => {
                style.justify_content = match value.as_str() {
                    "auto" => StyleJustifyContent::Auto,
                    "flex-start" => StyleJustifyContent::FlexStart,
                    "flex-end" => StyleJustifyContent::FlexEnd,
                    "center" => StyleJustifyContent::Center,
                    "space-between" => StyleJustifyContent::SpaceBetween,
                    _ => {
                        println!("Failed to parse style justify-content \"{}\"", value);
                        StyleJustifyContent::FlexStart
                    }
                };
            }
            "align-items" => {
                style.align_items = match value.as_str() {
                    "auto" => StyleJustifyContent::Auto,
                    "flex-start" => StyleJustifyContent::FlexStart,
                    "flex-end" => StyleJustifyContent::FlexEnd,
                    "center" => StyleJustifyContent::Center,
                    "space-between" => StyleJustifyContent::SpaceBetween,
                    _ => {
                        println!("Failed to parse style justify-content \"{}\"", value);
                        StyleJustifyContent::FlexStart
                    }
                };
            }
            "align-self" => {
                style.align_self = match value.as_str() {
                    "auto" => StyleJustifyContent::Auto,
                    "flex-start" => StyleJustifyContent::FlexStart,
                    "flex-end" => StyleJustifyContent::FlexEnd,
                    "center" => StyleJustifyContent::Center,
                    "space-between" => StyleJustifyContent::SpaceBetween,
                    _ => {
                        println!("Failed to parse style justify-content \"{}\"", value);
                        StyleJustifyContent::FlexStart
                    }
                };
            }
            "flex-direction" => {
                style.flex_direction = match value.as_str() {
                    "row" => StyleFlexDirection::Row,
                    "column" => StyleFlexDirection::Column,
                    _ => Err(anyhow!(
                        "Failed to parse style flex-direction \"{}\"",
                        value
                    ))?,
                };
            }
            _ => {
                println!("Failed to parse style \"{}\"", property.property);
            }
        };
    }
    Ok(style)
}
