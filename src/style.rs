use std::collections::HashMap;

use anyhow::{Context, Result, anyhow};
use winit::dpi::PhysicalSize;

use crate::css::{ClassName, ClassNamePart, CssParser, MediaQuery, Node, Property};
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
    Em(i32),
    Percent(i32),
    Calc(Vec<CalcExpression>),
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
    InlineFlex,
    Flex,
}

impl StyleDisplay {
    pub fn is_inline(self) -> bool {
        self == StyleDisplay::InlineBlock || self == StyleDisplay::InlineFlex
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StyleJustifyContent {
    Auto,
    FlexStart,
    FlexEnd,
    Center,
    SpaceBetween,
    Stretch,
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
pub enum StyleBorderStyle {
    None,
    Solid,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StyleSizeAndColor {
    pub color: StyleBackground,
    pub size: StyleSize,
    pub style: StyleBorderStyle,
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
    pub border_left: StyleSizeAndColor,
    pub border_top: StyleSizeAndColor,
    pub border_right: StyleSizeAndColor,
    pub border_bottom: StyleSizeAndColor,
}

pub fn get_base_style(node: &HtmlNode, parent_style: Option<Style>) -> Style {
    let implied_text_align = parent_style
        .clone()
        .and_then(|v| Some(v.text_align))
        .unwrap_or(StyleAlign::Left);
    Style {
        width: match node {
            HtmlNode::Element(element) => {
                if let Some(width) = element.attributes.get(&"width".to_string()) {
                    parse_style_size(width.clone()).unwrap()
                } else {
                    match element.tag.as_str() {
                        "br" => StyleSize::Px(0),
                        "input" => match element
                            .attributes
                            .get(&"type".to_string())
                            .and_then(|v| Some(v.as_str()))
                        {
                            Some("button") | Some("submit") | Some("reset") => StyleSize::Auto,
                            _ => StyleSize::Px(20),
                        },
                        _ => StyleSize::Auto,
                    }
                }
            }
            _ => StyleSize::Auto,
        },
        height: match node {
            HtmlNode::Element(element) => {
                if let Some(height) = element.attributes.get(&"height".to_string()) {
                    parse_style_size(height.clone()).unwrap()
                } else {
                    match element.tag.as_str() {
                        "br" => StyleSize::Px(10),
                        "input" => StyleSize::Px(22),
                        _ => StyleSize::Auto,
                    }
                }
            }
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
                "button" | "input" => {
                    if element
                        .attributes
                        .get("type")
                        .is_some_and(|v| v == "hidden")
                    {
                        StyleDisplay::None
                    } else {
                        StyleDisplay::InlineBlock
                    }
                }
                "span" | "img" | "a" => StyleDisplay::InlineBlock,
                _ => StyleDisplay::Block,
            },
            HtmlNode::Text(_) => StyleDisplay::InlineBlock,
        },
        flex_shrink: 1,
        flex_grow: 0,
        justify_content: StyleJustifyContent::FlexStart,
        align_items: StyleJustifyContent::Stretch,
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
            HtmlNode::Element(element) => parent_style
                .clone()
                .and_then(|v| Some(v.color))
                .unwrap_or(if element.tag == "input" {
                    StyleBackground::Hex(0x00_00_00_FF)
                } else {
                    StyleBackground::Transparent
                }),
            HtmlNode::Text(_) => parent_style
                .clone()
                .and_then(|v| {
                    if v.color != StyleBackground::Transparent {
                        Some(v.color)
                    } else {
                        None
                    }
                })
                .unwrap_or(StyleBackground::Hex(0x00_00_00_FF)),
        },
        min_height: StyleSize::Auto,
        max_height: StyleSize::Auto,
        min_width: StyleSize::Auto,
        max_width: StyleSize::Auto,
        position: StylePosition::Static,
        text_align: match node {
            HtmlNode::Element(element) => {
                if element.tag == "center" {
                    StyleAlign::Center
                } else {
                    implied_text_align
                }
            }
            HtmlNode::Text(_) => implied_text_align,
        },
        variables: HashMap::new(),
        font_size: parent_style
            .clone()
            .and_then(|v| Some(v.font_size))
            .unwrap_or(StyleSize::Px(16)),
        align_self: StyleJustifyContent::Auto,
        // TODO: This should default to currentColor
        border_left: StyleSizeAndColor { color: StyleBackground::Hex(0xFF_FF_FF_FF), size: StyleSize::Px(3), style: StyleBorderStyle::None },
        border_top: StyleSizeAndColor { color: StyleBackground::Hex(0xFF_FF_FF_FF), size: StyleSize::Px(3), style: StyleBorderStyle::None },
        border_right: StyleSizeAndColor { color: StyleBackground::Hex(0xFF_FF_FF_FF), size: StyleSize::Px(3), style: StyleBorderStyle::None },
        border_bottom: StyleSizeAndColor { color: StyleBackground::Hex(0xFF_FF_FF_FF), size: StyleSize::Px(3), style: StyleBorderStyle::None },
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

fn parse_size_number(value: &str) -> Result<i32> {
    Ok(value
        .parse::<f32>()
        .with_context(|| format!("Failed to parse size value: {}", value))?
        .round() as i32)
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
        return Ok(StyleSize::Percent(parse_size_number(percentage)?));
    }
    // TODO: Better handle commas later
    if value.ends_with("px") && !value.contains(",") {
        let px = value
            .strip_suffix("px")
            .with_context(|| "Failed to strip px")?
            .trim();
        return Ok(StyleSize::Px(parse_size_number(px)?));
    }
    if value.ends_with("pt") {
        let pt = value
            .strip_suffix("pt")
            .with_context(|| "Failed to strip pt")?
            .trim();
        let parsed = parse_size_number(pt)?;
        return Ok(StyleSize::Px(parsed * 96 / 72));
    }
    if value.ends_with("em") {
        let em = value
            .strip_suffix("em")
            .with_context(|| "Failed to strip pt")?
            .trim();
        let parsed = parse_size_number(em)?;
        return Ok(StyleSize::Em(parsed));
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
        ClassNamePart::Id(id) => element
            .attributes
            .get(&"id".to_string())
            .is_some_and(|v| *v == *id),
        ClassNamePart::PseudoClass(class) => {
            match class.as_str() {
                // No parent means it's a root element
                "root" => element.parent.is_none(),
                _ => false,
            }
        }
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
                } else if split.len() == 1 {
                    if element.attributes.contains_key(split[0]) {
                        return true;
                    }
                }
            }

            false
        }
    }
}

#[derive(Debug, Clone)]
pub struct NodeMatchResult {
    pub parent_matched: bool,
    pub target_matched: bool,
}

pub fn class_matches_element(
    element: &HtmlElement,
    class: &ClassName,
    node_idx: usize,
    partial_matches: &mut HashMap<(usize, usize), usize>,
) -> NodeMatchResult {
    let empty_str = "".to_string();
    let element_classes: Vec<&str> = element
        .attributes
        .get("class")
        .unwrap_or(&empty_str)
        .split(" ")
        .collect();

    for (part_group_idx, parts) in class.name_parts.iter().enumerate() {
        let key = (node_idx, part_group_idx);
        let progress = partial_matches.get(&key).copied().unwrap_or(0);

        // If already completed and selector targets this element, return true
        if progress == parts.len() - 1 {
            let target_matched =
                class_part_matches_element(element, &element_classes, &parts.last().unwrap());
            return NodeMatchResult {
                target_matched,
                parent_matched: true,
            };
        }

        // If there's still parts left to complete, handle that
        if progress < parts.len() - 1
            && class_part_matches_element(element, &element_classes, &parts[progress + 1])
        {
            partial_matches.insert(key, progress + 1);
            // If it's now complete, return true
            if progress + 1 == parts.len() - 1 {
                return NodeMatchResult {
                    target_matched: true,
                    parent_matched: false,
                };
            }
        }
    }
    NodeMatchResult {
        parent_matched: false,
        target_matched: false,
    }
}

fn build_children_index(nodes: &Vec<(usize, &Node)>) -> HashMap<usize, Vec<usize>> {
    let mut children_index = HashMap::new();

    for (idx, node) in nodes.iter() {
        if let Some(parent_idx) = node.get_parent() {
            let entry: &mut Vec<usize> = children_index.entry(parent_idx).or_default();
            entry.push(*idx);
        }
    }

    // Insert something for everyone
    for (idx, _) in nodes.iter() {
        if !children_index.contains_key(idx) {
            children_index.insert(*idx, vec![]);
        }
    }

    children_index
}

pub fn media_query_matches(query: &MediaQuery, window_size: &PhysicalSize<u32>) -> bool {
    query.criterias.iter().all(|q| {
        match q.property.as_str() {
            // Default to dark mode
            "prefers-color-scheme" => q.value == "dark",
            "max-width" => {
                let value = q.value.strip_suffix("px").unwrap_or(&q.value).trim();
                let px = value.parse::<f32>();
                if let Ok(px) = px {
                    window_size.width < px as u32
                } else {
                    println!("Failed to parse max-width px: {}", q.value);
                    false
                }
            }
            p => {
                println!("Unsupported media query property: {}", p);
                false
            }
        }
    })
}

fn walk_class_nodes(
    applicable_nodes: &mut Vec<usize>,
    element: &HtmlElement,
    nodes: &Vec<(usize, &Node)>,
    partial_matches: &mut HashMap<(usize, usize), usize>,
    walk_nodes: &Vec<usize>,
    window_size: &PhysicalSize<u32>,
) -> Result<()> {
    let children_index = build_children_index(nodes);

    for node_idx in walk_nodes {
        let result = match nodes[*node_idx].1 {
            Node::ClassName(class) => {
                class_matches_element(element, class, *node_idx, partial_matches)
            }
            Node::MediaQuery(query) => {
                let parent_matched = media_query_matches(query, window_size);
                NodeMatchResult {
                    target_matched: false,
                    parent_matched,
                }
            }
            _ => NodeMatchResult {
                parent_matched: false,
                target_matched: false,
            },
        };

        let children: Vec<&usize> = children_index
            .get(&node_idx)
            .unwrap()
            .iter()
            .map(|idx| idx)
            .collect();

        if result.target_matched {
            let applicable: Vec<&usize> = children
                .iter()
                .filter(|c| match nodes[***c].1 {
                    Node::Property(_) | Node::Variable(_) => true,
                    _ => false,
                })
                .cloned()
                .collect();
            for a in applicable {
                applicable_nodes.push(*a);
            }
        }

        if result.parent_matched {
            let followups: Vec<usize> = children
                .iter()
                .filter(|c| match nodes[***c].1 {
                    Node::Property(_) | Node::Variable(_) => false,
                    _ => true,
                })
                .cloned()
                .cloned()
                .collect();

            if followups.len() > 0 {
                walk_class_nodes(
                    applicable_nodes,
                    element,
                    nodes,
                    partial_matches,
                    &followups,
                    window_size,
                )?;
            }
        }
    }

    Ok(())
}

fn get_highest_parent(nodes: &Vec<(usize, &Node)>, node_idx: usize) -> usize {
    if let Some(parent) = nodes[node_idx].1.get_parent() {
        get_highest_parent(nodes, parent)
    } else {
        node_idx
    }
}

fn parse_border_style(value: String) -> Result<StyleBorderStyle> {
    match value.as_str() {
        "solid" => Ok(StyleBorderStyle::Solid),
        "none" => Ok(StyleBorderStyle::None),
        _ => Err(anyhow!("Failed to parse border style: {}", value)),
    }
}

fn apply_border_side(side: &mut StyleSizeAndColor, value: String) -> Result<()> {
    let parts: Vec<&str> = value.split(" ").collect();
    match parts.len() {
        1 => {
            side.size = parse_style_size(parts[0].to_string())?;
            Ok(())
        },
        2 => {
            side.size = parse_style_size(parts[0].to_string())?;
            side.style = parse_border_style(parts[1].to_string())?;
            Ok(())
        },
        3 => {
            side.size = parse_style_size(parts[0].to_string())?;
            side.style = parse_border_style(parts[1].to_string())?;
            side.color = parse_color(parts[2].to_string())?;
            Ok(())
        },
        len => Err(anyhow!("Unexpected border side count: {}", len)),
    }
}

fn get_class_nodes(
    element: &HtmlElement,
    nodes: &Vec<(usize, &Node)>,
    partial_matches: &mut HashMap<(usize, usize), usize>,
    window_size: &PhysicalSize<u32>,
) -> Result<Vec<usize>> {
    let mut applicable_nodes: Vec<usize> = vec![];
    let root_nodes: Vec<usize> = nodes
        .iter()
        .filter(|(_, n)| n.get_parent().is_none())
        .map(|(idx, _)| idx)
        .cloned()
        .collect();

    walk_class_nodes(
        &mut applicable_nodes,
        element,
        nodes,
        partial_matches,
        &root_nodes,
        window_size,
    )?;

    // Sort, prioritize media query over regular CSS with more to come
    applicable_nodes.sort_by(|a, b| {
        let highest_a = if let Some(parent) = nodes[*a].1.get_parent() {
            Some(get_highest_parent(nodes, parent))
        } else {
            None
        };
        let highest_b = if let Some(parent) = nodes[*b].1.get_parent() {
            Some(get_highest_parent(nodes, parent))
        } else {
            None
        };

        let a_comp: i32 = highest_a
            .and_then(|idx| match nodes[idx].1 {
                Node::MediaQuery(_) => Some(1),
                _ => Some(0),
            })
            .unwrap_or(0);
        let b_comp: i32 = highest_b
            .and_then(|idx| match nodes[idx].1 {
                Node::MediaQuery(_) => Some(1),
                _ => Some(0),
            })
            .unwrap_or(0);

        a_comp.cmp(&b_comp)
    });

    Ok(applicable_nodes)
}

fn rgba_to_hex((r, g, b, a): (u8, u8, u8, u8)) -> u32 {
    ((r as u32) << 24) | ((g as u32) << 16) | ((b as u32) << 8) | (a as u32)
}

fn parse_color(value: String) -> Result<StyleBackground> {
    if value.starts_with("#") {
        let code_str = value
            .strip_prefix("#")
            .with_context(|| "Failed to strip hex hashtag")?;
        let tweaked_code_str = match code_str.len() {
            6 => u32::from_str_radix(code_str, 16),
            3 => {
                let expanded = code_str.chars().flat_map(|c| [c, c]).collect::<String>();
                u32::from_str_radix(&expanded, 16)
            }
            _ => panic!("expected 3 or 6 hex chars"),
        };
        let mut parsed = tweaked_code_str
            .ok()
            .with_context(|| "Failed to parse HEX")?;
        // Convert into RGBA with the alpha being 255
        parsed = (parsed << 8) | 0xFF;
        Ok(StyleBackground::Hex(parsed))
    } else if let Some(rgba) = value.strip_prefix("rgba(") {
        let cleaned: &str = rgba.strip_suffix(")").unwrap_or(rgba);
        let parts: Vec<&str> = cleaned.split(",").collect();
        if parts.len() != 4 {
            panic!("Invalid RGBA string: {}", cleaned);
        }
        let parsed_parts: Vec<u8> = parts
            .iter()
            .take(3)
            .filter_map(|part| part.trim().parse::<u8>().ok())
            .collect();
        let alpha = (parts[3].trim().parse::<f32>()?.clamp(0.0, 1.0) * 255.0).round() as u8;
        if parsed_parts.len() != 3 {
            panic!("Invalid RGBA string: {}", cleaned);
        }
        let hex = rgba_to_hex((parsed_parts[0], parsed_parts[1], parsed_parts[2], alpha));
        Ok(StyleBackground::Hex(hex))
    } else if value == "transparent" || value == "none" {
        Ok(StyleBackground::Transparent)
    } else {
        Err(anyhow!("Failed to parse color \"{}\"", value))
    }
}

// Map variable references
pub fn resolve_node_variables<'a>(
    nodes: &'a mut Vec<Node>,
    variables: &mut HashMap<String, String>,
) -> Vec<&'a mut Property> {
    for node in nodes.iter() {
        match node {
            Node::Variable(variable) => {
                variables.insert(variable.variable.clone(), variable.value.clone());
            }
            _ => {}
        };
    }

    let properties = nodes
        .iter_mut()
        .filter_map(|node| match node {
            Node::Property(property) => {
                let parts: Vec<String> = property
                    .value
                    .split(" ")
                    .map(|part| {
                        if let Some(value) = part.strip_prefix("var(") {
                            if let Some(value) = value.strip_suffix(")") {
                                let string = value.to_string();
                                let mapped = variables.get(&string).unwrap_or(&string).clone();
                                mapped.to_string()
                            } else {
                                part.to_string()
                            }
                        } else {
                            part.to_string()
                        }
                    })
                    .collect();

                property.value = parts.join(" ");
                Some(property)
            }
            _ => None,
        })
        .collect();

    properties
}

fn parse_justify_content(value: &str) -> StyleJustifyContent {
    match value {
        "auto" => StyleJustifyContent::Auto,
        "flex-start" => StyleJustifyContent::FlexStart,
        "flex-end" => StyleJustifyContent::FlexEnd,
        "center" => StyleJustifyContent::Center,
        "space-between" => StyleJustifyContent::SpaceBetween,
        "stretch" => StyleJustifyContent::Stretch,
        _ => {
            println!(
                "Failed to parse style in parse_justify_content \"{}\"",
                value
            );
            StyleJustifyContent::FlexStart
        }
    }
}

pub fn apply_style_property(
    element: &HtmlElement,
    style: &mut Style,
    property: &Property,
) -> Result<()> {
    let value = property.value.clone();
    match property.property.as_str() {
        "width" => {
            if element.attributes.contains_key("width") {
                return Ok(());
            }
            style.width = parse_style_size(value)?;
        }
        "height" => {
            if element.attributes.contains_key("height") {
                return Ok(());
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
        }
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
            let parsed = parse_color(value);
            match parsed {
                Ok(parsed) => {
                    style.background = parsed;
                }
                Err(err) => println!("{}", err),
            };
        }
        "color" => {
            let parsed = parse_color(value);
            match parsed {
                Ok(parsed) => {
                    style.color = parsed;
                }
                Err(err) => println!("{}", err),
            };
        }
        "display" => {
            let parsed = match value.as_str().trim() {
                "block" => Some(StyleDisplay::Block),
                "inline-block" => Some(StyleDisplay::InlineBlock),
                "flex" => Some(StyleDisplay::Flex),
                "inline-flex" => Some(StyleDisplay::InlineFlex),
                "none" => Some(StyleDisplay::None),
                _ => {
                    println!("Failed to parse style display \"{}\"", value);
                    None
                }
            };
            if let Some(parsed) = parsed {
                style.display = parsed;
            }
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
                }
                2 => {
                    style.flex_grow = parts[0].parse::<u32>()?;
                    if let Ok(value) = parts[1].parse::<u32>() {
                        style.flex_shrink = value;
                    }
                    // Otherwise it refers to the flex-basis, which we don't yet handle
                }
                3 => {
                    style.flex_grow = parts[0].parse::<u32>()?;
                    style.flex_shrink = parts[1].parse::<u32>()?;
                }
                _ => {}
            }
        }
        "justify-content" => {
            style.justify_content = parse_justify_content(value.as_str());
        }
        "align-items" => {
            style.align_items = parse_justify_content(value.as_str());
        }
        "align-self" => {
            style.align_self = parse_justify_content(value.as_str());
        }
        "place-content" => {
            let parts: Vec<&str> = value.split(" ").collect();
            // align-content ignored for now
            match parts.len() {
                1 => {
                    style.justify_content = parse_justify_content(parts[0].trim());
                }
                2 => {
                    style.justify_content = parse_justify_content(parts[1].trim());
                }
                _ => {}
            }
        }
        "place-items" => {
            let parts: Vec<&str> = value.split(" ").collect();
            // justify-items ignored for now
            match parts.len() {
                1 => {
                    style.align_items = parse_justify_content(parts[0].trim());
                }
                2 => {
                    style.align_items = parse_justify_content(parts[0].trim());
                }
                _ => {}
            }
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
        "border-left-width" => {
            style.border_left.size = parse_style_size(value)?;
        }
        "border-left-color" => {
            style.border_left.color = parse_color(value)?;
        }
        "border-left-style" => {
            style.border_left.style = parse_border_style(value)?;
        }
        "border-left" => {
            apply_border_side(&mut style.border_left, value)?;
        }
        "border-top-width" => {
            style.border_top.size = parse_style_size(value)?;
        }
        "border-top-color" => {
            style.border_top.color = parse_color(value)?;
        }
        "border-top-style" => {
            style.border_top.style = parse_border_style(value)?;
        }
        "border-top" => {
            apply_border_side(&mut style.border_top, value)?;
        }
        "border-right-width" => {
            style.border_right.size = parse_style_size(value)?;
        }
        "border-right-color" => {
            style.border_right.color = parse_color(value)?;
        }
        "border-right-style" => {
            style.border_right.style = parse_border_style(value)?;
        }
        "border-right" => {
            apply_border_side(&mut style.border_right, value)?;
        }
        "border-bottom-width" => {
            style.border_bottom.size = parse_style_size(value)?;
        }
        "border-bottom-color" => {
            style.border_bottom.color = parse_color(value)?;
        }
        "border-bottom-style" => {
            style.border_bottom.style = parse_border_style(value)?;
        }
        "border-bottom" => {
            apply_border_side(&mut style.border_bottom, value)?;
        }
        "border" => {
            apply_border_side(&mut style.border_left, value.clone())?;
            apply_border_side(&mut style.border_top, value.clone())?;
            apply_border_side(&mut style.border_right, value.clone())?;
            apply_border_side(&mut style.border_bottom, value.clone())?;
        }
        "border-width" => {
            style.border_left.size = parse_style_size(value.clone())?;
            style.border_top.size = parse_style_size(value.clone())?;
            style.border_right.size = parse_style_size(value.clone())?;
            style.border_bottom.size = parse_style_size(value.clone())?;
        }
        "border-style" => {
            style.border_left.style = parse_border_style(value.clone())?;
            style.border_top.style = parse_border_style(value.clone())?;
            style.border_right.style = parse_border_style(value.clone())?;
            style.border_bottom.style = parse_border_style(value.clone())?;
        }
        _ => {
            println!("Failed to parse style \"{}\"", property.property);
        }
    };
    Ok(())
}

pub fn parse_style(
    element: &HtmlElement,
    class_css_nodes: &Vec<Node>,
    parent_style: Option<Style>,
    parent_variables: &mut HashMap<String, String>,
    partial_matches: &mut HashMap<(usize, usize), usize>,
    window_size: &PhysicalSize<u32>,
) -> Result<Style> {
    let mut style = get_base_style(&HtmlNode::Element(element.clone()), parent_style);
    let mut inline_nodes = get_inline_nodes(&element)?;
    let enumerated_nodes: Vec<(usize, &Node)> = class_css_nodes.iter().enumerate().collect();
    let applicable_class_nodes =
        get_class_nodes(&element, &enumerated_nodes, partial_matches, window_size)?;
    let mut nodes: Vec<Node> = applicable_class_nodes
        .iter()
        .map(|idx| class_css_nodes[*idx].clone())
        .collect();
    nodes.append(&mut inline_nodes);
    let properties = resolve_node_variables(&mut nodes, parent_variables);
    style.variables = parent_variables.clone();
    for property in properties {
        if let Err(result) = apply_style_property(&element, &mut style, &property) {
            println!(
                "Failed to apply property {:?} due to: {:?}",
                property, result
            );
        }
    }
    Ok(style)
}
