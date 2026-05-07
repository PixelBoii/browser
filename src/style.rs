use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use anyhow::{Context, Result, anyhow};
use winit::dpi::PhysicalSize;

use crate::css::{BorderSideValue, ClassNamePartAttribute, CssParser, MediaQuery, MediaQueryCriteriaComparison, MediaQueryCriteriaValue, Node, Overflow, Property, PropertyValue, StyleComplexBackground, Variable, unquote};
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
    Px(f32),
    Em(f32),
    Rem(f32),
    Percent(f32),
    Vh(i32),
    Svh(i32),
    Vw(i32),
    Calc(Vec<CalcExpression>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum StyleBackground {
    Transparent,
    Hex(u32),
    DataUrl((String, String)),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StyleDisplay {
    None,
    Block,
    InlineBlock,
    Inline,
    InlineFlex,
    Flex,
    Grid,
}

impl StyleDisplay {
    pub fn is_inline(self) -> bool {
        self == StyleDisplay::InlineBlock || self == StyleDisplay::InlineFlex || self == StyleDisplay::Inline
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
    SpaceEvenly,
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
pub enum GridColumnSize {
    Px(i32),
    Fraction(i32),
}

#[derive(Debug, Clone, PartialEq)]
pub enum GridTemplateColumnsValue {
    MinMax((GridColumnSize, GridColumnSize)),
    Size(GridColumnSize),
}

#[derive(Debug, Clone, PartialEq)]
pub enum GridTemplateColumns {
    Values(Vec<GridTemplateColumnsValue>),
    None,
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
    pub grid_template_columns: GridTemplateColumns,
    pub overflow: Overflow,
}

pub fn get_base_style(node: &HtmlNode, parent_style: Option<&Style>) -> Style {
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
                        "br" => StyleSize::Px(0.),
                        "input" => match element
                            .attributes
                            .get(&"type".to_string())
                            .and_then(|v| Some(v.as_str()))
                        {
                            Some("button") | Some("submit") | Some("reset") => StyleSize::Auto,
                            _ => StyleSize::Px(20.),
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
                        "br" => StyleSize::Px(10.),
                        "input" => StyleSize::Px(22.),
                        _ => StyleSize::Auto,
                    }
                }
            }
            _ => StyleSize::Auto,
        },
        background: match node {
            HtmlNode::Element(element) => {
                if element.tag == "input" {
                    StyleBackground::Hex(0xDD_DD_DD_FF)
                } else {
                    StyleBackground::Transparent
                }
            }
            HtmlNode::Text(_) | HtmlNode::Comment(_) => StyleBackground::Transparent,
        },
        display: match node {
            HtmlNode::Element(element) => match element.tag.as_str() {
                "head" | "script" | "style" | "noscript" => StyleDisplay::None,
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
                "br" => StyleDisplay::Inline,
                _ => StyleDisplay::Block,
            },
            HtmlNode::Text(_) => StyleDisplay::Inline,
            HtmlNode::Comment(_) => StyleDisplay::None,
        },
        flex_shrink: 1,
        flex_grow: 0,
        justify_content: StyleJustifyContent::FlexStart,
        align_items: StyleJustifyContent::Stretch,
        flex_direction: StyleFlexDirection::Row,
        gap: StyleSize::Px(0.),
        margin_left: StyleSize::Px(0.),
        margin_right: StyleSize::Px(0.),
        margin_top: StyleSize::Px(0.),
        margin_bottom: StyleSize::Px(0.),
        padding_left: StyleSize::Px(0.),
        padding_right: StyleSize::Px(0.),
        padding_top: StyleSize::Px(0.),
        padding_bottom: StyleSize::Px(0.),
        left: StyleSize::Auto,
        right: StyleSize::Auto,
        top: StyleSize::Auto,
        bottom: StyleSize::Auto,
        color: match node {
            HtmlNode::Element(element) => parent_style
                .clone()
                .and_then(|v| Some(v.color.clone()))
                .unwrap_or(if element.tag == "input" {
                    StyleBackground::Hex(0x00_00_00_FF)
                } else {
                    StyleBackground::Transparent
                }),
            HtmlNode::Text(_) => parent_style
                .clone()
                .and_then(|v| {
                    if v.color != StyleBackground::Transparent {
                        Some(v.color.clone())
                    } else {
                        None
                    }
                })
                .unwrap_or(StyleBackground::Hex(0x00_00_00_FF)),
            HtmlNode::Comment(_) => StyleBackground::Transparent,
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
            HtmlNode::Text(_) | HtmlNode::Comment(_) => implied_text_align,
        },
        variables: HashMap::new(),
        font_size: parent_style
            .clone()
            .and_then(|v| Some(v.font_size.clone()))
            .unwrap_or(StyleSize::Px(16.)),
        align_self: StyleJustifyContent::Auto,
        // TODO: This should default to currentColor
        border_left: StyleSizeAndColor { color: StyleBackground::Hex(0xFF_FF_FF_FF), size: StyleSize::Px(3.), style: StyleBorderStyle::None },
        border_top: StyleSizeAndColor { color: StyleBackground::Hex(0xFF_FF_FF_FF), size: StyleSize::Px(3.), style: StyleBorderStyle::None },
        border_right: StyleSizeAndColor { color: StyleBackground::Hex(0xFF_FF_FF_FF), size: StyleSize::Px(3.), style: StyleBorderStyle::None },
        border_bottom: StyleSizeAndColor { color: StyleBackground::Hex(0xFF_FF_FF_FF), size: StyleSize::Px(3.), style: StyleBorderStyle::None },
        grid_template_columns: GridTemplateColumns::None,
        overflow: Overflow::Visible,
    }
}

fn parse_two_axis_size(value: String) -> Result<(StyleSize, StyleSize)> {
    let values: Vec<StyleSize> = split_ignoring_parentheses(value.clone(), ' ', &[])
        .into_iter()
        .map(|s| parse_style_size(s.to_string()))
        .collect::<Result<Vec<StyleSize>>>()?;

    match values.len() {
        1 => Ok((
            values[0].clone(),
            values[0].clone(),
        )),
        2 => Ok((
            values[0].clone(),
            values[1].clone(),
        )),
        _ => Err(anyhow!("Failed to parse inline size {}", value)),
    }
}

fn parse_combined_style<T, F>(
    value: String,
    parse: F,
) -> Result<(T, T, T, T)>
where
    T: Clone,
    F: Fn(String) -> Result<T>,
{
    let values: Vec<T> = split_ignoring_parentheses(value.clone(), ' ', &[])
        .iter()
        .map(|s| parse(s.to_string()))
        .collect::<Result<Vec<T>>>()?;

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

const CALC_NUMBER_CHARS: [char; 11] = ['.', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];

fn parse_calc(value: &str) -> Result<StyleSize> {
    let mut parts: Vec<CalcExpression> = vec![];
    let mut buffer = String::new();
    // Remove whitespace
    let mut value = value.to_string();
    value.retain(|c| !c.is_whitespace());
    let mut last_numberish = false;
    for char in value.chars() {
        if let Some(operator) = extract_operator(char) && last_numberish {
            flush_calc_value(&mut buffer, &mut parts)?;
            parts.push(operator);
            last_numberish = false;
        } else {
            if char != ' ' && CALC_NUMBER_CHARS.contains(&char) {
                last_numberish = true;
            }
            buffer.push(char);
        }
    }
    flush_calc_value(&mut buffer, &mut parts)?;
    Ok(StyleSize::Calc(parts))
}

fn parse_size_number(value: &str) -> Result<f32> {
    Ok(value
        .parse::<f32>()
        .with_context(|| format!("Failed to parse size value: {}", value))?)
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
        return Ok(StyleSize::Percent(parse_size_number(percentage)? as f32));
    }
    if value.ends_with("svh") {
        let svh = value
            .strip_suffix("svh")
            .with_context(|| "Failed to strip svh")?
            .trim();
        return Ok(StyleSize::Svh(parse_size_number(svh)? as i32));
    }
    if value.ends_with("vh") {
        let vh = value
            .strip_suffix("vh")
            .with_context(|| "Failed to strip vh")?
            .trim();
        return Ok(StyleSize::Vh(parse_size_number(vh)? as i32));
    }
    if value.ends_with("vw") {
        let vw = value
            .strip_suffix("vw")
            .with_context(|| "Failed to strip vw")?
            .trim();
        return Ok(StyleSize::Vw(parse_size_number(vw)? as i32));
    }
    if value.ends_with("px") {
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
        return Ok(StyleSize::Px(parsed * 96. / 72.));
    }
    if value.ends_with("rem") {
        let rem = value
            .strip_suffix("rem")
            .with_context(|| "Failed to strip rem")?
            .trim();
        let parsed = parse_size_number(rem)?;
        return Ok(StyleSize::Rem(parsed));
    }
    if value.ends_with("em") {
        let em = value
            .strip_suffix("em")
            .with_context(|| "Failed to strip em")?
            .trim();
        let parsed = parse_size_number(em)?;
        return Ok(StyleSize::Em(parsed));
    }
    let mut adjusted = value.clone();
    if value.starts_with('.') {
        adjusted = format!("0{}", adjusted);
    }
    if let Ok(parsed) = adjusted.parse::<f32>() {
        return Ok(StyleSize::Px(parsed));
    }
    println!("Failed to parse style value \"{}\"", value);
    Ok(StyleSize::Auto)
}

fn parse_grid_size(value: String) -> Result<GridColumnSize> {
    if value.ends_with("px") {
        let px = value
            .strip_suffix("px")
            .with_context(|| "Failed to strip px")?
            .trim();
        return Ok(GridColumnSize::Px(parse_size_number(px)? as i32));
    }
    if value.ends_with("fr") {
        let fr = value
            .strip_suffix("fr")
            .with_context(|| "Failed to strip fr")?
            .trim();
        return Ok(GridColumnSize::Fraction(parse_size_number(fr)? as i32));
    }
    if let Ok(parsed) = value.parse::<i32>() {
        return Ok(GridColumnSize::Px(parsed));
    }
    Err(anyhow!("Failed to parse style value \"{}\"", value))
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

pub fn element_matched_attributes(element: &HtmlElement, attributes: &Vec<ClassNamePartAttribute>) -> bool {
    for attribute in attributes.iter() {
        match attribute {
            ClassNamePartAttribute::Key(key) => {
                if !element.attributes.contains_key(key) {
                    return false;
                }
            },
            ClassNamePartAttribute::KeyValue((key, value)) => {
                if let Some(stripped) = key.strip_suffix('*') {
                    if element.attributes.get(stripped).is_none_or(|v| !v.contains(value)) {
                        return false;
                    }
                } else {
                    if element.attributes.get(key).is_none_or(|v| v != value) {
                        return false;
                    }
                }
            }
        }
    }

    return true;
}

pub fn build_css_children_index(nodes: &Vec<(usize, &Node)>) -> HashMap<usize, Vec<usize>> {
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
        // TODO: Implement more + handle q.comparison
        // Media queries REM are not resolved against the font-size configured by CSS, but the default in the browser, which we hard-code to 16
        match (q.property.as_str(), q.comparison.clone(), q.value.clone()) {
            // Default to dark mode
            ("prefers-color-scheme", MediaQueryCriteriaComparison::Is, MediaQueryCriteriaValue::String(value)) => value == "dark",
            ("max-width", MediaQueryCriteriaComparison::Is, MediaQueryCriteriaValue::Px(px)) => window_size.width < px as u32,
            ("width", MediaQueryCriteriaComparison::MoreOrEqual, MediaQueryCriteriaValue::Px(px)) => window_size.width >= px as u32,
            ("width", MediaQueryCriteriaComparison::MoreOrEqual, MediaQueryCriteriaValue::Rem(rem)) => window_size.width >= rem as u32 * 16,
            ("width", MediaQueryCriteriaComparison::LessOrEqual, MediaQueryCriteriaValue::Px(px)) => window_size.width <= px as u32,
            ("width", MediaQueryCriteriaComparison::LessOrEqual, MediaQueryCriteriaValue::Rem(rem)) => window_size.width <= rem as u32 * 16,
            (_, _, _) => {
                // println!("Unsupported media query property: {} {:?} {:?}", p, c, v);
                false
            }
        }
    })
}

fn parse_border_style(value: String) -> Result<StyleBorderStyle> {
    match value.as_str() {
        "solid" => Ok(StyleBorderStyle::Solid),
        "none" => Ok(StyleBorderStyle::None),
        _ => Err(anyhow!("Failed to parse border style: {}", value)),
    }
}

pub fn get_class_list(element: &HtmlElement) -> HashSet<String> {
    let element_classes: HashSet<String> = element
        .attributes
        .get("class")
        .cloned()
        .unwrap_or(String::new())
        .split(" ")
        .map(|s| s.to_string())
        .collect();

    element_classes
}

fn rgba_to_hex((r, g, b, a): (u8, u8, u8, u8)) -> u32 {
    ((r as u32) << 24) | ((g as u32) << 16) | ((b as u32) << 8) | (a as u32)
}

fn parse_color(value: String) -> Result<StyleBackground> {
    if value.starts_with("#") {
        let code_str = value
            .strip_prefix("#")
            .with_context(|| "Failed to strip hex hashtag")?;
        let parsed = match code_str.len() {
            8 => u32::from_str_radix(code_str, 16)?,
            // This also adds alpha
            6 => (u32::from_str_radix(code_str, 16)? << 8) | 0xFF,
            4 => {
                let expanded = code_str.chars().flat_map(|c| [c, c]).collect::<String>();
                u32::from_str_radix(&expanded, 16)?
            }
            // This also adds alpha
            3 => {
                let expanded = code_str.chars().flat_map(|c| [c, c]).collect::<String>();
                (u32::from_str_radix(&expanded, 16)? << 8) | 0xFF
            }
            _ => Err(anyhow!("expected 3, 6 or 8 hex chars, got {}", code_str))?,
        };
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
    } else if let Some(rgb) = value.strip_prefix("rgb(") {
        let cleaned: &str = rgb.strip_suffix(")").unwrap_or(rgb);
        let parts: Vec<&str> = cleaned.split(",").collect();
        if parts.len() != 3 {
            panic!("Invalid RGB string: {}", cleaned);
        }
        let parsed_parts: Vec<u8> = parts
            .iter()
            .filter_map(|part| part.trim().parse::<u8>().ok())
            .collect();
        if parsed_parts.len() != 3 {
            panic!("Invalid RGBA string: {}", cleaned);
        }
        let hex = rgba_to_hex((parsed_parts[0], parsed_parts[1], parsed_parts[2], 255));
        Ok(StyleBackground::Hex(hex))
    } else if value == "transparent" || value == "none" {
        Ok(StyleBackground::Transparent)
    } else {
        Err(anyhow!("Failed to parse color \"{}\"", value))
    }
}

// Map variable references
fn resolve_variable_value(value: &str, variables: &HashMap<String, String>) -> String {
    let mut out = String::new();
    let mut buffer = String::new();
    let mut inside = false;
    for char in value.chars() {
        if inside && char == ')' {
            if let Some(mapped) = variables.get(&buffer) {
                out += &mapped;
            } else {
                out += &buffer;
            }
            inside = false;
            buffer.clear();
            continue;
        }
        buffer.push(char);
        if let Some(stripped) = buffer.strip_suffix("var(") {
            inside = true;
            out += stripped;
            buffer.clear();
            continue;
        }
    }
    if buffer.len() > 0 {
        out += &buffer;
    }
    out
}

fn apply_node_variables_dependencies(collected_variables: &mut HashMap<usize, String>, css_nodes: &Vec<Node>, variable_dependence: &mut HashMap<&str, Vec<usize>>, var_idx: usize, value: String) {
    collected_variables.insert(var_idx, value.clone());
    let name = match &css_nodes[var_idx] {
        Node::Variable(variable) => &variable.variable,
        _ => panic!(),
    };
    let Some(dependent) = variable_dependence.get(name.as_str()).cloned() else {
        return;
    };
    for idx in dependent.iter() {
        apply_node_variables_dependencies(collected_variables, css_nodes, variable_dependence, *idx, value.clone());
    }
    variable_dependence.remove(name.as_str());
}

fn order_variables(idxs: &Vec<&usize>, css_node_ranking: &HashMap<usize, usize>) -> Vec<usize> {
    let mut idxs = idxs.clone();
    idxs.sort_by(|a, b| {
        let a_rank = css_node_ranking.get(&a).unwrap();
        let b_rank = css_node_ranking.get(&b).unwrap();
        a_rank.cmp(b_rank)
    });

    idxs.into_iter().copied().collect()
}

fn apply_node_variables(
    nodes: &Vec<(usize, Node)>,
    variables: &mut HashMap<String, String>,
    css_nodes: &Vec<Node>,
    css_node_ranking: &HashMap<usize, usize>,
) {
    let variables_to_parse: HashMap<usize, &Variable> = nodes
        .iter()
        .filter_map(|(idx, node)| match node {
            Node::Variable(variable) => {
                Some((*idx, variable))
            }
            _ => None
        })
        .collect();
    let mut variable_dependence: HashMap<&str, Vec<usize>> = HashMap::new();
    let mut no_dependence = vec![];
    for (idx, var) in variables_to_parse.iter() {
        if let PropertyValue::Raw(value) = &var.value {
            if let Some(value) = value.strip_prefix("var(") {
                if let Some(value) = value.strip_suffix(")") {
                    variable_dependence.entry(value).or_default().push(*idx);
                    continue;
                }
            }
        }
        no_dependence.push(*idx);
    }
    let mut collected_variables: HashMap<usize, String> = HashMap::new();
    for idx in no_dependence {
        // Ignore fake idxs
        if idx == usize::MAX {
            continue;
        }
        let value = match &css_nodes[idx] {
            Node::Variable(variable) => &variable.value,
            _ => panic!(),
        };
        if let PropertyValue::Raw(value) = value {
            apply_node_variables_dependencies(&mut collected_variables, css_nodes, &mut variable_dependence, idx, value.clone());
        }
    }
    for (variable, idxs) in variable_dependence.clone() {
        let Some(resolved) = variables.get(variable).cloned() else {
            continue;
        };

        for idx in idxs {
            apply_node_variables_dependencies(&mut collected_variables, css_nodes, &mut variable_dependence, idx, resolved.clone());
        }
    }
    let unordered_collected_idxs = collected_variables.keys().collect::<Vec<&usize>>();
    let ordered_idxs = order_variables(&unordered_collected_idxs, css_node_ranking);
    for idx in ordered_idxs {
        let value = collected_variables.get(&idx).unwrap();
        let var = variables_to_parse.get(&idx).unwrap();
        variables.insert(var.variable.clone(), value.to_string());
    }
}

pub fn resolve_node_variables<'a>(
    nodes: &'a mut Vec<(usize, Node)>,
    variables: &mut HashMap<String, String>,
    css_nodes: &Vec<Node>,
    css_node_ranking: &HashMap<usize, usize>,
) -> Vec<&'a mut Property> {
    apply_node_variables(nodes, variables, css_nodes, css_node_ranking);

    let properties = nodes
        .iter_mut()
        .filter_map(|(_, node)| match node {
            Node::Property(property) => {
                if let PropertyValue::Raw(value) = &property.value {
                    let value = resolve_variable_value(value, variables);
                    if let Ok((parsed, _)) = parse_property_value(property.property.clone(), value) {
                        property.value = parsed;
                    }
                }
                Some(property)
            }
            _ => None,
        })
        .collect();

    properties
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::css::{Node, Property, PropertyValue, Variable};

    use super::{resolve_node_variables, resolve_variable_value, split_ignoring_parentheses, StyleSize};

    #[test]
    fn resolves_node_variables() {
        let nodes = vec![
            Node::Variable(Variable { variable: "--size".into(), value: PropertyValue::Raw("12px".into()), parent: None }),
            Node::Variable(Variable { variable: "--dependent".into(), value: PropertyValue::Raw("var(--size)".into()), parent: None }),
            Node::Variable(Variable { variable: "--another-one".into(), value: PropertyValue::Raw("var(--test)".into()), parent: None }),
            Node::Property(Property { property: "width".into(), value: PropertyValue::Raw("var(--size)".into()), parent: None, important: false }),
            Node::Property(Property { property: "height".into(), value: PropertyValue::Raw("var(--dependent)".into()), parent: None , important: false}),
            Node::Property(Property { property: "gap".into(), value: PropertyValue::Raw("var(--another-one)".into()), parent: None, important: false }),
        ];

        let mut already_resolved = HashMap::new();
        already_resolved.insert("--test".to_string(), "16px".to_string());
        let mut nodes_to_parse = nodes.clone().into_iter().enumerate().collect();
        let properties = resolve_node_variables(&mut nodes_to_parse, &mut already_resolved, &nodes, &HashMap::new());

        assert_eq!(
            properties[0].value,
            PropertyValue::Size(StyleSize::Px(12.))
        );
        assert_eq!(
            properties[1].value,
            PropertyValue::Size(StyleSize::Px(12.))
        );
        assert_eq!(
            properties[2].value,
            PropertyValue::Size(StyleSize::Px(16.))
        );
    }

    #[test]
    fn resolves_variable_values_embedded_in_strings() {
        let variables = HashMap::from([("--size".to_string(), "12px".to_string())]);

        assert_eq!(
            resolve_variable_value("calc(var(--size) * 2)", &variables),
            "calc(12px * 2)"
        );
    }

    #[test]
    fn splits_space_ignoring_parentheses() {
        assert_eq!(
            split_ignoring_parentheses("repeat(2, 1fr) 20px".into(), ' ', &[]),
            vec!["repeat(2, 1fr)", "20px"]
        );
        assert_eq!(
            split_ignoring_parentheses("test>lol".into(), ' ', &['>']),
            vec!["test", ">", "lol"]
        );
    }
}

fn parse_justify_content(value: &str) -> StyleJustifyContent {
    match value {
        "auto" => StyleJustifyContent::Auto,
        "flex-start" => StyleJustifyContent::FlexStart,
        "flex-end" => StyleJustifyContent::FlexEnd,
        "center" => StyleJustifyContent::Center,
        "space-between" => StyleJustifyContent::SpaceBetween,
        "stretch" => StyleJustifyContent::Stretch,
        "space-evenly" => StyleJustifyContent::SpaceEvenly,
        _ => {
            println!(
                "Failed to parse style in parse_justify_content \"{}\"",
                value
            );
            StyleJustifyContent::FlexStart
        }
    }
}

fn parse_border_side_value(value: String) -> Result<BorderSideValue> {
    let parts: Vec<&str> = value.split(" ").collect();
    match parts.len() {
        1 => Ok(BorderSideValue {
            size: Some(parse_style_size(parts[0].to_string())?),
            color: None,
            style: None,
        }),
        2 => Ok(BorderSideValue {
            size: Some(parse_style_size(parts[0].to_string())?),
            style: Some(parse_border_style(parts[1].to_string())?),
            color: None,
        }),
        3 => Ok(BorderSideValue {
            size: Some(parse_style_size(parts[0].to_string())?),
            style: Some(parse_border_style(parts[1].to_string())?),
            color: Some(parse_color(parts[2].to_string())?),
        }),
        len => Err(anyhow!("Unexpected border side count: {}", len)),
    }
}

pub fn split_ignoring_parentheses(value: String, split_char: char, break_chars: &[char]) -> Vec<String> {
    let mut parentheses_depth = 0;
    let mut buffer = String::new();
    let mut result = vec![];
    let parentheses_start = '(';
    let parentheses_close = ')';
    let mut auto_break = false;
    for char in value.chars() {
        if char == parentheses_start {
            parentheses_depth += 1;
            buffer.push(char);
            auto_break = false;
            continue;
        }
        if char == parentheses_close {
            parentheses_depth -= 1;
            buffer.push(char);
            auto_break = false;
            continue;
        }
        if auto_break {
            result.push(buffer.clone());
            buffer = char.to_string();
            auto_break = false;
            continue;
        }
        if char == split_char && parentheses_depth == 0 {
            result.push(buffer.clone());
            buffer.clear();
            continue;
        }
        if break_chars.contains(&char) && parentheses_depth == 0 {
            result.push(buffer.clone());
            buffer = char.to_string();
            auto_break = true;
            continue;
        }
        buffer.push(char);
    }
    if !buffer.is_empty() {
        result.push(buffer.clone());
    }
    result
}

fn strip_prefix_and_suffix<'a>(value: &'a str, prefix: &'a str, suffix: &'a str) -> Option<&'a str> {
    if let Some(stripped) = value.strip_prefix(prefix) {
        stripped.strip_suffix(suffix)
    } else {
        None
    }
}

fn parse_grid_template_columns_inner_value(value: String) -> Result<GridTemplateColumnsValue> {
    if let Some(stripped) = strip_prefix_and_suffix(&value, "minmax(", ")") {
        let (min, max) = stripped.split_once(",").with_context(|| "Failed to split minmax value")?;
        let parsed_min = parse_grid_size(min.trim().to_string())?;
        let parsed_max = parse_grid_size(max.trim().to_string())?;
        Ok(GridTemplateColumnsValue::MinMax((parsed_min, parsed_max)))
    } else {
        Ok(GridTemplateColumnsValue::Size(parse_grid_size(value)?))
    }
}

fn parse_overflow(value: String) -> Result<PropertyValue> {
    match value.as_str() {
        "hidden" => Ok(PropertyValue::Overflow(Overflow::Hidden)),
        "visible" => Ok(PropertyValue::Overflow(Overflow::Visible)),
        _ => Err(anyhow!("Failed to parse overflow value: {}", value))
    }
}

fn parse_grid_template_columns_value(value: String) -> Result<PropertyValue> {
    let parts: Vec<String> = split_ignoring_parentheses(value, ' ', &[]);
    // TODO: Also support minmax etc. here
    let mut parsed: Vec<GridTemplateColumnsValue> = vec![];
    for p in parts {
        if let Some(stripped) = strip_prefix_and_suffix(&p, "repeat(", ")") {
            let (count, sizes) = stripped.split_once(",").with_context(|| format!("Failed to parse repeat: {}", stripped))?;
            let parsed_count = count.parse::<i32>().with_context(|| format!("Failed to parse count: {}", count))?;
            let sizes_split: Vec<&str> = sizes.trim().split(" ").collect();
            for _ in 0..parsed_count {
                for size in sizes_split.iter() {
                    parsed.push(parse_grid_template_columns_inner_value(size.trim().to_string())?);
                }
            }
            continue;
        }
        parsed.push(parse_grid_template_columns_inner_value(p)?);
    }
    Ok(PropertyValue::GridTemplateColumns(GridTemplateColumns::Values(parsed)))
}

fn parse_background(value: String) -> Result<PropertyValue> {
    let parts = split_ignoring_parentheses(value, ' ', &[]);
    let mut background = StyleBackground::Transparent;
    for part in parts {
        if let Some(stripped) = part.strip_prefix("url(") {
            if let Some(stripped) = stripped.strip_suffix(")") {
                let stripped = unquote(stripped);
                if let Some(data) = stripped.strip_prefix("data:") {
                    let (format, data) = data.split_once(',').with_context(|| "Failed to parse data url")?;
                    background = StyleBackground::DataUrl((format.to_string(), data.to_string()));
                } else {
                    //
                }
            }
        }
    }
    Ok(PropertyValue::ComplexBackground(StyleComplexBackground { background }))
}

pub fn parse_property_value(property: String, value: String) -> Result<(PropertyValue, bool)> {
    if let Some(stripped) = value.strip_suffix("!important") {
        return parse_property_value(property, stripped.trim().to_string()).and_then(|(value, _)| Ok((value, true)));
    }

    if property.starts_with("--") || value.contains("var(") {
        return Ok((PropertyValue::Raw(value), false));
    }

    Ok((match property.as_str() {
        "width" | "height" | "min-height" | "max-height" | "min-width" | "max-width" | "gap" |
        "margin-left" | "margin-top" | "margin-right" | "margin-bottom" | "font-size" | "left" |
        "top" | "right" | "bottom" | "padding-left" | "padding-top" | "padding-right" | "padding-bottom" |
        "border-left-width" | "border-top-width" | "border-right-width" | "border-bottom-width" |
        "border-width" | "padding-block-start" | "padding-block-end" | "padding-inline-start" | "padding-inline-end" =>
            PropertyValue::Size(parse_style_size(value)?),
        "margin" | "padding" | "inset" =>
            PropertyValue::CombinedSize(parse_combined_style(value, parse_style_size)?),
        "margin-inline" => PropertyValue::HorizontalCombinedSize(parse_two_axis_size(value)?),
        "padding-block" => PropertyValue::VerticalCombinedSize(parse_two_axis_size(value)?),
        "padding-inline" => PropertyValue::HorizontalCombinedSize(parse_two_axis_size(value)?),
        "background" => parse_background(value)?,
        "background-color" | "color" |
        "border-left-color" | "border-top-color" | "border-right-color" | "border-bottom-color" =>
            PropertyValue::Color(parse_color(value)?),
        "border-color" => PropertyValue::CombinedColor(parse_combined_style(value, parse_color)?),
        "display" => PropertyValue::Display(match value.as_str().trim() {
            "block" => Some(StyleDisplay::Block),
            "inline-block" => Some(StyleDisplay::InlineBlock),
            "inline" => Some(StyleDisplay::Inline),
            "flex" => Some(StyleDisplay::Flex),
            "inline-flex" => Some(StyleDisplay::InlineFlex),
            "grid" => Some(StyleDisplay::Grid),
            "none" => Some(StyleDisplay::None),
            _ => None
        }.with_context(|| "Failed to parse display")?),
        "position" => PropertyValue::Position(match value.as_str().trim() {
            "static" => Some(StylePosition::Static),
            "relative" => Some(StylePosition::Relative),
            "absolute" => Some(StylePosition::Absolute),
            "fixed" => Some(StylePosition::Fixed),
            _ => {
                println!("Failed to parse style position \"{}\"", value);
                None
            }
        }.with_context(|| "Failed to parse position")?),
        "text-align" => PropertyValue::Align(match value.as_str().trim() {
            "left" => Some(StyleAlign::Left),
            "center" => Some(StyleAlign::Center),
            "right" => Some(StyleAlign::Right),
            _ => None
        }.with_context(|| "Failed to parse text-align")?),
        "flex-shrink" | "flex-grow" => PropertyValue::Int(value.parse::<u32>()?),
        "flex" => {
            let parts: Vec<&str> = value.split(" ").collect();
            let mut grow = None;
            let mut shrink = None;
            // Flex-basis ignored for now
            match parts.len() {
                1 => {
                    // If it can be parsed as a u32, it refers to grow
                    if let Ok(value) = parts[0].parse::<u32>() {
                        grow = Some(value);
                    }
                    // Otherwise it refers to the flex-basis, which we don't yet handle
                }
                2 => {
                    grow = Some(parts[0].parse::<u32>()?);
                    if let Ok(value) = parts[1].parse::<u32>() {
                        shrink = Some(value);
                    }
                    // Otherwise it refers to the flex-basis, which we don't yet handle
                }
                3 => {
                    grow = Some(parts[0].parse::<u32>()?);
                    shrink = Some(parts[1].parse::<u32>()?);
                }
                _ => {}
            }
            PropertyValue::Flex { grow, shrink }
        },
        "justify-content" | "align-items" | "align-self" =>
            PropertyValue::JustifyContent(parse_justify_content(value.as_str())),
        "place-content" => {
            let parts: Vec<&str> = value.split(" ").collect();
            // align-content ignored for now
            match parts.len() {
                1 => PropertyValue::JustifyContent(parse_justify_content(parts[0].trim())),
                2 => PropertyValue::JustifyContent(parse_justify_content(parts[1].trim())),
                _ => PropertyValue::Raw(value),
            }
        }
        "place-items" => {
            let parts: Vec<&str> = value.split(" ").collect();
            // justify-items ignored for now
            match parts.len() {
                1 => PropertyValue::JustifyContent(parse_justify_content(parts[0].trim())),
                2 => PropertyValue::JustifyContent(parse_justify_content(parts[0].trim())),
                _ => PropertyValue::Raw(value),
            }
        }
        "flex-direction" => PropertyValue::FlexDirection(match value.as_str() {
            "row" => StyleFlexDirection::Row,
            "column" => StyleFlexDirection::Column,
            _ => Err(anyhow!(
                "Failed to parse style flex-direction \"{}\"",
                value
            ))?,
        }),
        "border-left-style" | "border-top-style" | "border-right-style" | "border-bottom-style" |
        "border-style" =>
            PropertyValue::BorderStyle(parse_border_style(value)?),
        "border-left" | "border-top" | "border-right" | "border-bottom" | "border" =>
            PropertyValue::BorderSide(parse_border_side_value(value)?),
        "grid-template-columns" => parse_grid_template_columns_value(value)?,
        "overflow" => parse_overflow(value)?,
        _ => {
            // println!("Failed to parse style \"{}\"", property);
            PropertyValue::Raw(value)
        }
    }, false))
}

fn apply_parsed_border_side(side: &mut StyleSizeAndColor, value: BorderSideValue) {
    if let Some(size) = value.size {
        side.size = size;
    }
    if let Some(color) = value.color {
        side.color = color;
    }
    if let Some(style) = value.style {
        side.style = style;
    }
}

pub fn apply_style_property(
    style: &mut Style,
    property: &Property,
) -> Result<()> {
    match (property.property.as_str(), property.value.clone()) {
        ("width", PropertyValue::Size(value)) => {
            style.width = value;
        }
        ("height", PropertyValue::Size(value)) => {
            style.height = value;
        }
        ("min-height", PropertyValue::Size(value)) => {
            style.min_height = value;
        }
        ("max-height", PropertyValue::Size(value)) => {
            style.max_height = value;
        }
        ("min-width", PropertyValue::Size(value)) => {
            style.min_width = value;
        }
        ("max-width", PropertyValue::Size(value)) => {
            style.max_width = value;
        }
        ("gap", PropertyValue::Size(value)) => {
            style.gap = value;
        }
        ("margin", PropertyValue::CombinedSize((top, right, bottom, left))) => {
            style.margin_top = top;
            style.margin_right = right;
            style.margin_bottom = bottom;
            style.margin_left = left;
        }
        ("margin-left", PropertyValue::Size(value)) => {
            style.margin_left = value;
        }
        ("margin-right", PropertyValue::Size(value)) => {
            style.margin_right = value;
        }
        ("margin-top", PropertyValue::Size(value)) => {
            style.margin_top = value;
        }
        ("margin-bottom", PropertyValue::Size(value)) => {
            style.margin_bottom = value;
        }
        // This assumes LTR for now
        ("margin-inline", PropertyValue::HorizontalCombinedSize((left, right))) => {
            style.margin_left = left;
            style.margin_right = right;
        },
        ("padding-block", PropertyValue::VerticalCombinedSize((top, bottom))) => {
            style.padding_top = top;
            style.padding_bottom = bottom;
        },
        ("padding-block-start", PropertyValue::Size(value)) => {
            style.padding_top = value;
        },
        ("padding-block-end", PropertyValue::Size(value)) => {
            style.padding_bottom = value;
        },
        ("padding-inline", PropertyValue::HorizontalCombinedSize((left, right))) => {
            style.padding_left = left;
            style.padding_right = right;
        },
        ("padding-inline-start", PropertyValue::Size(value)) => {
            style.padding_left = value;
        },
        ("padding-inline-end", PropertyValue::Size(value)) => {
            style.padding_right = value;
        },
        ("font-size", PropertyValue::Size(value)) => {
            style.font_size = value;
        }
        ("inset", PropertyValue::CombinedSize((top, right, bottom, left))) => {
            style.top = top;
            style.right = right;
            style.bottom = bottom;
            style.left = left;
        }
        ("left", PropertyValue::Size(value)) => {
            style.left = value;
        }
        ("right", PropertyValue::Size(value)) => {
            style.right = value;
        }
        ("top", PropertyValue::Size(value)) => {
            style.top = value;
        }
        ("bottom", PropertyValue::Size(value)) => {
            style.bottom = value;
        }
        ("padding", PropertyValue::CombinedSize((top, right, bottom, left))) => {
            style.padding_top = top;
            style.padding_right = right;
            style.padding_bottom = bottom;
            style.padding_left = left;
        }
        ("padding-left", PropertyValue::Size(value)) => {
            style.padding_left = value;
        }
        ("padding-right", PropertyValue::Size(value)) => {
            style.padding_right = value;
        }
        ("padding-top", PropertyValue::Size(value)) => {
            style.padding_top = value;
        }
        ("padding-bottom", PropertyValue::Size(value)) => {
            style.padding_bottom = value;
        }
        ("background", PropertyValue::ComplexBackground(background)) => {
            style.background = background.background;
            // TODO: Add more attribute mappings here
        },
        ("background" | "background-color", PropertyValue::Color(value)) => {
            style.background = value;
        }
        ("color", PropertyValue::Color(value)) => {
            style.color = value;
        }
        ("display", PropertyValue::Display(value)) => {
            style.display = value;
        }
        ("position", PropertyValue::Position(value)) => {
            style.position = value;
        }
        ("text-align", PropertyValue::Align(value)) => {
            style.text_align = value;
        }
        ("flex-shrink", PropertyValue::Int(value)) => {
            style.flex_shrink = value;
        }
        ("flex-grow", PropertyValue::Int(value)) => {
            style.flex_grow = value;
        }
        ("flex", PropertyValue::Flex { grow, shrink }) => {
            if let Some(grow) = grow {
                style.flex_grow = grow;
            }
            if let Some(shrink) = shrink {
                style.flex_shrink = shrink;
            }
        }
        ("justify-content", PropertyValue::JustifyContent(value)) => {
            style.justify_content = value;
        }
        ("align-items", PropertyValue::JustifyContent(value)) => {
            style.align_items = value;
        }
        ("align-self", PropertyValue::JustifyContent(value)) => {
            style.align_self = value;
        }
        ("place-content", PropertyValue::JustifyContent(value)) => {
            style.justify_content = value;
        }
        ("place-items", PropertyValue::JustifyContent(value)) => {
            style.align_items = value;
        }
        ("flex-direction", PropertyValue::FlexDirection(value)) => {
            style.flex_direction = value;
        }
        ("border-left-width", PropertyValue::Size(value)) => {
            style.border_left.size = value;
        }
        ("border-left-color", PropertyValue::Color(value)) => {
            style.border_left.color = value;
        }
        ("border-left-style", PropertyValue::BorderStyle(value)) => {
            style.border_left.style = value;
        }
        ("border-color", PropertyValue::CombinedColor((top, right, bottom, left))) => {
            style.border_top.color = top;
            style.border_right.color = right;
            style.border_bottom.color = bottom;
            style.border_left.color = left;
        }
        ("border-left", PropertyValue::BorderSide(value)) => {
            apply_parsed_border_side(&mut style.border_left, value);
        }
        ("border-top-width", PropertyValue::Size(value)) => {
            style.border_top.size = value;
        }
        ("border-top-color", PropertyValue::Color(value)) => {
            style.border_top.color = value;
        }
        ("border-top-style", PropertyValue::BorderStyle(value)) => {
            style.border_top.style = value;
        }
        ("border-top", PropertyValue::BorderSide(value)) => {
            apply_parsed_border_side(&mut style.border_top, value);
        }
        ("border-right-width", PropertyValue::Size(value)) => {
            style.border_right.size = value;
        }
        ("border-right-color", PropertyValue::Color(value)) => {
            style.border_right.color = value;
        }
        ("border-right-style", PropertyValue::BorderStyle(value)) => {
            style.border_right.style = value;
        }
        ("border-right", PropertyValue::BorderSide(value)) => {
            apply_parsed_border_side(&mut style.border_right, value);
        }
        ("border-bottom-width", PropertyValue::Size(value)) => {
            style.border_bottom.size = value;
        }
        ("border-bottom-color", PropertyValue::Color(value)) => {
            style.border_bottom.color = value;
        }
        ("border-bottom-style", PropertyValue::BorderStyle(value)) => {
            style.border_bottom.style = value;
        }
        ("border-bottom", PropertyValue::BorderSide(value)) => {
            apply_parsed_border_side(&mut style.border_bottom, value);
        }
        ("border", PropertyValue::BorderSide(value)) => {
            apply_parsed_border_side(&mut style.border_left, value.clone());
            apply_parsed_border_side(&mut style.border_top, value.clone());
            apply_parsed_border_side(&mut style.border_right, value.clone());
            apply_parsed_border_side(&mut style.border_bottom, value);
        }
        ("border-width", PropertyValue::Size(value)) => {
            style.border_left.size = value.clone();
            style.border_top.size = value.clone();
            style.border_right.size = value.clone();
            style.border_bottom.size = value;
        }
        ("border-style", PropertyValue::BorderStyle(value)) => {
            style.border_left.style = value.clone();
            style.border_top.style = value.clone();
            style.border_right.style = value.clone();
            style.border_bottom.style = value;
        }
        ("grid-template-columns", PropertyValue::GridTemplateColumns(columns)) => {
            style.grid_template_columns = columns;
        },
        ("overflow", PropertyValue::Overflow(overflow)) => {
            style.overflow = overflow;
        },
        (_, PropertyValue::Raw(_)) => {}
        (_, value) => {
            println!("Failed to apply style \"{}\" with value {:?}", property.property, value);
        }
    };
    Ok(())
}

pub fn get_parent_chain(nodes: &Vec<(usize, &Node)>, node_idx: usize, chain: &mut Vec<usize>) {
    let node = nodes[node_idx].1;
    chain.push(node_idx);
    if let Some(parent) = node.get_parent() {
        // Only save class names in chain
        if let Node::ClassName(_) = nodes[parent].1 {
            get_parent_chain(nodes, parent, chain)
        }
    }
}

pub fn get_parent_layer(nodes: &Vec<(usize, &Node)>, node_idx: usize) -> Option<usize> {
    let node = nodes[node_idx].1;
    if let Some(parent) = node.get_parent() {
        if let Node::Layer(_) = nodes[parent].1 {
            return Some(parent);
        } else {
            return get_parent_layer(nodes, parent)
        }
    }
    None
}

pub fn get_specificity_order(a_specificity: &[i32; 3], b_specificity: &[i32; 3]) -> Ordering {
    for idx in 0usize..3usize {
        if a_specificity[idx] > b_specificity[idx] {
            return Ordering::Greater; 
        }
        if a_specificity[idx] < b_specificity[idx] {
            return Ordering::Less; 
        }
    }
    Ordering::Equal
}

pub fn get_chain_order(a_chain: &Vec<usize>, b_chain: &Vec<usize>) -> Ordering {
    // At first parent which is different, compare and order ascending
    for (a, b) in a_chain.iter().rev().zip(b_chain.iter().rev()) {
        if a != b {
            return a.cmp(b);
        }
    }

    Ordering::Equal
}

pub fn parse_style(
    node_idx: usize,
    element: &HtmlElement,
    css_nodes: &Vec<Node>,
    parent_style: Option<&Style>,
    parent_variables: &mut HashMap<String, String>,
    collected_css_nodes: &HashMap<usize, Vec<usize>>,
    css_children_index: &HashMap<usize, Vec<usize>>,
    css_node_ranking: &HashMap<usize, usize>,
) -> Result<Style> {
    let mut style = get_base_style(&HtmlNode::Element(element.clone()), parent_style);
    let inline_nodes = get_inline_nodes(&element)?;
    let applicable_class_nodes = collected_css_nodes.get(&node_idx).cloned().unwrap_or_default();
    let mut applicable_class_properties = vec![];
    for class_node in applicable_class_nodes {
        let children = css_children_index.get(&class_node).unwrap();
        for c in children {
            let would = match css_nodes[*c] {
                Node::Property(_) | Node::Variable(_) => true,
                _ => false,
            };
            if would {
                applicable_class_properties.push(c);
            }
        }
    }
    applicable_class_properties.sort_by(|a, b| {
        let a_rank = css_node_ranking.get(&a).unwrap();
        let b_rank = css_node_ranking.get(&b).unwrap();
        a_rank.cmp(b_rank)
    });
    let mut nodes: Vec<(usize, Node)> = applicable_class_properties
        .iter()
        .map(|idx| (**idx, css_nodes[**idx].clone()))
        .collect();
    // This is a bit hacky, but we don't have an ID for inline nodes, but we also don't need one, so we just set it to usize::MAX
    nodes.append(&mut inline_nodes.into_iter().map(|node| (usize::MAX, node)).collect());
    let properties = resolve_node_variables(&mut nodes, parent_variables, css_nodes, css_node_ranking);
    style.variables = parent_variables.clone();
    for property in properties {
        if let Err(result) = apply_style_property(&mut style, &property) {
            println!(
                "Failed to apply property {:?} due to: {:?}",
                property, result
            );
        }
    }
    Ok(style)
}
