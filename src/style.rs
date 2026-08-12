use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display};
use std::rc::Rc;

use anyhow::{Context, Result, anyhow};
use palette::{FromColor, Hsl, Srgb};

use crate::css::{
    BorderSideValue, ClassNamePartAttribute, CssParser, MediaQuery, MediaQueryCriteria,
    MediaQueryCriteriaComparison, MediaQueryCriteriaValue, Node, Overflow, Property, PropertyValue,
    StyleComplexBackground, Variable, VariableTemplatePart, unquote,
};
use crate::parser::{Element as HtmlElement, Node as HtmlNode};
use crate::{VariableDefinitions, ViewportSize};

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
    Nesting(Vec<CalcExpression>),
    Solved(f32),
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
    Clamp {
        min: Box<StyleSize>,
        value: Box<StyleSize>,
        max: Box<StyleSize>,
    },
    Calc(Vec<CalcExpression>),
    FitContent,
    MinContent,
    MaxContent,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StyleBackground {
    Transparent,
    CurrentColor,
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
        self == StyleDisplay::InlineBlock
            || self == StyleDisplay::InlineFlex
            || self == StyleDisplay::Inline
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StyleJustifyContent {
    Auto,
    FlexStart,
    FlexEnd,
    Center,
    SpaceBetween,
    SpaceAround,
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
    Sticky,
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
    Auto,
    Px(i32),
    Rem(f32),
    Percent(f32),
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
pub enum StyleZIndex {
    Number(i32),
    Auto,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StylePointerEvents {
    None,
    Auto,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StyleVisibility {
    Visible,
    Hidden,
    Collapse,
}

impl StyleVisibility {
    pub fn is_visible(self) -> bool {
        self == StyleVisibility::Visible
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StyleTransformOperation {
    Translate { x: StyleSize, y: StyleSize },
}

#[derive(Debug, Clone, PartialEq)]
pub enum StyleTransform {
    None,
    Operations(Vec<StyleTransformOperation>),
}

pub fn format_css_number(value: f32) -> String {
    if value == -0.0 {
        "0".to_string()
    } else {
        value.to_string()
    }
}

fn calc_expression_to_css(expression: &[CalcExpression]) -> String {
    expression
        .iter()
        .map(|part| match part {
            CalcExpression::Size(size) => size.to_string(),
            CalcExpression::Operator(StyleCalcOperator::Plus) => "+".to_string(),
            CalcExpression::Operator(StyleCalcOperator::Minus) => "-".to_string(),
            CalcExpression::Operator(StyleCalcOperator::Divide) => "/".to_string(),
            CalcExpression::Operator(StyleCalcOperator::Multiply) => "*".to_string(),
            CalcExpression::Nesting(expression) => {
                format!("({})", calc_expression_to_css(expression))
            }
            CalcExpression::Solved(value) => format_css_number(*value),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

impl Display for StyleSize {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StyleSize::Auto => write!(formatter, "auto"),
            StyleSize::Px(value) => write!(formatter, "{}px", format_css_number(*value)),
            StyleSize::Em(value) => write!(formatter, "{}em", format_css_number(*value)),
            StyleSize::Rem(value) => write!(formatter, "{}rem", format_css_number(*value)),
            StyleSize::Percent(value) => write!(formatter, "{}%", format_css_number(*value)),
            StyleSize::Vh(value) => write!(formatter, "{value}vh"),
            StyleSize::Svh(value) => write!(formatter, "{value}svh"),
            StyleSize::Vw(value) => write!(formatter, "{value}vw"),
            StyleSize::Clamp { min, value, max } => {
                write!(formatter, "clamp({min}, {value}, {max})")
            }
            StyleSize::Calc(expression) => {
                write!(formatter, "calc({})", calc_expression_to_css(expression))
            }
            StyleSize::FitContent => write!(formatter, "fit-content"),
            StyleSize::MinContent => write!(formatter, "min-content"),
            StyleSize::MaxContent => write!(formatter, "max-content"),
        }
    }
}

impl StyleBackground {
    pub fn to_css_color(&self) -> String {
        match self {
            StyleBackground::DataUrl(_) => "rgba(0, 0, 0, 0)".to_string(),
            _ => self.to_string(),
        }
    }

    pub fn to_css_image(&self) -> String {
        match self {
            StyleBackground::DataUrl(_) => self.to_string(),
            _ => "none".to_string(),
        }
    }
}

impl Display for StyleBackground {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StyleBackground::Transparent => write!(formatter, "rgba(0, 0, 0, 0)"),
            StyleBackground::CurrentColor => write!(formatter, "currentcolor"),
            StyleBackground::Hex(value) => {
                let red = value >> 24;
                let green = value >> 16 & 0xff;
                let blue = value >> 8 & 0xff;
                let alpha = value & 0xff;
                if alpha == 0xff {
                    write!(formatter, "rgb({red}, {green}, {blue})")
                } else {
                    write!(
                        formatter,
                        "rgba({red}, {green}, {blue}, {})",
                        format_css_number(alpha as f32 / 255.0)
                    )
                }
            }
            StyleBackground::DataUrl((format, data)) => {
                write!(formatter, "url(\"data:{format},{data}\")")
            }
        }
    }
}

macro_rules! impl_css_keyword {
    ($type:ty, $($variant:path => $value:literal),+ $(,)?) => {
        impl Display for $type {
            fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str(match self {
                    $($variant => $value),+
                })
            }
        }
    };
}

impl_css_keyword!(
    StyleDisplay,
    StyleDisplay::None => "none",
    StyleDisplay::Block => "block",
    StyleDisplay::InlineBlock => "inline-block",
    StyleDisplay::Inline => "inline",
    StyleDisplay::InlineFlex => "inline-flex",
    StyleDisplay::Flex => "flex",
    StyleDisplay::Grid => "grid",
);
impl_css_keyword!(
    StyleJustifyContent,
    StyleJustifyContent::Auto => "auto",
    StyleJustifyContent::FlexStart => "flex-start",
    StyleJustifyContent::FlexEnd => "flex-end",
    StyleJustifyContent::Center => "center",
    StyleJustifyContent::SpaceBetween => "space-between",
    StyleJustifyContent::SpaceAround => "space-around",
    StyleJustifyContent::Stretch => "stretch",
    StyleJustifyContent::SpaceEvenly => "space-evenly",
);
impl_css_keyword!(
    StyleFlexDirection,
    StyleFlexDirection::Row => "row",
    StyleFlexDirection::Column => "column",
);
impl_css_keyword!(
    StylePosition,
    StylePosition::Static => "static",
    StylePosition::Relative => "relative",
    StylePosition::Absolute => "absolute",
    StylePosition::Fixed => "fixed",
    StylePosition::Sticky => "sticky",
);
impl_css_keyword!(
    StyleAlign,
    StyleAlign::Left => "left",
    StyleAlign::Center => "center",
    StyleAlign::Right => "right",
);
impl_css_keyword!(
    StyleBorderStyle,
    StyleBorderStyle::None => "none",
    StyleBorderStyle::Solid => "solid",
);
impl_css_keyword!(
    Overflow,
    Overflow::Hidden => "hidden",
    Overflow::Visible => "visible",
    Overflow::Auto => "auto",
    Overflow::Scroll => "scroll",
    Overflow::Clip => "clip",
);
impl_css_keyword!(
    StylePointerEvents,
    StylePointerEvents::None => "none",
    StylePointerEvents::Auto => "auto",
);
impl_css_keyword!(
    StyleVisibility,
    StyleVisibility::Visible => "visible",
    StyleVisibility::Hidden => "hidden",
    StyleVisibility::Collapse => "collapse",
);

impl Display for StyleZIndex {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StyleZIndex::Number(value) => value.fmt(formatter),
            StyleZIndex::Auto => formatter.write_str("auto"),
        }
    }
}

impl Display for StyleTransform {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StyleTransform::None => formatter.write_str("none"),
            StyleTransform::Operations(operations) => formatter.write_str(
                &operations
                    .iter()
                    .map(|operation| match operation {
                        StyleTransformOperation::Translate { x, y } => {
                            format!("translate({x}, {y})")
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" "),
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Style {
    pub width: StyleSize,
    pub height: StyleSize,
    pub background: StyleBackground,
    pub display: StyleDisplay,
    pub flex_shrink: u32,
    pub flex_grow: u32,
    pub flex_basis: StyleSize,
    pub order: i32,
    pub justify_content: StyleJustifyContent,
    pub justify_items: StyleJustifyContent,
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
    pub variables: Rc<HashMap<usize, String>>,
    pub font_size: StyleSize,
    pub line_height: StyleSize,
    pub align_self: StyleJustifyContent,
    pub border_left: StyleSizeAndColor,
    pub border_top: StyleSizeAndColor,
    pub border_right: StyleSizeAndColor,
    pub border_bottom: StyleSizeAndColor,
    pub grid_template_columns: GridTemplateColumns,
    pub grid_template_rows: GridTemplateColumns,
    pub grid_column_span: u32,
    pub overflow_x: Overflow,
    pub overflow_y: Overflow,
    pub z_index: StyleZIndex,
    pub pointer_events: StylePointerEvents,
    pub opacity: f32,
    pub visibility: StyleVisibility,
    pub transform: StyleTransform,
    pub border_radius_top_left: StyleSize,
    pub border_radius_top_right: StyleSize,
    pub border_radius_bottom_right: StyleSize,
    pub border_radius_bottom_left: StyleSize,
}

impl Style {
    pub fn clone_without_variables(&self) -> Self {
        Style {
            width: self.width.clone(),
            height: self.height.clone(),
            background: self.background.clone(),
            display: self.display,
            flex_shrink: self.flex_shrink,
            flex_grow: self.flex_grow,
            flex_basis: self.flex_basis.clone(),
            order: self.order,
            justify_content: self.justify_content,
            justify_items: self.justify_items,
            align_items: self.align_items,
            flex_direction: self.flex_direction,
            gap: self.gap.clone(),
            margin_left: self.margin_left.clone(),
            margin_right: self.margin_right.clone(),
            margin_top: self.margin_top.clone(),
            margin_bottom: self.margin_bottom.clone(),
            padding_left: self.padding_left.clone(),
            padding_right: self.padding_right.clone(),
            padding_top: self.padding_top.clone(),
            padding_bottom: self.padding_bottom.clone(),
            color: self.color.clone(),
            min_height: self.min_height.clone(),
            max_height: self.max_height.clone(),
            min_width: self.min_width.clone(),
            max_width: self.max_width.clone(),
            position: self.position,
            left: self.left.clone(),
            right: self.right.clone(),
            top: self.top.clone(),
            bottom: self.bottom.clone(),
            text_align: self.text_align,
            variables: Rc::new(HashMap::new()),
            font_size: self.font_size.clone(),
            line_height: self.line_height.clone(),
            align_self: self.align_self,
            border_left: self.border_left.clone(),
            border_top: self.border_top.clone(),
            border_right: self.border_right.clone(),
            border_bottom: self.border_bottom.clone(),
            grid_template_columns: self.grid_template_columns.clone(),
            grid_template_rows: self.grid_template_rows.clone(),
            grid_column_span: self.grid_column_span,
            overflow_x: self.overflow_x.clone(),
            overflow_y: self.overflow_y.clone(),
            z_index: self.z_index.clone(),
            pointer_events: self.pointer_events.clone(),
            opacity: self.opacity,
            visibility: self.visibility,
            transform: self.transform.clone(),
            border_radius_top_left: self.border_radius_top_left.clone(),
            border_radius_top_right: self.border_radius_top_right.clone(),
            border_radius_bottom_right: self.border_radius_bottom_right.clone(),
            border_radius_bottom_left: self.border_radius_bottom_left.clone(),
        }
    }
}

pub fn get_base_style(node: &HtmlNode, parent_style: Option<&Style>) -> Style {
    let implied_text_align = parent_style
        .clone()
        .and_then(|v| Some(v.text_align))
        .unwrap_or(StyleAlign::Left);
    Style {
        width: match node {
            HtmlNode::Element(element) => {
                if let Some(width) = element.attributes.get_str(&"width".to_string()) {
                    parse_style_size(width.as_ref()).unwrap()
                } else {
                    match element.tag.as_str() {
                        "br" => StyleSize::Px(0.),
                        "input" => match element.attributes.get_str(&"type".to_string()).as_deref()
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
                if let Some(height) = element.attributes.get_str(&"height".to_string()) {
                    parse_style_size(height.as_ref()).unwrap()
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
            HtmlNode::Element(element) => {
                if element.attributes.contains_key("hidden") {
                    StyleDisplay::None
                } else {
                    match element.tag.as_str() {
                        "head" | "script" | "style" | "noscript" => StyleDisplay::None,
                        "button" | "input" => {
                            if element
                                .attributes
                                .get_str("type")
                                .is_some_and(|v| v == "hidden")
                            {
                                StyleDisplay::None
                            } else {
                                StyleDisplay::InlineBlock
                            }
                        }
                        "span" | "img" | "a" => StyleDisplay::InlineBlock,
                        "br" | "code" => StyleDisplay::Inline,
                        _ => StyleDisplay::Block,
                    }
                }
            }
            HtmlNode::Text(_) => StyleDisplay::Inline,
            HtmlNode::Comment(_) => StyleDisplay::None,
        },
        flex_shrink: 1,
        flex_grow: 0,
        flex_basis: StyleSize::Auto,
        order: 0,
        justify_content: StyleJustifyContent::FlexStart,
        justify_items: StyleJustifyContent::Stretch,
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
        variables: Rc::new(HashMap::new()),
        font_size: parent_style
            .clone()
            .and_then(|v| Some(v.font_size.clone()))
            .unwrap_or(StyleSize::Px(16.)),
        line_height: parent_style
            .clone()
            .and_then(|v| Some(v.line_height.clone()))
            .unwrap_or(StyleSize::Auto),
        align_self: StyleJustifyContent::Auto,
        // TODO: This should default to currentColor
        border_left: StyleSizeAndColor {
            color: StyleBackground::Hex(0xFF_FF_FF_FF),
            size: StyleSize::Px(3.),
            style: StyleBorderStyle::None,
        },
        border_top: StyleSizeAndColor {
            color: StyleBackground::Hex(0xFF_FF_FF_FF),
            size: StyleSize::Px(3.),
            style: StyleBorderStyle::None,
        },
        border_right: StyleSizeAndColor {
            color: StyleBackground::Hex(0xFF_FF_FF_FF),
            size: StyleSize::Px(3.),
            style: StyleBorderStyle::None,
        },
        border_bottom: StyleSizeAndColor {
            color: StyleBackground::Hex(0xFF_FF_FF_FF),
            size: StyleSize::Px(3.),
            style: StyleBorderStyle::None,
        },
        grid_template_columns: GridTemplateColumns::None,
        grid_template_rows: GridTemplateColumns::None,
        grid_column_span: 1,
        overflow_x: Overflow::Visible,
        overflow_y: Overflow::Visible,
        z_index: StyleZIndex::Auto,
        pointer_events: StylePointerEvents::Auto,
        opacity: parent_style.map(|v| v.opacity).unwrap_or(1.0),
        visibility: parent_style
            .map(|style| style.visibility)
            .unwrap_or(StyleVisibility::Visible),
        transform: StyleTransform::None,
        border_radius_top_left: StyleSize::Px(0.),
        border_radius_top_right: StyleSize::Px(0.),
        border_radius_bottom_right: StyleSize::Px(0.),
        border_radius_bottom_left: StyleSize::Px(0.),
    }
}

fn parse_z_index(value: String) -> Result<StyleZIndex> {
    if value == "auto" {
        return Ok(StyleZIndex::Auto);
    }

    if let Ok(parsed) = value.parse::<i32>() {
        return Ok(StyleZIndex::Number(parsed));
    }

    Err(anyhow!("Failed to parse z-index: {}", value))
}

fn parse_poiner_events(value: String) -> Result<StylePointerEvents> {
    match value.as_str() {
        "auto" => Ok(StylePointerEvents::Auto),
        "none" => Ok(StylePointerEvents::None),
        _ => Err(anyhow!("Failed to parse pointer-events: {}", value)),
    }
}

fn parse_two_axis_size(value: String) -> Result<(StyleSize, StyleSize)> {
    let values: Vec<StyleSize> = split_ignoring_parentheses(value.clone(), ' ', &[])
        .into_iter()
        .map(|s| parse_style_size(s.to_string()))
        .collect::<Result<Vec<StyleSize>>>()?;

    match values.len() {
        1 => Ok((values[0].clone(), values[0].clone())),
        2 => Ok((values[0].clone(), values[1].clone())),
        _ => Err(anyhow!("Failed to parse inline size {}", value)),
    }
}

fn split_transform_args(value: &str) -> Vec<String> {
    let comma_parts: Vec<String> = split_ignoring_parentheses(value.to_string(), ',', &[])
        .into_iter()
        .map(|part| part.trim().to_string())
        .filter(|part| !part.is_empty())
        .collect();
    if comma_parts.len() > 1 {
        comma_parts
    } else {
        split_ignoring_parentheses(value.to_string(), ' ', &[])
            .into_iter()
            .map(|part| part.trim().to_string())
            .filter(|part| !part.is_empty())
            .collect()
    }
}

fn parse_transform_operation(name: &str, args: &str) -> Result<Option<StyleTransformOperation>> {
    let parts = split_transform_args(args);
    match name.to_ascii_lowercase().as_str() {
        "translate" => {
            if parts.is_empty() || parts.len() > 2 {
                return Ok(None);
            }
            Ok(Some(StyleTransformOperation::Translate {
                x: parse_style_size(&parts[0])?,
                y: parts
                    .get(1)
                    .map(|part| parse_style_size(part))
                    .transpose()?
                    .unwrap_or(StyleSize::Px(0.)),
            }))
        }
        "translatex" => {
            if parts.len() != 1 {
                return Ok(None);
            }
            Ok(Some(StyleTransformOperation::Translate {
                x: parse_style_size(&parts[0])?,
                y: StyleSize::Px(0.),
            }))
        }
        "translatey" => {
            if parts.len() != 1 {
                return Ok(None);
            }
            Ok(Some(StyleTransformOperation::Translate {
                x: StyleSize::Px(0.),
                y: parse_style_size(&parts[0])?,
            }))
        }
        "translate3d" => {
            if parts.len() != 3 {
                return Ok(None);
            }
            Ok(Some(StyleTransformOperation::Translate {
                x: parse_style_size(&parts[0])?,
                y: parse_style_size(&parts[1])?,
            }))
        }
        _ => Ok(None),
    }
}

fn parse_transform(value: &str) -> Result<Option<StyleTransform>> {
    let original = value.trim();
    if original == "none" {
        return Ok(Some(StyleTransform::None));
    }

    let mut operations = vec![];
    for function in split_ignoring_parentheses(original.to_string(), ' ', &[]) {
        let function = function.trim();
        if function.is_empty() {
            continue;
        }
        let Some((name, args)) = function.split_once('(') else {
            return Ok(None);
        };
        let name = name.trim();
        let Some(args) = args.strip_suffix(')') else {
            return Ok(None);
        };
        if name.is_empty() {
            return Ok(None);
        }
        let Some(operation) = parse_transform_operation(name, args)? else {
            return Ok(None);
        };
        operations.push(operation);
    }

    if operations.is_empty() {
        Ok(None)
    } else {
        Ok(Some(StyleTransform::Operations(operations)))
    }
}

fn parse_translate(value: &str) -> Result<Option<StyleTransform>> {
    if value.trim() == "none" {
        return Ok(Some(StyleTransform::None));
    }

    Ok(parse_transform_operation("translate", value)?
        .map(|operation| StyleTransform::Operations(vec![operation])))
}

fn parse_combined_style<T, F>(value: String, parse: F) -> Result<(T, T, T, T)>
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

fn add_part_to_calc(parts: &mut Vec<CalcExpression>, part: CalcExpression, nesting: i32) {
    if nesting > 0 {
        match parts.last_mut() {
            Some(CalcExpression::Nesting(parts)) => parts.push(part),
            _ => parts.push(part),
        };
    } else {
        parts.push(part);
    }
}

fn flush_calc_value(
    buffer: &mut String,
    parts: &mut Vec<CalcExpression>,
    nesting: i32,
) -> Result<()> {
    if buffer.len() > 0 {
        let size = if let Ok(parsed) = buffer.parse::<f32>() {
            CalcExpression::Solved(parsed)
        } else {
            CalcExpression::Size(parse_style_size(buffer.clone())?)
        };
        buffer.clear();
        add_part_to_calc(parts, size, nesting);
    }
    Ok(())
}

const CALC_NUMBER_CHARS: [char; 11] = ['.', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];

pub fn parse_calc(value: &str) -> Result<StyleSize> {
    let mut parts: Vec<CalcExpression> = vec![];
    let mut buffer = String::new();
    // Remove whitespace
    let mut value = value.to_string();
    value.retain(|c| !c.is_whitespace());
    let mut last_numberish = false;
    let mut nesting = 0;
    for char in value.chars() {
        if char == '(' {
            nesting += 1;
            if buffer == "calc" {
                buffer.clear();
            } else {
                flush_calc_value(&mut buffer, &mut parts, nesting)?;
            }
            add_part_to_calc(&mut parts, CalcExpression::Nesting(vec![]), nesting);
        } else if char == ')' {
            flush_calc_value(&mut buffer, &mut parts, nesting)?;
            nesting -= 1;
        } else if let Some(operator) = extract_operator(char)
            && last_numberish
        {
            flush_calc_value(&mut buffer, &mut parts, nesting)?;
            add_part_to_calc(&mut parts, operator, nesting);
            last_numberish = false;
        } else {
            if char != ' ' && CALC_NUMBER_CHARS.contains(&char) {
                last_numberish = true;
            }
            buffer.push(char);
        }
    }
    flush_calc_value(&mut buffer, &mut parts, nesting)?;
    Ok(StyleSize::Calc(parts))
}

fn parse_size_number(value: &str) -> Result<f32> {
    Ok(value
        .parse::<f32>()
        .with_context(|| format!("Failed to parse size value: {}", value))?)
}

fn parse_clamp_size_part(value: &str) -> Result<StyleSize> {
    let value = value.trim();
    if value.contains(' ') || value.contains('+') || value.contains('*') || value.contains('/') {
        parse_calc(value)
    } else {
        parse_style_size(value.to_string())
    }
}

fn parse_style_size(value: impl AsRef<str>) -> Result<StyleSize> {
    let value = value.as_ref();
    if value == "auto" {
        return Ok(StyleSize::Auto);
    }
    if value == "fit-content" {
        return Ok(StyleSize::FitContent);
    }
    if value == "min-content" {
        return Ok(StyleSize::MinContent);
    }
    if value == "max-content" {
        return Ok(StyleSize::MaxContent);
    }
    if let Some(value) = strip_prefix_and_suffix(&value, "clamp(", ")") {
        let parts = split_ignoring_parentheses(value.to_string(), ',', &[]);
        if parts.len() == 3 {
            return Ok(StyleSize::Clamp {
                min: Box::new(parse_clamp_size_part(&parts[0])?),
                value: Box::new(parse_clamp_size_part(&parts[1])?),
                max: Box::new(parse_clamp_size_part(&parts[2])?),
            });
        }
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
    if value.ends_with("dvh") {
        let dvh = value
            .strip_suffix("dvh")
            .with_context(|| "Failed to strip dvh")?
            .trim();
        return Ok(StyleSize::Vh(parse_size_number(dvh)? as i32));
    }
    if value.ends_with("lvh") {
        let lvh = value
            .strip_suffix("lvh")
            .with_context(|| "Failed to strip lvh")?
            .trim();
        return Ok(StyleSize::Vh(parse_size_number(lvh)? as i32));
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
    let adjusted = if value.starts_with('.') {
        format!("0{}", value)
    } else {
        value.to_string()
    };
    if let Ok(parsed) = adjusted.parse::<f32>() {
        return Ok(StyleSize::Px(parsed));
    }
    println!("Failed to parse style size \"{}\"", value);
    Ok(StyleSize::Auto)
}

fn parse_line_height(value: String) -> Result<StyleSize> {
    let value = value.trim();
    if value == "normal" {
        return Ok(StyleSize::Auto);
    }

    let adjusted = if value.starts_with('.') {
        format!("0{}", value)
    } else {
        value.to_string()
    };
    if let Ok(parsed) = adjusted.parse::<f32>() {
        return Ok(StyleSize::Em(parsed));
    }

    parse_style_size(value)
}

fn parse_grid_size(value: String) -> Result<GridColumnSize> {
    if value == "auto" {
        return Ok(GridColumnSize::Auto);
    }
    if value.ends_with("%") {
        let percentage = value
            .strip_suffix("%")
            .with_context(|| "Failed to strip percentage")?
            .trim();
        return Ok(GridColumnSize::Percent(parse_size_number(percentage)?));
    }
    if value.ends_with("px") {
        let px = value
            .strip_suffix("px")
            .with_context(|| "Failed to strip px")?
            .trim();
        return Ok(GridColumnSize::Px(parse_size_number(px)? as i32));
    }
    if value.ends_with("rem") {
        let rem = value
            .strip_suffix("rem")
            .with_context(|| "Failed to strip rem")?
            .trim();
        return Ok(GridColumnSize::Rem(parse_size_number(rem)?));
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
    Err(anyhow!("Failed to parse grid size value \"{}\"", value))
}

fn get_inline_nodes(element: &HtmlElement) -> Result<Vec<Node>> {
    let style_str = element.attributes.get_str("style");
    match style_str {
        Some(style) => {
            let mut inline_parser = CssParser::new_inline();
            inline_parser.parse(&style)?;
            Ok(inline_parser.nodes)
        }
        None => Ok(vec![]),
    }
}

pub fn element_matched_attributes(
    element: &HtmlElement,
    attributes: &Vec<ClassNamePartAttribute>,
) -> bool {
    for attribute in attributes.iter() {
        match attribute {
            ClassNamePartAttribute::Key(key) => {
                if !element.attributes.contains_key(key) {
                    return false;
                }
            }
            ClassNamePartAttribute::KeyValue((key, value, like, starts_with)) => {
                if element
                    .attributes
                    .get_str(key)
                    .is_none_or(|v| match (like, starts_with) {
                        (true, true) => unreachable!(),
                        (false, true) => !v.starts_with(value),
                        (true, false) => !v.contains(value),
                        (false, false) => v.as_ref() != value,
                    })
                {
                    return false;
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

pub fn media_query_matches(query: &MediaQuery, window_size: &ViewportSize) -> bool {
    query.criterias.iter().all(|q| {
        match q {
            // Media queries REM are not resolved against the font-size configured by CSS, but the default in the browser, which we hard-code to 16
            MediaQueryCriteria::Feature(feature) => match (
                feature.property.as_str(),
                feature.comparison.clone(),
                feature.value.clone(),
            ) {
                // Default to dark mode
                (
                    "prefers-color-scheme",
                    MediaQueryCriteriaComparison::Is,
                    MediaQueryCriteriaValue::String(value),
                ) => value == "dark",
                (
                    "min-width",
                    MediaQueryCriteriaComparison::Is,
                    MediaQueryCriteriaValue::Px(px),
                ) => window_size.width >= px as u32,
                (
                    "min-width",
                    MediaQueryCriteriaComparison::Is,
                    MediaQueryCriteriaValue::Rem(rem),
                ) => window_size.width >= rem as u32 * 16,
                (
                    "max-width",
                    MediaQueryCriteriaComparison::Is,
                    MediaQueryCriteriaValue::Px(px),
                ) => window_size.width < px as u32,
                (
                    "width",
                    MediaQueryCriteriaComparison::MoreOrEqual,
                    MediaQueryCriteriaValue::Px(px),
                ) => window_size.width >= px as u32,
                (
                    "width",
                    MediaQueryCriteriaComparison::MoreOrEqual,
                    MediaQueryCriteriaValue::Rem(rem),
                ) => window_size.width >= rem as u32 * 16,
                (
                    "width",
                    MediaQueryCriteriaComparison::LessOrEqual,
                    MediaQueryCriteriaValue::Px(px),
                ) => window_size.width <= px as u32,
                (
                    "width",
                    MediaQueryCriteriaComparison::LessOrEqual,
                    MediaQueryCriteriaValue::Rem(rem),
                ) => window_size.width <= rem as u32 * 16,
                (_, _, _) => {
                    // println!("Unsupported media query property: {} {:?} {:?}", p, c, v);
                    false
                }
            },
            MediaQueryCriteria::NotAllAnd(criterias) => !media_query_matches(
                &MediaQuery {
                    criterias: criterias.clone(),
                    parent: None,
                },
                window_size,
            ),
            MediaQueryCriteria::Screen => true,
            MediaQueryCriteria::Print => false,
            MediaQueryCriteria::All => true,
            MediaQueryCriteria::Unsupported => false,
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
        .get_str("class")
        .map(|v| v.into_owned())
        .unwrap_or_default()
        .split(" ")
        .map(|s| s.to_string())
        .collect();

    element_classes
}

fn rgba_to_hex((r, g, b, a): (u8, u8, u8, u8)) -> u32 {
    ((r as u32) << 24) | ((g as u32) << 16) | ((b as u32) << 8) | (a as u32)
}

fn parse_percent(value: &str) -> Result<f32> {
    let Some(value) = value.trim().strip_suffix('%') else {
        return Err(anyhow!("Expected percentage, got {}", value));
    };
    Ok(value.parse::<f32>()? / 100.0)
}

fn parse_alpha(value: &str) -> Result<u8> {
    let value = value.trim();
    let parsed = if value.ends_with('%') {
        parse_percent(value)?
    } else {
        value.parse::<f32>()?
    };
    Ok((parsed.clamp(0.0, 1.0) * 255.0).round() as u8)
}

fn parse_hsl_color(raw: &str) -> Result<StyleBackground> {
    let cleaned = raw.strip_suffix(')').unwrap_or(raw);
    let (hsl, alpha) = if let Some((hsl, alpha)) = cleaned.split_once('/') {
        (hsl.trim(), Some(alpha.trim()))
    } else {
        (cleaned.trim(), None)
    };
    let mut parts = hsl
        .split([',', ' '])
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>();
    let alpha = match parts.len() {
        3 => alpha.map(parse_alpha).transpose()?.unwrap_or(255),
        4 => parse_alpha(parts.pop().unwrap())?,
        _ => return Err(anyhow!("Invalid HSL string: {}", hsl)),
    };
    let hue = parts[0].trim_end_matches("deg").parse::<f32>()?;
    let saturation = parse_percent(parts[1])?;
    let lightness = parse_percent(parts[2])?;
    let hsl = Hsl::new_srgb(hue, saturation, lightness);
    let rgb: Srgb<u8> = Srgb::from_color(hsl).into_format();
    Ok(StyleBackground::Hex(rgba_to_hex((
        rgb.red, rgb.green, rgb.blue, alpha,
    ))))
}

// TODO: Come back to this and add a more complete implementation
fn parse_color_mix(raw: &str) -> Result<StyleBackground> {
    let cleaned = raw.strip_suffix(')').unwrap_or(raw).trim();
    let rest = cleaned
        .strip_prefix("in oklab,")
        .or_else(|| cleaned.strip_prefix("in srgb,"))
        .ok_or_else(|| anyhow!("Unsupported color-mix space: {}", raw))?;
    let Some((color_and_percentage, transparent)) = rest.rsplit_once(',') else {
        return Err(anyhow!("Unsupported color-mix: {}", raw));
    };
    if transparent.trim() != "transparent" {
        return Err(anyhow!("Unsupported color-mix: {}", raw));
    }

    let color_and_percentage = color_and_percentage.trim();
    let (color, percentage) = if let Some(end) = color_and_percentage.rfind(')') {
        color_and_percentage.split_at(end + 1)
    } else {
        color_and_percentage
            .rsplit_once(' ')
            .ok_or_else(|| anyhow!("Expected color and mix percentage, got {}", raw))?
    };
    let percentage = percentage.trim();
    if !percentage.ends_with('%') {
        return Err(anyhow!("Expected color and mix percentage, got {}", raw));
    }

    let mix = parse_percent(percentage)?;
    match parse_color(color.to_string())? {
        StyleBackground::Hex(hex) => {
            let alpha = ((hex & 0xFF) as f32 * mix).round() as u32;
            Ok(StyleBackground::Hex((hex & 0xFF_FF_FF_00) | alpha.min(255)))
        }
        StyleBackground::Transparent => Ok(StyleBackground::Transparent),
        _ => Err(anyhow!("Unsupported color-mix color: {}", color)),
    }
}

pub(crate) fn parse_color(value: String) -> Result<StyleBackground> {
    let value = value.trim();
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
    } else if let Some(raw) = value.strip_prefix("rgba(").or(value.strip_prefix("rgb(")) {
        let cleaned: &str = raw.strip_suffix(")").unwrap_or(raw);
        let (rgba, mut alpha) = if let Some((rgba, alpha)) = cleaned.split_once("/") {
            (rgba.trim(), Some(alpha.trim()))
        } else {
            (cleaned.trim(), None)
        };
        let mut parts: Vec<&str> = rgba
            .split([',', ' '])
            .filter(|str| !str.is_empty())
            .collect();
        match parts.len() {
            3 => {}
            4 => {
                alpha = Some(parts[3]);
                parts = parts[..3].to_vec();
            }
            _ => panic!("Invalid RGBA string: {}", rgba),
        }
        let parsed_parts: Vec<f32> = parts
            .iter()
            .take(3)
            .filter_map(|part| part.trim().parse::<f32>().ok())
            .collect();
        let alpha = if let Some(alpha) = alpha {
            (alpha.parse::<f32>()?.clamp(0.0, 1.0) * 255.0).round() as u8
        } else {
            255
        };
        if parsed_parts.len() != 3 {
            panic!("Invalid RGBA string: {}", rgba);
        }
        let hex = rgba_to_hex((
            parsed_parts[0] as u8,
            parsed_parts[1] as u8,
            parsed_parts[2] as u8,
            alpha,
        ));
        Ok(StyleBackground::Hex(hex))
    } else if let Some(raw) = value.strip_prefix("hsla(").or(value.strip_prefix("hsl(")) {
        parse_hsl_color(raw)
    } else if let Some(raw) = value.strip_prefix("color-mix(") {
        parse_color_mix(raw)
    } else {
        match value.to_ascii_lowercase().as_str() {
            "black" | "buttontext" | "canvastext" | "linktext" => {
                Ok(StyleBackground::Hex(0x00_00_00_FF))
            }
            "white" | "buttonface" | "selecteditemtext" => Ok(StyleBackground::Hex(0xFF_FF_FF_FF)),
            "gray" | "grey" | "graytext" | "buttonborder" => {
                Ok(StyleBackground::Hex(0x80_80_80_FF))
            }
            "highlight" | "selecteditem" => Ok(StyleBackground::Hex(0x33_99_FF_FF)),
            "transparent" | "none" => Ok(StyleBackground::Transparent),
            "currentcolor" => Ok(StyleBackground::CurrentColor),
            _ => Err(anyhow!("Failed to parse color \"{}\"", value)),
        }
    }
}

fn parse_variable_template(value: &str) -> Vec<VariableTemplatePart> {
    let mut out = vec![];
    let mut buffer = String::new();
    let mut inside_depth = 0;
    for char in value.trim().chars() {
        if char == ')' {
            inside_depth -= 1;
            if inside_depth == 0 {
                let collected: String = buffer.drain(..).collect();
                let (name, default) = if let Some(collected) = collected.split_once(",") {
                    let default_parts = parse_variable_template(collected.1.trim());
                    (collected.0.trim().to_owned(), Some(default_parts))
                } else {
                    (collected.trim().to_string(), None)
                };
                out.push(VariableTemplatePart::Var((name, default)));
                buffer.clear();
                continue;
            }
        }
        buffer.push(char);
        if let Some(stripped) = buffer.strip_suffix("var(") {
            if inside_depth == 0 {
                if stripped.len() > 0 {
                    out.push(VariableTemplatePart::Text(stripped.to_string()));
                }
                buffer.clear();
            }
            inside_depth += 1;
        } else if char == '(' && inside_depth > 0 {
            inside_depth += 1;
        }
    }
    if buffer.len() > 0 {
        out.push(VariableTemplatePart::Text(buffer));
    }
    out
}

fn resolve_node_variable(
    value: &PropertyValue,
    map: &HashMap<String, PropertyValue>,
    parent_variables: &Rc<HashMap<usize, String>>,
    variable_definitions: &VariableDefinitions,
) -> Option<String> {
    resolve_node_variable_inner(
        value,
        map,
        parent_variables,
        variable_definitions,
        &mut HashSet::new(),
    )
}

fn resolve_node_variable_inner(
    value: &PropertyValue,
    map: &HashMap<String, PropertyValue>,
    parent_variables: &Rc<HashMap<usize, String>>,
    variable_definitions: &VariableDefinitions,
    resolving: &mut HashSet<String>,
) -> Option<String> {
    match value {
        PropertyValue::Raw(value) => {
            return Some(value.clone());
        }
        PropertyValue::VariableTemplate(template) => {
            // TODO: Handle multi variable dependence
            if template.len() == 1 {
                if let VariableTemplatePart::Var((var, _)) = &template[0] {
                    if !resolving.insert(var.clone()) {
                        return None;
                    }

                    let resolved = if let Some(resolved) = map.get(var) {
                        resolve_node_variable_inner(
                            resolved,
                            map,
                            parent_variables,
                            variable_definitions,
                            resolving,
                        )
                    } else if let Some(resolved) = variable_definitions
                        .variable_to_idx
                        .get(var)
                        .and_then(|var| parent_variables.get(var))
                    {
                        resolve_node_variable_inner(
                            &PropertyValue::Raw(resolved.to_string()),
                            map,
                            parent_variables,
                            variable_definitions,
                            resolving,
                        )
                    } else {
                        None
                    };

                    resolving.remove(var);
                    return resolved;
                }
            }
        }
        _ => {}
    };
    None
}

fn apply_node_variables(
    nodes: &[(usize, Cow<'_, Node>)],
    variables: &Rc<HashMap<usize, String>>,
    css_node_ranking: &[usize],
    variable_definitions: &VariableDefinitions,
) -> Rc<HashMap<usize, String>> {
    let mut variables_to_parse: Vec<(usize, usize, &Variable)> = nodes
        .iter()
        .enumerate()
        .filter_map(|(source_order, (idx, node))| match node.as_ref() {
            Node::Variable(variable) => Some((source_order, *idx, variable)),
            _ => None,
        })
        .collect();
    if variables_to_parse.len() == 0 {
        return Rc::clone(variables);
    }

    variables_to_parse.sort_by_key(|(source_order, idx, _)| {
        let rank = if *idx == usize::MAX {
            usize::MAX
        } else {
            css_node_ranking[*idx]
        };
        (rank, *source_order)
    });

    let mut map = HashMap::new();
    for (_, _, var) in variables_to_parse.iter() {
        map.insert(var.variable.clone(), var.value.clone());
    }

    let mut new_variables = (**variables).clone();

    for (_, _, var) in variables_to_parse {
        if let Some(resolved) =
            resolve_node_variable(&var.value, &map, variables, variable_definitions)
        {
            if let Some(def_idx) = variable_definitions.variable_to_idx.get(&var.variable) {
                new_variables.insert(*def_idx, resolved);
            }
        }
    }

    Rc::new(new_variables)
}

fn resolve_variable_template(
    template: &Vec<VariableTemplatePart>,
    resolved_variables: &Rc<HashMap<usize, String>>,
    variable_definitions: &VariableDefinitions,
) -> String {
    let mut out = String::new();
    let mut previous_was_var = false;
    for el in template.iter() {
        match el {
            VariableTemplatePart::Text(text) => {
                out += text;
                previous_was_var = false;
            }
            VariableTemplatePart::Var((name, default)) => {
                let value = if let Some(value) = variable_definitions
                    .variable_to_idx
                    .get(name)
                    .and_then(|name| resolved_variables.get(name))
                {
                    value.clone()
                } else {
                    default
                        .as_ref()
                        .map(|v| {
                            resolve_variable_template(&v, resolved_variables, variable_definitions)
                        })
                        .unwrap_or(name.to_string())
                };
                if previous_was_var
                    && !out.ends_with(char::is_whitespace)
                    && !value.starts_with(char::is_whitespace)
                {
                    out.push(' ');
                }
                out += &value;
                previous_was_var = true;
            }
        };
    }
    out
}

pub fn resolve_node_variables<'nodes, 'css>(
    nodes: &'nodes mut [(usize, Cow<'css, Node>)],
    variables: &Rc<HashMap<usize, String>>,
    css_node_ranking: &[usize],
    variable_definitions: &VariableDefinitions,
) -> (Vec<&'nodes Property>, Rc<HashMap<usize, String>>) {
    // TODO: Might make sense for the variables to just be represented by idx references instead so that we dont have to clone expensive hashmaps
    let resolved_variables =
        apply_node_variables(nodes, variables, css_node_ranking, variable_definitions);

    for (_, node) in nodes.iter_mut() {
        let parsed_value = match node.as_ref() {
            Node::Property(property) => match &property.value {
                PropertyValue::VariableTemplate(template) => {
                    let value = resolve_variable_template(
                        template,
                        &resolved_variables,
                        variable_definitions,
                    );
                    parse_property_value(property.property.clone(), value)
                        .map(|(parsed, _)| parsed)
                        .ok()
                }
                _ => None,
            },
            _ => None,
        };

        if let Some(parsed_value) = parsed_value {
            if let Node::Property(property) = node.to_mut() {
                property.value = parsed_value;
            }
        }
    }

    let properties = nodes
        .iter()
        .filter_map(|(_, node)| match node.as_ref() {
            Node::Property(property) => Some(property),
            _ => None,
        })
        .collect();

    (properties, resolved_variables)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn self_referential_variable_does_not_recurse_forever() {
        let mut map = HashMap::new();
        map.insert(
            "--color".to_string(),
            PropertyValue::VariableTemplate(vec![VariableTemplatePart::Var((
                "--color".to_string(),
                None,
            ))]),
        );

        let resolved = resolve_node_variable(
            map.get("--color").unwrap(),
            &map,
            &Rc::new(HashMap::new()),
            &VariableDefinitions::new(),
        );

        assert_eq!(resolved, None);
    }

    #[test]
    fn parses_signed_flex_order() {
        let (value, important) =
            parse_property_value("order".to_string(), "-2".to_string()).unwrap();

        assert_eq!(value, PropertyValue::SignedInt(-2));
        assert!(!important);
    }
}

fn parse_justify_content(value: &str) -> StyleJustifyContent {
    match value {
        "auto" => StyleJustifyContent::Auto,
        "normal" | "start" | "left" | "self-start" | "flex-start" => StyleJustifyContent::FlexStart,
        "end" | "right" | "self-end" | "flex-end" => StyleJustifyContent::FlexEnd,
        "center" => StyleJustifyContent::Center,
        "space-between" => StyleJustifyContent::SpaceBetween,
        "space-around" => StyleJustifyContent::SpaceAround,
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

pub fn split_ignoring_parentheses(
    value: String,
    split_char: char,
    break_chars: &[char],
) -> Vec<String> {
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

fn strip_prefix_and_suffix<'a>(
    value: &'a str,
    prefix: &'a str,
    suffix: &'a str,
) -> Option<&'a str> {
    if let Some(stripped) = value.strip_prefix(prefix) {
        stripped.strip_suffix(suffix)
    } else {
        None
    }
}

fn parse_grid_template_columns_inner_value(value: String) -> Result<GridTemplateColumnsValue> {
    if let Some(stripped) = strip_prefix_and_suffix(&value, "minmax(", ")") {
        let (min, max) = stripped
            .split_once(",")
            .with_context(|| "Failed to split minmax value")?;
        let parsed_min = parse_grid_size(min.trim().to_string())?;
        let parsed_max = parse_grid_size(max.trim().to_string())?;
        Ok(GridTemplateColumnsValue::MinMax((parsed_min, parsed_max)))
    } else {
        Ok(GridTemplateColumnsValue::Size(parse_grid_size(value)?))
    }
}

fn parse_overflow_value(value: &str) -> Result<Overflow> {
    match value {
        "hidden" => Ok(Overflow::Hidden),
        "visible" => Ok(Overflow::Visible),
        "auto" => Ok(Overflow::Auto),
        "scroll" => Ok(Overflow::Scroll),
        "clip" => Ok(Overflow::Clip),
        _ => Err(anyhow!("Failed to parse overflow value: {}", value)),
    }
}

fn parse_overflow(value: String) -> Result<PropertyValue> {
    let values = split_ignoring_parentheses(value.clone(), ' ', &[]);
    match values.as_slice() {
        [overflow] => Ok(PropertyValue::Overflow(parse_overflow_value(overflow)?)),
        [x, y] => Ok(PropertyValue::OverflowXY((
            parse_overflow_value(x)?,
            parse_overflow_value(y)?,
        ))),
        _ => Err(anyhow!("Failed to parse overflow value: {}", value)),
    }
}

fn parse_grid_template_columns_value(value: String) -> Result<PropertyValue> {
    let parts: Vec<String> = split_ignoring_parentheses(value, ' ', &[]);
    // TODO: Also support minmax etc. here
    let mut parsed: Vec<GridTemplateColumnsValue> = vec![];
    for p in parts {
        if let Some(stripped) = strip_prefix_and_suffix(&p, "repeat(", ")") {
            let (count, sizes) = stripped
                .split_once(",")
                .with_context(|| format!("Failed to parse repeat: {}", stripped))?;
            let parsed_count = count
                .parse::<i32>()
                .with_context(|| format!("Failed to parse count: {}", count))?;
            let sizes_split: Vec<&str> = sizes.trim().split(" ").collect();
            for _ in 0..parsed_count {
                for size in sizes_split.iter() {
                    parsed.push(parse_grid_template_columns_inner_value(
                        size.trim().to_string(),
                    )?);
                }
            }
            continue;
        }
        parsed.push(parse_grid_template_columns_inner_value(p)?);
    }
    Ok(PropertyValue::GridTemplateColumns(
        GridTemplateColumns::Values(parsed),
    ))
}

fn parse_grid_column_span(value: &str) -> Option<u32> {
    let mut parts = value.split_whitespace();
    while let Some(part) = parts.next() {
        if part == "span" {
            return parts.next()?.parse().ok();
        }
    }
    None
}

fn parse_background(value: String) -> Result<PropertyValue> {
    let parts = split_ignoring_parentheses(value, ' ', &[]);
    let mut background = StyleBackground::Transparent;
    for part in parts {
        if let Some(stripped) = part.strip_prefix("url(") {
            if let Some(stripped) = stripped.strip_suffix(")") {
                let stripped = unquote(stripped);
                if let Some(data) = stripped.strip_prefix("data:") {
                    let (format, data) = data
                        .split_once(',')
                        .with_context(|| "Failed to parse data url")?;
                    background = StyleBackground::DataUrl((format.to_string(), data.to_string()));
                } else {
                    //
                }
            }
        } else if let Ok(value) = parse_color(part) {
            background = value;
        }
    }
    Ok(PropertyValue::ComplexBackground(StyleComplexBackground {
        background,
    }))
}

pub fn parse_property_value(property: String, value: String) -> Result<(PropertyValue, bool)> {
    if let Some(stripped) = value.strip_suffix("!important") {
        return parse_property_value(property, stripped.trim().to_string())
            .and_then(|(value, _)| Ok((value, true)));
    }

    if value.contains("var(") {
        return Ok((
            PropertyValue::VariableTemplate(parse_variable_template(&value)),
            false,
        ));
    }

    if property.starts_with("--") {
        return Ok((PropertyValue::Raw(value), false));
    }

    Ok((
        match property.as_str() {
            "width"
            | "height"
            | "min-height"
            | "max-height"
            | "min-width"
            | "max-width"
            | "gap"
            | "margin-left"
            | "margin-top"
            | "margin-right"
            | "margin-bottom"
            | "margin-inline-start"
            | "margin-inline-end"
            | "font-size"
            | "left"
            | "top"
            | "right"
            | "bottom"
            | "inset-inline-start"
            | "inset-inline-end"
            | "padding-left"
            | "padding-top"
            | "padding-right"
            | "padding-bottom"
            | "border-left-width"
            | "border-top-width"
            | "border-right-width"
            | "border-bottom-width"
            | "border-width"
            | "padding-block-start"
            | "padding-block-end"
            | "padding-inline-start"
            | "padding-inline-end" => PropertyValue::Size(parse_style_size(value)?),
            "line-height" => PropertyValue::Size(parse_line_height(value)?),
            "margin" | "padding" | "inset" | "border-radius" => {
                PropertyValue::CombinedSize(parse_combined_style(value, parse_style_size)?)
            }
            "margin-inline" => PropertyValue::HorizontalCombinedSize(parse_two_axis_size(value)?),
            "padding-block" => PropertyValue::VerticalCombinedSize(parse_two_axis_size(value)?),
            "padding-inline" => PropertyValue::HorizontalCombinedSize(parse_two_axis_size(value)?),
            "background" => parse_background(value)?,
            "background-color"
            | "color"
            | "border-left-color"
            | "border-top-color"
            | "border-right-color"
            | "border-bottom-color" => PropertyValue::Color(parse_color(value)?),
            "border-color" => {
                PropertyValue::CombinedColor(parse_combined_style(value, parse_color)?)
            }
            "display" => PropertyValue::Display(
                match value.as_str().trim() {
                    "block" => Some(StyleDisplay::Block),
                    "inline-block" => Some(StyleDisplay::InlineBlock),
                    "inline" => Some(StyleDisplay::Inline),
                    "flex" => Some(StyleDisplay::Flex),
                    "inline-flex" => Some(StyleDisplay::InlineFlex),
                    "grid" => Some(StyleDisplay::Grid),
                    "none" => Some(StyleDisplay::None),
                    _ => None,
                }
                .with_context(|| "Failed to parse display")?,
            ),
            "position" => PropertyValue::Position(
                match value.as_str().trim() {
                    "static" => Some(StylePosition::Static),
                    "relative" => Some(StylePosition::Relative),
                    "absolute" => Some(StylePosition::Absolute),
                    "fixed" => Some(StylePosition::Fixed),
                    "sticky" => Some(StylePosition::Sticky),
                    _ => {
                        println!("Failed to parse style position \"{}\"", value);
                        None
                    }
                }
                .with_context(|| "Failed to parse position")?,
            ),
            "text-align" => PropertyValue::Align(
                match value.as_str().trim() {
                    "left" | "start" => Some(StyleAlign::Left),
                    "center" => Some(StyleAlign::Center),
                    "right" | "end" => Some(StyleAlign::Right),
                    _ => None,
                }
                .with_context(|| "Failed to parse text-align")?,
            ),
            "flex-shrink" | "flex-grow" => PropertyValue::Int(value.parse::<u32>()?),
            "order" => PropertyValue::SignedInt(value.parse::<i32>()?),
            "flex-basis" => PropertyValue::Size(parse_style_size(value)?),
            "flex" => {
                let parts: Vec<&str> = value.split(" ").collect();
                let mut grow = None;
                let mut shrink = None;
                let mut basis = None;
                if value == "none" {
                    grow = Some(0);
                    shrink = Some(0);
                    basis = Some(StyleSize::Auto);
                } else if value == "auto" {
                    grow = Some(1);
                    shrink = Some(1);
                    basis = Some(StyleSize::Auto);
                } else if value == "initial" {
                    grow = Some(0);
                    shrink = Some(1);
                    basis = Some(StyleSize::Auto);
                } else {
                    match parts.len() {
                        1 => {
                            if let Ok(value) = parts[0].parse::<u32>() {
                                grow = Some(value);
                                shrink = Some(1);
                                basis = Some(StyleSize::Percent(0.));
                            } else {
                                basis = Some(parse_style_size(parts[0].to_string())?);
                            }
                        }
                        2 => {
                            grow = Some(parts[0].parse::<u32>()?);
                            if let Ok(value) = parts[1].parse::<u32>() {
                                shrink = Some(value);
                                basis = Some(StyleSize::Percent(0.));
                            } else {
                                shrink = Some(1);
                                basis = Some(parse_style_size(parts[1].to_string())?);
                            }
                        }
                        3 => {
                            grow = Some(parts[0].parse::<u32>()?);
                            shrink = Some(parts[1].parse::<u32>()?);
                            basis = Some(parse_style_size(parts[2].to_string())?);
                        }
                        _ => {}
                    }
                }
                PropertyValue::Flex {
                    grow,
                    shrink,
                    basis,
                }
            }
            "justify-content" | "justify-items" | "align-items" | "align-self" => {
                PropertyValue::JustifyContent(parse_justify_content(value.as_str()))
            }
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
            "border-left-style"
            | "border-top-style"
            | "border-right-style"
            | "border-bottom-style"
            | "border-style" => PropertyValue::BorderStyle(parse_border_style(value)?),
            "border-left" | "border-top" | "border-right" | "border-bottom" | "border" => {
                PropertyValue::BorderSide(parse_border_side_value(value)?)
            }
            "grid-template-columns" => parse_grid_template_columns_value(value)?,
            "grid-template-rows" => parse_grid_template_columns_value(value)?,
            "grid-column" => parse_grid_column_span(&value)
                .map(PropertyValue::Int)
                .unwrap_or(PropertyValue::Raw(value)),
            "overflow" | "overflow-y" | "overflow-x" => parse_overflow(value)?,
            "z-index" => PropertyValue::ZIndex(parse_z_index(value)?),
            "pointer-events" => PropertyValue::PointerEvents(parse_poiner_events(value)?),
            "visibility" => match value.as_str().trim() {
                "visible" => PropertyValue::Visibility(StyleVisibility::Visible),
                "hidden" => PropertyValue::Visibility(StyleVisibility::Hidden),
                "collapse" => PropertyValue::Visibility(StyleVisibility::Collapse),
                "inherit" | "unset" => PropertyValue::Raw(value),
                "initial" => PropertyValue::Visibility(StyleVisibility::Visible),
                _ => Err(anyhow!("Failed to parse visibility: {}", value))?,
            },
            "transform" => parse_transform(&value)?
                .map(PropertyValue::Transform)
                .unwrap_or(PropertyValue::Raw(value)),
            "translate" => parse_translate(&value)?
                .map(PropertyValue::Transform)
                .unwrap_or(PropertyValue::Raw(value)),
            "initial-value" | "syntax" | "inherits" => PropertyValue::Raw(value),
            _ => {
                // println!("Failed to parse style \"{}\"", property);
                PropertyValue::Raw(value)
            }
        },
        false,
    ))
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

pub fn apply_style_property(style: &mut Style, property: &Property) -> Result<()> {
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
        ("margin-inline-start", PropertyValue::Size(value)) => {
            style.margin_left = value;
        }
        ("margin-inline-end", PropertyValue::Size(value)) => {
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
        }
        ("padding-block", PropertyValue::VerticalCombinedSize((top, bottom))) => {
            style.padding_top = top;
            style.padding_bottom = bottom;
        }
        ("padding-block-start", PropertyValue::Size(value)) => {
            style.padding_top = value;
        }
        ("padding-block-end", PropertyValue::Size(value)) => {
            style.padding_bottom = value;
        }
        ("padding-inline", PropertyValue::HorizontalCombinedSize((left, right))) => {
            style.padding_left = left;
            style.padding_right = right;
        }
        ("padding-inline-start", PropertyValue::Size(value)) => {
            style.padding_left = value;
        }
        ("padding-inline-end", PropertyValue::Size(value)) => {
            style.padding_right = value;
        }
        ("font-size", PropertyValue::Size(value)) => {
            style.font_size = value;
        }
        ("line-height", PropertyValue::Size(value)) => {
            style.line_height = value;
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
        ("inset-inline-start", PropertyValue::Size(value)) => {
            style.left = value;
        }
        ("inset-inline-end", PropertyValue::Size(value)) => {
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
        }
        ("background" | "background-color", PropertyValue::Color(value)) => {
            style.background = value;
        }
        ("color", PropertyValue::Color(value)) => {
            style.color = value;
        }
        ("display", PropertyValue::Display(value)) => {
            style.display = value;
        }
        (
            "border-radius",
            PropertyValue::CombinedSize((top_left, top_right, bottom_right, bottom_left)),
        ) => {
            style.border_radius_top_left = top_left;
            style.border_radius_top_right = top_right;
            style.border_radius_bottom_right = bottom_right;
            style.border_radius_bottom_left = bottom_left;
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
        ("flex-basis", PropertyValue::Size(value)) => {
            style.flex_basis = value;
        }
        ("order", PropertyValue::SignedInt(value)) => {
            style.order = value;
        }
        (
            "flex",
            PropertyValue::Flex {
                grow,
                shrink,
                basis,
            },
        ) => {
            if let Some(grow) = grow {
                style.flex_grow = grow;
            }
            if let Some(shrink) = shrink {
                style.flex_shrink = shrink;
            }
            if let Some(basis) = basis {
                style.flex_basis = basis;
            }
        }
        ("justify-content", PropertyValue::JustifyContent(value)) => {
            style.justify_content = value;
        }
        ("justify-items", PropertyValue::JustifyContent(value)) => {
            style.justify_items = value;
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
        }
        ("grid-template-rows", PropertyValue::GridTemplateColumns(rows)) => {
            style.grid_template_rows = rows;
        }
        ("grid-column", PropertyValue::Int(span)) => {
            style.grid_column_span = span.max(1);
        }
        ("overflow", PropertyValue::Overflow(overflow)) => {
            style.overflow_x = overflow.clone();
            style.overflow_y = overflow;
        }
        ("overflow", PropertyValue::OverflowXY((x, y))) => {
            style.overflow_x = x;
            style.overflow_y = y;
        }
        ("overflow-x", PropertyValue::Overflow(overflow)) => {
            style.overflow_x = overflow;
        }
        ("overflow-y", PropertyValue::Overflow(overflow)) => {
            style.overflow_y = overflow;
        }
        ("z-index", PropertyValue::ZIndex(value)) => {
            style.z_index = value;
        }
        ("pointer-events", PropertyValue::PointerEvents(value)) => {
            style.pointer_events = value;
        }
        ("transform" | "translate", PropertyValue::Transform(value)) => {
            style.transform = value;
        }
        ("opacity", PropertyValue::Raw(value)) => {
            if let Ok(value) = value.parse::<f32>() {
                style.opacity = value.clamp(0.0, 1.0);
            }
        }
        ("visibility", PropertyValue::Visibility(value)) => {
            style.visibility = value;
        }
        (_, PropertyValue::Raw(_) | PropertyValue::VariableTemplate(_)) => {}
        (_, value) => {
            println!(
                "Failed to apply style \"{}\" with value {:?}",
                property.property, value
            );
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
            return get_parent_layer(nodes, parent);
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
    node: &HtmlNode,
    css_nodes: &Vec<Node>,
    parent_style: Option<&Style>,
    parent_variables: &Rc<HashMap<usize, String>>,
    collected_css_nodes: &HashMap<usize, Vec<usize>>,
    css_children_index: &HashMap<usize, Vec<usize>>,
    css_node_ranking: &[usize],
    variable_definitions: &VariableDefinitions,
) -> Result<Style> {
    let mut style = get_base_style(node, parent_style);

    let inline_nodes = if let HtmlNode::Element(element) = node {
        get_inline_nodes(&element)?
    } else {
        vec![]
    };

    let mut applicable_class_properties = vec![];
    if let Some(applicable_class_nodes) = collected_css_nodes.get(&node_idx) {
        for class_node in applicable_class_nodes.iter() {
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
    }

    applicable_class_properties.sort_by(|a, b| {
        let a_rank = css_node_ranking[**a];
        let b_rank = css_node_ranking[**b];
        a_rank.cmp(&b_rank)
    });

    let mut nodes: Vec<(usize, Cow<'_, Node>)> = applicable_class_properties
        .iter()
        .map(|idx| (**idx, Cow::Borrowed(&css_nodes[**idx])))
        .collect();
    // This is a bit hacky, but we don't have an ID for inline nodes, but we also don't need one, so we just set it to usize::MAX
    nodes.extend(
        inline_nodes
            .into_iter()
            .map(|node| (usize::MAX, Cow::Owned(node))),
    );

    let (properties, resolved_variables) = resolve_node_variables(
        &mut nodes,
        parent_variables,
        css_node_ranking,
        variable_definitions,
    );
    style.variables = resolved_variables;

    for property in properties {
        if let Err(result) = apply_style_property(&mut style, property) {
            println!(
                "Failed to apply property {:?} due to: {:?}",
                property, result
            );
        }
    }
    Ok(style)
}
