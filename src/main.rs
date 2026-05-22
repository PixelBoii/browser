mod css;
mod loader;
mod parser;
mod style;

use deno_web::{BlobStore, InMemoryBroadcastChannel};
use fixedbitset::FixedBitSet;
use image::{DynamicImage, ImageReader};
use parser::{Element, HtmlParser, Node};
use reqwest::cookie::{CookieStore, Jar};
use resvg::tiny_skia::{IntSize, Pixmap};
use resvg::usvg::Tree;
use style::{
    Style, StyleBackground, StyleDisplay, StyleFlexDirection, StyleJustifyContent, StylePosition,
    StyleSize, get_base_style, parse_style,
};

use std::cell::{Ref, RefCell};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::io::Cursor;
use std::num::NonZeroU32;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant, SystemTime};
use std::{env, fs, u32};

use ab_glyph::{Font, FontRef, Glyph, OutlinedGlyph, ScaleFont};
use anyhow::{Context, Result, anyhow};
use bytes::Bytes;
use deno_core::error::JsError;
use deno_core::{JsRuntime, OpState, extension, op2, v8};
use raw_window_handle::{DisplayHandle, HasDisplayHandle, HasWindowHandle, WindowHandle};
use reqwest::Url as ReqwestUrl;
use resvg::{tiny_skia, usvg};
use softbuffer::{Context as SoftContext, Surface};
use winit::dpi::PhysicalSize;
use winit::event::{ElementState, Event, KeyEvent, MouseButton, MouseScrollDelta, WindowEvent};
use winit::event_loop::{ControlFlow, EventLoopBuilder, EventLoopProxy};
use winit::window::{Window, WindowBuilder};

use crate::css::{
    ClassName, ClassNamePart, ClassNamePartAttribute, CssParser, MediaQuery, Node as CssNode,
    Overflow, PropertyValue, PseudoClass, parse_media_query_parts, selector_to_parts,
};
use crate::loader::HttpModuleLoader;
use crate::parser::{CommentElement, TextElement};
use crate::style::{
    CalcExpression, GridColumnSize, GridTemplateColumns, GridTemplateColumnsValue, StyleAlign,
    StyleBorderStyle, StyleCalcOperator, StylePointerEvents, StyleSizeAndColor, StyleZIndex,
    build_css_children_index, element_matched_attributes, get_chain_order, get_class_list,
    get_parent_chain, get_parent_layer, get_specificity_order, media_query_matches,
};

const WINDOW_WIDTH: u32 = 1920;
const WINDOW_HEIGHT: u32 = 1080;

// Many websites rely on the user-agent to be one of the major browsers, so we don't use our own for now
const USER_AGENT: &str = "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36";

#[derive(Debug, Clone)]
struct RectBorderSide {
    size: u32,
    color: u32,
}

impl RectBorderSide {
    pub fn parse_from_style(
        style: &StyleSizeAndColor,
        font_size: u32,
        available_size: &Size,
        window_size: &PhysicalSize<u32>,
    ) -> Option<RectBorderSide> {
        match style.style {
            StyleBorderStyle::Solid => Some(Self {
                size: get_specified_size(
                    font_size,
                    &style.size,
                    Some(available_size.width),
                    None,
                    window_size,
                )? as u32,
                color: match style.color {
                    StyleBackground::Hex(hex) => hex,
                    StyleBackground::Transparent => 0xFF_FF_FF_00,
                    StyleBackground::DataUrl(_) => {
                        return None;
                    }
                },
            }),
            StyleBorderStyle::None => None,
        }
    }
}

#[derive(Debug, Clone)]
struct RectBorder {
    left: Option<RectBorderSide>,
    top: Option<RectBorderSide>,
    right: Option<RectBorderSide>,
    bottom: Option<RectBorderSide>,
}

impl RectBorder {
    pub fn new_empty() -> Self {
        Self {
            left: None,
            top: None,
            right: None,
            bottom: None,
        }
    }
}

#[derive(Debug, Clone)]
struct Rect {
    x: i32,
    y: i32,
    width: u32,
    height: u32,
    background: StyleBackground,
    border: RectBorder,
}

#[derive(Debug, Clone)]
enum LayoutKind {
    Element,
    PixMap((tiny_skia::Pixmap, bool)),
    Text(tiny_skia::Pixmap),
    Iframe,
}

#[derive(Debug, Clone)]
struct LayoutBox {
    rect: Rect,
    kind: LayoutKind,
    children: Vec<usize>,
    node_idx: usize,
    allow_overflow: bool,
    content_height: u32,
    z_index: i32,
}

#[derive(Debug, Clone)]
enum RequestCacheEntry {
    PngData(Bytes),
    SvgData(String),
    CssData(String),
    JpegData(Bytes),
    Unsupported,
}

#[derive(Debug, Clone, PartialEq)]
enum LayoutMode {
    BaseCalculation,
    Complete,
}

#[derive(Debug)]
struct DomIndexes {
    class_elements: HashMap<String, FixedBitSet>,
    tag_elements: HashMap<String, FixedBitSet>,
    id_elements: HashMap<String, FixedBitSet>,
    children_index: HashMap<usize, Vec<usize>>,
    attribute_elements: HashMap<String, FixedBitSet>,
    root_indice: usize,
}

#[derive(Debug)]
struct CanvasBuffer {
    buffer: Vec<u32>,
    width: u32,
    height: u32,
}

impl CanvasBuffer {
    fn new(width: u32, height: u32) -> Self {
        Self {
            buffer: vec![0xFF_FF_FF_00; width as usize * height as usize],
            width,
            height,
        }
    }

    fn resize_if_needed(&mut self, width: u32, height: u32) {
        if self.width == width
            && self.height == height
            && self.buffer.len() == width as usize * height as usize
        {
            return;
        }

        self.width = width;
        self.height = height;
        self.buffer.resize(width as usize * height as usize, 0);
    }
}

#[derive(Debug, Clone)]
struct ScrollAnimation {
    start: i32,
    end: i32,
    start_at: SystemTime,
    duration: Duration,
    node_idx: usize,
}

#[derive(Debug, Clone)]
enum Animation {
    ScrollAnimation(ScrollAnimation),
}

impl Animation {
    pub fn is_done(&self, now: SystemTime) -> bool {
        match self {
            Animation::ScrollAnimation(animation) => animation
                .start_at
                .checked_add(animation.duration)
                .unwrap()
                .lt(&now),
        }
    }
}

#[derive(Debug)]
enum FrameCommand {
    Render,
    UserEvent(UserEvent),
}

#[derive(Debug)]
struct FrameHandle {
    surface: Arc<Mutex<Vec<u32>>>,
}

#[derive(Debug, Clone)]
enum RendererProxy {
    WindowLoop(EventLoopProxy<UserEvent>),
    FrameLoop(std::sync::mpsc::Sender<FrameCommand>),
}

impl RendererProxy {
    fn fire_user_event(&self, event: UserEvent) -> Result<()> {
        match self {
            RendererProxy::FrameLoop(tx) => tx.send(FrameCommand::UserEvent(event))?,
            RendererProxy::WindowLoop(proxy) => proxy.send_event(event)?,
        };
        Ok(())
    }
}

#[derive(Debug)]
struct RenderedNode {
    layout_box_idx: usize,
    offset_y: i32,
}

#[derive(Debug)]
struct Renderer {
    url: String,
    node_idx_cursor: usize,
    pub nodes_idxs: Vec<usize>,
    pub nodes: HashMap<usize, parser::Node>,
    node_styles: HashMap<usize, Style>,
    layout_table: HashMap<usize, LayoutBox>,
    node_layout_mapping: HashMap<usize, usize>,
    containing_nodes: HashMap<usize, ContainingNode>,
    request_cache: HashMap<ReqwestUrl, RequestCacheEntry>,
    rendered_nodes_ordered: Vec<RenderedNode>,
    pub hovering: Option<usize>,
    pub focusable: Option<usize>,
    tokio: Rc<RefCell<tokio::runtime::Runtime>>,
    resolved_font_sizes: HashMap<usize, u32>,
    resolved_pixmaps: HashMap<String, tiny_skia::Pixmap>,
    window_size: PhysicalSize<u32>,
    font_handler: Rc<FontHandler>,
    pending_dom_update: bool,
    scroll_y: HashMap<usize, i32>,
    layout_roots: Vec<usize>,
    resolved_specified_heights: HashMap<usize, Option<u32>>,
    resolved_specified_widths: HashMap<usize, Option<u32>>,
    resolved_heights: HashMap<usize, u32>,
    resolved_widths: HashMap<usize, u32>,
    dom_indexes: DomIndexes,
    canvas_buffers: HashMap<usize, CanvasBuffer>,
    network_fetch: Rc<RefCell<NetworkFetch>>,
    cached_rasterizations: CachedRasterizations,
    animations: Vec<Animation>,
    cached_text_buffers: HashMap<(String, u32), (Pixmap, u32, u32)>,
    css_parse_cache: HashMap<ExpandableCssNode, Vec<CssNode>>,
    variable_definitions: VariableDefinitions,
    event_loop_proxy: Option<RendererProxy>,
    hovering_impact: HashSet<usize>,
    frames: HashMap<usize, FrameHandle>,
}

#[derive(Debug, Clone)]
struct FlexItem {
    node_idx: usize,
    target_size: f32,
    base_size: f32,
    cross_size: f32,
    shrink: u32,
    grow: u32,
}

#[derive(Debug, Clone, Copy)]
struct Size {
    height: u32,
    width: u32,
}

#[derive(Debug, Clone, Copy)]
struct OptionalSize {
    height: Option<u32>,
    width: Option<u32>,
}

#[derive(Debug, Clone, Copy)]
struct Position {
    x: i32,
    y: i32,
}

#[derive(Debug, Clone, Copy)]
struct ResumableNode {
    parent_idx: usize,
    node_idx: usize,
    available_size: Size,
    cursor: Position,
}

#[derive(Debug, Clone)]
struct ContainingNode {
    node_idx: usize,
    waiters: Vec<ResumableNode>,
}

#[derive(Debug, Clone)]
struct ContainerSizes {
    inner_width: u32,
    inner_height: u32,
    container_width: u32,
    container_width_non_filling: Option<u32>,
    container_height: u32,
    container_height_non_filling: Option<u32>,
    min_height: Option<u32>,
    max_height: Option<u32>,
    min_width: Option<u32>,
    max_width: Option<u32>,
    padding_x: u32,
}

impl ContainerSizes {
    pub fn clamp_width(&self, value: u32) -> u32 {
        value
            .min(self.max_width.unwrap_or(u32::MAX))
            .max(self.min_width.unwrap_or(u32::MIN))
    }

    pub fn compute_actual_container_width(&self, used_width: u32) -> u32 {
        self.container_width_non_filling
            .unwrap_or(self.clamp_width(used_width) + self.padding_x)
    }
}

impl ContainingNode {
    pub fn layout_waiters(
        &mut self,
        renderer: &mut Renderer,
        height: u32,
        width: u32,
        children: &mut Vec<usize>,
        mode: &LayoutMode,
    ) -> Result<()> {
        for waiter in &self.waiters {
            let style = renderer.node_styles.get(&waiter.node_idx).unwrap().clone();
            let mut forced_size = OptionalSize {
                height: None,
                width: None,
            };
            let resolved_parent_font_size = renderer.get_parent_font_size(waiter.node_idx);
            let font_size = get_specified_size(
                resolved_parent_font_size,
                &style.font_size,
                Some(resolved_parent_font_size),
                None,
                &renderer.window_size,
            )
            .with_context(|| "Failed to get specific size")? as u32;
            renderer
                .resolved_font_sizes
                .insert(waiter.node_idx, font_size as u32);
            let top = get_specified_size(
                font_size,
                &style.top,
                Some(waiter.available_size.height),
                None,
                &renderer.window_size,
            );
            let right = get_specified_size(
                font_size,
                &style.right,
                Some(waiter.available_size.width),
                None,
                &renderer.window_size,
            );
            let bottom = get_specified_size(
                font_size,
                &style.bottom,
                Some(waiter.available_size.height),
                None,
                &renderer.window_size,
            );
            let left = get_specified_size(
                font_size,
                &style.left,
                Some(waiter.available_size.width),
                None,
                &renderer.window_size,
            );

            let margin_right = get_specified_size(
                font_size,
                &style.margin_right,
                Some(waiter.available_size.width),
                None,
                &renderer.window_size,
            );
            let margin_left = get_specified_size(
                font_size,
                &style.margin_left,
                Some(waiter.available_size.width),
                None,
                &renderer.window_size,
            );

            let positioning_width = if style.position == StylePosition::Fixed {
                waiter.available_size.width
            } else {
                width
            };
            let positioning_height = if style.position == StylePosition::Fixed {
                waiter.available_size.height
            } else {
                height
            };

            if style.position.is_free()
                && style.width == StyleSize::Auto
                && left.is_some()
                && right.is_some()
            {
                forced_size.width =
                    Some((positioning_width as i32 - left.unwrap() - right.unwrap()) as u32);
            }
            if style.position.is_free()
                && style.height == StyleSize::Auto
                && top.is_some()
                && bottom.is_some()
            {
                forced_size.height =
                    Some((positioning_height as i32 - top.unwrap() - bottom.unwrap()) as u32);
            }

            if let Some(layout_idx) = renderer.layout_node(
                waiter.node_idx,
                waiter.cursor,
                waiter.available_size,
                forced_size,
                self.node_idx,
                true,
                true,
                mode,
            ) {
                let waiter_layout_box = renderer.layout_table.get(&layout_idx).unwrap().clone();

                if style.position.is_free() {
                    if style.width == StyleSize::Auto && left.is_some() && right.is_some() {
                        // Width is taken care of above, so just move by left
                        renderer.move_entire_box(layout_idx, left.unwrap(), 0);
                    } else if right.is_some() {
                        let move_by = positioning_width as i32
                            - waiter_layout_box.rect.width as i32
                            - right.unwrap()
                            - margin_right.unwrap_or(0);
                        renderer.move_entire_box(layout_idx, move_by, 0);
                    } else if left.is_some() {
                        renderer.move_entire_box(
                            layout_idx,
                            left.unwrap() - margin_left.unwrap_or(0),
                            0,
                        );
                    } else if style.margin_left == StyleSize::Auto
                        && style.margin_right == StyleSize::Auto
                    {
                        let free_space =
                            positioning_width.saturating_sub(waiter_layout_box.rect.width);
                        renderer.move_entire_box(layout_idx, (free_space / 2) as i32, 0);
                    }

                    if top.is_some() && bottom.is_some() {
                        // Height is taken care of above, so just move by top
                        renderer.move_entire_box(layout_idx, 0, top.unwrap());
                    } else if top.is_some() {
                        renderer.move_entire_box(layout_idx, 0, top.unwrap());
                    } else if bottom.is_some() {
                        let move_by = positioning_height as i32
                            - waiter_layout_box.rect.height as i32
                            - bottom.unwrap();
                        renderer.move_entire_box(layout_idx, 0, move_by);
                    }
                }

                // If the waiter's parent is us, we haven't been laid out yet, so just add to children vector
                if waiter.parent_idx == self.node_idx {
                    children.push(layout_idx);
                } else if let Some(parent_layout_idx) =
                    renderer.node_layout_mapping.get(&waiter.parent_idx)
                {
                    renderer
                        .layout_table
                        .get_mut(parent_layout_idx)
                        .unwrap()
                        .children
                        .push(layout_idx);
                }
            }
        }
        self.waiters.clear();
        Ok(())
    }
}

fn get_specified_size(
    font_size: u32,
    value: &StyleSize,
    available_size: Option<u32>,
    auto_size: Option<i32>,
    window_size: &PhysicalSize<u32>,
) -> Option<i32> {
    match value {
        StyleSize::Auto => auto_size,
        StyleSize::Percent(percentage) => {
            if let Some(available_size) = available_size {
                let computed = available_size as f32 * (*percentage as f32 / 100f32);
                Some(computed as i32)
            } else {
                None
            }
        }
        StyleSize::Px(px) => Some(*px as i32),
        StyleSize::Vh(vh) => Some((window_size.height as i32 * vh / 100) as i32),
        StyleSize::Svh(vh) => Some((window_size.height as i32 * vh / 100) as i32),
        StyleSize::Vw(vw) => Some((window_size.width as i32 * vw / 100) as i32),
        StyleSize::Clamp { min, value, max } => {
            let min = get_specified_size(font_size, min, available_size, auto_size, window_size)?;
            let value =
                get_specified_size(font_size, value, available_size, auto_size, window_size)?;
            let max = get_specified_size(font_size, max, available_size, auto_size, window_size)?;
            Some(value.min(max).max(min))
        }
        StyleSize::Calc(calc) => {
            solve_calc(calc, font_size, available_size, auto_size, window_size)
        }
        StyleSize::Em(em) => Some((*em * font_size as f32) as i32),
        // TODO: This should actually be the font-size of the root element, so figure that out
        StyleSize::Rem(rem) => Some((*rem * 16 as f32) as i32),
    }
}

// TODO: Make this handle order of operations
fn solve_calc(
    calc: &Vec<CalcExpression>,
    font_size: u32,
    available_size: Option<u32>,
    auto_size: Option<i32>,
    window_size: &PhysicalSize<u32>,
) -> Option<i32> {
    let mut value = match &calc[0] {
        CalcExpression::Size(size) => {
            get_specified_size(font_size, &size, available_size, auto_size, window_size)?
        }
        _ => panic!("Expected first calc expression to be value"),
    };
    let mut exp_idx = 1;
    while exp_idx < calc.len() {
        let loop_operator = match &calc[exp_idx] {
            CalcExpression::Operator(operator) => operator,
            _ => panic!("Expected calc expression to be operator"),
        };
        let loop_value = match &calc[exp_idx + 1] {
            CalcExpression::Size(size) => {
                get_specified_size(font_size, &size, available_size, auto_size, window_size)?
            }
            CalcExpression::Nesting(nesting) => {
                solve_calc(nesting, font_size, available_size, auto_size, window_size)?
            }
            _ => panic!(
                "Expected calc expression to be size. Got: {:?} [{}]",
                calc,
                exp_idx + 1
            ),
        };
        value = match loop_operator {
            StyleCalcOperator::Plus => value + loop_value,
            StyleCalcOperator::Minus => value - loop_value,
            StyleCalcOperator::Divide => value / loop_value,
            StyleCalcOperator::Multiply => value * loop_value,
        };
        exp_idx += 2;
    }
    Some(value)
}

fn infer_image_size(base_size: Size, input_w: Option<u32>, input_h: Option<u32>) -> (u32, u32) {
    let (target_h, target_w) = match (input_h, input_w) {
        (None, None) => (base_size.height, base_size.width),
        (Some(height), None) => (
            height,
            (base_size.width as f32 * (height as f32 / base_size.height as f32)) as u32,
        ),
        (None, Some(width)) => (
            (base_size.height as f32 * (width as f32 / base_size.width as f32)) as u32,
            width,
        ),
        (Some(height), Some(width)) => (height, width),
    };

    (target_h, target_w)
}

fn blend_rgba_with_rgba(dst: u32, src: (u8, u8, u8, u8)) -> u32 {
    let a = src.3 as u32;
    if a == 0 {
        return dst;
    }
    if a == 255 {
        return ((src.0 as u32) << 24)
            | ((src.1 as u32) << 16)
            | ((src.2 as u32) << 8)
            | (src.3 as u32);
    }

    let inv_a = 255 - a;

    let dr = (dst >> 24) & 0xFF;
    let dg = (dst >> 16) & 0xFF;
    let db = (dst >> 8) & 0xFF;

    let r = src.0 as u32 + (dr * inv_a + 127) / 255;
    let g = src.1 as u32 + (dg * inv_a + 127) / 255;
    let b = src.2 as u32 + (db * inv_a + 127) / 255;

    (r << 24) | (g << 16) | (b << 8) | a
}

fn blend_rgb_with_rgba(dst: u32, src: (u8, u8, u8, u8)) -> u32 {
    let a = src.3 as u32;
    if a == 0 {
        return dst;
    }
    if a == 255 {
        return ((src.0 as u32) << 16) | ((src.1 as u32) << 8) | (src.2 as u32);
    }

    let inv_a = 255 - a;

    let dr = (dst >> 16) & 0xFF;
    let dg = (dst >> 8) & 0xFF;
    let db = dst & 0xFF;

    let r = src.0 as u32 + (dr * inv_a + 127) / 255;
    let g = src.1 as u32 + (dg * inv_a + 127) / 255;
    let b = src.2 as u32 + (db * inv_a + 127) / 255;

    (r << 16) | (g << 8) | b
}

fn clamp_with_ratio(mut main_value: u32, max_value: u32, mut other_value: u32) -> (u32, u32) {
    if main_value > max_value {
        let ratio = main_value as f32 / max_value as f32;
        main_value = max_value;
        other_value = (other_value as f32 / ratio) as u32;
    }
    (main_value, other_value)
}

fn rasterize_svg(
    cached_rasterizations: &mut CachedRasterizations,
    svg_str: &String,
    input_w: Option<u32>,
    input_h: Option<u32>,
    max_w: u32,
    max_h: u32,
    style: &Style,
    mode: &LayoutMode,
) -> Result<(tiny_skia::Pixmap, u32, u32, bool)> {
    let color_hex = match style.color {
        StyleBackground::Hex(hex) => hex,
        _ => 0x00_FF_FF_FF,
    };
    let key = (svg_str.clone(), color_hex);
    let tree = if let Some(cached) = cached_rasterizations.decoded_svgs.get(&key) {
        cached
    } else {
        let normalized_svg;
        let svg_data = if svg_str.contains("viewbox=") {
            normalized_svg = svg_str.replace("viewbox=", "viewBox=");
            normalized_svg.as_bytes()
        } else {
            svg_str.as_bytes()
        };
        let mut opt = usvg::Options::default();
        opt.style_sheet =
            Some(format!("svg {{ color: #{:08X}; fill: currentColor }}", color_hex).into());

        let tree = usvg::Tree::from_data(&svg_data, &opt)?;
        cached_rasterizations.decoded_svgs.insert(key.clone(), tree);
        cached_rasterizations.decoded_svgs.get(&key).unwrap()
    };
    let svg_size = tree.size().to_int_size();

    let (mut target_h, mut target_w) = infer_image_size(
        Size {
            height: svg_size.height(),
            width: svg_size.width(),
        },
        input_w,
        input_h,
    );
    (target_h, target_w) = clamp_with_ratio(target_h, max_h, target_w);
    (target_w, target_h) = clamp_with_ratio(target_w, max_w, target_h);

    let key = (svg_str.clone(), target_h, target_w);
    if let Some(cached) = cached_rasterizations.svgs.get(&key) {
        Ok((cached.clone(), target_h, target_w, false))
    } else {
        let mut pixmap = tiny_skia::Pixmap::new(target_w.max(1), target_h.max(1))
            .context("failed to allocate svg pixmap")?;

        if *mode == LayoutMode::Complete {
            let scale = f32::min(
                target_w as f32 / svg_size.width() as f32,
                target_h as f32 / svg_size.height() as f32,
            );

            let tx = (target_w as f32 - svg_size.width() as f32 * scale) * 0.5;
            let ty = (target_h as f32 - svg_size.height() as f32 * scale) * 0.5;

            let transform = tiny_skia::Transform::from_row(scale, 0.0, 0.0, scale, tx, ty);
            resvg::render(&tree, transform, &mut pixmap.as_mut());
            cached_rasterizations
                .svgs
                .insert(key.clone(), pixmap.clone());
        }

        let opaque = *mode == LayoutMode::Complete && pixmap_is_opaque(&pixmap);
        Ok((pixmap, target_h, target_w, opaque))
    }
}

fn pixmap_is_opaque(pixmap: &tiny_skia::Pixmap) -> bool {
    pixmap.pixels().iter().all(|p| p.alpha() == 255)
}

fn rasterize_png(
    cached_rasterizations: &mut CachedRasterizations,
    src: &String,
    bytes: &[u8],
    input_w: Option<u32>,
    input_h: Option<u32>,
    max_w: u32,
    max_h: u32,
    mode: &LayoutMode,
) -> Result<(tiny_skia::Pixmap, u32, u32, bool)> {
    let pixmap = if let Some(cached) = cached_rasterizations.decoded_pngs.get(src) {
        cached
    } else {
        cached_rasterizations
            .decoded_pngs
            .insert(src.clone(), tiny_skia::Pixmap::decode_png(bytes)?);
        cached_rasterizations.decoded_pngs.get(src).unwrap()
    };
    if input_w.is_some_and(|v| v == pixmap.width()) && input_h.is_some_and(|v| v == pixmap.height())
    {
        let opaque = pixmap_is_opaque(pixmap);
        return Ok((pixmap.clone(), input_h.unwrap(), input_w.unwrap(), opaque));
    }

    let (mut target_h, mut target_w) = infer_image_size(
        Size {
            height: pixmap.height(),
            width: pixmap.width(),
        },
        input_w,
        input_h,
    );
    (target_h, target_w) = clamp_with_ratio(target_h, max_h, target_w);
    (target_w, target_h) = clamp_with_ratio(target_w, max_w, target_h);

    let mut dst = tiny_skia::Pixmap::new(target_w.max(1), target_h.max(1))
        .context("failed to allocate png pixmap")?;

    if *mode == LayoutMode::Complete {
        dst.as_mut().draw_pixmap(
            0,
            0,
            pixmap.as_ref(),
            &tiny_skia::PixmapPaint::default(),
            tiny_skia::Transform::from_row(
                target_w as f32 / pixmap.width() as f32,
                0.0,
                0.0,
                target_h as f32 / pixmap.height() as f32,
                0.0,
                0.0,
            ),
            None,
        );
    }

    let opaque = *mode == LayoutMode::Complete && pixmap_is_opaque(&dst);
    Ok((dst, target_h, target_w, opaque))
}

fn prepare_jpeg(
    cached_rasterizations: &mut CachedRasterizations,
    src: &String,
    bytes: &[u8],
    input_w: Option<u32>,
    input_h: Option<u32>,
    max_w: u32,
    max_h: u32,
) -> Result<(u32, u32)> {
    let result = if let Some(cached) = cached_rasterizations.decoded_jpegs.get(src) {
        cached
    } else {
        let mut reader = ImageReader::new(Cursor::new(bytes));
        reader.set_format(image::ImageFormat::Jpeg);
        cached_rasterizations
            .decoded_jpegs
            .insert(src.clone(), reader.decode()?);
        cached_rasterizations.decoded_jpegs.get(src).unwrap()
    };

    let (mut target_h, mut target_w) = infer_image_size(
        Size {
            height: result.height(),
            width: result.width(),
        },
        input_w,
        input_h,
    );
    (target_h, target_w) = clamp_with_ratio(target_h, max_h, target_w);
    (target_w, target_h) = clamp_with_ratio(target_w, max_w, target_h);

    Ok((target_h, target_w))
}

fn rasterize_jpeg(
    cached_rasterizations: &mut CachedRasterizations,
    src: &String,
    target_w: u32,
    target_h: u32,
) -> Result<tiny_skia::Pixmap> {
    let decoded = cached_rasterizations.decoded_jpegs.get(src).unwrap();
    let key = (src.clone(), target_h, target_w);
    let pixmap = if let Some(cached) = cached_rasterizations.jpegs.get(&key) {
        cached
    } else {
        let result =
            decoded.resize_exact(target_w, target_h, image::imageops::FilterType::Triangle);
        let rgba = result.to_rgba8();

        let width = rgba.width();
        let height = rgba.height();
        let value = Pixmap::from_vec(
            rgba.to_owned().into_raw(),
            IntSize::from_wh(width, height).with_context(|| "Failed to create IntSize")?,
        )
        .with_context(|| "Failed to convert to pixmap")?;
        cached_rasterizations.jpegs.insert(key.clone(), value);
        cached_rasterizations.jpegs.get(&key).unwrap()
    };

    Ok(pixmap.clone())
}

fn resolve_url(href: &str, base_url: Option<&ReqwestUrl>) -> Result<ReqwestUrl> {
    if let Ok(url) = ReqwestUrl::parse(href) {
        return Ok(url);
    }

    let base_url = base_url.context(format!("relative URL without base: {href}"))?;
    Ok(base_url.join(href)?)
}

async fn fetch_link_strings(
    base_url: &String,
    network_fetch: &Rc<RefCell<NetworkFetch>>,
    links: &Vec<&String>,
    map_fn: impl Fn(String) -> RequestCacheEntry,
) -> Result<Vec<String>> {
    let mut results = vec![];
    for link in links.iter() {
        // TODO: Don't hardcode this
        let base = ReqwestUrl::parse(base_url)?;
        let url = resolve_url(link, Some(&base))?;

        if let Some(cache) = network_fetch.borrow_mut().request_cache.get(&url) {
            results.push(cache.clone());
        } else {
            println!("Fetching {}", url);
            let resp = network_fetch
                .borrow_mut()
                .client
                .get(url.clone())
                .send()
                .await?
                .text()
                .await?;
            let cache_entry = map_fn(resp);
            network_fetch
                .borrow_mut()
                .request_cache
                .insert(url, cache_entry.clone());

            results.push(cache_entry);
        }
    }
    let strings = results
        .iter()
        .map(|r| match r {
            RequestCacheEntry::CssData(data) => Some(data.clone()),
            _ => None,
        })
        .flatten()
        .collect::<Vec<String>>();

    Ok(strings)
}

#[derive(Eq, PartialEq, Hash, Clone, Debug)]
enum ExpandableCssNode {
    Link(String),
    Inline(String),
}

fn get_expandable_css_nodes_walk(
    expandable: &mut Vec<ExpandableCssNode>,
    nodes: &HashMap<usize, Node>,
    children_index: &HashMap<usize, Vec<usize>>,
    idx: usize,
) {
    let node = &nodes.get(&idx).unwrap();
    let Node::Element(element) = node else {
        return;
    };
    if element.tag == "style" {
        let children = &children_index.get(&idx).unwrap();
        if children.len() != 1 {
            println!("Unexpected children count: {}", children.len());
            return;
        }
        let child = children.first().unwrap();
        let child_node = &nodes.get(child).unwrap();
        let text = match child_node {
            Node::Element(element) => {
                println!("Got element when expecting CSS text {:?}", element);
                return;
            }
            Node::Comment(_) => {
                return;
            }
            Node::Text(text) => text,
        };
        expandable.push(ExpandableCssNode::Inline(text.text.clone()));
    } else if element.tag == "link"
        && let Some(href) = element.attributes.get("href")
        && element.attributes.get("rel").is_some_and(|v| {
            let rels: Vec<&str> = v.split(" ").collect();
            rels.contains(&"stylesheet")
        })
    {
        expandable.push(ExpandableCssNode::Link(href.clone()));
    } else if element.tag != "noscript" {
        let children = &children_index.get(&idx).unwrap();
        for child in children.iter() {
            get_expandable_css_nodes_walk(expandable, nodes, children_index, *child);
        }
    }
}

fn get_expandable_css_nodes(
    nodes: &HashMap<usize, Node>,
    root_indice: usize,
    children_index: &HashMap<usize, Vec<usize>>,
) -> Vec<ExpandableCssNode> {
    let mut expandable = vec![];

    get_expandable_css_nodes_walk(&mut expandable, nodes, children_index, root_indice);

    expandable
}

fn compute_node_style(
    node_styles: &mut HashMap<usize, Style>,
    resolved_font_sizes: &mut HashMap<usize, u32>,
    nodes: &HashMap<usize, Node>,
    node_idx: usize,
    children_index: &HashMap<usize, Vec<usize>>,
    css_nodes: &Vec<CssNode>,
    parent_style: Option<usize>,
    parent_variables: &Rc<HashMap<usize, String>>,
    parent_font_size: Option<u32>,
    collected_class_nodes: &HashMap<usize, Vec<usize>>,
    css_children_index: &HashMap<usize, Vec<usize>>,
    window_size: &PhysicalSize<u32>,
    css_node_ranking: &[usize],
    variable_definitions: &VariableDefinitions,
) {
    let parent_style = parent_style.and_then(|idx| Some(node_styles.get(&idx).unwrap()));
    let node = &nodes.get(&node_idx).unwrap();
    let mut style = if matches!(node, Node::Element(_)) {
        parse_style(
            node_idx,
            node,
            css_nodes,
            parent_style,
            parent_variables,
            collected_class_nodes,
            css_children_index,
            css_node_ranking,
            variable_definitions,
        )
        .unwrap()
    } else {
        get_base_style(node, parent_style)
    };

    let resolved_font_size = get_specified_size(
        parent_font_size.unwrap_or(16),
        &style.font_size,
        Some(parent_font_size.unwrap_or(16)),
        None,
        window_size,
    )
    .unwrap_or_else(|| {
        println!("Failed to get font size for node idx {}", node_idx);
        16
    });
    resolved_font_sizes.insert(node_idx, resolved_font_size as u32);

    // Set to resolved size in px so that ems dont stack on top of each other
    style.font_size = StyleSize::Px(resolved_font_size as f32);

    let resolved_variables = Rc::clone(&style.variables);

    node_styles.insert(node_idx, style);

    for child_idx in children_index.get(&node_idx).unwrap().iter() {
        compute_node_style(
            node_styles,
            resolved_font_sizes,
            nodes,
            *child_idx,
            children_index,
            css_nodes,
            Some(node_idx),
            &resolved_variables,
            Some(resolved_font_size as u32),
            collected_class_nodes,
            css_children_index,
            window_size,
            css_node_ranking,
            variable_definitions,
        );
    }
}

fn parse_css_nodes(css_nodes: &Vec<String>) -> Result<Vec<CssNode>> {
    let joined = css_nodes.join("\n");
    let mut parser = CssParser::new(&joined.as_str());
    parser.parse()?;

    Ok(parser.nodes)
}

fn flatten_css_chunks(mut parsed_css_chunks: Vec<(usize, Vec<CssNode>)>) -> Vec<CssNode> {
    parsed_css_chunks.sort_by_key(|(idx, _)| *idx);

    let mut parsed_css_nodes = vec![];
    for (_, nodes) in parsed_css_chunks {
        let offset = parsed_css_nodes.len();
        for mut node in nodes {
            node.offset_parent(offset);
            parsed_css_nodes.push(node);
        }
    }

    parsed_css_nodes
}

fn move_up_ancestor_chain(
    element: usize,
    html_nodes: &HashMap<usize, &Node>,
    css_nodes: &Vec<(usize, &CssNode)>,
    class_elements: &HashMap<String, FixedBitSet>,
    css_node: &CssNode,
    window_size: &PhysicalSize<u32>,
    require_immediate_match: bool,
    walk_up_parent: bool,
    dom_indexes: &DomIndexes,
    hovering_chain: &Vec<usize>,
    hovering_has_impact: &mut HashSet<usize>,
) -> bool {
    let parent = css_node.get_parent();
    if let Some(parent) = parent {
        let parent_node = css_nodes[parent].1;
        if let CssNode::ClassName(parent_node_class) = parent_node {
            let mut is_match = false;
            for (name_part_idx, _) in parent_node_class.name_parts.iter().enumerate() {
                let nested_parts = &parent_node_class.name_parts[name_part_idx];
                let next_class_part = &nested_parts[nested_parts.len() - 1];
                let el = if walk_up_parent && walk_into_part(next_class_part) {
                    get_parent_html_idx(element, html_nodes)
                } else {
                    Some(element)
                };
                if let Some(el) = el {
                    is_match |= narrow_elements_by_ancestors(
                        el,
                        css_nodes,
                        html_nodes,
                        class_elements,
                        parent,
                        name_part_idx,
                        0,
                        window_size,
                        require_immediate_match,
                        dom_indexes,
                        hovering_chain,
                        hovering_has_impact,
                    );
                }
            }
            return is_match;
        } else {
            // Media queries and layers should not cause a walk up a HTML parent
            // I think this happens at the right time, but might be worth double-checking later
            return narrow_elements_by_ancestors(
                element,
                css_nodes,
                html_nodes,
                class_elements,
                parent,
                0,
                0,
                window_size,
                require_immediate_match,
                dom_indexes,
                hovering_chain,
                hovering_has_impact,
            );
        }
    } else {
        // If no parent, we've reached the end and are done
        return true;
    }
}

fn move_up_class_part(
    element: usize,
    css_nodes: &Vec<(usize, &CssNode)>,
    html_nodes: &HashMap<usize, &Node>,
    class_elements: &HashMap<String, FixedBitSet>,
    parts: &Vec<ClassNamePart>,
    css_node: usize,
    nested_part_idx: usize,
    name_part_idx: usize,
    window_size: &PhysicalSize<u32>,
    walk_up_parent: bool,
    require_immediate_match: bool,
    dom_indexes: &DomIndexes,
    hovering_chain: &Vec<usize>,
    hovering_has_impact: &mut HashSet<usize>,
) -> bool {
    let node = css_nodes[css_node].1;
    // If we've reached the beginning, that means this node is done, so move up the chain
    if nested_part_idx == parts.len() - 1 {
        return move_up_ancestor_chain(
            element,
            html_nodes,
            css_nodes,
            class_elements,
            node,
            window_size,
            require_immediate_match,
            walk_up_parent,
            dom_indexes,
            hovering_chain,
            hovering_has_impact,
        );
    } else {
        let class_name = match node {
            CssNode::ClassName(class_name) => class_name,
            _ => unreachable!(),
        };
        let nested_parts = &class_name.name_parts[name_part_idx];
        let next_class_part = &nested_parts[nested_parts.len() - 1 - (nested_part_idx + 1)];
        let walk_el = if walk_up_parent && walk_into_part(next_class_part) {
            get_parent_html_idx(element, html_nodes)
        } else {
            Some(element)
        };
        if let Some(walk_el) = walk_el {
            return narrow_elements_by_ancestors(
                walk_el,
                css_nodes,
                html_nodes,
                class_elements,
                css_node,
                name_part_idx,
                nested_part_idx + 1,
                window_size,
                require_immediate_match,
                dom_indexes,
                hovering_chain,
                hovering_has_impact,
            );
        } else {
            return false;
        }
    }
}

fn walk_for_html_match<F>(
    element: usize,
    html_nodes: &HashMap<usize, &Node>,
    match_fn: &mut F,
    quota: Option<i32>,
) -> Option<usize>
where
    F: FnMut(usize) -> bool,
{
    // If we're not allowed to walk anymore, give up
    if quota.is_some_and(|quota| quota == 0) {
        None
    } else if match_fn(element) {
        Some(element)
    } else if let Some(parent) = html_nodes.get(&element).unwrap().get_parent() {
        walk_for_html_match(
            parent,
            html_nodes,
            match_fn,
            quota.and_then(|quota| Some(quota - 1)),
        )
    } else {
        None
    }
}

fn element_matches_class_part(
    part: &ClassNamePart,
    element: usize,
    html_nodes: &HashMap<usize, &Node>,
    class_elements: &HashMap<String, FixedBitSet>,
    dom_indexes: &DomIndexes,
    hovering_chain: &Vec<usize>,
    hovering_has_impact: &mut HashSet<usize>,
) -> bool {
    match part {
        ClassNamePart::Class(class) => {
            if let Some(elements_to_keep) = class_elements.get(class) {
                elements_to_keep.contains(element)
            } else {
                false
            }
        }
        ClassNamePart::Id(id) => match html_nodes.get(&element).unwrap() {
            Node::Element(walk_element) => walk_element
                .attributes
                .get("id")
                .is_some_and(|el_id| *el_id == *id),
            _ => false,
        },
        ClassNamePart::ArrowRight | ClassNamePart::Ampersand | ClassNamePart::Tilde => true,
        ClassNamePart::PseudoClass(class) => {
            match class {
                // All elements are children of root
                PseudoClass::Root => true,
                PseudoClass::Not(selector) => {
                    let negative_matches = query_selector_all(
                        &html_nodes,
                        selector.clone(),
                        &PhysicalSize {
                            width: 0,
                            height: 0,
                        },
                        dom_indexes,
                        hovering_chain,
                    );
                    !negative_matches.contains(&element)
                }
                PseudoClass::Hover => {
                    hovering_has_impact.insert(element);
                    hovering_chain.contains(&element)
                }
                PseudoClass::FirstChild => html_nodes
                    .get(&element)
                    .and_then(|node| node.get_parent())
                    .and_then(|parent| dom_indexes.children_index.get(&parent))
                    .is_some_and(|siblings| siblings.first().is_some_and(|idx| *idx == element)),
                PseudoClass::LastChild => html_nodes
                    .get(&element)
                    .and_then(|node| node.get_parent())
                    .and_then(|parent| dom_indexes.children_index.get(&parent))
                    .is_some_and(|siblings| siblings.last().is_some_and(|idx| *idx == element)),
                PseudoClass::OnlyChild => html_nodes
                    .get(&element)
                    .and_then(|node| node.get_parent())
                    .and_then(|parent| dom_indexes.children_index.get(&parent))
                    .is_some_and(|siblings| siblings.len() == 1 && siblings[0] == element),
                PseudoClass::Empty => dom_indexes
                    .children_index
                    .get(&element)
                    .is_none_or(|children| children.is_empty()),
                PseudoClass::Link => match html_nodes.get(&element).unwrap() {
                    Node::Element(el) => el.tag == "a" && el.attributes.contains_key("href"),
                    _ => false,
                },
                PseudoClass::Visited => false,
                PseudoClass::Disabled => match html_nodes.get(&element).unwrap() {
                    Node::Element(el) => el.attributes.contains_key("disabled"),
                    _ => false,
                },
                _ => false,
            }
        }
        ClassNamePart::Tag(tag) => match html_nodes.get(&element).unwrap() {
            Node::Element(walk_element) => tag == "*" || walk_element.tag == *tag,
            _ => false,
        },
        ClassNamePart::Attributes(attributes) => match html_nodes.get(&element).unwrap() {
            Node::Element(walk_element) => element_matched_attributes(walk_element, attributes),
            _ => false,
        },
        ClassNamePart::Combined(combined) => combined.iter().all(|part| {
            element_matches_class_part(
                part,
                element,
                html_nodes,
                class_elements,
                dom_indexes,
                hovering_chain,
                hovering_has_impact,
            )
        }),
    }
}

fn narrow_elements_by_ancestors(
    element: usize,
    css_nodes: &Vec<(usize, &CssNode)>,
    html_nodes: &HashMap<usize, &Node>,
    class_elements: &HashMap<String, FixedBitSet>,
    css_node: usize,
    name_part_idx: usize,
    nested_part_idx: usize,
    window_size: &PhysicalSize<u32>,
    require_immediate_match: bool,
    dom_indexes: &DomIndexes,
    hovering_chain: &Vec<usize>,
    hovering_has_impact: &mut HashSet<usize>,
) -> bool {
    let walk_quota = if require_immediate_match {
        Some(1)
    } else {
        None
    };
    let node = css_nodes[css_node].1;
    match node {
        CssNode::ClassName(classes) => {
            let parts = &classes.name_parts[name_part_idx];
            let part = &parts[parts.len() - 1 - nested_part_idx];
            if let ClassNamePart::Tilde = part {
                let Some(parent) = html_nodes.get(&element).and_then(|v| v.get_parent()) else {
                    return false;
                };
                let Some(siblings) = dom_indexes.children_index.get(&parent) else {
                    return false;
                };
                let Some(pos) = siblings.iter().position(|sibling| *sibling == element) else {
                    return false;
                };
                return siblings
                    .iter()
                    .enumerate()
                    .filter(|idx| *idx.1 != element && html_nodes.contains_key(idx.1))
                    .any(|(sibling_pos, sibling_idx)| {
                        sibling_pos < pos
                            && move_up_class_part(
                                *sibling_idx,
                                css_nodes,
                                html_nodes,
                                class_elements,
                                parts,
                                css_node,
                                nested_part_idx,
                                name_part_idx,
                                window_size,
                                false,
                                false,
                                dom_indexes,
                                hovering_chain,
                                hovering_has_impact,
                            )
                    });
            };
            let walk_result = walk_for_html_match(
                element,
                html_nodes,
                &mut |idx| {
                    element_matches_class_part(
                        part,
                        idx,
                        html_nodes,
                        class_elements,
                        dom_indexes,
                        hovering_chain,
                        hovering_has_impact,
                    )
                },
                walk_quota,
            );
            let (walk_up_parent, require_immediate_match) = match part {
                ClassNamePart::Class(_)
                | ClassNamePart::Id(_)
                | ClassNamePart::PseudoClass(_)
                | ClassNamePart::Tag(_)
                | ClassNamePart::Attributes(_)
                | ClassNamePart::Combined(_) => (true, false),
                ClassNamePart::Tilde => (false, false),
                ClassNamePart::Ampersand => (false, require_immediate_match),
                ClassNamePart::ArrowRight => (false, true),
            };
            if let Some(html_match) = walk_result {
                return move_up_class_part(
                    html_match,
                    css_nodes,
                    html_nodes,
                    class_elements,
                    parts,
                    css_node,
                    nested_part_idx,
                    name_part_idx,
                    window_size,
                    walk_up_parent,
                    require_immediate_match,
                    dom_indexes,
                    hovering_chain,
                    hovering_has_impact,
                );
            } else {
                return false;
            }
        }
        CssNode::MediaQuery(query) => {
            if media_query_matches(query, window_size) {
                return move_up_ancestor_chain(
                    element,
                    html_nodes,
                    css_nodes,
                    class_elements,
                    node,
                    window_size,
                    false,
                    true,
                    dom_indexes,
                    hovering_chain,
                    hovering_has_impact,
                );
            } else {
                return false;
            }
        }
        // Layers always pass through, they just affect sorting
        CssNode::Layer(_) => {
            return move_up_ancestor_chain(
                element,
                html_nodes,
                css_nodes,
                class_elements,
                node,
                window_size,
                false,
                true,
                dom_indexes,
                hovering_chain,
                hovering_has_impact,
            );
        }
        _ => {
            return false;
        }
    };
}

fn get_parent_html_idx(node_idx: usize, html_nodes: &HashMap<usize, &Node>) -> Option<usize> {
    html_nodes.get(&node_idx).unwrap().get_parent()
}

// Wrapper around search_elements_for_css_nodes that narrows the css_nodes down to only nodes that have property/variable children
// Query selectors skip this step
fn collect_class_nodes_for_elements(
    css_nodes: &Vec<(usize, &CssNode)>,
    raw_html_nodes: &HashMap<usize, Node>,
    window_size: &PhysicalSize<u32>,
    dom_indexes: &DomIndexes,
    hovering_chain: &Vec<usize>,
) -> (
    HashMap<usize, Vec<usize>>,
    HashMap<usize, [i32; 3]>,
    HashSet<usize>,
) {
    // All class names and media queries that have properties/children and need to be resolved
    let mut to_resolve = HashSet::new();
    for (idx, n) in css_nodes.iter() {
        match n {
            CssNode::Property(_) | CssNode::Variable(_) => {
                // TODO: Should probably add back the variables and properties that are at the root at the end, if that's even a thing?
                if let Some(parent) = n.get_parent() {
                    to_resolve.insert(parent);
                } else {
                    println!("Found no parent for css node {}: {:?}", idx, n);
                }
            }
            _ => {}
        };
    }
    search_elements_for_css_nodes(
        to_resolve,
        css_nodes,
        &filter_to_elements(raw_html_nodes),
        window_size,
        dom_indexes,
        hovering_chain,
    )
}

fn filter_to_elements(html_nodes: &HashMap<usize, Node>) -> HashMap<usize, &Node> {
    html_nodes
        .into_iter()
        .filter(|(_, value)| matches!(value, Node::Element(_)))
        .map(|(key, value)| (*key, value))
        .collect()
}

// Returns a tuple representing scores to be ordered by
// (IDs   classes/attrs/pseudo-classes   elements)
// TODO: Implement nested pseudo classes like NOT
fn get_specificity_tuple(parts: &Vec<ClassNamePart>) -> [i32; 3] {
    let mut tuple = [0; 3];
    for part in parts.iter() {
        match part {
            ClassNamePart::Id(_) => tuple[0] += 1,
            ClassNamePart::Attributes(_)
            | ClassNamePart::PseudoClass(_)
            | ClassNamePart::Class(_) => tuple[1] += 1,
            ClassNamePart::Tag(_) => tuple[2] += 1,
            ClassNamePart::Combined(combined) => {
                let specificity = get_specificity_tuple(combined);
                for (idx, value) in specificity.iter().enumerate() {
                    tuple[idx] += value;
                }
            }
            _ => {}
        };
    }
    tuple
}

fn get_base_elements_by_attributes(
    html_nodes: &HashMap<usize, &Node>,
    dom_indexes: &DomIndexes,
    attributes: &Vec<ClassNamePartAttribute>,
) -> FixedBitSet {
    let mut base_items = FixedBitSet::with_capacity(*html_nodes.keys().max().unwrap_or(&0));
    let mut base_items_init = false;
    // Base items are the elements that contain all the keys in attributes
    for attr in attributes.iter() {
        match attr {
            ClassNamePartAttribute::Key(key) => {
                if let Some(matched) = dom_indexes.attribute_elements.get(key) {
                    if !base_items_init {
                        base_items = matched.clone();
                        base_items_init = true;
                    } else {
                        base_items.intersect_with(matched);
                    }
                } else {
                    if !base_items_init {
                        base_items_init = true;
                    }
                    base_items.clear();
                }
            }
            ClassNamePartAttribute::KeyValue((key, _)) => {
                // TODO: Move this to parsing
                let key = key.strip_suffix('*').unwrap_or(key);
                if let Some(matched) = dom_indexes.attribute_elements.get(key) {
                    if !base_items_init {
                        base_items = matched.clone();
                        base_items_init = true;
                    } else {
                        base_items.intersect_with(matched);
                    }
                } else {
                    if !base_items_init {
                        base_items_init = true;
                    }
                    base_items.clear();
                }
            }
        }
    }

    let filtered_elements = base_items
        .ones()
        .filter(|idx| match html_nodes.get(idx).unwrap() {
            Node::Element(element) => element_matched_attributes(element, attributes),
            _ => false,
        })
        .collect();
    filtered_elements
}

fn walk_into_part(part: &ClassNamePart) -> bool {
    *part != ClassNamePart::Tilde
}

// It is assumed that html_nodes only contains Node::Element here
fn search_elements_for_css_nodes(
    to_resolve: HashSet<usize>,
    css_nodes: &Vec<(usize, &CssNode)>,
    html_nodes: &HashMap<usize, &Node>,
    window_size: &PhysicalSize<u32>,
    dom_indexes: &DomIndexes,
    hovering_chain: &Vec<usize>,
) -> (
    HashMap<usize, Vec<usize>>,
    HashMap<usize, [i32; 3]>,
    HashSet<usize>,
) {
    let class_elements = &dom_indexes.class_elements;
    let id_elements = &dom_indexes.id_elements;
    let tag_elements = &dom_indexes.tag_elements;

    let mut matches: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut specificity: HashMap<usize, [i32; 3]> = HashMap::new();

    let mut hovering_has_impact = HashSet::new();

    for css_node_idx in to_resolve {
        let node = css_nodes[css_node_idx].1;
        match node {
            CssNode::ClassName(classes) => {
                for (name_part_idx, parts) in classes.name_parts.iter().enumerate() {
                    if parts.len() == 0 {
                        continue;
                    }
                    let last_part = parts.last().unwrap();
                    let node_specificity = get_specificity_tuple(parts);
                    let all_elements = || {
                        html_nodes
                            .iter()
                            .map(|(idx, _)| idx)
                            .cloned()
                            .collect::<FixedBitSet>()
                    };

                    let elements: Option<FixedBitSet> = match last_part {
                        ClassNamePart::Class(class) => class_elements.get(class).cloned(),
                        ClassNamePart::Id(id) => id_elements.get(id).cloned(),
                        ClassNamePart::PseudoClass(class) => {
                            match class {
                                // No parent means it's a root element
                                PseudoClass::Root => {
                                    let elements = html_nodes
                                        .iter()
                                        .filter(|(_, node)| node.get_parent().is_none())
                                        .map(|(idx, _)| idx)
                                        .cloned()
                                        .collect::<FixedBitSet>();
                                    Some(elements)
                                }
                                // TODO: This looks quite inefficient, should probably try and improve this
                                PseudoClass::Not(selector) => {
                                    let (negative_matches, _, _) = {
                                        let mut to_resolve = HashSet::new();
                                        to_resolve.insert(0);
                                        let class = CssNode::ClassName(ClassName {
                                            name: vec![],
                                            name_parts: vec![selector.clone()],
                                            parent: None,
                                        });
                                        let css_nodes = vec![class];
                                        let css_nodes = css_nodes.iter().enumerate().collect();
                                        search_elements_for_css_nodes(
                                            to_resolve,
                                            &css_nodes,
                                            html_nodes,
                                            window_size,
                                            dom_indexes,
                                            hovering_chain,
                                        )
                                    };
                                    let elements = html_nodes
                                        .iter()
                                        .map(|(idx, _)| idx)
                                        .filter(|idx| !negative_matches.contains_key(idx))
                                        .cloned()
                                        .collect::<FixedBitSet>();
                                    Some(elements)
                                }
                                _ => None,
                            }
                        }
                        ClassNamePart::Tag(tag) => {
                            if tag == "*" {
                                Some(all_elements())
                            } else {
                                tag_elements.get(tag).cloned()
                            }
                        }
                        ClassNamePart::Combined(combined) => {
                            let last_part_combined = combined.last().unwrap();
                            let (indexed, base_elements) = match last_part_combined {
                                ClassNamePart::Tag(tag) => {
                                    if tag == "*" {
                                        (true, Some(all_elements()))
                                    } else {
                                        (true, tag_elements.get(tag).cloned())
                                    }
                                }
                                ClassNamePart::Class(class) => {
                                    (true, class_elements.get(class).cloned())
                                }
                                ClassNamePart::Id(id) => (true, id_elements.get(id).cloned()),
                                ClassNamePart::Attributes(attributes) => (
                                    true,
                                    Some(get_base_elements_by_attributes(
                                        html_nodes,
                                        dom_indexes,
                                        attributes,
                                    )),
                                ),
                                _ => (false, Some(all_elements())),
                            };
                            let rules_to_apply = if indexed {
                                &combined[..combined.len() - 1].to_vec()
                            } else {
                                combined
                            };

                            let capacity = if let Some(base_elements) = &base_elements {
                                base_elements.len()
                            } else {
                                0usize
                            };
                            let mut filtered_elements = FixedBitSet::with_capacity(capacity);
                            if let Some(base_elements) = base_elements {
                                for el in base_elements.ones() {
                                    let matched_all = rules_to_apply.iter().all(|part| {
                                        element_matches_class_part(
                                            part,
                                            el,
                                            &html_nodes,
                                            &class_elements,
                                            dom_indexes,
                                            hovering_chain,
                                            &mut hovering_has_impact,
                                        )
                                    });
                                    if matched_all {
                                        filtered_elements.insert(el);
                                    }
                                }
                            }
                            Some(filtered_elements)
                        }
                        ClassNamePart::Attributes(attributes) => {
                            let filtered_elements = get_base_elements_by_attributes(
                                html_nodes,
                                dom_indexes,
                                attributes,
                            );
                            Some(filtered_elements)
                        }
                        // TODO: Implement remaining name part logic
                        _ => None,
                    };

                    if let Some(elements) = elements {
                        for el in elements.ones() {
                            // If there's only a single part, we've already completed this class name by doing the last one
                            let is_match = if parts.len() == 1 {
                                move_up_ancestor_chain(
                                    el,
                                    &html_nodes,
                                    css_nodes,
                                    &class_elements,
                                    node,
                                    window_size,
                                    false,
                                    true,
                                    dom_indexes,
                                    hovering_chain,
                                    &mut hovering_has_impact,
                                )
                            } else {
                                let next_class_part = &parts[parts.len() - 2];
                                let next_el = if walk_into_part(next_class_part) {
                                    get_parent_html_idx(el, &html_nodes)
                                } else {
                                    Some(el)
                                };
                                if let Some(next_el) = next_el {
                                    narrow_elements_by_ancestors(
                                        next_el,
                                        css_nodes,
                                        &html_nodes,
                                        &class_elements,
                                        css_node_idx,
                                        name_part_idx,
                                        1,
                                        window_size,
                                        false,
                                        dom_indexes,
                                        hovering_chain,
                                        &mut hovering_has_impact,
                                    )
                                } else {
                                    false
                                }
                            };

                            if is_match {
                                matches.entry(el).or_default().push(css_node_idx);
                                // TODO: Probably index this by css node idx + name part idx
                                specificity.insert(css_node_idx, node_specificity);
                            }
                        }
                    }
                }
            }
            CssNode::MediaQuery(query) => {
                if media_query_matches(query, window_size) {
                    let elements: Vec<&usize> = html_nodes
                        .iter()
                        .filter_map(|(idx, node)| match node {
                            Node::Element(_) => Some(idx),
                            _ => None,
                        })
                        .collect();

                    for el in elements {
                        // If there's only a single part, we've already completed this class name by doing the last one
                        let is_match = move_up_ancestor_chain(
                            *el,
                            &html_nodes,
                            css_nodes,
                            &class_elements,
                            node,
                            window_size,
                            false,
                            true,
                            dom_indexes,
                            hovering_chain,
                            &mut hovering_has_impact,
                        );

                        if is_match {
                            matches.entry(*el).or_default().push(css_node_idx);
                        }
                    }
                }
            }
            // Layers always pass through, they just affect sorting
            CssNode::Layer(_) => {
                let elements: Vec<&usize> = html_nodes
                    .iter()
                    .filter_map(|(idx, node)| match node {
                        Node::Element(_) => Some(idx),
                        _ => None,
                    })
                    .collect();

                for el in elements {
                    // If there's only a single part, we've already completed this class name by doing the last one
                    let is_match = move_up_ancestor_chain(
                        *el,
                        &html_nodes,
                        css_nodes,
                        &class_elements,
                        node,
                        window_size,
                        false,
                        true,
                        dom_indexes,
                        hovering_chain,
                        &mut hovering_has_impact,
                    );

                    if is_match {
                        matches.entry(*el).or_default().push(css_node_idx);
                    }
                }
            }
            // Property definitions cannot be walked
            CssNode::PropertyDefinition(_) => {
                //
            }
            _ => println!("Unexpected node appeared: {:?}", node),
        }
    }

    (matches, specificity, hovering_has_impact)
}

fn compute_css_node_ranking(
    raw_nodes: &Vec<CssNode>,
    class_node_specificity: &HashMap<usize, [i32; 3]>,
) -> Vec<usize> {
    let nodes: Vec<(usize, &CssNode)> = raw_nodes.into_iter().enumerate().collect();
    let node_idxs: Vec<&usize> = nodes.iter().map(|(idx, _)| idx).collect();
    let mut chains = HashMap::new();
    for idx in node_idxs.iter() {
        let mut chain = vec![];
        get_parent_chain(&nodes, **idx, &mut chain);
        chains.insert(*idx, chain);
    }
    let mut sorted_idxs = node_idxs.clone();
    sorted_idxs.sort_by(|a, b| {
        let a_important_score = match nodes[**a].1 {
            CssNode::Property(property) => property.important as i32,
            _ => 0i32,
        };
        let b_important_score = match nodes[**b].1 {
            CssNode::Property(property) => property.important as i32,
            _ => 0i32,
        };

        match a_important_score.cmp(&b_important_score) {
            Ordering::Equal => {
                let a_layer = get_parent_layer(&nodes, **a);
                let b_layer = get_parent_layer(&nodes, **b);

                let layer_ordering = a_layer.cmp(&b_layer);

                if layer_ordering != Ordering::Equal {
                    // TODO: Might want to flip this if both nodes have !important
                    return layer_ordering;
                }

                let a_chain = chains.get(a).unwrap();
                let b_chain = chains.get(b).unwrap();

                let a_parent = if a_chain.len() >= 2 {
                    Some(a_chain[1])
                } else {
                    None
                };
                let b_parent = if b_chain.len() >= 2 {
                    Some(b_chain[1])
                } else {
                    None
                };

                let a_specificity = a_parent
                    .and_then(|parent| class_node_specificity.get(&parent))
                    .unwrap_or(&[0; 3]);
                let b_specificity = b_parent
                    .and_then(|parent| class_node_specificity.get(&parent))
                    .unwrap_or(&[0; 3]);

                let specificity_order = get_specificity_order(a_specificity, b_specificity);

                match specificity_order {
                    Ordering::Equal => get_chain_order(a_chain, b_chain),
                    ordering => ordering,
                }
            }
            ordering => ordering,
        }
    });
    let mut rankings = vec![0; raw_nodes.len()];
    for (ranking, idx) in sorted_idxs.into_iter().enumerate() {
        rankings[*idx] = ranking;
    }
    rankings
}

fn fetch_expandable_css(
    base_url: &String,
    tokio: &Rc<RefCell<tokio::runtime::Runtime>>,
    network_fetch: &Rc<RefCell<NetworkFetch>>,
    needs_fetching: &Vec<(usize, &String, &ExpandableCssNode)>,
) -> Result<Vec<String>> {
    let links: Vec<&String> = needs_fetching.iter().map(|(_, n, _)| *n).collect();
    let fetched_nodes = tokio.borrow_mut().block_on(fetch_link_strings(
        base_url,
        &network_fetch,
        &links,
        |str| RequestCacheEntry::CssData(str),
    ))?;
    println!("Fetched {} CSS nodes", fetched_nodes.len());
    Ok(fetched_nodes)
}

fn get_css_nodes(
    base_url: &String,
    tokio: &Rc<RefCell<tokio::runtime::Runtime>>,
    network_fetch: &Rc<RefCell<NetworkFetch>>,
    nodes: &HashMap<usize, Node>,
    root_indice: usize,
    dom_indexes: &DomIndexes,
    css_parse_cache: &mut HashMap<ExpandableCssNode, Vec<CssNode>>,
) -> Vec<CssNode> {
    let expandable = get_expandable_css_nodes(nodes, root_indice, &dom_indexes.children_index);
    let mut parsed_css_chunks = vec![];
    let mut needs_fetching = vec![];
    for (idx, exp) in expandable.iter().enumerate() {
        if let Some(cached) = css_parse_cache.get(&exp) {
            parsed_css_chunks.push((idx, cached.clone()));
        } else {
            match exp {
                ExpandableCssNode::Link(link) => needs_fetching.push((idx, link, exp)),
                ExpandableCssNode::Inline(text) => {
                    let parsed = parse_css_nodes(&vec![text.clone()]).unwrap();
                    css_parse_cache.insert(exp.clone(), parsed.clone());
                    parsed_css_chunks.push((idx, parsed));
                }
            };
        }
    }
    if needs_fetching.len() > 0 {
        let fetched =
            fetch_expandable_css(base_url, tokio, network_fetch, &needs_fetching).unwrap();
        for (str, (idx, _, exp)) in fetched.into_iter().zip(needs_fetching) {
            let parsed = parse_css_nodes(&vec![str]).unwrap();
            css_parse_cache.insert(exp.clone(), parsed.clone());
            parsed_css_chunks.push((idx, parsed));
        }
    }
    flatten_css_chunks(parsed_css_chunks)
}

#[derive(Debug)]
struct ParsedPropertyDefinition {
    property: String,
    #[allow(dead_code)]
    syntax: Option<String>,
    initial_value: Option<String>,
}

fn get_parsed_property_definitions(
    nodes: &Vec<CssNode>,
    css_children_index: &HashMap<usize, Vec<usize>>,
) -> Vec<ParsedPropertyDefinition> {
    let mut definitions = vec![];
    for (idx, node) in nodes.iter().enumerate() {
        let CssNode::PropertyDefinition(definition) = node else {
            continue;
        };
        let Some(children) = css_children_index.get(&idx) else {
            continue;
        };
        let mut syntax = None;
        let mut initial_value = None;
        for child in children.iter() {
            let child_node = &nodes[*child];
            let CssNode::Property(property) = child_node else {
                continue;
            };
            if property.property == "syntax"
                && let PropertyValue::Raw(value) = &property.value
            {
                syntax = Some(value.clone());
            }
            if property.property == "initial-value"
                && let PropertyValue::Raw(value) = &property.value
            {
                initial_value = Some(value.clone());
            }
        }
        definitions.push(ParsedPropertyDefinition {
            property: definition.name.clone(),
            syntax,
            initial_value,
        });
    }
    definitions
}

#[derive(Debug)]
struct VariableDefinitions {
    cursor: usize,
    data: HashMap<usize, ParsedPropertyDefinition>,
    variable_to_idx: HashMap<String, usize>,
}

impl VariableDefinitions {
    pub fn new() -> Self {
        VariableDefinitions {
            cursor: 0,
            data: HashMap::new(),
            variable_to_idx: HashMap::new(),
        }
    }

    pub fn insert_definition(&mut self, def: ParsedPropertyDefinition) {
        self.variable_to_idx
            .insert(def.property.clone(), self.cursor);
        self.data.insert(self.cursor, def);
        self.cursor += 1;
    }
}

fn build_definitions_map(
    parsed_definitions: Vec<ParsedPropertyDefinition>,
    css_nodes: &Vec<CssNode>,
) -> VariableDefinitions {
    let mut definitions = VariableDefinitions::new();
    for def in parsed_definitions {
        definitions.insert_definition(def);
    }
    for node in css_nodes.iter() {
        if let CssNode::Variable(var) = node
            && !definitions.variable_to_idx.contains_key(&var.variable)
        {
            definitions.insert_definition(ParsedPropertyDefinition {
                property: var.variable.clone(),
                syntax: None,
                initial_value: None,
            });
        }
    }
    definitions
}

fn compute_node_styles(
    base_url: &String,
    tokio: &Rc<RefCell<tokio::runtime::Runtime>>,
    network_fetch: &Rc<RefCell<NetworkFetch>>,
    nodes: &HashMap<usize, Node>,
    root_indice: usize,
    window_size: &PhysicalSize<u32>,
    dom_indexes: &DomIndexes,
    css_parse_cache: &mut HashMap<ExpandableCssNode, Vec<CssNode>>,
    hovering_chain: &Vec<usize>,
) -> (
    HashMap<usize, Style>,
    HashMap<usize, u32>,
    VariableDefinitions,
    HashSet<usize>,
) {
    let start = Instant::now();
    let parsed_css_nodes = get_css_nodes(
        base_url,
        tokio,
        network_fetch,
        nodes,
        root_indice,
        dom_indexes,
        css_parse_cache,
    );
    println!(
        "Retrieved parsed css nodes in {}ms",
        Instant::now().duration_since(start).as_millis()
    );

    let css_children_index =
        build_css_children_index(&parsed_css_nodes.iter().enumerate().collect());

    let start = Instant::now();
    let (collected_class_nodes, class_node_specificity, hovering_impact) =
        collect_class_nodes_for_elements(
            &parsed_css_nodes.iter().enumerate().collect(),
            &nodes,
            window_size,
            dom_indexes,
            hovering_chain,
        );
    println!(
        "collect_class_nodes_for_elements took {} microseconds",
        Instant::now().duration_since(start).as_micros()
    );

    let start = Instant::now();
    let css_node_ranking = compute_css_node_ranking(&parsed_css_nodes, &class_node_specificity);

    let mut default_variables = HashMap::new();
    let parsed_definitions =
        get_parsed_property_definitions(&parsed_css_nodes, &css_children_index);
    let definitions_map = build_definitions_map(parsed_definitions, &parsed_css_nodes);
    for (idx, definition) in definitions_map.data.iter() {
        if let Some(initial) = &definition.initial_value {
            default_variables.insert(*idx, initial.to_string());
        }
    }

    let mut node_styles = HashMap::new();
    let mut resolved_font_sizes = HashMap::new();
    compute_node_style(
        &mut node_styles,
        &mut resolved_font_sizes,
        nodes,
        dom_indexes.root_indice,
        &dom_indexes.children_index,
        &parsed_css_nodes,
        None,
        &Rc::new(default_variables),
        None,
        &collected_class_nodes,
        &css_children_index,
        window_size,
        &css_node_ranking,
        &definitions_map,
    );
    println!(
        "computing styles took {}ms",
        Instant::now().duration_since(start).as_millis()
    );
    (
        node_styles,
        resolved_font_sizes,
        definitions_map,
        hovering_impact,
    )
}

#[derive(Debug, Clone)]
enum UserNavigateUrl {
    Raw(String),
    Parsed(ReqwestUrl),
}

#[derive(Debug, Clone)]
enum UserEvent {
    DomUpdated,
    Navigate((UserNavigateUrl, bool)),
    FrameUpdated,
    ChildMessage(String),
}

#[derive(Debug, Clone)]
struct JsHostState {
    renderer: Rc<RefCell<Renderer>>,
    proxy: RendererProxy,
}

#[op2]
fn op_tls_peer_certificate<'s>(
    scope: &mut v8::PinScope<'s, '_>,
    #[smi] _rid: u32,
    _detailed: bool,
) -> v8::Local<'s, v8::Value> {
    v8::null(scope).into()
}

#[op2(fast)]
fn op_set_location_href(
    state: &mut OpState,
    #[string] href: String,
    reload: bool,
) -> Result<(), JsError> {
    let host = state.borrow::<JsHostState>();

    host.proxy
        .fire_user_event(UserEvent::Navigate((UserNavigateUrl::Raw(href), reload)))
        .unwrap();

    Ok(())
}

// TODO: Somehow hook this into fetch as well
#[op2(fast)]
fn op_set_cookie(
    state: &mut OpState,
    #[string] url: String,
    #[string] cookie: String,
) -> Result<(), JsError> {
    let Ok(url) = ReqwestUrl::parse(&url) else {
        return Ok(());
    };

    let host = state.borrow::<JsHostState>();
    let renderer = host.renderer.borrow();
    let network_fetch = renderer.network_fetch.borrow();
    let jar = &network_fetch.cookie_jar;
    jar.add_cookie_str(&cookie, &url);
    Ok(())
}

#[op2]
#[string]
fn op_get_cookie(state: &mut OpState, #[string] url: String) -> Result<String, JsError> {
    let Ok(url) = ReqwestUrl::parse(&url) else {
        return Ok(String::new());
    };

    let host = state.borrow::<JsHostState>();
    let renderer = host.renderer.borrow();
    let network_fetch = renderer.network_fetch.borrow();
    let cookie = network_fetch
        .cookie_jar
        .cookies(&url)
        .and_then(|value| value.to_str().ok().map(String::from))
        .unwrap_or_default();

    Ok(cookie)
}

#[op2(fast)]
fn op_create_element(state: &mut OpState, #[string] tag: String) -> Result<i32, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    renderer.push_node(Node::Element(Element {
        tag,
        attributes: HashMap::new(),
        parent: None,
    }));
    let node_idx = renderer.node_idx_cursor;
    renderer.dom_indexes.children_index.insert(node_idx, vec![]);
    Ok(node_idx as i32)
}

#[op2(fast)]
fn op_create_text_element(state: &mut OpState, #[string] text: String) -> Result<i32, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    renderer.push_node(Node::Text(TextElement { text, parent: None }));
    let node_idx = renderer.node_idx_cursor;
    renderer.dom_indexes.children_index.insert(node_idx, vec![]);
    Ok(node_idx as i32)
}

#[op2]
#[string]
fn op_get_attribute(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[string] attribute: String,
) -> Result<Option<String>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow_mut();
    let value = renderer
        .nodes
        .get(&node_idx)
        .and_then(|node| match node {
            Node::Element(element) => element.attributes.get(&attribute),
            _ => None,
        })
        .cloned();
    Ok(value)
}

#[op2(fast)]
fn op_post_message_to_parent(
    state: &mut OpState,
    #[string] message: String,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    host.proxy
        .fire_user_event(UserEvent::ChildMessage(message))
        .unwrap();
    Ok(())
}

fn get_offset_y_walk(renderer: &Ref<'_, Renderer>, node_idx: usize, mut parent_offset: i32) -> i32 {
    if let Some(scroll_y) = renderer.scroll_y.get(&node_idx) {
        parent_offset += scroll_y;
    }

    if let Some(parent) = renderer
        .nodes
        .get(&node_idx)
        .and_then(|node| node.get_parent())
    {
        get_offset_y_walk(renderer, parent, parent_offset)
    } else {
        parent_offset
    }
}

#[op2(fast)]
fn op_get_offset_y(state: &mut OpState, #[number] node_idx: usize) -> Result<i32, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let offset_y = get_offset_y_walk(&renderer, node_idx, 0);
    Ok(offset_y)
}

#[op2]
#[serde]
fn op_get_attributes(
    state: &mut OpState,
    #[number] node_idx: usize,
) -> Result<Option<HashMap<String, String>>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow_mut();
    let value = renderer
        .nodes
        .get(&node_idx)
        .and_then(|node| match node {
            Node::Element(element) => Some(element.attributes.clone()),
            _ => None,
        })
        .clone();
    Ok(value)
}

#[op2(fast)]
fn op_create_comment_element(
    state: &mut OpState,
    #[string] comment: String,
) -> Result<i32, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    renderer.push_node(Node::Comment(CommentElement {
        comment,
        parent: None,
    }));
    let node_idx = renderer.node_idx_cursor;
    renderer.dom_indexes.children_index.insert(node_idx, vec![]);
    Ok(node_idx as i32)
}

#[op2]
#[serde]
fn op_append_child(
    state: &mut OpState,
    #[number] parent_idx: usize,
    #[number] node_idx: usize,
    #[number] before_reference_idx: Option<usize>,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    if before_reference_idx.is_some_and(|idx| idx == node_idx) {
        return Ok(());
    }
    if let Some(old_parent_idx) = renderer.nodes.get(&node_idx).unwrap().get_parent() {
        if let Some(children) = renderer.dom_indexes.children_index.get_mut(&old_parent_idx) {
            children.retain(|idx| *idx != node_idx);
        }
    }
    renderer
        .nodes
        .get_mut(&node_idx)
        .unwrap()
        .set_parent(Some(parent_idx));
    let children = renderer
        .dom_indexes
        .children_index
        .entry(parent_idx)
        .or_default();
    let insert_pos = before_reference_idx
        .and_then(|before_idx| children.iter().position(|idx| *idx == before_idx))
        .unwrap_or(children.len());
    children.insert(insert_pos, node_idx);
    renderer
        .dom_indexes
        .children_index
        .entry(node_idx)
        .or_default();

    if let Some(before_reference_idx) = before_reference_idx {
        let mut node_pos = None;
        let mut before_pos = None;
        for (pos, idx) in renderer.nodes_idxs.iter().enumerate() {
            if *idx == node_idx {
                node_pos = Some(pos);
            } else if *idx == before_reference_idx {
                before_pos = Some(pos);
            }

            if node_pos.is_some() && before_pos.is_some() {
                break;
            }
        }

        let node_pos = node_pos.unwrap();
        let before_pos = before_pos.unwrap();
        if node_pos != before_pos {
            let idx = renderer.nodes_idxs.remove(node_pos);
            let before_pos = if node_pos < before_pos {
                before_pos - 1
            } else {
                before_pos
            };
            renderer.nodes_idxs.insert(before_pos, idx);
        }
    }
    renderer.recompute_dom_indexes();
    renderer.schedule_dom_update();
    Ok(())
}

#[op2]
#[string]
fn op_get_inner_html(state: &mut OpState, #[number] node_idx: usize) -> Result<String, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let html = host.renderer.borrow_mut().get_element_inner_html(node_idx);
    Ok(html)
}

#[op2(fast)]
fn op_remove_child(state: &mut OpState, #[number] child_idx: usize) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    renderer.remove_node(child_idx, true);
    renderer.recompute_dom_indexes();
    renderer.schedule_dom_update();
    Ok(())
}

#[op2]
fn op_get_node(
    state: &mut OpState,
    #[number] idx: usize,
) -> Result<Option<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    Ok(renderer
        .nodes
        .get(&idx)
        .and_then(|node| Some((idx, node.clone()))))
}

#[op2]
fn op_get_element_by_id(
    state: &mut OpState,
    #[string] id: String,
) -> Result<Option<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let node_idx = renderer
        .dom_indexes
        .id_elements
        .get(&id)
        .and_then(|v| v.minimum());
    let node = node_idx.and_then(|idx| Some((idx, renderer.nodes.get(&idx).unwrap().clone())));
    Ok(node)
}

#[op2]
fn op_get_elements_by_tag_name(
    state: &mut OpState,
    #[string] tag: String,
) -> Result<Vec<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let node_idxs = renderer.dom_indexes.tag_elements.get(&tag);
    let nodes: Vec<(usize, Node)> = if let Some(idxs) = node_idxs {
        idxs.ones()
            .map(|idx| (idx, renderer.nodes.get(&idx).unwrap().clone()))
            .collect()
    } else {
        vec![]
    };
    Ok(nodes)
}

#[op2]
fn op_query_selector(
    state: &mut OpState,
    #[string] selector: String,
    #[number] required_parent: Option<usize>,
) -> Result<Option<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let mut node_idxs: Vec<usize> = query_selector_all(
        &filter_to_elements(&renderer.nodes),
        selector_to_parts(&selector),
        &renderer.window_size,
        &renderer.dom_indexes,
        &renderer.get_hover_chain(),
    );
    if let Some(required_parent) = required_parent {
        node_idxs = node_idxs
            .into_iter()
            .filter(|idx| has_parent(&renderer.nodes, *idx, required_parent))
            .collect();
    }
    let node = node_idxs.first();
    let owned = node
        .cloned()
        .map(|idx| (idx, renderer.nodes.get(&idx).unwrap().clone()));
    Ok(owned)
}

fn walk_closest(buffer: &mut Vec<usize>, nodes: &HashMap<usize, Node>, node_idx: usize) {
    buffer.push(node_idx);
    if let Some(parent) = nodes.get(&node_idx).and_then(|node| node.get_parent()) {
        walk_closest(buffer, nodes, parent);
    }
}

#[op2]
fn op_get_closest(
    state: &mut OpState,
    #[string] selector: String,
    #[number] node_idx: usize,
) -> Result<Option<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let matched_idxs: Vec<usize> = query_selector_all(
        &filter_to_elements(&renderer.nodes),
        selector_to_parts(&selector),
        &renderer.window_size,
        &renderer.dom_indexes,
        &renderer.get_hover_chain(),
    );
    let mut allowed_idxs = vec![];
    walk_closest(&mut allowed_idxs, &renderer.nodes, node_idx);
    let mut allowed_matched_idxs: Vec<usize> = matched_idxs
        .into_iter()
        .filter_map(|idx| allowed_idxs.iter().position(|lidx| idx == *lidx))
        .collect();
    allowed_matched_idxs.sort();
    let most_applicable = allowed_matched_idxs.first().map(|lidx| allowed_idxs[*lidx]);
    let owned = most_applicable.map(|idx| (idx, renderer.nodes.get(&idx).unwrap().clone()));
    Ok(owned)
}

fn has_parent(nodes_table: &HashMap<usize, Node>, node_idx: usize, target_parent: usize) -> bool {
    if node_idx == target_parent {
        return true;
    }

    if let Some(parent) = nodes_table.get(&node_idx).and_then(|v| v.get_parent()) {
        has_parent(nodes_table, parent, target_parent)
    } else {
        false
    }
}

#[op2]
fn op_query_selector_all(
    state: &mut OpState,
    #[string] selector: String,
    #[number] required_parent: Option<usize>,
) -> Result<Vec<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let node_idxs: Vec<usize> = query_selector_all(
        &filter_to_elements(&renderer.nodes),
        selector_to_parts(&selector),
        &renderer.window_size,
        &renderer.dom_indexes,
        &renderer.get_hover_chain(),
    );
    let mut owned: Vec<(usize, Node)> = node_idxs
        .into_iter()
        .map(|idx| (idx, renderer.nodes.get(&idx).unwrap().clone()))
        .collect();
    if let Some(required_parent) = required_parent {
        owned = owned
            .into_iter()
            .filter(|(idx, _)| has_parent(&renderer.nodes, *idx, required_parent))
            .collect();
    }
    Ok(owned)
}

#[op2(fast)]
fn op_set_inner_html(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[string] html: String,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let children = renderer
        .dom_indexes
        .children_index
        .get(&node_idx)
        .unwrap_or(&vec![])
        .clone();
    for child in children {
        renderer.remove_node(child, true);
    }
    renderer.create_children_from_html(node_idx, html);
    renderer.recompute_dom_indexes();
    renderer.schedule_dom_update();
    Ok(())
}

#[op2(fast)]
fn op_set_text_content(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[string] text: String,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();

    match renderer.nodes.get_mut(&node_idx).unwrap() {
        Node::Text(element) => {
            element.text = text;
        }
        Node::Comment(element) => {
            element.comment = text;
        }
        Node::Element(_) => {
            let children = renderer
                .dom_indexes
                .children_index
                .get(&node_idx)
                .unwrap_or(&vec![])
                .clone();
            for child in children {
                renderer.remove_node(child, true);
            }
            renderer.push_node(Node::Text(TextElement {
                text,
                parent: Some(node_idx),
            }));
            let text_idx = renderer.node_idx_cursor;
            renderer
                .dom_indexes
                .children_index
                .insert(node_idx, vec![text_idx]);
            renderer.dom_indexes.children_index.insert(text_idx, vec![]);
        }
    }

    renderer.recompute_dom_indexes();
    renderer.schedule_dom_update();
    Ok(())
}

#[op2]
#[string]
fn op_get_text_content(state: &mut OpState, #[number] node_idx: usize) -> Result<String, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let text = host
        .renderer
        .borrow_mut()
        .get_element_text_content(node_idx);
    Ok(text)
}

#[op2(fast)]
fn op_media_query_matches(state: &mut OpState, #[string] query: String) -> Result<bool, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow_mut();
    let matches = media_query_matches(
        &MediaQuery {
            criterias: parse_media_query_parts(query.as_str()),
            parent: None,
        },
        &renderer.window_size,
    );
    Ok(matches)
}

#[op2]
fn op_get_child_nodes(
    state: &mut OpState,
    #[number] node_idx: usize,
) -> Result<Vec<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow_mut();
    let children: Vec<(usize, Node)> = renderer
        .dom_indexes
        .children_index
        .get(&node_idx)
        .unwrap()
        .iter()
        .map(|idx| (*idx, renderer.nodes.get(idx).unwrap().clone()))
        .collect();
    Ok(children)
}

#[op2]
fn op_get_parent_node(
    state: &mut OpState,
    #[number] node_idx: usize,
) -> Result<Option<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow_mut();
    let parent_idx =
        if let Some(parent) = renderer.nodes.get(&node_idx).and_then(|v| v.get_parent()) {
            parent
        } else {
            return Ok(None);
        };
    let parent = (parent_idx, renderer.nodes.get(&parent_idx).unwrap().clone());
    Ok(Some(parent))
}

#[op2]
#[serde]
fn op_update_attributes(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[serde] attributes: HashMap<String, String>,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    match renderer.nodes.get_mut(&node_idx).unwrap() {
        Node::Element(element) => {
            for (key, value) in attributes {
                element.attributes.insert(key, value);
            }
        }
        _ => {}
    };
    renderer.recompute_dom_indexes();
    renderer.schedule_dom_update();
    Ok(())
}

#[op2(fast)]
fn op_remove_attribute(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[string] attribute: String,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    match renderer.nodes.get_mut(&node_idx).unwrap() {
        Node::Element(element) => {
            element.attributes.remove(&attribute);
        }
        _ => {}
    };
    renderer.recompute_dom_indexes();
    renderer.schedule_dom_update();
    Ok(())
}

fn get_canvas_wh(node: &Node) -> (Option<u32>, Option<u32>) {
    match node {
        Node::Element(element) => (
            element
                .attributes
                .get("width")
                .and_then(|v| v.parse::<u32>().ok())
                .or(Some(150)),
            element
                .attributes
                .get("height")
                .and_then(|v| v.parse::<u32>().ok())
                .or(Some(150)),
        ),
        _ => (None, None),
    }
}

#[op2(fast)]
fn op_fill_canvas_rect(
    state: &mut OpState,
    #[number] node_idx: usize,
    x: f64,
    y: f64,
    width: f64,
    height: f64,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let node = renderer.nodes.get(&node_idx).unwrap();
    let (Some(node_width), Some(node_height)) = get_canvas_wh(node) else {
        return Ok(());
    };

    let x = x.round() as i32;
    let y = y.round() as i32;
    let width = width.round() as u32;
    let height = height.round() as u32;

    let canvas = renderer
        .canvas_buffers
        .entry(node_idx)
        .or_insert_with(|| CanvasBuffer::new(node_width, node_height));
    canvas.resize_if_needed(node_width, node_height);

    draw_rect_filled(
        &mut canvas.buffer,
        false,
        node_width,
        node_height,
        x,
        y,
        width,
        height,
        0x00_00_00_FF,
    );

    renderer.schedule_dom_update();

    Ok(())
}

#[op2(fast)]
fn op_stroke_canvas_rect(
    state: &mut OpState,
    #[number] node_idx: usize,
    x: f64,
    y: f64,
    width: f64,
    height: f64,
    line_width: f64,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let node = renderer.nodes.get(&node_idx).unwrap();
    let (Some(node_width), Some(node_height)) = get_canvas_wh(node) else {
        return Ok(());
    };

    let x = x.round() as i32;
    let y = y.round() as i32;
    let width = width.round() as u32;
    let height = height.round() as u32;
    let line_width = line_width.round() as u32;

    let canvas = renderer
        .canvas_buffers
        .entry(node_idx)
        .or_insert_with(|| CanvasBuffer::new(node_width, node_height));
    canvas.resize_if_needed(node_width, node_height);

    draw_rect_filled(
        &mut canvas.buffer,
        false,
        node_width,
        node_height,
        x,
        y,
        line_width,
        height,
        0x00_00_00_FF,
    ); // Left
    draw_rect_filled(
        &mut canvas.buffer,
        false,
        node_width,
        node_height,
        x,
        y,
        width,
        line_width,
        0x00_00_00_FF,
    ); // Top
    draw_rect_filled(
        &mut canvas.buffer,
        false,
        node_width,
        node_height,
        x + width as i32 - line_width as i32,
        y,
        line_width,
        height,
        0x00_00_00_FF,
    ); // Right
    draw_rect_filled(
        &mut canvas.buffer,
        false,
        node_width,
        node_height,
        x,
        y + height as i32 - line_width as i32,
        width,
        line_width,
        0x00_00_00_FF,
    ); // Bottom

    renderer.schedule_dom_update();

    Ok(())
}

#[op2]
fn op_canvas_path_stroke(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[serde] path: Vec<Vec<f64>>,
    line_width: f64,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let node = renderer.nodes.get(&node_idx).unwrap();
    let (Some(node_width), Some(node_height)) = get_canvas_wh(node) else {
        return Ok(());
    };

    let canvas = renderer
        .canvas_buffers
        .entry(node_idx)
        .or_insert_with(|| CanvasBuffer::new(node_width, node_height));

    let mut cursor = Position {
        x: path[0][0] as i32,
        y: path[0][1] as i32,
    };
    let color_tuple = rgba_to_premul_tuple(0x00_00_00_FF);
    for line in path.iter().skip(1) {
        let x = line[0];
        let y = line[1];
        let start_x = cursor.x as f64;
        let start_y = cursor.y as f64;
        let x_delta = x - cursor.x as f64;
        let y_delta = y - cursor.y as f64;

        let hyp = (x_delta.powi(2) + y_delta.powi(2)).sqrt().round() as i32;
        let stride = node_width as usize;

        let x_ratio = x_delta / hyp as f64;
        let y_ratio = y_delta / hyp as f64;

        let line_width_offset = -line_width as i32 / 2;
        let line_width_end = line_width as i32 / 2;

        for idx in 0..hyp {
            for wxidx in line_width_offset..line_width_end {
                for wyidx in line_width_offset..line_width_end {
                    let px = (start_x + idx as f64 * x_ratio + wxidx as f64)
                        .round()
                        .min(node_width as f64) as i32;
                    let py = (start_y + idx as f64 * y_ratio + wyidx as f64)
                        .round()
                        .min(node_height as f64) as i32;

                    let row = &mut canvas.buffer[py as usize * stride..(py as usize + 1) * stride];
                    row[px as usize] = blend_rgb_with_rgba(row[px as usize], color_tuple);
                }
            }
        }

        cursor.x = x.round() as i32;
        cursor.y = y.round() as i32;
    }

    renderer.schedule_dom_update();

    Ok(())
}

#[op2]
#[serde]
fn op_collect_data_for_form(
    state: &mut OpState,
    #[number] form_node_idx: usize,
) -> HashMap<String, String> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let inputs = renderer.collect_inputs_in_form(form_node_idx, None);
    let mut data = HashMap::new();
    for input in inputs.iter() {
        let Some(Node::Element(element)) = renderer.nodes.get(&input) else {
            continue;
        };
        let Some(name) = element.attributes.get("name") else {
            continue;
        };
        let Some(value) = element.attributes.get("value") else {
            continue;
        };
        data.insert(name.clone(), value.clone());
    }
    data
}

// This should walk the tree to be fully correct I think
fn query_selector_all(
    nodes_table: &HashMap<usize, &Node>,
    selector: Vec<ClassNamePart>,
    window_size: &PhysicalSize<u32>,
    dom_indexes: &DomIndexes,
    hovering_chain: &Vec<usize>,
) -> Vec<usize> {
    let class = CssNode::ClassName(ClassName {
        name: vec![],
        name_parts: vec![selector],
        parent: None,
    });
    let css_vec = vec![class];
    let css_nodes: Vec<(usize, &CssNode)> = css_vec.iter().enumerate().collect();
    let mut to_resolve = HashSet::new();
    to_resolve.insert(0);
    let (collected, _, _) = search_elements_for_css_nodes(
        to_resolve,
        &css_nodes,
        nodes_table,
        window_size,
        dom_indexes,
        hovering_chain,
    );

    collected.keys().cloned().collect()
}

extension!(
  browser,
  ops = [
    op_create_element,
    op_create_text_element,
    op_create_comment_element,
    op_append_child,
    op_remove_child,
    op_get_child_nodes,
    op_get_parent_node,
    op_get_element_by_id,
    op_get_elements_by_tag_name,
    op_query_selector,
    op_query_selector_all,
    op_set_inner_html,
    op_set_text_content,
    op_media_query_matches,
    op_update_attributes,
    op_remove_attribute,
    op_get_inner_html,
    op_get_text_content,
    op_tls_peer_certificate,
    op_fill_canvas_rect,
    op_stroke_canvas_rect,
    op_canvas_path_stroke,
    op_set_cookie,
    op_get_cookie,
    op_set_location_href,
    op_get_node,
    op_get_closest,
    op_get_attribute,
    op_get_attributes,
    op_post_message_to_parent,
    op_get_offset_y,
    op_collect_data_for_form,
  ],
  esm_entry_point = "ext:browser/runtime.js",
  esm = [dir "src", "runtime.js", "runtime_fetch.js"],
  state = |state| {
    let parser = Arc::new(deno_permissions::RuntimePermissionDescriptorParser::new(
      sys_traits::impls::RealSys,
    ));
    state.put(deno_permissions::PermissionsContainer::allow_all(parser));
  },
);

extension!(
    deno_node_crypto_shim,
    esm = ["ext:deno_node/internal/crypto/constants.ts" =
        { source = "export const kKeyObject = Symbol('kKeyObject');" },],
);

fn deno_fetch_without_telemetry() -> deno_core::Extension {
    let mut extension = deno_fetch::deno_fetch::init(Default::default());
    extension.esm_files.to_mut().retain(|source| {
        !matches!(
            source.specifier,
            "ext:deno_fetch/26_fetch.js" | "ext:deno_fetch/27_eventsource.js"
        )
    });
    extension
}

#[derive(Debug)]
pub struct MarginRows {
    rows: Vec<Vec<usize>>,
    alignment_movements: HashMap<usize, i32>,
}

impl MarginRows {
    pub fn new() -> Self {
        Self {
            rows: vec![],
            alignment_movements: HashMap::new(),
        }
    }

    pub fn new_row(&mut self, idx: usize, alignment_movement: i32) {
        self.rows.push(vec![idx]);
        self.alignment_movements.insert(idx, alignment_movement);
    }

    pub fn last_row(&mut self, idx: usize, alignment_movement: i32) {
        if let Some(last) = self.rows.last_mut() {
            last.push(idx);
        } else {
            self.rows.push(vec![idx]);
        }
        self.alignment_movements.insert(idx, alignment_movement);
    }
}

#[derive(Debug, Clone)]
pub enum ScriptContent {
    Link(String),
    Code(String),
}

#[derive(Debug, Clone)]
pub enum ScriptType {
    Classic,
    Module,
}

#[derive(Debug, Clone)]
pub struct Script {
    content: ScriptContent,
    script_type: ScriptType,
    node_idx: Option<usize>,
    defer: bool,
    is_async: bool,
}

fn sorted_node_idxs(nodes: &HashMap<usize, Node>) -> Vec<usize> {
    let mut node_idxs: Vec<usize> = nodes.keys().copied().collect();
    node_idxs.sort_unstable();
    node_idxs
}

fn get_dom_indexes(html_nodes: &HashMap<usize, Node>, nodes_idxs: &Vec<usize>) -> DomIndexes {
    let bitset_capacity = nodes_idxs.iter().max().map_or(0, |idx| idx + 1);

    let mut class_elements: HashMap<String, FixedBitSet> = HashMap::new();
    for (html_node_idx, html_node) in html_nodes.iter() {
        match html_node {
            Node::Element(element) => {
                let class_list = get_class_list(element);
                for class in class_list {
                    class_elements
                        .entry(class)
                        .or_insert_with(|| FixedBitSet::with_capacity(bitset_capacity))
                        .insert(*html_node_idx);
                }
            }
            _ => {}
        };
    }

    let mut id_elements: HashMap<String, FixedBitSet> = HashMap::new();
    for (html_node_idx, html_node) in html_nodes.iter() {
        match html_node {
            Node::Element(element) => {
                if let Some(id) = element.attributes.get("id") {
                    id_elements
                        .entry(id.clone())
                        .or_insert_with(|| FixedBitSet::with_capacity(bitset_capacity))
                        .insert(*html_node_idx);
                }
            }
            _ => {}
        };
    }

    let mut tag_elements: HashMap<String, FixedBitSet> = HashMap::new();
    for (html_node_idx, html_node) in html_nodes.iter() {
        match html_node {
            Node::Element(element) => {
                tag_elements
                    .entry(element.tag.clone())
                    .or_insert_with(|| FixedBitSet::with_capacity(bitset_capacity))
                    .insert(*html_node_idx);
            }
            _ => {}
        };
    }

    let children_index = build_children_index(&html_nodes, nodes_idxs);

    let mut root_indices: Vec<usize> = html_nodes
        .iter()
        .filter_map(|(idx, node)| node.get_parent().is_none().then_some(idx))
        .filter(|idx| match html_nodes.get(idx).unwrap() {
            Node::Element(_) | Node::Text(_) => true,
            Node::Comment(_) => false,
        })
        .cloned()
        .collect();
    root_indices.sort_unstable();
    let root_indice = root_indices
        .iter()
        .find(|idx| match html_nodes.get(idx).unwrap() {
            Node::Element(element) => element.tag == "html",
            Node::Text(_) | Node::Comment(_) => false,
        })
        .or(root_indices.first())
        .copied()
        .expect("Expected at least one root index");

    let mut attribute_elements: HashMap<String, FixedBitSet> = HashMap::new();
    for (html_node_idx, html_node) in html_nodes.iter() {
        let Node::Element(element) = html_node else {
            continue;
        };

        for key in element.attributes.keys() {
            attribute_elements
                .entry(key.clone())
                .or_insert_with(|| FixedBitSet::with_capacity(bitset_capacity))
                .insert(*html_node_idx);
        }
    }

    DomIndexes {
        class_elements,
        tag_elements,
        id_elements,
        children_index,
        attribute_elements,
        root_indice,
    }
}

#[derive(Debug)]
struct CachedRasterizations {
    decoded_pngs: HashMap<String, Pixmap>,
    decoded_jpegs: HashMap<String, DynamicImage>,
    decoded_svgs: HashMap<(String, u32), Tree>,
    jpegs: HashMap<(String, u32, u32), Pixmap>,
    svgs: HashMap<(String, u32, u32), Pixmap>,
}

impl CachedRasterizations {
    pub fn new() -> Self {
        Self {
            decoded_pngs: HashMap::new(),
            decoded_jpegs: HashMap::new(),
            decoded_svgs: HashMap::new(),
            jpegs: HashMap::new(),
            svgs: HashMap::new(),
        }
    }
}

pub enum HtmlEvent {
    Click,
    Change,
}

const FOCUSABLE_ELEMENTS: [&'static str; 2] = ["input", "textarea"];
const FOCUSABLE_INPUT_TYPES: [&'static str; 2] = ["text", "password"];

fn is_supported_form_element(
    element: &Element,
    node_idx: usize,
    submitted_by: Option<usize>,
) -> bool {
    if element.attributes.contains_key("disabled") {
        return false;
    }
    if element.tag == "textarea" && element.attributes.contains_key("name") {
        return true;
    }
    if element.tag == "input" && element.attributes.contains_key("name") {
        return match element
            .attributes
            .get("type")
            .and_then(|v| Some(v.as_str()))
        {
            // If type="submit", only include its value if it was clicked
            Some("submit") => submitted_by.is_some_and(|v| v == node_idx),
            _ => true,
        };
    }
    false
}

fn blit_rgb_buffer(
    dst: &mut [u32],
    dst_width: u32,
    dst_height: u32,
    src: &[u32],
    src_width: u32,
    src_height: u32,
    dst_x: i32,
    dst_y: i32,
) {
    if dst_width == 0 || dst_height == 0 || src_width == 0 || src_height == 0 {
        return;
    }

    let src_x0 = (-dst_x).max(0) as u32;
    let src_y0 = (-dst_y).max(0) as u32;
    let dst_x0 = dst_x.max(0) as u32;
    let dst_y0 = dst_y.max(0) as u32;

    if src_x0 >= src_width || src_y0 >= src_height {
        return;
    }
    if dst_x0 >= dst_width || dst_y0 >= dst_height {
        return;
    }

    let copy_width = (src_width - src_x0).min(dst_width - dst_x0);
    let copy_height = (src_height - src_y0).min(dst_height - dst_y0);

    for row in 0..copy_height {
        let src_start = ((src_y0 + row) * src_width + src_x0) as usize;
        let dst_start = ((dst_y0 + row) * dst_width + dst_x0) as usize;

        let src_row = &src[src_start..src_start + copy_width as usize];
        let dst_row = &mut dst[dst_start..dst_start + copy_width as usize];

        dst_row.copy_from_slice(src_row);
    }
}

impl Renderer {
    fn new(
        url: String,
        tokio: Rc<RefCell<tokio::runtime::Runtime>>,
        nodes_table: HashMap<usize, Node>,
        window_size: PhysicalSize<u32>,
        font_handler: Rc<FontHandler>,
        network_fetch: Rc<RefCell<NetworkFetch>>,
        dom_indexes: DomIndexes,
        nodes_idxs: Vec<usize>,
    ) -> Self {
        let request_cache = HashMap::new();

        let layout_table = HashMap::new();
        let containing_nodes = HashMap::new();
        let node_layout_mapping = HashMap::new();

        let rendered_nodes_ordered = vec![];
        let hovering = None;

        let mut css_parse_cache = HashMap::new();

        let (node_styles, resolved_font_sizes, variable_definitions, hovering_impact) =
            compute_node_styles(
                &url,
                &tokio,
                &network_fetch,
                &nodes_table,
                dom_indexes.root_indice,
                &window_size,
                &dom_indexes,
                &mut css_parse_cache,
                &vec![],
            );

        let node_idx_cursor = nodes_idxs.len();

        Self {
            url,
            node_idx_cursor,
            nodes_idxs,
            nodes: nodes_table,
            node_styles,
            layout_table,
            node_layout_mapping,
            containing_nodes,
            request_cache,
            rendered_nodes_ordered,
            hovering,
            tokio,
            resolved_font_sizes,
            resolved_pixmaps: HashMap::new(),
            window_size,
            font_handler,
            pending_dom_update: false,
            scroll_y: HashMap::new(),
            layout_roots: vec![],
            resolved_specified_heights: HashMap::new(),
            resolved_specified_widths: HashMap::new(),
            resolved_heights: HashMap::new(),
            resolved_widths: HashMap::new(),
            dom_indexes,
            canvas_buffers: HashMap::new(),
            network_fetch,
            cached_rasterizations: CachedRasterizations::new(),
            animations: vec![],
            cached_text_buffers: HashMap::new(),
            css_parse_cache,
            variable_definitions,
            focusable: None,
            event_loop_proxy: None,
            hovering_impact,
            frames: HashMap::new(),
        }
    }

    fn clear_layout_state(&mut self) {
        self.layout_table.clear();
        self.node_layout_mapping.clear();
        self.containing_nodes.clear();
        self.rendered_nodes_ordered.clear();
        self.resolved_pixmaps.clear();
        self.layout_roots.clear();
        self.resolved_specified_heights.clear();
        self.resolved_specified_widths.clear();
        self.resolved_heights.clear();
        self.resolved_widths.clear();
    }

    fn replace_document(
        &mut self,
        url: String,
        nodes_table: HashMap<usize, Node>,
        nodes_idxs: Vec<usize>,
    ) {
        self.url = url;
        self.node_idx_cursor = nodes_idxs.len();
        self.nodes = nodes_table;
        self.nodes_idxs = nodes_idxs;
        self.hovering = None;
        self.pending_dom_update = false;
        self.scroll_y.clear();
        self.canvas_buffers.clear();
        self.animations.clear();
        self.clear_layout_state();
        self.recompute_nodes();
    }

    fn get_implicit_click_events(&self, node_idx: usize) -> Vec<(usize, HtmlEvent)> {
        let node = self.nodes.get(&node_idx).unwrap();
        let mut events = vec![];
        if let Node::Element(element) = node {
            if element.tag == "label" {
                if let Some(for_attr) = element.attributes.get("for") {
                    if let Some(for_elements) = self.dom_indexes.id_elements.get(for_attr) {
                        for el in for_elements.ones() {
                            let node = self.nodes.get(&el).unwrap();
                            if let Node::Element(element) = node {
                                if element.tag == "input"
                                    && element.attributes.get("type").is_some_and(|v| v == "radio")
                                {
                                    events.push((el, HtmlEvent::Change));
                                }
                            }
                        }
                    }
                }
            }
        }
        events
    }

    fn get_scrollable_height(&self) -> (usize, u32) {
        if let Some(hovering) = self.get_scrollable_node_idx() {
            let hovering_layout_idx = self.node_layout_mapping.get(&hovering).unwrap();
            if let Some(layout) = self.layout_table.get(hovering_layout_idx) {
                return (hovering, layout.content_height);
            }
        }
        // TODO: This might not cover all cases, like maybe the HTML tag can be larger than the window? Idk. Might wanna add some scroll logic that is independent from nodes.
        let layout_root_idx = self.layout_roots[0];
        let root_node_idx = self.layout_to_node_idx(&layout_root_idx);
        let root_height = self
            .layout_table
            .get(&layout_root_idx)
            .and_then(|l| Some(l.content_height))
            .unwrap();
        (root_node_idx, root_height)
    }

    fn get_scrollable_node_idx_inner(&self, node_idx: usize) -> Option<usize> {
        let style = self.node_styles.get(&node_idx);
        let allow_scroll = if let Some(layout) = self
            .node_layout_mapping
            .get(&node_idx)
            .and_then(|layout_idx| self.layout_table.get(layout_idx))
        {
            layout.content_height > layout.rect.height
        } else {
            false
        };
        if style.is_some_and(|style| {
            style.overflow_y == Overflow::Auto || style.overflow_y == Overflow::Scroll
        }) && allow_scroll
        {
            Some(node_idx)
        } else if let Some(parent) = self.nodes.get(&node_idx).and_then(|n| n.get_parent()) {
            self.get_scrollable_node_idx_inner(parent)
        } else {
            None
        }
    }

    fn get_scrollable_node_idx(&self) -> Option<usize> {
        if let Some(hovering) = self.hovering {
            self.get_scrollable_node_idx_inner(self.layout_to_node_idx(&hovering))
        } else {
            None
        }
    }

    pub fn get_scripts(&mut self) -> Vec<Script> {
        let mut scripts: Vec<Script> = self
            .nodes_idxs
            .iter()
            .filter(|node_idx| match self.nodes.get(*node_idx).unwrap() {
                Node::Element(element) => element.tag == "script",
                _ => false,
            })
            .map(|idx| -> Option<Script> {
                match self.nodes.get(idx).unwrap() {
                    Node::Element(element) => {
                        let script_type = match element
                            .attributes
                            .get("type")
                            .map(|v| v.trim().to_ascii_lowercase())
                        {
                            None => ScriptType::Classic,
                            Some(script_type) if script_type.is_empty() => ScriptType::Classic,
                            Some(script_type) if script_type == "text/javascript" => {
                                ScriptType::Classic
                            }
                            Some(script_type) if script_type == "application/javascript" => {
                                ScriptType::Classic
                            }
                            Some(script_type) if script_type == "text/ecmascript" => {
                                ScriptType::Classic
                            }
                            Some(script_type) if script_type == "application/ecmascript" => {
                                ScriptType::Classic
                            }
                            Some(script_type) if script_type == "module" => ScriptType::Module,
                            _ => return None,
                        };
                        let src = element.attributes.get("src");
                        let has_src = src.is_some();
                        let is_async = has_src && element.attributes.get("async").is_some();
                        let defer =
                            has_src && !is_async && element.attributes.get("defer").is_some();
                        if let Some(src) = src {
                            return Some(Script {
                                content: ScriptContent::Link(src.to_string()),
                                script_type,
                                node_idx: Some(*idx),
                                defer,
                                is_async,
                            });
                        }

                        let children = &self.dom_indexes.children_index.get(idx).unwrap();
                        if children.len() != 1 {
                            println!("Unexpected children count: {}", children.len());
                            return None;
                        }
                        let child = children.first().unwrap();
                        let child_node = &self.nodes.get(child).unwrap();

                        let text = match child_node {
                            Node::Element(element) => {
                                println!("Got element when expecting JS text {:?}", element);
                                return None;
                            }
                            Node::Text(text_element) => Some(Script {
                                content: ScriptContent::Code(text_element.text.clone()),
                                script_type,
                                node_idx: Some(*idx),
                                defer,
                                is_async,
                            }),
                            Node::Comment(_) => {
                                return None;
                            }
                        };

                        text
                    }
                    Node::Text(_) | Node::Comment(_) => None,
                }
            })
            .flatten()
            .collect();

        scripts.sort_by(|a, b| {
            let defer_order = (a.defer as u32).cmp(&(b.defer as u32));
            if defer_order != Ordering::Equal {
                defer_order
            } else {
                let async_order = (a.is_async as u32).cmp(&(b.is_async as u32));
                if async_order != Ordering::Equal {
                    async_order
                } else {
                    (a.script_type.clone() as u32).cmp(&(b.script_type.clone() as u32))
                }
            }
        });

        scripts
    }

    pub fn walk_node_upwards(&self, idx: usize, callback: impl Fn(&Node) -> bool) -> Option<usize> {
        if let Some(node) = self.nodes.get(&idx) {
            if callback(node) {
                return Some(idx);
            }

            if let Some(parent) = node.get_parent() {
                return self.walk_node_upwards(parent, callback);
            }
        }
        None
    }

    fn submit_form_walk(
        &self,
        inputs: &mut Vec<usize>,
        node_idx: usize,
        submitted_by: Option<usize>,
    ) {
        if let Some(node) = self.nodes.get(&node_idx) {
            if let Node::Element(element) = node
                && is_supported_form_element(element, node_idx, submitted_by)
            {
                inputs.push(node_idx);
            }

            if let Some(children) = self.dom_indexes.children_index.get(&node_idx) {
                for c in children {
                    self.submit_form_walk(inputs, *c, submitted_by);
                }
            }
        }
    }

    pub fn collect_inputs_in_form(&self, form: usize, submitted_by: Option<usize>) -> Vec<usize> {
        let mut inputs = vec![];
        self.submit_form_walk(&mut inputs, form, submitted_by);
        inputs
    }

    pub fn submit_form(&mut self, form: usize, submitted_by: Option<usize>) -> Result<()> {
        let Some(Node::Element(element)) = self.nodes.get(&form) else {
            return Err(anyhow!("Failed to get form node"));
        };
        let Some(action) = element.attributes.get("action") else {
            return Ok(());
        };
        let inputs = self.collect_inputs_in_form(form, submitted_by);

        let base_url = ReqwestUrl::parse(&self.url)?;
        let mut parsed_url = resolve_url(action, Some(&base_url))?;

        {
            let mut query_parms = parsed_url.query_pairs_mut();
            for input in inputs {
                let Some(Node::Element(element)) = self.nodes.get(&input) else {
                    continue;
                };
                let Some(name) = element.attributes.get("name") else {
                    continue;
                };
                let Some(value) = element.attributes.get("value") else {
                    continue;
                };
                query_parms.append_pair(name, value);
            }
        };

        let proxy = self.event_loop_proxy.as_ref().unwrap();
        proxy
            .fire_user_event(UserEvent::Navigate((
                UserNavigateUrl::Parsed(parsed_url),
                true,
            )))
            .unwrap();

        Ok(())
    }

    fn apply_overflow_constraints_inner(
        &mut self,
        layout_box_id: usize,
        mut overflow_box: Option<(u32, u32, u32, u32)>,
    ) {
        let layout_box = self.layout_table.get_mut(&layout_box_id).unwrap();

        if let Some((start_x, start_y, end_x, end_y)) = overflow_box {
            layout_box.rect.x = layout_box.rect.x.max(start_x as i32);
            layout_box.rect.y = layout_box.rect.y.max(start_y as i32);
            let target_end_x = layout_box.rect.x + layout_box.rect.width as i32;
            let overflow_right = target_end_x - end_x as i32;
            layout_box.rect.width = layout_box
                .rect
                .width
                .saturating_sub_signed(overflow_right.max(0));
            let target_end_y = layout_box.rect.y + layout_box.rect.height as i32;
            let overflow_bottom = target_end_y - end_y as i32;
            layout_box.rect.height = layout_box
                .rect
                .height
                .saturating_sub_signed(overflow_bottom.max(0));
        }

        if !layout_box.allow_overflow {
            let rect = &layout_box.rect;
            overflow_box = Some((
                rect.x as u32,
                rect.y as u32,
                (rect.x + rect.width as i32) as u32,
                (rect.y + rect.height as i32) as u32,
            ));
        }

        for child in layout_box.children.clone() {
            self.apply_overflow_constraints_inner(child, overflow_box);
        }
    }

    fn apply_overflow_constraints(&mut self) {
        for l in self.layout_roots.clone() {
            self.apply_overflow_constraints_inner(l, None);
        }
    }

    fn render_into(&mut self, buffer: &mut [u32], width: u32, height: u32, rebuild_layout: bool) {
        if width == 0 || height == 0 {
            return;
        }

        clear_buffer(buffer, 0xFF_FF_FF_FF);

        if rebuild_layout {
            self.clear_layout_state();
            self.layout_roots = self.build_layout(width, height);
            self.apply_overflow_constraints();
        }
        let mut new_rendered_nodes_ordered = vec![];
        for layout_box_idx in self.layout_roots.clone().iter() {
            let scroll_y = self
                .scroll_y
                .get(&self.layout_to_node_idx(&layout_box_idx))
                .cloned()
                .unwrap_or(0);
            self.paint_layout_box(
                *layout_box_idx,
                buffer,
                width,
                height,
                scroll_y,
                &mut new_rendered_nodes_ordered,
            );
        }
        self.rendered_nodes_ordered = new_rendered_nodes_ordered;
    }

    fn move_entire_box(&mut self, layout_box_idx: usize, x: i32, y: i32) {
        let layout_box = self.layout_table.get_mut(&layout_box_idx).unwrap();
        layout_box.rect.x += x;
        layout_box.rect.y += y;
        for child in layout_box.children.clone() {
            self.move_entire_box(child, x, y);
        }
    }

    fn tick_animations(&mut self) -> bool {
        if self.animations.len() > 0 {
            let mut to_keep = vec![];
            let now = SystemTime::now();
            for a in self.animations.iter() {
                match a {
                    Animation::ScrollAnimation(animation) => {
                        let elapsed = now.duration_since(animation.start_at).unwrap();
                        let progress = elapsed.div_duration_f32(animation.duration).clamp(0., 1.);
                        let curr_value = animation.start as f32
                            + (animation.end - animation.start) as f32 * progress;
                        self.scroll_y.insert(animation.node_idx, curr_value as i32);
                    }
                }
                if a.is_done(now) {
                    continue;
                }
                to_keep.push(a.clone());
            }
            self.animations = to_keep;
            self.animations.len() > 0
        } else {
            false
        }
    }

    fn img_src_extension(src: &str) -> Option<&'static str> {
        if src.ends_with(".png") {
            Some("image/png")
        } else if src.ends_with(".svg") {
            Some("image/svg+xml")
        } else if src.ends_with(".jpg") || src.ends_with(".jpeg") {
            Some("image/jpeg")
        } else {
            None
        }
    }

    async fn fetch_img_src_data_url(
        client: reqwest::Client,
        url: ReqwestUrl,
        src_extension: &'static str,
    ) -> (ReqwestUrl, Result<RequestCacheEntry>) {
        println!("Fetching img src: {}", url);
        let fetch_url = url.clone();
        let cache_entry = async move {
            let resp = client
                .get(fetch_url)
                .header(reqwest::header::ACCEPT, src_extension)
                .send()
                .await?;
            let content_type = resp
                .headers()
                .get("content-type")
                .and_then(|v| v.to_str().ok())
                // TODO: Consider whether this is a sane production default
                .or(Some(src_extension))
                .with_context(|| "Failed to get content-type for image")?;
            match content_type {
                "image/png" => Ok(RequestCacheEntry::PngData(resp.bytes().await?)),
                "image/svg+xml" => Ok(RequestCacheEntry::SvgData(resp.text().await?)),
                "image/jpeg" => Ok(RequestCacheEntry::JpegData(resp.bytes().await?)),
                content_type => Err(anyhow!(
                    "Failed to handle image content-type: {}",
                    content_type
                )),
            }
        }
        .await;

        (url, cache_entry)
    }

    fn prefetch_images(&mut self) {
        let base = match ReqwestUrl::parse(&self.url) {
            Ok(base) => base,
            Err(err) => {
                println!("Failed to parse base URL for image prefetch: {}", err);
                return;
            }
        };
        let mut seen = HashSet::new();
        let requests: Vec<(ReqwestUrl, &'static str)> = self
            .nodes
            .iter()
            .filter_map(|(idx, n)| match n {
                Node::Element(element)
                    if element.tag == "img"
                        && self
                            .node_styles
                            .get(idx)
                            .is_some_and(|v| v.display != StyleDisplay::None) =>
                {
                    element.attributes.get("src").map(|src| src.as_str())
                }
                _ => None,
            })
            .filter(|src| !src.starts_with("data:"))
            .filter_map(|src| {
                let url = match resolve_url(src, Some(&base)) {
                    Ok(url) => url,
                    Err(err) => {
                        println!("Failed to resolve image URL {}: {}", src, err);
                        return None;
                    }
                };
                if self.request_cache.contains_key(&url) || !seen.insert(url.clone()) {
                    return None;
                }

                Some((url, Self::img_src_extension(src)?))
            })
            .collect();

        println!("Pre-fetching {} images", requests.len());

        if requests.is_empty() {
            return;
        }

        let client = self.network_fetch.borrow().client.clone();
        let results = self.tokio.clone().borrow_mut().block_on(async move {
            let mut join_set = tokio::task::JoinSet::new();
            for (url, src_extension) in requests {
                let client = client.clone();
                join_set.spawn(Self::fetch_img_src_data_url(client, url, src_extension));
            }

            let mut results = Vec::new();
            while let Some(result) = join_set.join_next().await {
                match result {
                    Ok(result) => results.push(result),
                    Err(err) => println!("Failed to join image fetch task: {}", err),
                }
            }
            results
        });

        for (url, cache_entry) in results {
            match cache_entry {
                Ok(entry) => {
                    self.request_cache.insert(url, entry);
                }
                Err(err) => {
                    println!("Failed to prefetch img src {}: {}", url, err);
                    self.request_cache
                        .insert(url, RequestCacheEntry::Unsupported);
                }
            }
        }
    }

    fn build_layout(&mut self, width: u32, height: u32) -> Vec<usize> {
        let mut layout_roots = Vec::new();

        self.node_layout_mapping.clear();

        self.prefetch_images();

        // Create initial containing node
        self.containing_nodes.insert(
            self.dom_indexes.root_indice,
            ContainingNode {
                node_idx: self.dom_indexes.root_indice,
                waiters: vec![],
            },
        );
        let containing_node_idx = self.dom_indexes.root_indice;

        if let Some(layout_box_idx) = self.layout_node(
            self.dom_indexes.root_indice,
            Position { x: 0, y: 0 },
            Size { width, height },
            OptionalSize {
                height: None,
                width: None,
            },
            containing_node_idx,
            true,
            true,
            &LayoutMode::Complete,
        ) {
            layout_roots.push(layout_box_idx);
        }

        layout_roots
    }

    fn inject_css_variables_into_str(&self, str: &mut String, variables: &HashMap<usize, String>) {
        // Return early if string doesn't need any vars
        if !str.contains("var(") {
            return;
        }
        for (variable, value) in variables.iter() {
            let variable = self.variable_definitions.data.get(variable).unwrap();
            *str = str.replace(&format!("var({})", variable.property), value);
        }
    }

    fn get_element_text_content(&self, node_idx: usize) -> String {
        let mut str = String::new();
        for child_idx in self.dom_indexes.children_index.get(&node_idx).unwrap() {
            str += &self.get_text_content(*child_idx);
        }
        str
    }

    fn get_element_inner_html(&self, node_idx: usize) -> String {
        let mut str = String::new();
        for child_idx in self.dom_indexes.children_index.get(&node_idx).unwrap() {
            str += &self.get_element_html(*child_idx);
        }
        str
    }

    fn get_text_content(&self, node_idx: usize) -> String {
        let node = &self.nodes.get(&node_idx).unwrap();
        let mut str = String::new();
        match node {
            Node::Text(element) => {
                str += &element.text;
            }
            Node::Element(_) => {
                for child_idx in self.dom_indexes.children_index.get(&node_idx).unwrap() {
                    str += &self.get_text_content(*child_idx);
                }
            }
            Node::Comment(_) => {}
        };
        str
    }

    fn get_element_html(&self, node_idx: usize) -> String {
        let node = &self.nodes.get(&node_idx).unwrap();
        let mut str = String::new();
        match node {
            Node::Text(element) => {
                str += &element.text;
            }
            Node::Element(element) => {
                str += "<";
                str += &element.tag;
                for (key, value) in element.attributes.iter() {
                    str += " ";
                    str += key;
                    str += "=\"";
                    str += value;
                    str += "\"";
                }
                str += ">";
                for child_idx in self.dom_indexes.children_index.get(&node_idx).unwrap() {
                    str += &self.get_element_html(*child_idx);
                }
                str += "</";
                str += &element.tag;
                str += ">";
            }
            Node::Comment(element) => {
                str += &format!("<!--{}-->", element.comment);
            }
        }
        str
    }

    async fn get_img_src_data(&mut self, src: &str) -> Result<RequestCacheEntry> {
        let base = ReqwestUrl::parse(&self.url)?;
        let url = resolve_url(src, Some(&base))?;
        let src_extension = Self::img_src_extension(src)
            .with_context(|| format!("Unsupported img extension: {}", src))?;
        if let Some(cache) = self.request_cache.get(&url) {
            match cache {
                RequestCacheEntry::Unsupported => Err(anyhow!("Unsupported image")),
                v => Ok(v.clone()),
            }
        } else {
            let (url, cache_entry) = Self::fetch_img_src_data_url(
                self.network_fetch.borrow().client.clone(),
                url,
                src_extension,
            )
            .await;
            if let Ok(ref entry) = cache_entry {
                self.request_cache.insert(url, entry.clone());
            } else {
                self.request_cache
                    .insert(url, RequestCacheEntry::Unsupported);
            }
            cache_entry
        }
    }

    fn register_layout_box(&mut self, layout_box: LayoutBox, save_as_final: bool) -> usize {
        // This effectively acts as a vector right now
        let node_idx = layout_box.node_idx;
        let idx = self.layout_table.len() + 1;
        self.layout_table.insert(idx, layout_box);
        // Only store first team as that'll be the highest parent
        if save_as_final && !self.node_layout_mapping.contains_key(&node_idx) {
            self.node_layout_mapping.insert(node_idx, idx);
        }
        idx
    }

    // Get resolved parent font size, or fall back to base font size (16)
    fn get_parent_font_size(&self, node_idx: usize) -> u32 {
        let resolved_parent_font_size = self
            .resolved_font_sizes
            .get(
                &self
                    .nodes
                    .get(&node_idx)
                    .unwrap()
                    .get_parent()
                    .unwrap_or(node_idx),
            )
            .unwrap_or(&16);
        *resolved_parent_font_size
    }

    fn layout_node(
        &mut self,
        node_idx: usize,
        cursor: Position,
        available_size: Size,
        forced_size: OptionalSize,
        containing_node_idx: usize,
        allow_fill: bool,
        save_as_final: bool,
        mode: &LayoutMode,
    ) -> Option<usize> {
        let resolved_font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();

        match self.nodes.get(&node_idx).unwrap().clone() {
            Node::Comment(_) => None,
            Node::Text(text) => {
                let style = self.node_styles.get(&node_idx).unwrap();
                let text = collapse_whitespace(&text.text).unwrap_or("".to_string());
                let text_hex = match style.color {
                    StyleBackground::Hex(code) => Some(code),
                    _ => None,
                }?;
                let (buffer, width, height) = if let Some(cached) = self
                    .cached_text_buffers
                    .get(&(text.clone(), resolved_font_size))
                {
                    cached
                } else {
                    let result = text_to_buffer(
                        &self.font_handler,
                        text_hex,
                        &text.clone(),
                        resolved_font_size,
                        Some(available_size.width),
                    )?;
                    self.cached_text_buffers
                        .insert((text.clone(), resolved_font_size), result);
                    self.cached_text_buffers.get(&(text, resolved_font_size))?
                };

                Some(self.register_layout_box(
                    LayoutBox {
                        rect: Rect {
                            x: cursor.x,
                            y: cursor.y,
                            width: *width,
                            height: *height,
                            background: StyleBackground::Transparent,
                            border: RectBorder::new_empty(),
                        },
                        // TODO: Can probably avoid cloning here
                        kind: LayoutKind::Text(buffer.clone()),
                        children: vec![],
                        node_idx,
                        allow_overflow: style.overflow_y.visible(),
                        content_height: *height,
                        z_index: 0,
                    },
                    save_as_final,
                ))
            }
            Node::Element(element) => {
                if element.tag == "svg" || element.tag == "img" || element.tag == "canvas" {
                    let style = self.node_styles.get(&node_idx).unwrap().clone();
                    if let StyleDisplay::None = style.display {
                        return None;
                    }
                    let container_size = self.get_container_sizes(
                        node_idx,
                        &OptionalSize {
                            height: None,
                            width: None,
                        },
                        &style,
                        &available_size,
                    );
                    let (containing_block_height, containing_block_width) =
                        self.get_containing_block_size(containing_node_idx, node_idx, &style);
                    let max_h = get_specified_size(
                        resolved_font_size as u32,
                        &style.max_height,
                        containing_block_height,
                        None,
                        &self.window_size,
                    )
                    .map(|height| height as u32)
                    .unwrap_or(
                        container_size
                            .container_height_non_filling
                            .unwrap_or(available_size.height),
                    );
                    let max_w = get_specified_size(
                        resolved_font_size as u32,
                        &style.max_width,
                        containing_block_width,
                        None,
                        &self.window_size,
                    )
                    .map(|width| width as u32)
                    .unwrap_or(
                        container_size
                            .container_width_non_filling
                            .unwrap_or(available_size.width),
                    );
                    let (pixmap, height, width, opaque) = match element.tag.as_str() {
                        "canvas" => {
                            let (Some(canvas_width), Some(canvas_height)) =
                                (match self.nodes.get(&node_idx).unwrap() {
                                    Node::Element(element) => (
                                        element
                                            .attributes
                                            .get("width")
                                            .and_then(|v| v.parse::<u32>().ok())
                                            .or(Some(150)),
                                        element
                                            .attributes
                                            .get("height")
                                            .and_then(|v| v.parse::<u32>().ok())
                                            .or(Some(150)),
                                    ),
                                    _ => (None, None),
                                })
                            else {
                                return None;
                            };
                            let canvas = self
                                .canvas_buffers
                                .entry(node_idx)
                                .or_insert_with(|| CanvasBuffer::new(canvas_width, canvas_height));
                            canvas.resize_if_needed(canvas_width, canvas_height);
                            let data = rgba_buffer_to_premul_bytes(&canvas.buffer);
                            let pixmap = tiny_skia::Pixmap::from_vec(
                                data,
                                IntSize::from_wh(canvas_width, canvas_height)?,
                            )?;
                            (
                                pixmap,
                                container_size.container_height,
                                container_size.container_width,
                                false,
                            )
                        }
                        "svg" => {
                            let mut svg_data = self.get_element_html(node_idx);
                            self.inject_css_variables_into_str(&mut svg_data, &style.variables);
                            let result = rasterize_svg(
                                &mut self.cached_rasterizations,
                                &svg_data,
                                container_size.container_width_non_filling,
                                container_size.container_height_non_filling,
                                max_w,
                                max_h,
                                &style,
                                mode,
                            );
                            match result {
                                Err(err) => {
                                    println!("Failed to rasterize SVG data: {}", err);
                                    return None;
                                }
                                Ok(res) => res,
                            }
                        }
                        "img" => {
                            let src = element.attributes.get("src")?;
                            if src.starts_with("data:") {
                                if let Some(data) = src.strip_prefix("data:image/svg+xml,") {
                                    let mut decoded = percent_encoding::percent_decode_str(data)
                                        .decode_utf8()
                                        .ok()?
                                        .to_string();
                                    self.inject_css_variables_into_str(
                                        &mut decoded,
                                        &style.variables,
                                    );
                                    let result = rasterize_svg(
                                        &mut self.cached_rasterizations,
                                        &decoded,
                                        container_size.container_width_non_filling,
                                        container_size.container_height_non_filling,
                                        max_w,
                                        max_h,
                                        &style,
                                        mode,
                                    );
                                    match result {
                                        Err(err) => {
                                            println!("Failed to rasterize SVG data: {}", err);
                                            return None;
                                        }
                                        Ok(res) => res,
                                    }
                                } else {
                                    return None;
                                }
                            } else {
                                let img_data = self
                                    .tokio
                                    .clone()
                                    .borrow_mut()
                                    .block_on(self.get_img_src_data(src))
                                    .ok()?;
                                let result = match img_data {
                                    RequestCacheEntry::PngData(bytes) => rasterize_png(
                                        &mut self.cached_rasterizations,
                                        src,
                                        &bytes,
                                        container_size.container_width_non_filling,
                                        container_size.container_height_non_filling,
                                        max_w,
                                        max_h,
                                        mode,
                                    )
                                    .unwrap(),
                                    RequestCacheEntry::JpegData(bytes) => {
                                        let (target_h, target_w) = prepare_jpeg(
                                            &mut self.cached_rasterizations,
                                            &src,
                                            &bytes,
                                            container_size.container_width_non_filling,
                                            container_size.container_height_non_filling,
                                            max_w,
                                            max_h,
                                        )
                                        .unwrap();
                                        if *mode == LayoutMode::Complete {
                                            let pixmap = rasterize_jpeg(
                                                &mut self.cached_rasterizations,
                                                src,
                                                target_w,
                                                target_h,
                                            )
                                            .unwrap();
                                            (pixmap, target_h, target_w, true)
                                        } else {
                                            (
                                                Pixmap::new(target_w, target_h).unwrap(),
                                                target_h,
                                                target_w,
                                                true,
                                            )
                                        }
                                    }
                                    RequestCacheEntry::SvgData(svg_data) => {
                                        let mut injected = svg_data.clone();
                                        self.inject_css_variables_into_str(
                                            &mut injected,
                                            &style.variables,
                                        );
                                        let result = rasterize_svg(
                                            &mut self.cached_rasterizations,
                                            &injected,
                                            container_size.container_width_non_filling,
                                            container_size.container_height_non_filling,
                                            max_w,
                                            max_h,
                                            &style,
                                            mode,
                                        );
                                        match result {
                                            Err(err) => {
                                                println!("Failed to rasterize SVG data: {}", err);
                                                return None;
                                            }
                                            Ok(res) => res,
                                        }
                                    }
                                    _ => panic!(),
                                };
                                result
                            }
                        }
                        _ => panic!(),
                    };
                    let z_index = match style.z_index {
                        StyleZIndex::Auto => 0,
                        StyleZIndex::Number(value) => value,
                    };

                    Some(self.register_layout_box(
                        LayoutBox {
                            rect: Rect {
                                x: cursor.x,
                                y: cursor.y,
                                width,
                                height,
                                background: StyleBackground::Transparent,
                                border: RectBorder::new_empty(),
                            },
                            kind: LayoutKind::PixMap((pixmap, opaque)),
                            children: vec![],
                            node_idx,
                            allow_overflow: style.overflow_y.visible(),
                            content_height: height,
                            z_index,
                        },
                        save_as_final,
                    ))
                } else if element.tag == "iframe" {
                    let height = element
                        .attributes
                        .get("height")
                        .and_then(|v| v.parse::<f32>().ok())
                        .unwrap_or(150.) as u32;
                    let width = element
                        .attributes
                        .get("width")
                        .and_then(|v| v.parse::<f32>().ok())
                        .unwrap_or(300.) as u32;
                    let Some(url) = element.attributes.get("src") else {
                        return None;
                    };
                    let style = self.node_styles.get(&node_idx).unwrap();
                    let z_index = match style.z_index {
                        StyleZIndex::Auto => 0,
                        StyleZIndex::Number(value) => value,
                    };
                    if !self.frames.contains_key(&node_idx) {
                        let handle = self
                            .spawn_frame(url.clone(), PhysicalSize { width, height })
                            .ok()?;
                        self.frames.insert(node_idx, handle);
                    }
                    Some(self.register_layout_box(
                        LayoutBox {
                            rect: Rect {
                                x: cursor.x,
                                y: cursor.y,
                                width,
                                height,
                                background: StyleBackground::Transparent,
                                border: RectBorder {
                                    left: None,
                                    top: None,
                                    right: None,
                                    bottom: None,
                                },
                            },
                            kind: LayoutKind::Iframe,
                            children: vec![],
                            node_idx,
                            allow_overflow: false,
                            content_height: height,
                            z_index,
                        },
                        save_as_final,
                    ))
                } else {
                    let layout = match self.node_styles.get(&node_idx).unwrap().display {
                        StyleDisplay::Block | StyleDisplay::InlineBlock | StyleDisplay::Inline => {
                            self.layout_block(
                                node_idx,
                                cursor,
                                available_size,
                                forced_size,
                                containing_node_idx,
                                allow_fill,
                                save_as_final,
                                mode,
                            )
                        }
                        StyleDisplay::Flex | StyleDisplay::InlineFlex => self.layout_flex(
                            node_idx,
                            cursor,
                            available_size,
                            forced_size,
                            containing_node_idx,
                            allow_fill,
                            save_as_final,
                            mode,
                        ),
                        StyleDisplay::Grid => self.layout_grid(
                            node_idx,
                            cursor,
                            available_size,
                            forced_size,
                            containing_node_idx,
                            allow_fill,
                            save_as_final,
                            mode,
                        ),
                        StyleDisplay::None => None,
                    };

                    if let Some((width, height, mut children, content_height)) = layout {
                        let style = self.node_styles.get(&node_idx).unwrap();
                        let style_bg = style.background.clone();
                        let allow_overflow = style.overflow_y.visible();
                        let border = RectBorder {
                            left: RectBorderSide::parse_from_style(
                                &style.border_left,
                                resolved_font_size as u32,
                                &available_size,
                                &self.window_size,
                            ),
                            top: RectBorderSide::parse_from_style(
                                &style.border_top,
                                resolved_font_size as u32,
                                &available_size,
                                &self.window_size,
                            ),
                            right: RectBorderSide::parse_from_style(
                                &style.border_right,
                                resolved_font_size as u32,
                                &available_size,
                                &self.window_size,
                            ),
                            bottom: RectBorderSide::parse_from_style(
                                &style.border_bottom,
                                resolved_font_size as u32,
                                &available_size,
                                &self.window_size,
                            ),
                        };
                        let z_index = match style.z_index {
                            StyleZIndex::Auto => 0,
                            StyleZIndex::Number(value) => value,
                        };

                        if let StyleBackground::DataUrl((format, data)) = &style_bg {
                            let container_size = self.get_container_sizes(
                                node_idx,
                                &OptionalSize {
                                    height: None,
                                    width: None,
                                },
                                &style,
                                &available_size,
                            );
                            let _ = self
                                .resolve_background_data_url(
                                    node_idx,
                                    format,
                                    data,
                                    &container_size,
                                    mode,
                                )
                                .inspect_err(|err| {
                                    eprintln!(
                                        "An error occured while resolving background data url: {}",
                                        err
                                    )
                                });
                        }

                        children.sort_by(|a, b| {
                            let a_z = self.layout_table.get(a).unwrap().z_index;
                            let b_z = self.layout_table.get(b).unwrap().z_index;
                            a_z.cmp(&b_z)
                        });

                        Some(self.register_layout_box(
                            LayoutBox {
                                rect: Rect {
                                    x: cursor.x,
                                    y: cursor.y,
                                    width,
                                    height,
                                    background: style_bg,
                                    border,
                                },
                                kind: LayoutKind::Element,
                                children,
                                node_idx,
                                allow_overflow,
                                content_height,
                                z_index,
                            },
                            save_as_final,
                        ))
                    } else {
                        None
                    }
                }
            }
        }
    }

    fn spawn_frame(&mut self, url: String, size: PhysicalSize<u32>) -> Result<FrameHandle> {
        let (tx, rx) = std::sync::mpsc::channel();
        let latest_bitmap = Arc::new(Mutex::new(vec![0; (size.width * size.height) as usize]));
        let bitmap_for_thread = Arc::clone(&latest_bitmap);
        let parent_proxy = self.event_loop_proxy.as_ref().unwrap().clone();
        tx.send(FrameCommand::Render).unwrap();
        let tx_proxy = RendererProxy::FrameLoop(tx);
        std::thread::spawn(move || {
            let mut browser = Browser::new(url.to_string(), false);

            let browser_result = browser.open();
            match browser_result {
                Ok(params) => {
                    let _ = browser
                        .set_up_without_event_loop(
                            params,
                            PhysicalSize::new(size.width, size.height),
                            tx_proxy,
                        )
                        .inspect_err(|err| eprintln!("Failed to start iframe renderer: {:?}", err));
                }
                Err(err) => {
                    eprintln!("Failed to boot iframe browser: {:?}", err);
                    return;
                }
            }

            let start = Instant::now();
            let js_result = browser.run_js();
            println!(
                "Finished running JS code in {}ms: {:?}",
                Instant::now().duration_since(start).as_millis(),
                js_result
            );

            loop {
                while let Ok(cmd) = rx.try_recv() {
                    match cmd {
                        FrameCommand::Render | FrameCommand::UserEvent(UserEvent::DomUpdated) => {
                            if browser
                                .renderer
                                .as_ref()
                                .is_some_and(|renderer| renderer.borrow().pending_dom_update)
                            {
                                browser.process_dom_update();
                            }

                            let mut pixels = vec![0; (size.width * size.height) as usize];
                            browser.renderer.as_ref().unwrap().borrow_mut().render_into(
                                &mut pixels,
                                size.width,
                                size.height,
                                true,
                            );

                            *bitmap_for_thread.lock().unwrap() = pixels;

                            let _ = parent_proxy.fire_user_event(UserEvent::FrameUpdated);
                        }
                        FrameCommand::UserEvent(UserEvent::ChildMessage(message)) => {
                            let _ = parent_proxy.fire_user_event(UserEvent::ChildMessage(message));
                        }
                        _ => {}
                    }
                }

                let _ = browser.pump_js_event_loop_once();
            }
        });
        Ok(FrameHandle {
            surface: latest_bitmap,
        })
    }

    fn resolve_background_data_url(
        &mut self,
        node_idx: usize,
        format: &String,
        data: &String,
        container_size: &ContainerSizes,
        mode: &LayoutMode,
    ) -> Result<()> {
        let style = self.node_styles.get(&node_idx).unwrap();
        match format.as_str() {
            "image/svg+xml" => {
                let mut svg_data = percent_encoding::percent_decode_str(data)
                    .decode_utf8()?
                    .to_string();
                self.inject_css_variables_into_str(&mut svg_data, &style.variables);
                let result = rasterize_svg(
                    &mut self.cached_rasterizations,
                    &svg_data,
                    Some(container_size.container_width),
                    Some(container_size.container_height),
                    container_size.container_width,
                    container_size.container_height,
                    &style,
                    mode,
                );
                match result {
                    Err(err) => {
                        println!("Failed to rasterize SVG data: {}", err);
                    }
                    Ok((pixmap, _, _, _)) => {
                        self.resolved_pixmaps.insert(node_idx.to_string(), pixmap);
                    }
                };
            }
            format => panic!("Unsupported background data format: {}", format),
        };
        Ok(())
    }

    fn get_margin_free_space_to_give(
        &self,
        free_space: u32,
        first_margin: &StyleSize,
        last_margin: &StyleSize,
    ) -> u32 {
        match (first_margin, last_margin) {
            (StyleSize::Auto, StyleSize::Auto) => free_space / 2,
            (StyleSize::Auto, _) => free_space,
            (_, StyleSize::Auto) => 0,
            _ => 0,
        }
    }

    fn layout_to_node_idx(&self, layout_box_idx: &usize) -> usize {
        self.layout_table.get(layout_box_idx).unwrap().node_idx
    }

    fn divide_free_space_for_margin(
        &mut self,
        children_rows: &MarginRows,
        container_width: i32,
        free_space_y: u32,
    ) {
        let mut free_space_to_give_y = 0;
        // TODO: I don't think this is 100% accurate
        if let (Some(first_child), Some(last_child)) = (
            children_rows.rows.first().and_then(|v| v.first()),
            children_rows.rows.last().and_then(|v| v.last()),
        ) {
            let first_child_style = &self
                .node_styles
                .get(&self.layout_to_node_idx(first_child))
                .unwrap();
            let last_child_style = &self
                .node_styles
                .get(&self.layout_to_node_idx(last_child))
                .unwrap();
            free_space_to_give_y = self.get_margin_free_space_to_give(
                free_space_y,
                &first_child_style.margin_top,
                &last_child_style.margin_bottom,
            );
        }
        for row in children_rows.rows.iter() {
            let first_child = row.first().unwrap();
            let last_child = row.last().unwrap();

            let first_child_style = &self
                .node_styles
                .get(&self.layout_to_node_idx(first_child))
                .unwrap();
            let last_child_style = &self
                .node_styles
                .get(&self.layout_to_node_idx(last_child))
                .unwrap();

            let mut used_space = 0i32;
            for child in row.iter() {
                let child_box = &self.layout_table.get(child).unwrap();
                used_space += child_box.rect.width as i32;
            }
            let free_space_x = (container_width - used_space).max(0) as u32;

            let mut first_margin = first_child_style.margin_left.clone();
            let mut last_margin = last_child_style.margin_right.clone();
            // If the text-align isn't left, and all children in this row are the same, use that instead of the margin
            if first_child_style.text_align != StyleAlign::Left
                && row.iter().all(|c| {
                    self.node_styles
                        .get(&self.layout_to_node_idx(c))
                        .unwrap()
                        .text_align
                        == first_child_style.text_align
                })
            {
                (first_margin, last_margin) = match first_child_style.text_align {
                    StyleAlign::Left => panic!(),
                    StyleAlign::Center => (StyleSize::Auto, StyleSize::Auto),
                    StyleAlign::Right => (StyleSize::Auto, StyleSize::Px(0.)),
                };
            }

            let free_space_to_give_x =
                self.get_margin_free_space_to_give(free_space_x, &first_margin, &last_margin);
            for child in row {
                let already_moved_x = children_rows.alignment_movements.get(child).unwrap();
                // TODO: Maybe do this for Y too
                self.move_entire_box(
                    *child,
                    free_space_to_give_x as i32 - already_moved_x,
                    free_space_to_give_y as i32,
                );
            }
        }
    }

    fn get_container_sizes(
        &self,
        node_idx: usize,
        forced_size: &OptionalSize,
        style: &Style,
        available_size: &Size,
    ) -> ContainerSizes {
        let (padding_left_size, padding_right_size, padding_top_size, padding_bottom_size) =
            self.get_paddings(node_idx, style, *available_size);
        let (border_left_size, border_right_size, border_top_size, border_bottom_size) =
            self.get_border_sizes(node_idx, style, *available_size);

        let resolved_font_size = self.resolved_font_sizes.get(&node_idx).unwrap();

        let min_height = get_specified_size(
            *resolved_font_size,
            &style.min_height,
            Some(available_size.height),
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32));
        let max_height = get_specified_size(
            *resolved_font_size,
            &style.max_height,
            Some(available_size.height),
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32));
        let min_width = get_specified_size(
            *resolved_font_size,
            &style.min_width,
            Some(available_size.width),
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32));
        let max_width = get_specified_size(
            *resolved_font_size,
            &style.max_width,
            Some(available_size.width),
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32));

        let specified_width = forced_size.width.or(get_specified_size(
            *resolved_font_size,
            &style.width,
            Some(available_size.width),
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32)));
        let specified_height = forced_size.height.or(get_specified_size(
            *resolved_font_size,
            &style.height,
            Some(available_size.height),
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32)));
        let container_width_non_filling = specified_width.and_then(|v| {
            Some(
                v.min(max_width.unwrap_or(u32::MAX))
                    .max(min_width.unwrap_or(u32::MIN)),
            )
        });
        let container_width = specified_width
            .unwrap_or(available_size.width)
            .min(max_width.unwrap_or(u32::MAX))
            .max(min_width.unwrap_or(u32::MIN));
        let inner_width = container_width.saturating_sub(
            (padding_left_size + padding_right_size + border_left_size + border_right_size) as u32,
        );
        // TODO: Container heights should probably respect min and max height
        let container_height_non_filling = specified_height;
        let container_height = specified_height.unwrap_or(available_size.height);
        let inner_height = container_height.saturating_sub(
            (padding_top_size + padding_bottom_size + border_top_size + border_bottom_size) as u32,
        );

        ContainerSizes {
            inner_height,
            inner_width,
            container_width,
            container_width_non_filling,
            container_height,
            container_height_non_filling,
            min_height,
            max_height,
            min_width,
            max_width,
            padding_x: (padding_left_size + padding_right_size) as u32,
        }
    }

    fn create_input_text_box(
        &mut self,
        node_idx: usize,
        input_value: String,
        cursor: &mut Position,
        font_size: u32,
        save_as_final: bool,
    ) -> Result<usize> {
        let style = &self.node_styles.get(&node_idx).unwrap();
        let text = collapse_whitespace(&input_value).unwrap();
        let text_hex = match style.color {
            StyleBackground::Hex(code) => Some(code),
            _ => None,
        }
        .with_context(|| "No color was specified for text")?;
        let (buffer, width, height) =
            if let Some(cached) = self.cached_text_buffers.get(&(text.clone(), font_size)) {
                cached
            } else {
                let result = text_to_buffer(&self.font_handler, text_hex, &text, font_size, None)
                    .with_context(|| "Failed to build pixmap for input text")?;
                self.cached_text_buffers
                    .insert((text.clone(), font_size), result);
                self.cached_text_buffers
                    .get(&(text, font_size))
                    .with_context(|| "Failed to build pixmap for input text")?
            };

        let layout_box = self.register_layout_box(
            LayoutBox {
                rect: Rect {
                    x: cursor.x,
                    y: cursor.y,
                    width: *width,
                    height: *height,
                    background: StyleBackground::Transparent,
                    border: RectBorder::new_empty(),
                },
                // TODO: Could avoid a clone here
                kind: LayoutKind::Text(buffer.clone()),
                children: vec![],
                node_idx,
                allow_overflow: style.overflow_y.visible(),
                content_height: *height,
                z_index: 0,
            },
            save_as_final,
        );
        Ok(layout_box)
    }

    fn get_grid_column(
        &self,
        current_column: i32,
        template_columns: &Vec<GridTemplateColumnsValue>,
    ) -> bool {
        // Are we out of columns?
        current_column >= template_columns.len() as i32
    }

    fn layout_grid(
        &mut self,
        node_idx: usize,
        cursor: Position,
        available_size: Size,
        forced_size: OptionalSize,
        mut containing_node_idx: usize,
        allow_fill: bool,
        save_as_final: bool,
        mode: &LayoutMode,
    ) -> Option<(u32, u32, Vec<usize>, u32)> {
        let style = self.node_styles.get(&node_idx).unwrap();
        let container_sizes =
            self.get_container_sizes(node_idx, &forced_size, style, &available_size);
        if style.position == StylePosition::Relative || style.position == StylePosition::Sticky {
            self.containing_nodes.insert(
                node_idx,
                ContainingNode {
                    node_idx,
                    waiters: vec![],
                },
            );
            containing_node_idx = node_idx;
        }
        let mut children = vec![];
        let (padding_left_size, _, padding_top_size, _) =
            self.get_paddings(node_idx, style, available_size);
        let mut content_position = Position {
            x: cursor.x + padding_left_size as i32,
            y: cursor.y + padding_top_size as i32,
        };
        let original_content_position = content_position.clone();
        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();
        let (containing_block_height, containing_block_width) =
            self.get_containing_block_size(containing_node_idx, node_idx, style);
        let specified_height = forced_size.height.or(get_specified_size(
            font_size,
            &style.height,
            containing_block_height,
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32)));
        let specified_width = forced_size.width.or(get_specified_size(
            font_size,
            &style.width,
            containing_block_width,
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32)));
        self.resolved_specified_heights
            .insert(node_idx, specified_height);
        self.resolved_specified_widths
            .insert(node_idx, specified_width);
        let mut max_child_height = 0;
        let mut longest_row_width = 0;
        let width_to_distribute = container_sizes.inner_width;
        let children_idxs = self
            .dom_indexes
            .children_index
            .get(&node_idx)
            .cloned()
            .unwrap();
        let mut current_column = 0;
        let mut definitely_used_width = 0;
        let mut max_total_fractions = 0;
        if let GridTemplateColumns::Values(template_columns) = style.grid_template_columns.clone() {
            for value in template_columns.iter() {
                match value {
                    GridTemplateColumnsValue::Size(size) => {
                        definitely_used_width += match size {
                            GridColumnSize::Px(px) => *px,
                            GridColumnSize::Percent(percent) => {
                                (container_sizes.inner_width as f32 * (*percent / 100.)) as i32
                            }
                            GridColumnSize::Fraction(fraction) => {
                                max_total_fractions += fraction;
                                0
                            }
                        };
                    }
                    GridTemplateColumnsValue::MinMax((_, max)) => {
                        if let GridColumnSize::Fraction(fraction) = max {
                            max_total_fractions += fraction;
                        }
                    }
                };
            }
        }
        let dynamic_space_to_give = width_to_distribute - definitely_used_width as u32;
        let justify_items = style.justify_items;
        let align_items = style.align_items;
        // Inline-block doesn't fill the width, so instruct children to not do that either
        let child_allow_fill = match style.display {
            StyleDisplay::InlineBlock | StyleDisplay::Inline => false,
            StyleDisplay::Grid if justify_items != StyleJustifyContent::Stretch => false,
            _ => allow_fill,
        };
        let grid_template_columns = style.grid_template_columns.clone();
        for child_idx in children_idxs.iter() {
            let wrap =
                if let GridTemplateColumns::Values(ref template_columns) = grid_template_columns {
                    self.get_grid_column(current_column, &template_columns)
                } else {
                    false
                };
            if wrap {
                content_position.x = 0;
                content_position.y += max_child_height;
                max_child_height = 0;
                current_column = 0;
            }
            let specified_column_size =
                if let GridTemplateColumns::Values(ref template_columns) = grid_template_columns {
                    match &template_columns[current_column as usize] {
                        GridTemplateColumnsValue::Size(size) => match size {
                            GridColumnSize::Px(px) => *px,
                            GridColumnSize::Percent(percent) => {
                                (width_to_distribute as f32 * (*percent / 100.)) as i32
                            }
                            GridColumnSize::Fraction(fraction) => {
                                (dynamic_space_to_give as f32
                                    * (*fraction as f32 / max_total_fractions as f32))
                                    as i32
                            }
                        },
                        GridTemplateColumnsValue::MinMax((min, max)) => {
                            let min_parsed = match min {
                                GridColumnSize::Px(px) => *px,
                                GridColumnSize::Percent(percent) => {
                                    (width_to_distribute as f32 * (*percent / 100.)) as i32
                                }
                                GridColumnSize::Fraction(_) => panic!(),
                            };
                            let max_parsed = match max {
                                GridColumnSize::Px(px) => *px,
                                GridColumnSize::Percent(percent) => {
                                    (width_to_distribute as f32 * (*percent / 100.)) as i32
                                }
                                GridColumnSize::Fraction(fraction) => {
                                    (dynamic_space_to_give as f32
                                        * (*fraction as f32 / max_total_fractions as f32))
                                        as i32
                                }
                            };

                            max_parsed.max(min_parsed)
                        }
                    }
                } else {
                    container_sizes.inner_width as i32
                };
            if let Some(child) = self.layout_node(
                *child_idx,
                content_position,
                Size {
                    width: specified_column_size as u32,
                    height: container_sizes.inner_height,
                },
                OptionalSize {
                    height: None,
                    width: None,
                },
                containing_node_idx,
                child_allow_fill,
                save_as_final,
                mode,
            ) {
                let child_box = self.layout_table.get(&child).unwrap();
                let child_width = child_box.rect.width as i32;
                let child_height = child_box.rect.height as i32;
                let free_x = (specified_column_size - child_width).max(0);
                let free_y = (container_sizes.inner_height as i32 - child_height).max(0);
                let offset_x = match justify_items {
                    StyleJustifyContent::Center => free_x / 2,
                    StyleJustifyContent::FlexEnd => free_x,
                    _ => 0,
                };
                let offset_y = match align_items {
                    StyleJustifyContent::Center => free_y / 2,
                    StyleJustifyContent::FlexEnd => free_y,
                    _ => 0,
                };
                self.move_entire_box(child, offset_x, offset_y);
                content_position.x += specified_column_size;
                longest_row_width =
                    longest_row_width.max(content_position.x - original_content_position.x);
                current_column += 1;
                max_child_height = max_child_height.max(child_height);
                children.push(child);
            }
        }
        let content_height = (content_position.y + max_child_height) - original_content_position.y;
        let height = specified_height
            .unwrap_or(content_height as u32)
            .min(container_sizes.max_height.unwrap_or(u32::MAX))
            .max(container_sizes.min_height.unwrap_or(u32::MIN));
        let width = if allow_fill {
            container_sizes.container_width
        } else {
            container_sizes.compute_actual_container_width(longest_row_width as u32)
        };
        self.resolved_heights.insert(node_idx, height);
        self.resolved_widths.insert(node_idx, width);
        Some((width as u32, height as u32, children, content_height as u32))
    }

    fn get_containing_block_size(
        &self,
        containing_node_idx: usize,
        node_idx: usize,
        style: &Style,
    ) -> (Option<u32>, Option<u32>) {
        // This is the parent which this node uses for % sizing, and possibly more later on
        let containing_block = match style.position {
            StylePosition::Absolute | StylePosition::Fixed => Some(containing_node_idx),
            StylePosition::Relative | StylePosition::Static | StylePosition::Sticky => {
                self.nodes.get(&node_idx).unwrap().get_parent()
            }
        };
        let containing_block_height = containing_block
            .and_then(|idx| {
                self.resolved_heights
                    .get(&idx)
                    .or(self
                        .resolved_specified_heights
                        .get(&idx)
                        .and_then(|v| *v)
                        .as_ref())
                    .cloned()
            })
            .or((node_idx == self.dom_indexes.root_indice).then_some(self.window_size.height));
        let containing_block_width = containing_block
            .and_then(|idx| {
                self.resolved_widths
                    .get(&idx)
                    .or(self
                        .resolved_specified_widths
                        .get(&idx)
                        .and_then(|v| *v)
                        .as_ref())
                    .cloned()
            })
            .or((node_idx == self.dom_indexes.root_indice).then_some(self.window_size.width));

        (containing_block_height, containing_block_width)
    }

    fn layout_block(
        &mut self,
        node_idx: usize,
        cursor: Position,
        available_size: Size,
        forced_size: OptionalSize,
        mut containing_node_idx: usize,
        allow_fill: bool,
        save_as_final: bool,
        mode: &LayoutMode,
    ) -> Option<(u32, u32, Vec<usize>, u32)> {
        let style = self.node_styles.get(&node_idx).unwrap();
        let (padding_left_size, padding_right_size, padding_top_size, padding_bottom_size) =
            self.get_paddings(node_idx, style, available_size);

        let mut content_position = Position {
            x: cursor.x + padding_left_size as i32,
            y: cursor.y + padding_top_size as i32,
        };
        let original_cursor = content_position.clone();
        let mut children = Vec::new();

        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();

        let (containing_block_height, containing_block_width) =
            self.get_containing_block_size(containing_node_idx, node_idx, style);

        let specified_width = forced_size.width.or(get_specified_size(
            font_size,
            &style.width,
            containing_block_width,
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32)));
        let specified_height = forced_size.height.or(get_specified_size(
            font_size,
            &style.height,
            containing_block_height,
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32)));

        self.resolved_specified_heights
            .insert(node_idx, specified_height);
        self.resolved_specified_widths
            .insert(node_idx, specified_width);

        if *mode == LayoutMode::BaseCalculation {
            if let (Some(height), Some(width)) = (specified_height, specified_width) {
                return Some((width, height, vec![], height));
            }
        }

        let container_sizes =
            self.get_container_sizes(node_idx, &forced_size, style, &available_size);

        let children_idxs: Vec<usize> = self
            .dom_indexes
            .children_index
            .get(&node_idx)
            .unwrap()
            .clone();

        let immediate_children: Vec<&usize> = children_idxs
            .iter()
            .filter(|c| {
                let style = &self.node_styles.get(*c);
                style.is_some_and(|style| !style.position.is_free())
            })
            .collect();
        let free_children: Vec<&usize> = children_idxs
            .iter()
            .filter(|c| {
                let style = &self.node_styles.get(*c);
                style.is_some_and(|style| style.position.is_free())
            })
            .collect();

        if style.position == StylePosition::Relative || style.position == StylePosition::Sticky {
            self.containing_nodes.insert(
                node_idx,
                ContainingNode {
                    node_idx,
                    waiters: vec![],
                },
            );
            containing_node_idx = node_idx;
        }

        let mut max_child_width: u32 = 0;
        let mut max_child_height: u32 = 0;
        let mut child_width_buffer = 0;

        let mut children_rows = MarginRows::new();

        // By default block elements fill their available width, but if it's a child of a flex, it only uses what it needs
        let wants_to_fill =
            style.display != StyleDisplay::InlineBlock && style.display != StyleDisplay::Inline;

        // Inline-block doesn't fill the width, so instruct children to not do that either
        let child_allow_fill = match style.display {
            StyleDisplay::InlineBlock | StyleDisplay::Inline => false,
            _ => allow_fill,
        };

        for child_local_idx in 0..immediate_children.len() {
            let child_idx = immediate_children[child_local_idx];
            let prev_child_idx = if child_local_idx >= 1 {
                Some(immediate_children[child_local_idx - 1])
            } else {
                None
            };
            let next_child_idx = if child_local_idx + 1 < immediate_children.len() {
                Some(immediate_children[child_local_idx + 1])
            } else {
                None
            };
            let child_style = self.node_styles.get(child_idx).unwrap().clone();
            let (margin_left_size, margin_right_size, margin_top_size, margin_bottom_size) =
                self.get_margins(*child_idx, &child_style, available_size);
            content_position.x += margin_left_size as i32;
            content_position.y += margin_top_size as i32;
            if let Some(child) = self.layout_node(
                *child_idx,
                content_position,
                Size {
                    width: container_sizes.inner_width,
                    height: container_sizes.inner_height,
                },
                OptionalSize {
                    height: None,
                    width: None,
                },
                containing_node_idx,
                child_allow_fill,
                save_as_final,
                mode,
            ) {
                let child_box = self.layout_table.get(&child).unwrap();
                let prev_child_display: Option<StyleDisplay> =
                    prev_child_idx.and_then(|idx| Some(self.node_styles.get(idx).unwrap().display));
                let next_child_display: Option<StyleDisplay> =
                    next_child_idx.and_then(|idx| Some(self.node_styles.get(idx).unwrap().display));
                if child_style.display.is_inline()
                    && prev_child_display.is_none_or(|v| v.is_inline())
                    && next_child_display.is_none_or(|v| v.is_inline())
                {
                    // TODO: This will need to support overflows
                    content_position.x += child_box.rect.width as i32 + margin_right_size;
                    child_width_buffer += child_box.rect.width as i32 + margin_right_size;
                    children_rows.last_row(child, 0);

                    if !child_style.position.is_free() {
                        max_child_width = max_child_width.max(child_width_buffer as u32);
                        max_child_height = max_child_height.max(child_box.rect.height);
                    }
                } else {
                    // This is a wrap, so reset X
                    content_position.x = original_cursor.x;
                    content_position.y += child_box.rect.height as i32 + margin_bottom_size;
                    child_width_buffer = 0;
                    children_rows.new_row(child, 0);

                    if !child_style.position.is_free() {
                        max_child_width = max_child_width.max(child_box.rect.width);
                    }
                }
                children.push(child);
            }
        }

        let input_value = match &self.nodes.get(&node_idx).unwrap() {
            Node::Element(element) => element.attributes.get("value"),
            Node::Text(_) | Node::Comment(_) => None,
        };
        if immediate_children.len() == 0 && input_value.is_some_and(|v| v.len() > 0) {
            let layout_box = self
                .create_input_text_box(
                    node_idx,
                    input_value.unwrap().clone(),
                    &mut content_position,
                    font_size,
                    save_as_final,
                )
                .unwrap();
            max_child_width = self.layout_table.get(&layout_box).unwrap().rect.width;
            children.push(layout_box);
        }

        let content_height = (content_position.y - original_cursor.y)
            .max(max_child_height as i32)
            .max(0) as u32;
        let height = specified_height
            .unwrap_or_else(|| {
                if children.is_empty() {
                    (padding_top_size + padding_bottom_size) as u32
                } else {
                    content_height + (padding_top_size + padding_bottom_size) as u32
                }
            })
            .min(container_sizes.max_height.unwrap_or(u32::MAX))
            .max(container_sizes.min_height.unwrap_or(u32::MIN));

        let width = if allow_fill && wants_to_fill {
            container_sizes.container_width
        } else {
            container_sizes.compute_actual_container_width(max_child_width)
        };

        self.resolved_heights.insert(node_idx, height);
        self.resolved_widths.insert(node_idx, width);

        // Margin: auto
        let free_space_y =
            (container_sizes.inner_height as i32 - content_height as i32).max(0) as u32;
        self.divide_free_space_for_margin(
            &children_rows,
            width as i32 - padding_left_size - padding_right_size,
            free_space_y,
        );

        for child_idx in free_children {
            self.queue_free_child_for_layout(
                containing_node_idx,
                node_idx,
                *child_idx,
                Size { height, width },
                cursor.clone(),
            );
        }

        if containing_node_idx == node_idx {
            let mut containing_node = self
                .containing_nodes
                .get_mut(&containing_node_idx)
                .unwrap()
                .clone();
            containing_node
                .layout_waiters(self, height, width, &mut children, mode)
                .ok()?;
            self.containing_nodes
                .insert(containing_node_idx, containing_node);
        }

        Some((width, height, children, content_height))
    }

    fn calculate_cross_offset(
        &self,
        item: &FlexItem,
        parent_style: &Style,
        has_definite_height: bool,
        allow_fill: bool,
        container_sizes: &ContainerSizes,
    ) -> u32 {
        let Some(style) = self.node_styles.get(&item.node_idx) else {
            return 0;
        };
        let align = match self.node_styles.get(&item.node_idx).unwrap().align_self {
            StyleJustifyContent::Auto => parent_style.align_items,
            v => v,
        };
        let used_cross = item.cross_size.round() as u32;
        let cross_free_space = match parent_style.flex_direction {
            StyleFlexDirection::Column if allow_fill => {
                container_sizes.inner_width.saturating_sub(used_cross)
            }
            StyleFlexDirection::Column => 0,
            StyleFlexDirection::Row if has_definite_height => {
                container_sizes.inner_height.saturating_sub(used_cross)
            }
            StyleFlexDirection::Row => 0,
        };
        let cross_offset = match align {
            StyleJustifyContent::Auto | StyleJustifyContent::FlexStart => 0,
            StyleJustifyContent::FlexEnd => cross_free_space,
            StyleJustifyContent::Center => cross_free_space / 2,
            StyleJustifyContent::SpaceBetween => 0,
            StyleJustifyContent::SpaceAround => 0,
            StyleJustifyContent::Stretch => 0,
            StyleJustifyContent::SpaceEvenly => 0,
        };
        cross_offset
    }

    fn resolve_flex_basis(
        &self,
        item_style: &Style,
        font_size: u32,
        parent_style: &Style,
        container_sizes: &ContainerSizes,
        has_definite_height: bool,
    ) -> Option<u32> {
        if item_style.flex_basis == StyleSize::Auto {
            return None;
        }

        let available_size = match parent_style.flex_direction {
            StyleFlexDirection::Row => Some(container_sizes.inner_width),
            StyleFlexDirection::Column if has_definite_height => Some(container_sizes.inner_height),
            StyleFlexDirection::Column => None,
        };

        get_specified_size(
            font_size,
            &item_style.flex_basis,
            available_size,
            None,
            &self.window_size,
        )
        .and_then(|v| if v >= 0 { Some(v as u32) } else { None })
    }

    fn layout_flex(
        &mut self,
        node_idx: usize,
        cursor: Position,
        available_size: Size,
        forced_size: OptionalSize,
        mut containing_node_idx: usize,
        allow_fill: bool,
        save_as_final: bool,
        mode: &LayoutMode,
    ) -> Option<(u32, u32, Vec<usize>, u32)> {
        let style = self
            .node_styles
            .get(&node_idx)
            .unwrap()
            .clone_without_variables();
        let (padding_left_size, padding_right_size, padding_top_size, padding_bottom_size) =
            self.get_paddings(node_idx, &style, available_size);

        let mut content_position = Position {
            x: cursor.x + padding_left_size as i32,
            y: cursor.y + padding_top_size as i32,
        };
        let original_content_cursor = content_position.clone();
        let mut base_items = Vec::new();
        let mut children = Vec::new();

        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();

        let container_sizes =
            self.get_container_sizes(node_idx, &forced_size, &style, &available_size);
        let (containing_block_height, containing_block_width) =
            self.get_containing_block_size(containing_node_idx, node_idx, &style);

        let specified_height = forced_size.height.or(get_specified_size(
            font_size,
            &style.height,
            containing_block_height,
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32)));
        let specified_width = forced_size.width.or(get_specified_size(
            font_size,
            &style.width,
            containing_block_width,
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32)));
        let has_definite_height = forced_size.height.is_some() || specified_height.is_some();
        self.resolved_specified_heights
            .insert(node_idx, specified_height);
        self.resolved_specified_widths
            .insert(node_idx, specified_width);

        if style.position == StylePosition::Relative {
            self.containing_nodes.insert(
                node_idx,
                ContainingNode {
                    node_idx,
                    waiters: vec![],
                },
            );
            containing_node_idx = node_idx;
        }

        let children_idxs = self
            .dom_indexes
            .children_index
            .get(&node_idx)
            .unwrap()
            .clone();

        let immediate_children: Vec<&usize> = children_idxs
            .iter()
            .filter(|c| {
                let style = &self.node_styles.get(*c).unwrap();
                !style.position.is_free()
            })
            .collect();
        let free_children: Vec<&usize> = children_idxs
            .iter()
            .filter(|c| {
                let style = &self.node_styles.get(*c).unwrap();
                style.position.is_free()
            })
            .collect();

        let input_value = match &self.nodes.get(&node_idx).unwrap() {
            Node::Element(element) => element.attributes.get("value"),
            Node::Text(_) | Node::Comment(_) => None,
        };
        if immediate_children.len() == 0 && input_value.is_some_and(|v| v.len() > 0) {
            if let Ok(layout_box_idx) = self.create_input_text_box(
                node_idx,
                input_value.unwrap().clone(),
                &mut content_position,
                font_size,
                save_as_final,
            ) {
                children.push(layout_box_idx);
            }
        }

        for child_idx in immediate_children {
            let child_style = self.node_styles.get(child_idx).unwrap().clone();
            let child_font_size = self
                .resolved_font_sizes
                .get(child_idx)
                .cloned()
                .unwrap_or(font_size);
            let flex_basis = self.resolve_flex_basis(
                &child_style,
                child_font_size,
                &style,
                &container_sizes,
                has_definite_height,
            );
            let forced_size = match style.flex_direction {
                StyleFlexDirection::Row => OptionalSize {
                    width: flex_basis,
                    height: None,
                },
                StyleFlexDirection::Column => OptionalSize {
                    width: None,
                    height: flex_basis,
                },
            };
            if let Some(child) = self.layout_node(
                *child_idx,
                Position { x: 0, y: 0 },
                Size {
                    width: container_sizes.inner_width,
                    height: container_sizes.inner_height,
                },
                forced_size,
                containing_node_idx,
                false,
                false,
                &LayoutMode::BaseCalculation,
            ) {
                let child_box = self.layout_table.get(&child).unwrap();
                let size = match style.flex_direction {
                    StyleFlexDirection::Row => flex_basis.unwrap_or(child_box.rect.width),
                    StyleFlexDirection::Column => flex_basis.unwrap_or(child_box.rect.height),
                };
                let cross_size = match style.flex_direction {
                    StyleFlexDirection::Row => child_box.rect.height,
                    StyleFlexDirection::Column => child_box.rect.width,
                };
                base_items.push(FlexItem {
                    node_idx: *child_idx,
                    target_size: size as f32,
                    base_size: size as f32,
                    cross_size: cross_size as f32,
                    shrink: child_style.flex_shrink,
                    grow: child_style.flex_grow,
                });
            }
        }

        // Shrinking
        let total_base: f32 = base_items.iter().map(|i| i.base_size).sum();
        let flex_available_size = match style.flex_direction {
            StyleFlexDirection::Row => container_sizes.inner_width,
            StyleFlexDirection::Column if has_definite_height => container_sizes.inner_height,
            StyleFlexDirection::Column => total_base.max(0.).ceil() as u32,
        };
        let cross_available_size = match style.flex_direction {
            StyleFlexDirection::Column => container_sizes.inner_width,
            StyleFlexDirection::Row => container_sizes.inner_height,
        };
        let overflow = total_base - flex_available_size as f32;

        if overflow > 0. {
            let total_scaled: f32 = base_items
                .iter()
                .map(|i| i.base_size * i.shrink as f32)
                .sum();

            if total_scaled > 0. {
                for item in &mut base_items {
                    let scaled = item.base_size * item.shrink as f32;
                    let reduction = overflow * scaled / total_scaled;
                    item.target_size = (item.base_size - reduction).max(0.);
                }
            }
        } else if overflow < 0. && allow_fill {
            let left_to_grow: f32 = -overflow;
            let total_grow: u32 = base_items.iter().map(|i| i.grow).sum();
            if total_grow > 0 {
                for item in &mut base_items {
                    item.target_size =
                        item.base_size + left_to_grow * (item.grow as f32 / total_grow as f32);
                }
            }
        }

        // Stretch children on cross-axis if appropiate
        if style.align_items == StyleJustifyContent::Stretch && allow_fill {
            for item in &mut base_items {
                let child_style: &Style = &self.node_styles.get(&item.node_idx).unwrap();
                match style.flex_direction {
                    StyleFlexDirection::Column => {
                        if child_style.width == StyleSize::Auto {
                            item.cross_size = cross_available_size as f32;
                        }
                    }
                    StyleFlexDirection::Row => {
                        if child_style.height == StyleSize::Auto && has_definite_height {
                            item.cross_size = cross_available_size as f32;
                        }
                    }
                };
            }
        }

        // Justify-content
        let authored_gap = get_specified_size(
            font_size,
            &style.gap,
            Some(flex_available_size),
            None,
            &self.window_size,
        )
        .unwrap_or(0);
        let gap_total = authored_gap.saturating_mul(base_items.len().saturating_sub(1) as i32);

        let used_main: u32 = base_items
            .iter()
            .map(|i| i.target_size.round() as u32)
            .sum::<u32>()
            + gap_total as u32;
        let main_free_space = match style.flex_direction {
            StyleFlexDirection::Row if allow_fill => {
                container_sizes.inner_width.saturating_sub(used_main)
            }
            StyleFlexDirection::Row => 0,
            StyleFlexDirection::Column if has_definite_height => {
                container_sizes.inner_height.saturating_sub(used_main)
            }
            StyleFlexDirection::Column => 0,
        };

        let (main_start_offset, main_distributed_gap) = match style.justify_content {
            StyleJustifyContent::Auto
            | StyleJustifyContent::FlexStart
            | StyleJustifyContent::Stretch => (0, 0),
            StyleJustifyContent::FlexEnd => (main_free_space, 0),
            StyleJustifyContent::Center => (main_free_space / 2, 0),
            StyleJustifyContent::SpaceBetween if base_items.len() > 1 => {
                (0, main_free_space / (base_items.len() as u32 - 1))
            }
            StyleJustifyContent::SpaceBetween => (0, 0),
            StyleJustifyContent::SpaceAround if !base_items.is_empty() => {
                let slot = main_free_space / base_items.len() as u32;
                (slot / 2, slot)
            }
            StyleJustifyContent::SpaceAround => (0, 0),
            StyleJustifyContent::SpaceEvenly if !base_items.is_empty() => {
                let slot = main_free_space / (base_items.len() as u32 + 1);
                (slot, slot)
            }
            StyleJustifyContent::SpaceEvenly => (0, 0),
        };

        let main_gap = main_distributed_gap + authored_gap as u32;

        let (width, mut height, content_height) = match style.flex_direction {
            StyleFlexDirection::Row => {
                let mut max_child_height = 0u32;
                content_position.x = original_content_cursor.x + main_start_offset as i32;

                let mut children_rows = MarginRows::new();

                for (item_idx, item) in base_items.iter().enumerate() {
                    let cross_offset = self.calculate_cross_offset(
                        &item,
                        &style,
                        has_definite_height,
                        allow_fill,
                        &container_sizes,
                    );
                    let child_style = self.node_styles.get(&item.node_idx).unwrap().clone();
                    let (margin_left_size, margin_right_size, margin_top_size, _) =
                        self.get_margins(item.node_idx, &child_style, available_size);
                    // Re-compute cursor for each child so that align-self works
                    content_position.y =
                        original_content_cursor.y + cross_offset as i32 + margin_top_size;
                    content_position.x += margin_left_size;

                    let last = item_idx == base_items.len() - 1;
                    if let Some(child) = self.layout_node(
                        item.node_idx,
                        content_position,
                        Size {
                            width: item.target_size as u32,
                            height: container_sizes.inner_height,
                        },
                        OptionalSize {
                            height: Some(item.cross_size as u32),
                            width: Some(item.target_size as u32),
                        },
                        containing_node_idx,
                        allow_fill,
                        save_as_final,
                        mode,
                    ) {
                        let child_box = self.layout_table.get(&child).unwrap();
                        if !child_style.position.is_free() {
                            content_position.x += child_box.rect.width as i32 + margin_right_size;
                            children_rows.last_row(child, cross_offset as i32);
                            // Don't add gap for last item
                            if !last {
                                content_position.x += main_gap as i32;
                            }
                            max_child_height = max_child_height.max(child_box.rect.height);
                        }
                        children.push(child);
                    }
                }

                let height = specified_height.unwrap_or_else(|| {
                    if children.is_empty() {
                        (padding_top_size + padding_bottom_size) as u32
                    } else {
                        max_child_height + (padding_top_size + padding_bottom_size) as u32
                    }
                });

                // By default block elements fill their available width, but if it's a child of a flex, it only uses what it needs
                let wants_to_fill = style.display != StyleDisplay::InlineFlex;
                let width = if allow_fill && wants_to_fill {
                    container_sizes.container_width
                } else {
                    container_sizes.compute_actual_container_width(
                        (content_position.x - original_content_cursor.x).max(0) as u32,
                    )
                };

                // Margin: auto
                let free_space_y =
                    (container_sizes.inner_height as i32 - max_child_height as i32).max(0) as u32;
                self.divide_free_space_for_margin(
                    &children_rows,
                    width as i32 - padding_left_size - padding_right_size,
                    free_space_y,
                );

                (width, height, max_child_height)
            }
            StyleFlexDirection::Column => {
                content_position.y = original_content_cursor.y + main_start_offset as i32;

                let mut max_affecting_child_width = 0;
                let mut children_rows = MarginRows::new();

                for (item_idx, item) in base_items.iter().enumerate() {
                    let cross_offset = self.calculate_cross_offset(
                        &item,
                        &style,
                        has_definite_height,
                        allow_fill,
                        &container_sizes,
                    );
                    let child_style = self.node_styles.get(&item.node_idx).unwrap().clone();
                    let (margin_left_size, _, margin_top_size, margin_bottom_size) =
                        self.get_margins(item.node_idx, &child_style, available_size);
                    content_position.x =
                        original_content_cursor.x + cross_offset as i32 + margin_left_size;
                    // TODO: This should probably go into the flex calculation
                    content_position.y += margin_top_size;

                    let last = item_idx == base_items.len() - 1;
                    if let Some(child) = self.layout_node(
                        item.node_idx,
                        content_position,
                        Size {
                            width: container_sizes.inner_width,
                            height: item.target_size as u32,
                        },
                        OptionalSize {
                            height: Some(item.target_size as u32),
                            width: Some(item.cross_size as u32),
                        },
                        containing_node_idx,
                        allow_fill,
                        save_as_final,
                        mode,
                    ) {
                        let child_box = self.layout_table.get(&child).unwrap();
                        if !child_style.position.is_free() {
                            max_affecting_child_width =
                                max_affecting_child_width.max(child_box.rect.width);
                            content_position.y += child_box.rect.height as i32 + margin_bottom_size;
                            children_rows.new_row(child, cross_offset as i32);
                            // Don't add gap for last item
                            if !last {
                                content_position.y += main_gap as i32;
                            }
                        }
                        children.push(child);
                    }
                }

                let content_height = (content_position.y - original_content_cursor.y).max(0);
                let height = specified_height.unwrap_or_else(|| {
                    if children.is_empty() {
                        (padding_top_size + padding_bottom_size) as u32
                    } else {
                        (content_height + padding_top_size + padding_bottom_size) as u32
                    }
                });

                // By default block elements fill their available width, but if it's a child of a flex, it only uses what it needs
                let wants_to_fill = style.display != StyleDisplay::InlineFlex;
                let width = if allow_fill && wants_to_fill {
                    container_sizes.container_width
                } else {
                    container_sizes.compute_actual_container_width(max_affecting_child_width)
                };

                // Margin: auto
                let free_space_y =
                    (container_sizes.inner_height as i32 - content_height as i32).max(0) as u32;
                self.divide_free_space_for_margin(
                    &children_rows,
                    width as i32 - padding_left_size - padding_right_size,
                    free_space_y,
                );

                (width, height, content_height as u32)
            }
        };

        height = height
            .min(container_sizes.max_height.unwrap_or(u32::MAX))
            .max(container_sizes.min_height.unwrap_or(u32::MIN));

        self.resolved_heights.insert(node_idx, height);
        self.resolved_widths.insert(node_idx, width);

        for child_idx in free_children {
            self.queue_free_child_for_layout(
                containing_node_idx,
                node_idx,
                *child_idx,
                Size { height, width },
                cursor.clone(),
            );
        }

        if containing_node_idx == node_idx {
            let mut containing_node = self
                .containing_nodes
                .get_mut(&containing_node_idx)
                .unwrap()
                .clone();
            containing_node
                .layout_waiters(self, height, width, &mut children, mode)
                .ok()?;
            self.containing_nodes
                .insert(containing_node_idx, containing_node);
        }

        Some((width, height, children, content_height))
    }

    fn blend_premul_over_rgb(&self, dst: u32, src: tiny_skia::PremultipliedColorU8) -> u32 {
        blend_rgb_with_rgba(dst, (src.red(), src.green(), src.blue(), src.alpha()))
    }

    fn compute_hovering(&mut self, position: Position) {
        let hovering = self
            .rendered_nodes_ordered
            .iter()
            .rev()
            .find(|renderer_node| {
                let node_idx = self.layout_to_node_idx(&renderer_node.layout_box_idx);
                let Some(style) = self.node_styles.get(&node_idx) else {
                    return false;
                };
                if style.pointer_events == StylePointerEvents::None {
                    return false;
                }
                let layout_box = self
                    .layout_table
                    .get(&renderer_node.layout_box_idx)
                    .unwrap();
                let end_x = layout_box.rect.x + layout_box.rect.width as i32;
                let end_y = layout_box.rect.y + layout_box.rect.height as i32;
                let scroll_y = renderer_node.offset_y;

                position.x > layout_box.rect.x
                    && position.x < end_x
                    && position.y > layout_box.rect.y + scroll_y
                    && position.y < end_y + scroll_y
            });
        self.hovering = hovering.and_then(|v| Some(v.layout_box_idx));
    }

    fn paint_borders(
        &self,
        layout_box: &LayoutBox,
        buffer: &mut [u32],
        width: u32,
        height: u32,
        offset_y: i32,
    ) {
        if let Some(border) = &layout_box.rect.border.left {
            draw_rect_filled(
                buffer,
                false,
                width,
                height,
                layout_box.rect.x,
                layout_box.rect.y + offset_y,
                border.size,
                layout_box.rect.height,
                border.color,
            );
        }
        if let Some(border) = &layout_box.rect.border.top {
            draw_rect_filled(
                buffer,
                false,
                width,
                height,
                layout_box.rect.x,
                layout_box.rect.y + offset_y,
                layout_box.rect.width,
                border.size,
                border.color,
            );
        }
        if let Some(border) = &layout_box.rect.border.right {
            draw_rect_filled(
                buffer,
                false,
                width,
                height,
                layout_box.rect.x + layout_box.rect.width as i32 - border.size as i32,
                layout_box.rect.y + offset_y,
                border.size,
                layout_box.rect.height,
                border.color,
            );
        }
        if let Some(border) = &layout_box.rect.border.bottom {
            draw_rect_filled(
                buffer,
                false,
                width,
                height,
                layout_box.rect.x,
                layout_box.rect.y + offset_y + layout_box.rect.height as i32 - border.size as i32,
                layout_box.rect.width,
                border.size,
                border.color,
            );
        }
    }

    fn apply_pixmap_on_buffer(
        &self,
        layout_box: &LayoutBox,
        buffer: &mut [u32],
        width: u32,
        height: u32,
        container_start_y: i32,
        pixmap_buffer: &tiny_skia::Pixmap,
        opaque: bool,
    ) {
        let pixels = pixmap_buffer.pixels();
        let pixmap_width = layout_box.rect.width.min(pixmap_buffer.width());
        let pixmap_height = layout_box.rect.height.min(pixmap_buffer.height());
        let pixmap_stride = pixmap_buffer.width();
        let end_x = pixmap_width.min((width as i32 - layout_box.rect.x).max(0) as u32);
        let end_y = pixmap_height.min((height as i32 - container_start_y).max(0) as u32);
        let start_y = (-container_start_y).max(0) as u32;
        for pixel_y in start_y..end_y {
            let src_start = (pixel_y * pixmap_stride) as usize;
            let src_row = &pixels[src_start..src_start + pixmap_width as usize];
            let dst_start = (container_start_y * width as i32
                + layout_box.rect.x
                + pixel_y as i32 * width as i32) as usize;
            let dst_row = &mut buffer[dst_start..(dst_start + pixmap_width as usize)];
            for pixel_x in 0..end_x {
                let pixel = src_row[pixel_x as usize];
                if opaque {
                    dst_row[pixel_x as usize] = ((pixel.red() as u32) << 16)
                        | ((pixel.green() as u32) << 8)
                        | (pixel.blue() as u32);
                } else {
                    dst_row[pixel_x as usize] =
                        self.blend_premul_over_rgb(dst_row[pixel_x as usize], pixel);
                }
            }
        }
    }

    fn paint_layout_box(
        &mut self,
        layout_box_idx: usize,
        buffer: &mut [u32],
        width: u32,
        height: u32,
        parent_offset_y: i32,
        rendered_nodes_ordered: &mut Vec<RenderedNode>,
    ) {
        let offset_y = parent_offset_y
            + self
                .scroll_y
                .get(&self.layout_to_node_idx(&layout_box_idx))
                .cloned()
                .unwrap_or(0);
        rendered_nodes_ordered.push(RenderedNode {
            layout_box_idx,
            offset_y,
        });
        let layout_box = self.layout_table.get(&layout_box_idx).unwrap();
        if self
            .node_styles
            .get(&layout_box.node_idx)
            .is_some_and(|style| style.opacity == 0.0)
        {
            return;
        }
        let container_start_y = layout_box.rect.y + offset_y;
        let container_end_y = container_start_y + layout_box.content_height as i32;
        // If outside viewport, don't render
        // This is a bit naive but should be okay for now
        if container_start_y > height as i32 || container_end_y < 0 {
            return;
        }
        match &layout_box.kind {
            LayoutKind::Element => {
                let left_border_size = layout_box
                    .rect
                    .border
                    .left
                    .as_ref()
                    .and_then(|v| Some(v.size))
                    .unwrap_or(0) as i32;
                let top_border_size = layout_box
                    .rect
                    .border
                    .top
                    .as_ref()
                    .and_then(|v| Some(v.size))
                    .unwrap_or(0) as i32;
                let right_border_size = layout_box
                    .rect
                    .border
                    .right
                    .as_ref()
                    .and_then(|v| Some(v.size))
                    .unwrap_or(0) as i32;
                let bottom_border_size = layout_box
                    .rect
                    .border
                    .bottom
                    .as_ref()
                    .and_then(|v| Some(v.size))
                    .unwrap_or(0) as i32;
                match &layout_box.rect.background {
                    StyleBackground::Hex(code) => {
                        draw_rect_filled(
                            buffer,
                            false,
                            width,
                            height,
                            layout_box.rect.x + left_border_size,
                            container_start_y + top_border_size,
                            (layout_box.rect.width as i32 - left_border_size - right_border_size)
                                .max(0) as u32,
                            (layout_box.rect.height as i32 - top_border_size - bottom_border_size)
                                .max(0) as u32,
                            code.clone(),
                        );
                    }
                    StyleBackground::DataUrl(_) => {
                        if let Some(pixmap) =
                            self.resolved_pixmaps.get(&layout_box.node_idx.to_string())
                        {
                            self.apply_pixmap_on_buffer(
                                layout_box,
                                buffer,
                                width,
                                height,
                                container_start_y,
                                pixmap,
                                false,
                            );
                        }
                    }
                    _ => {}
                };
                self.paint_borders(&layout_box, buffer, width, height, offset_y);
            }
            LayoutKind::Text(text) => {
                let bg_hex: Option<u32> = match layout_box.rect.background {
                    StyleBackground::Hex(code) => Some(code),
                    _ => None,
                };
                if let Some(bg) = bg_hex {
                    draw_rect_filled(
                        buffer,
                        false,
                        width,
                        height,
                        layout_box.rect.x,
                        container_start_y,
                        layout_box.rect.width,
                        layout_box.rect.height,
                        bg,
                    );
                }
                self.apply_pixmap_on_buffer(
                    layout_box,
                    buffer,
                    width,
                    height,
                    container_start_y,
                    text,
                    false,
                );
            }
            LayoutKind::PixMap((pixmap_buffer, opaque)) => {
                self.apply_pixmap_on_buffer(
                    layout_box,
                    buffer,
                    width,
                    height,
                    container_start_y,
                    pixmap_buffer,
                    *opaque,
                );
            }
            LayoutKind::Iframe => {
                if let Some(handle) = self
                    .frames
                    .get_mut(&self.layout_to_node_idx(&layout_box_idx))
                {
                    blit_rgb_buffer(
                        buffer,
                        width,
                        height,
                        handle.surface.lock().unwrap().as_ref(),
                        layout_box.rect.width,
                        layout_box.rect.height,
                        layout_box.rect.x,
                        container_start_y,
                    );
                } else {
                    println!("Failed to find iframe frame");
                }
            }
        }

        for child in layout_box.children.clone() {
            self.paint_layout_box(
                child,
                buffer,
                width,
                height,
                offset_y,
                rendered_nodes_ordered,
            );
        }
    }

    fn walk_parent_tree(&self, buffer: &mut Vec<usize>, idx: usize) {
        buffer.push(idx);
        if let Some(node) = self.nodes.get(&idx) {
            if let Some(parent) = node.get_parent() {
                self.walk_parent_tree(buffer, parent);
            }
        }
    }

    pub fn get_parents(&self, idx: usize) -> Vec<usize> {
        let mut buffer = vec![];
        self.walk_parent_tree(&mut buffer, idx);
        buffer
    }

    pub fn reserve_node_idx(&mut self) {
        self.node_idx_cursor += 1;
        self.nodes_idxs.push(self.node_idx_cursor);
    }

    pub fn insert_node_at_idx(&mut self, idx: usize, node: Node) {
        self.nodes.insert(idx, node);
    }

    pub fn push_node(&mut self, node: Node) {
        self.reserve_node_idx();
        self.insert_node_at_idx(self.node_idx_cursor, node);
    }

    pub fn remove_node(&mut self, node_idx: usize, remove_from_parent: bool) {
        // Remove children
        for child in self
            .dom_indexes
            .children_index
            .get(&node_idx)
            .unwrap()
            .clone()
        {
            self.remove_node(child, false);
        }

        // Remove from parent
        if remove_from_parent {
            if let Some(parent) = self.nodes.get(&node_idx).unwrap().get_parent() {
                let children = self.dom_indexes.children_index.get(&parent).unwrap();
                let filtered: Vec<usize> = children
                    .into_iter()
                    .filter(|idx| **idx != node_idx)
                    .cloned()
                    .collect();
                self.dom_indexes.children_index.insert(parent, filtered);
            }
        }

        // Remove node itself
        self.nodes_idxs = self
            .nodes_idxs
            .iter()
            .filter(|idx| **idx != node_idx)
            .cloned()
            .collect();
        self.nodes.remove(&node_idx);
        self.node_layout_mapping.remove(&node_idx);
        self.dom_indexes.children_index.remove(&node_idx);
    }

    pub fn recompute_dom_indexes(&mut self) {
        self.dom_indexes = get_dom_indexes(&self.nodes, &self.nodes_idxs);
    }

    pub fn get_hover_chain(&self) -> Vec<usize> {
        if let Some(hovering_layout_idx) = self.hovering {
            self.get_parents(self.layout_to_node_idx(&hovering_layout_idx))
        } else {
            vec![]
        }
    }

    pub fn recompute_styles(&mut self) {
        let hover_chain = self.get_hover_chain();
        (
            self.node_styles,
            self.resolved_font_sizes,
            self.variable_definitions,
            self.hovering_impact,
        ) = compute_node_styles(
            &self.url,
            &self.tokio,
            &self.network_fetch,
            &self.nodes,
            self.dom_indexes.root_indice,
            &self.window_size,
            &self.dom_indexes,
            &mut self.css_parse_cache,
            &hover_chain,
        );
    }

    pub fn recompute_nodes(&mut self) {
        self.recompute_dom_indexes();
        self.recompute_styles();
    }

    fn queue_free_child_for_layout(
        &mut self,
        containing_node_idx: usize,
        parent_idx: usize,
        child_idx: usize,
        available_size: Size,
        cursor: Position,
    ) {
        let child_style = self.node_styles.get(&child_idx).unwrap();
        let (containing_node_idx, parent_idx, available_size, cursor) =
            if child_style.position == StylePosition::Fixed {
                (
                    self.dom_indexes.root_indice,
                    self.dom_indexes.root_indice,
                    Size {
                        height: self.window_size.height,
                        width: self.window_size.width,
                    },
                    Position { x: 0, y: 0 },
                )
            } else {
                (containing_node_idx, parent_idx, available_size, cursor)
            };

        let containing_node = self.containing_nodes.get_mut(&containing_node_idx).unwrap();

        containing_node
            .waiters
            // Note: We use the cursor here rather than content_position as free children are not affected by padding
            .push(ResumableNode {
                parent_idx,
                node_idx: child_idx,
                available_size,
                cursor,
            });
    }

    pub fn get_paddings(
        &self,
        node_idx: usize,
        style: &Style,
        available_size: Size,
    ) -> (i32, i32, i32, i32) {
        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();
        let padding_left_size = get_specified_size(
            font_size,
            &style.padding_left,
            Some(available_size.width),
            None,
            &self.window_size,
        )
        .unwrap_or(0);
        let padding_right_size = get_specified_size(
            font_size,
            &style.padding_right,
            Some(available_size.width),
            None,
            &self.window_size,
        )
        .unwrap_or(0);
        let padding_top_size = get_specified_size(
            font_size,
            &style.padding_top,
            Some(available_size.height),
            None,
            &self.window_size,
        )
        .unwrap_or(0);
        let padding_bottom_size = get_specified_size(
            font_size,
            &style.padding_bottom,
            Some(available_size.height),
            None,
            &self.window_size,
        )
        .unwrap_or(0);

        (
            padding_left_size,
            padding_right_size,
            padding_top_size,
            padding_bottom_size,
        )
    }

    pub fn get_border_sizes(
        &self,
        node_idx: usize,
        style: &Style,
        available_size: Size,
    ) -> (i32, i32, i32, i32) {
        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();
        let left_size = if style.border_left.style == StyleBorderStyle::Solid {
            get_specified_size(
                font_size,
                &style.border_left.size,
                Some(available_size.width),
                None,
                &self.window_size,
            )
            .unwrap_or(0)
        } else {
            0
        };
        let right_size = if style.border_right.style == StyleBorderStyle::Solid {
            get_specified_size(
                font_size,
                &style.border_right.size,
                Some(available_size.width),
                None,
                &self.window_size,
            )
            .unwrap_or(0)
        } else {
            0
        };
        let top_size = if style.border_top.style == StyleBorderStyle::Solid {
            get_specified_size(
                font_size,
                &style.border_top.size,
                Some(available_size.height),
                None,
                &self.window_size,
            )
            .unwrap_or(0)
        } else {
            0
        };
        let bottom_size = if style.border_bottom.style == StyleBorderStyle::Solid {
            get_specified_size(
                font_size,
                &style.border_bottom.size,
                Some(available_size.height),
                None,
                &self.window_size,
            )
            .unwrap_or(0)
        } else {
            0
        };

        (left_size, right_size, top_size, bottom_size)
    }

    pub fn get_margins(
        &self,
        node_idx: usize,
        style: &Style,
        available_size: Size,
    ) -> (i32, i32, i32, i32) {
        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();
        let margin_left_size = get_specified_size(
            font_size,
            &style.margin_left,
            Some(available_size.width),
            None,
            &self.window_size,
        )
        .unwrap_or(0);
        let margin_right_size = get_specified_size(
            font_size,
            &style.margin_right,
            Some(available_size.width),
            None,
            &self.window_size,
        )
        .unwrap_or(0);
        let margin_top_size = get_specified_size(
            font_size,
            &style.margin_top,
            Some(available_size.height),
            None,
            &self.window_size,
        )
        .unwrap_or(0);
        let margin_bottom_size = get_specified_size(
            font_size,
            &style.margin_bottom,
            Some(available_size.height),
            None,
            &self.window_size,
        )
        .unwrap_or(0);

        (
            margin_left_size,
            margin_right_size,
            margin_top_size,
            margin_bottom_size,
        )
    }

    pub fn create_children_from_html(&mut self, parent_idx: usize, html: String) {
        let mut parser = HtmlParser::new(html);
        parser.parse().expect("Failed to parse inner html");
        let mut idx_mapping = HashMap::new();
        for (node_internal_idx, _) in parser.nodes.iter().enumerate() {
            self.reserve_node_idx();
            idx_mapping.insert(node_internal_idx, self.node_idx_cursor);
        }
        for (node_internal_idx, node) in parser.nodes.iter_mut().enumerate() {
            // Set root elements parent to us
            if node.get_parent().is_none() {
                node.set_parent(Some(parent_idx));
            } else {
                let _ = node.set_parent(idx_mapping.get(&node.get_parent().unwrap()).copied());
            }
            self.insert_node_at_idx(*idx_mapping.get(&node_internal_idx).unwrap(), node.clone());
        }
    }

    pub fn schedule_dom_update(&mut self) {
        if !self.pending_dom_update
            && let Some(proxy) = &self.event_loop_proxy
        {
            proxy.fire_user_event(UserEvent::DomUpdated).unwrap();
            self.pending_dom_update = true;
        }
    }
}

#[derive(Debug)]
struct FontHandler {
    font: FontRef<'static>,
}

impl FontHandler {
    pub fn new() -> Result<Self> {
        let font = FontRef::try_from_slice(include_bytes!("./InterVariable.ttf"))?;
        Ok(Self { font })
    }

    pub fn outline_glyph_for(&self, char: char, scale: f32) -> Option<OutlinedGlyph> {
        self.font.outline_glyph(self.glyph_for(char, scale))
    }

    pub fn glyph_for(&self, char: char, scale: f32) -> Glyph {
        self.font.glyph_id(char).with_scale(scale)
    }
}

#[derive(Debug)]
struct NetworkFetch {
    request_cache: HashMap<ReqwestUrl, RequestCacheEntry>,
    client: reqwest::Client,
    cookie_jar: Arc<Jar>,
}

impl NetworkFetch {
    pub fn new() -> Self {
        let cookie_jar = Arc::new(Jar::default());
        Self {
            request_cache: HashMap::new(),
            client: reqwest::Client::builder()
                .cookie_provider(Arc::clone(&cookie_jar))
                .user_agent(USER_AGENT)
                .build()
                .unwrap(),
            cookie_jar,
        }
    }
}

#[derive(Debug)]
struct ExecutedScripts {
    links: Vec<String>,
    nodes: Vec<usize>,
}

impl ExecutedScripts {
    pub fn new() -> Self {
        Self {
            links: vec![],
            nodes: vec![],
        }
    }
}

struct Browser {
    url: String,
    renderer: Option<Rc<RefCell<Renderer>>>,
    window: Option<Arc<Window>>,
    js_runtime: Option<Rc<RefCell<JsRuntime>>>,
    tokio: Option<Rc<RefCell<tokio::runtime::Runtime>>>,
    html_parser: Option<HtmlParser>,
    font_handler: Rc<FontHandler>,
    layout_dirty: bool,
    layout_booted: bool,
    executed_scripts: ExecutedScripts,
    network_fetch: Rc<RefCell<NetworkFetch>>,
    document_id: u64,
    hover_debugging: bool,
}

struct BootParams {
    nodes_idxs: Vec<usize>,
    nodes: HashMap<usize, parser::Node>,
    dom_indexes: DomIndexes,
}

impl std::fmt::Debug for Browser {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Browser")
            .field("url", &self.url)
            .field("renderer", &self.renderer)
            .field("window", &self.window)
            .field("js_runtime", &self.js_runtime.is_some())
            .field("tokio", &self.tokio)
            .field("html_parser", &self.html_parser)
            .field("font_handler", &self.font_handler)
            .field("layout_dirty", &self.layout_dirty)
            .field("layout_booted", &self.layout_booted)
            .field("executed_scripts", &self.executed_scripts)
            .field("network_fetch", &self.network_fetch)
            .field("document_id", &self.document_id)
            .field("hover_debugging", &self.hover_debugging)
            .finish()
    }
}

impl Browser {
    fn new(url: String, hover_debugging: bool) -> Self {
        let font_handler = Rc::new(FontHandler::new().unwrap());

        Self {
            url,
            renderer: None,
            window: None,
            js_runtime: None,
            tokio: None,
            html_parser: None,
            font_handler,
            executed_scripts: ExecutedScripts::new(),
            layout_dirty: true,
            layout_booted: false,
            network_fetch: Rc::new(RefCell::new(NetworkFetch::new())),
            document_id: 0,
            hover_debugging,
        }
    }

    pub fn render_into(
        &mut self,
        buffer: &mut [u32],
        width: u32,
        height: u32,
        rebuild_layout: bool,
    ) {
        self.renderer.as_ref().unwrap().borrow_mut().render_into(
            buffer,
            width,
            height,
            rebuild_layout,
        );
    }

    async fn get_html(&self, url: String) -> Result<(String, String)> {
        if let Some(stripped) = url.strip_prefix("file://") {
            let contents = fs::read_to_string(stripped)?;
            Ok((contents, url))
        } else {
            let url = resolve_url(&url, None)?;
            println!("Fetching HTML for {:?}", url);
            let client = &self.network_fetch.borrow_mut().client;
            let resp = client.get(url).send().await?;
            let url = resp.url().to_string();
            let text = resp.text().await?;
            Ok((text, url))
        }
    }

    pub fn install_js_host(&mut self) {
        let blob_store = Arc::new(BlobStore::default());
        let broadcast_channel = InMemoryBroadcastChannel::default();
        self.js_runtime = Some(Rc::new(RefCell::new(deno_core::JsRuntime::new(
            deno_core::RuntimeOptions {
                module_loader: Some(Rc::new(HttpModuleLoader::new())),
                extensions: vec![
                    browser::init(),
                    deno_webidl::deno_webidl::init(),
                    deno_web::deno_web::init(blob_store, None, broadcast_channel),
                    deno_net::deno_net::init(None, None),
                    deno_fetch_without_telemetry(),
                    deno_node_crypto_shim::init(),
                    deno_crypto::deno_crypto::init(None),
                ],
                ..Default::default()
            },
        ))));
    }

    fn drain_microtasks(runtime: &mut JsRuntime) {
        deno_core::scope!(scope, runtime);
        scope.perform_microtask_checkpoint();
    }

    fn execute_host_script(
        &mut self,
        name: &'static str,
        code: String,
    ) -> Result<v8::Global<v8::Value>> {
        let tokio = self.tokio.as_ref().unwrap().clone();
        let tokio = tokio.borrow();
        let _guard = tokio.enter();

        let mut runtime = self.js_runtime.as_mut().unwrap().borrow_mut();
        let value = runtime.execute_script(name, code)?;
        Self::drain_microtasks(&mut runtime);
        Ok(value)
    }

    fn reset_js_document_state(&mut self) -> Result<()> {
        self.execute_host_script(
            "document navigation reset",
            "globalThis.__clear_all_timers?.(); globalThis.__EVENT_LISTENERS = {}; history.state = null;".to_string(),
        )?;
        Ok(())
    }

    fn pump_js_event_loop_once(&mut self) -> Result<bool> {
        let mut runtime = self.js_runtime.as_mut().unwrap().borrow_mut();

        // The current-thread Tokio runtime only drives network/timer IO while block_on is active,
        // so keep this as a short cooperative slice rather than a pure Winit waker.
        self.tokio
            .as_ref()
            .unwrap()
            .clone()
            .borrow_mut()
            .block_on(async {
                match tokio::time::timeout(
                    Duration::from_millis(10),
                    runtime.run_event_loop(Default::default()),
                )
                .await
                {
                    Ok(Ok(())) => Ok(false),
                    Ok(Err(err)) => Err(err.into()),
                    Err(_) => Ok(true),
                }
            })
    }

    async fn execute_js(&mut self, scripts: Vec<Script>) -> Result<()> {
        let document_id = self.document_id;
        let Some(mut runtime) = self.js_runtime.as_mut().and_then(|v| Some(v.borrow_mut())) else {
            return Ok(());
        };
        for (idx, js) in scripts.iter().enumerate() {
            if let ScriptContent::Link(link) = &js.content {
                if self.executed_scripts.links.contains(&link) {
                    println!("Script has already been ran, ignoring: {}", link);
                    continue;
                }

                self.executed_scripts.links.push(link.to_string());
            } else if let Some(node_idx) = js.node_idx {
                if self.executed_scripts.nodes.contains(&node_idx) {
                    println!("Script has already been ran, ignoring: {}", node_idx);
                    continue;
                }

                self.executed_scripts.nodes.push(node_idx);
            }

            match &js.content {
                ScriptContent::Code(code) => {
                    let code_context: String = code.chars().take(40).collect();
                    runtime.execute_script(
                        format!("injected code {} ({})", idx, code_context),
                        code.clone(),
                    )?;
                    Self::drain_microtasks(&mut runtime);
                }
                ScriptContent::Link(link) => {
                    let base = ReqwestUrl::parse(&self.url)?;
                    let url = resolve_url(&link, Some(&base))?;
                    match js.script_type {
                        ScriptType::Classic => {
                            let code = self
                                .network_fetch
                                .borrow_mut()
                                .client
                                .get(url.clone())
                                .send()
                                .await?
                                .text()
                                .await?;
                            let result = runtime.execute_script(url.to_string(), code);
                            match result {
                                Ok(_) => Self::drain_microtasks(&mut runtime),
                                Err(err) => eprintln!(
                                    "Failed to execute JS at {} with error: {:?}",
                                    link, err
                                ),
                            };
                        }
                        ScriptType::Module => {
                            let module_id = if document_id == 0 {
                                runtime.load_side_es_module(&url).await?
                            } else {
                                let code = self
                                    .network_fetch
                                    .borrow_mut()
                                    .client
                                    .get(url.clone())
                                    .send()
                                    .await?
                                    .text()
                                    .await?;
                                let mut module_url = url.clone();
                                module_url
                                    .query_pairs_mut()
                                    .append_pair("__browser_document", &document_id.to_string());
                                runtime
                                    .load_side_es_module_from_code(&module_url, code)
                                    .await?
                            };
                            let result = runtime.mod_evaluate(module_id);
                            let _ = runtime
                                .with_event_loop_promise(result, Default::default())
                                .await
                                .inspect_err(|err| {
                                    eprintln!(
                                        "Failed to execute JS at {} with error: {:?}",
                                        url, err
                                    )
                                });
                        }
                    }
                }
            };

            // Run onload handlers
            if let Some(node_idx) = js.node_idx {
                let code = format!("runEventListeners(`${{{}}}:load`)", node_idx);
                runtime.execute_script("script onload", code.clone())?;
                Self::drain_microtasks(&mut runtime);
            }
        }

        Ok(())
    }

    pub fn run_js(&mut self) -> Result<()> {
        let scripts = self.renderer.as_ref().unwrap().borrow_mut().get_scripts();

        println!("Running {} JS scripts", scripts.len());

        self.tokio
            .as_ref()
            .unwrap()
            .clone()
            .borrow_mut()
            .block_on(self.execute_js(scripts))?;

        Ok(())
    }

    fn detect_html_redirect_walk_inner(&mut self, node_idx: usize) -> Option<Result<()>> {
        let nodes = &self.html_parser.as_ref().unwrap().nodes;
        let node = &nodes[node_idx];

        let Node::Element(element) = node else {
            return None;
        };
        if element.tag == "meta"
            && element
                .attributes
                .get("http-equiv")
                .is_some_and(|v| v.to_lowercase() == "refresh")
        {
            let Some(content) = element.attributes.get("content") else {
                return None;
            };
            let Some((delay, instructions)) = content.split_once(";") else {
                return None;
            };
            let Some(url) = instructions.strip_prefix("url=") else {
                return None;
            };
            let Ok(delay) = delay.parse::<f64>() else {
                return None;
            };
            // Who cares about the delay
            // TODO: Care about the delay
            let Ok(current_url) = url::Url::parse(&self.url) else {
                return None;
            };
            let Ok(resolved_url) = current_url.join(&url) else {
                return None;
            };
            println!("Detected HTML redirect to {}", resolved_url);
            return Some(self.navigate(resolved_url.to_string()));
        }
        None
    }

    fn detect_html_redirect_walk(
        &mut self,
        node_idx: usize,
        dom_indexes: &DomIndexes,
    ) -> Option<Result<()>> {
        let html_tag = match self
            .html_parser
            .as_ref()
            .unwrap()
            .nodes
            .get(node_idx)
            .unwrap()
        {
            Node::Element(element) => Some(element.tag.clone()),
            _ => None,
        };
        if let Some(result) = self.detect_html_redirect_walk_inner(node_idx) {
            return Some(result);
        } else if html_tag.is_none_or(|v| v != "noscript") {
            let children = dom_indexes.children_index.get(&node_idx).unwrap().clone();
            for child in children {
                if let Some(result) = self.detect_html_redirect_walk(child, dom_indexes) {
                    return Some(result);
                }
            }
        }
        None
    }

    fn detect_html_redirect(&mut self, dom_indexes: &DomIndexes) -> Option<Result<()>> {
        self.detect_html_redirect_walk(dom_indexes.root_indice, dom_indexes)
    }

    pub fn navigate(&mut self, href: String) -> Result<()> {
        let (input, final_url) = self
            .tokio
            .as_ref()
            .unwrap()
            .borrow_mut()
            .block_on(self.get_html(href))?;
        println!("Changing url to {}", final_url);
        self.url = final_url;

        self.html_parser = Some(HtmlParser::new(input));
        self.html_parser.as_mut().unwrap().parse().expect(&format!(
            "Failed to parse. Context: {}",
            self.html_parser.as_mut().unwrap().get_context()
        ));

        if let Some(renderer) = &self.renderer {
            let nodes_table = self
                .html_parser
                .as_mut()
                .unwrap()
                .nodes
                .clone()
                .into_iter()
                .enumerate()
                .collect();
            let nodes_idxs = sorted_node_idxs(&nodes_table);
            renderer
                .borrow_mut()
                .replace_document(self.url.clone(), nodes_table, nodes_idxs);
            self.document_id += 1;
            self.executed_scripts = ExecutedScripts::new();
            self.reset_js_document_state()?;
            self.setup_js_dom()?;
            let start = Instant::now();
            let js_result = self.run_js();
            println!(
                "Finished running JS code in {}ms: {:?}",
                Instant::now().duration_since(start).as_millis(),
                js_result
            );
        }
        if let Some(window) = self.window.as_mut() {
            self.layout_dirty = true;
            window.request_redraw();
        }
        Ok(())
    }

    pub fn register_tokio_runtime(&mut self) -> Result<()> {
        self.tokio = Some(Rc::new(RefCell::new(
            tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()?,
        )));
        Ok(())
    }

    pub fn set_up_without_event_loop(
        &mut self,
        params: BootParams,
        size: PhysicalSize<u32>,
        proxy: RendererProxy,
    ) -> Result<()> {
        self.refresh_renderer(params.nodes, params.dom_indexes, params.nodes_idxs, size);

        self.renderer
            .as_mut()
            .unwrap()
            .borrow_mut()
            .event_loop_proxy = Some(proxy.clone());

        if let Some(js_runtime) = self.js_runtime.as_mut().and_then(|v| Some(v.borrow_mut())) {
            js_runtime.op_state().borrow_mut().put(JsHostState {
                renderer: self.renderer.as_mut().cloned().unwrap(),
                proxy: proxy,
            });
        }
        self.setup_js_dom()?;

        Ok(())
    }

    pub fn open(&mut self) -> Result<BootParams> {
        self.register_tokio_runtime()?;
        self.navigate(self.url.clone())?;
        self.install_js_host();
        let nodes_table = self
            .html_parser
            .as_mut()
            .unwrap()
            .nodes
            .clone()
            .into_iter()
            .enumerate()
            .collect();
        let nodes_idxs = sorted_node_idxs(&nodes_table);
        let dom_indexes = get_dom_indexes(&nodes_table, &nodes_idxs);
        self.detect_html_redirect(&dom_indexes);
        Ok(BootParams {
            nodes: nodes_table,
            nodes_idxs,
            dom_indexes,
        })
    }

    fn on_click(&mut self) -> Result<()> {
        let hovering = self.renderer.as_ref().unwrap().borrow().hovering;
        if let Some(hovering) = hovering {
            // Run event listeners
            let hovering_node_idx = self
                .renderer
                .as_ref()
                .unwrap()
                .borrow()
                .layout_to_node_idx(&hovering);
            {
                let renderer = self.renderer.as_ref().unwrap().borrow();
                println!(
                    "Clicked on {} {:?}",
                    hovering_node_idx,
                    get_node_text_representation(
                        hovering_node_idx,
                        &renderer.nodes,
                        &renderer.node_layout_mapping,
                        &renderer.layout_table,
                        &renderer.node_styles
                    ),
                );
            }
            let parents = self
                .renderer
                .as_ref()
                .unwrap()
                .borrow()
                .get_parents(hovering_node_idx);
            let parents_strs: Vec<String> = parents.iter().map(|idx| idx.to_string()).collect();
            let code = format!(
                "__dispatchClickFromNodeIdx({}, [{}])",
                hovering_node_idx,
                parents_strs.join(", ")
            );

            let default_prevented = {
                let value = self.execute_host_script("click handler", code)?;
                let mut runtime = self.js_runtime.as_mut().unwrap().borrow_mut();

                deno_core::scope!(scope, &mut *runtime);
                let value = deno_core::v8::Local::new(scope, value);
                value.boolean_value(scope)
            };

            for p in parents.iter() {
                let implicit_events = self
                    .renderer
                    .as_ref()
                    .unwrap()
                    .borrow()
                    .get_implicit_click_events(*p);
                for (implicit, event) in implicit_events {
                    let Some(code) = (match event {
                        HtmlEvent::Change => Some(format!(
                            r#"
                                (() => {{
                                    const event = new Event("change")
                                    const idx = {}
                                    event.target = __elementFromNodeIdx(idx)
                                    event.target.__node_idx = idx
                                    runEventListeners(`${{idx}}:change`, event)
                                    return event.defaultPrevented
                                }})()
                            "#,
                            implicit.to_string()
                        )),
                        _ => None,
                    }) else {
                        continue;
                    };
                    self.execute_host_script("implicit event handler", code)?;
                    let mut runtime = self.js_runtime.as_mut().unwrap().borrow_mut();
                    let future = runtime.run_event_loop(Default::default());
                    self.tokio
                        .as_ref()
                        .unwrap()
                        .clone()
                        .borrow_mut()
                        .block_on(future)?;
                }
            }

            {
                let mut renderer = self.renderer.as_mut().unwrap().borrow_mut();
                let focusable = renderer.walk_node_upwards(hovering_node_idx, |node| {
                    let Node::Element(element) = node else {
                        return false;
                    };
                    FOCUSABLE_ELEMENTS.contains(&element.tag.as_str())
                        && element
                            .attributes
                            .get("type")
                            .is_none_or(|v| FOCUSABLE_INPUT_TYPES.contains(&v.as_str()))
                });
                renderer.focusable = focusable;
            }

            let submittable_input = self.renderer.as_ref().unwrap().borrow().walk_node_upwards(
                hovering_node_idx,
                |node| {
                    let Node::Element(element) = node else {
                        return false;
                    };
                    ["input", "button"].contains(&element.tag.as_str())
                        && element
                            .attributes
                            .get("type")
                            .is_some_and(|v| v == "submit")
                },
            );
            if let Some(submittable_input) = submittable_input {
                let form = self.renderer.as_ref().unwrap().borrow().walk_node_upwards(
                    submittable_input,
                    |node| {
                        let Node::Element(element) = node else {
                            return false;
                        };
                        element.tag == "form"
                    },
                );

                if let Some(form) = form {
                    let default_prevented = {
                        let value = self.execute_host_script(
                            "submit event handler",
                            format!(
                                r#"
                        (() => {{
                            const event = new Event("submit", {{
                                bubbles: false,
                            }})
                            __elementFromNodeIdx({}).dispatchEvent(event)
                            return event.defaultPrevented
                        }})()
                        "#,
                                form
                            ),
                        )?;
                        let mut runtime = self.js_runtime.as_mut().unwrap().borrow_mut();

                        deno_core::scope!(scope, &mut *runtime);
                        let value = deno_core::v8::Local::new(scope, value);
                        value.boolean_value(scope)
                    };
                    if !default_prevented {
                        self.renderer
                            .as_mut()
                            .unwrap()
                            .borrow_mut()
                            .submit_form(form, Some(submittable_input))?;
                    }
                }
            }

            let parent_link = self.renderer.as_ref().unwrap().borrow().walk_node_upwards(
                hovering_node_idx,
                |node| {
                    let Node::Element(element) = node else {
                        return false;
                    };
                    element.tag == "a"
                },
            );
            if let Some(parent) = parent_link {
                let parent_href = if let Some(Node::Element(element)) =
                    self.renderer.as_ref().unwrap().borrow().nodes.get(&parent)
                {
                    element.attributes.get("href").cloned()
                } else {
                    None
                };
                if let Some(href) = parent_href
                    && !default_prevented
                {
                    let current_url = url::Url::parse(&self.url)?;
                    let resolved_url = current_url.join(&href)?;
                    self.navigate(resolved_url.to_string()).unwrap();
                }
            }
        }

        Ok(())
    }

    fn setup_js_dom(&mut self) -> Result<()> {
        let code = ScriptContent::Code(
            format!(
                r#"
            document.documentElement = document.querySelector("html");
            document.body = document.querySelector("body");
            document.head = document.querySelector("head");
            document.activeElement = document.body;

            navigator.userAgent = "{}";

            window.__init_location("{}");
        "#,
                USER_AGENT, self.url
            )
            .to_string(),
        );
        self.tokio
            .as_ref()
            .unwrap()
            .clone()
            .borrow_mut()
            .block_on(self.execute_js(vec![Script {
                content: code,
                script_type: ScriptType::Classic,
                node_idx: None,
                defer: false,
                is_async: false,
            }]))?;
        Ok(())
    }

    fn refresh_renderer(
        &mut self,
        nodes_table: HashMap<usize, Node>,
        dom_indexes: DomIndexes,
        nodes_idxs: Vec<usize>,
        size: PhysicalSize<u32>,
    ) {
        self.renderer = Some(Rc::new(RefCell::new(Renderer::new(
            self.url.clone(),
            self.tokio.as_ref().unwrap().clone(),
            nodes_table,
            size,
            Rc::clone(&self.font_handler),
            Rc::clone(&self.network_fetch),
            dom_indexes,
            nodes_idxs,
        ))));
    }

    fn tick_animations(&mut self) -> bool {
        let mut renderer = self.renderer.as_mut().unwrap().borrow_mut();
        renderer.tick_animations()
    }

    fn render_loop(
        &mut self,
        surf: &mut Surface<DisplayHandle, WindowHandle>,
        size: &PhysicalSize<u32>,
        cursor: &Position,
    ) {
        let first_boot = self.render(surf, &size);
        if first_boot {
            let start = Instant::now();
            let js_result = self.run_js();
            println!(
                "Finished running JS code in {}ms: {:?}",
                Instant::now().duration_since(start).as_millis(),
                js_result
            );
        }

        // If there are animations, continue re-rendering until there aren't
        if self.tick_animations() {
            self.render_loop(surf, size, cursor);
        }
    }

    fn render(
        &mut self,
        surf: &mut Surface<DisplayHandle, WindowHandle>,
        size: &PhysicalSize<u32>,
    ) -> bool {
        let start = Instant::now();

        let width = NonZeroU32::new(size.width.max(1)).expect("Non-zero width");
        let height = NonZeroU32::new(size.height.max(1)).expect("Non-zero height");
        surf.resize(width, height).expect("Resize failed");

        let mut buffer = surf.buffer_mut().expect("Failed to get back buffer");
        self.renderer.as_mut().unwrap().borrow_mut().render_into(
            &mut buffer,
            size.width,
            size.height,
            self.layout_dirty,
        );
        self.layout_dirty = false;
        buffer.present().expect("Failed to present");

        println!(
            "Render took {} microseconds",
            Instant::now().duration_since(start).as_micros()
        );

        if !self.layout_booted {
            self.layout_booted = true;
            true
        } else {
            false
        }
    }

    fn process_dom_update(&mut self) {
        println!("DOM UPDATED");
        self.renderer
            .as_ref()
            .unwrap()
            .borrow_mut()
            .pending_dom_update = false;
        self.renderer
            .as_ref()
            .unwrap()
            .borrow_mut()
            .recompute_nodes();
        self.layout_dirty = true;
        let start = Instant::now();
        let js_result = self.run_js();
        println!(
            "Finished running JS code in {}ms: {:?}",
            Instant::now().duration_since(start).as_millis(),
            js_result
        );

        // If the JS caused another update, execute it immediately
        if self
            .renderer
            .as_ref()
            .unwrap()
            .borrow_mut()
            .pending_dom_update
        {
            self.process_dom_update();
        }
    }

    fn execute_dom_update(&mut self) {
        self.process_dom_update();
        if let Some(window) = self.window.as_ref() {
            window.request_redraw();
        }
    }

    fn apply_debug_hover(&mut self, hovering_layout_idx: usize) {
        let mut renderer = self.renderer.as_mut().unwrap().borrow_mut();
        let hovering_node_idx = renderer.layout_to_node_idx(&hovering_layout_idx);
        let style = renderer.node_styles.get_mut(&hovering_node_idx).unwrap();
        style.background = StyleBackground::Hex(0x32_a8_52_FF);
    }

    fn apply_hovering(&mut self, cursor: &Position) {
        let (should_re_render, hovering) = {
            let mut renderer = self.renderer.as_mut().unwrap().borrow_mut();
            let old_value = renderer.hovering.clone();
            renderer.compute_hovering(*cursor);
            let new_value = renderer.hovering;
            let one_has_hovering_impact = new_value.is_some_and(|idx| {
                renderer
                    .hovering_impact
                    .contains(&renderer.layout_to_node_idx(&idx))
            }) || old_value.is_some_and(|idx| {
                renderer
                    .hovering_impact
                    .contains(&renderer.layout_to_node_idx(&idx))
            });
            (new_value != old_value && one_has_hovering_impact, new_value)
        };
        if should_re_render || self.hover_debugging {
            self.layout_dirty = true;
            self.renderer
                .as_mut()
                .unwrap()
                .borrow_mut()
                .recompute_nodes();
            if let Some(hovering) = hovering
                && self.hover_debugging
            {
                self.apply_debug_hover(hovering);
            }
            self.window.as_mut().unwrap().request_redraw();
        }
    }

    pub fn pump_with_limit(&mut self, latest_end: Instant) -> Result<()> {
        match self.pump_js_event_loop_once() {
            Ok(js_pending) => {
                let dom_pending = self.renderer.as_ref().unwrap().borrow().pending_dom_update;

                if dom_pending {
                    self.execute_dom_update();
                }

                if js_pending && Instant::now().le(&latest_end) {
                    self.pump_with_limit(latest_end)
                } else {
                    Ok(())
                }
            }
            Err(err) => Err(err),
        }
    }

    pub fn start_event_loop(&mut self, params: BootParams) -> Result<()> {
        let event_loop = EventLoopBuilder::with_user_event()
            .build()
            .expect("Failed to create event loop");
        let window = Arc::new(
            WindowBuilder::new()
                .with_title("XML demo")
                .with_inner_size(PhysicalSize::new(WINDOW_WIDTH, WINDOW_HEIGHT))
                .build(&event_loop)
                .expect("Failed to create window"),
        );
        self.window = Some(Arc::clone(&window));
        let mut size = window.inner_size();

        let ctx = SoftContext::new(window.display_handle().expect("Display handle"))
            .expect("Softbuffer context failed");
        let mut surf = Surface::new(&ctx, window.window_handle().expect("Window handle"))
            .expect("Softbuffer surface failed");

        self.refresh_renderer(
            params.nodes,
            params.dom_indexes,
            params.nodes_idxs,
            self.window.as_ref().unwrap().inner_size(),
        );

        self.renderer
            .as_mut()
            .unwrap()
            .borrow_mut()
            .event_loop_proxy = Some(RendererProxy::WindowLoop(event_loop.create_proxy()));

        self.js_runtime
            .as_mut()
            .unwrap()
            .borrow_mut()
            .op_state()
            .borrow_mut()
            .put(JsHostState {
                renderer: self.renderer.as_mut().cloned().unwrap(),
                proxy: RendererProxy::WindowLoop(event_loop.create_proxy()),
            });

        self.setup_js_dom()?;

        let mut cursor = Position { x: 0, y: 0 };

        event_loop
            .run(move |event, elwt| {
                let window = self.window.as_ref().unwrap();
                match event {
                    Event::UserEvent(UserEvent::FrameUpdated) => {
                        self.render_loop(&mut surf, &size, &cursor);
                    }
                    Event::UserEvent(UserEvent::DomUpdated) => self.execute_dom_update(),
                    Event::UserEvent(UserEvent::ChildMessage(message)) => {
                        let code = format!(
                            r#"
                        (() => {{
                            const event = new MessageEvent("{}")
                            runEventListeners('window:message', event)
                        }})()
                        "#,
                            message
                        );
                        self.execute_host_script("child message handler", code)
                            .unwrap();
                    }
                    Event::UserEvent(UserEvent::Navigate((href, reload))) => {
                        let resolved_url = match href {
                            UserNavigateUrl::Parsed(parsed) => parsed,
                            UserNavigateUrl::Raw(raw) => {
                                let current_url = url::Url::parse(&self.url).unwrap();
                                let resolved_url = current_url.join(&raw).unwrap();
                                resolved_url
                            }
                        };
                        if reload {
                            if let Err(err) = self.navigate(resolved_url.to_string()) {
                                eprintln!("Navigation failed: {err:?}");
                            }
                        } else {
                            self.url = resolved_url.to_string();
                            self.renderer.as_mut().unwrap().borrow_mut().url =
                                resolved_url.to_string();
                            self.setup_js_dom().unwrap();
                        }
                    }
                    Event::WindowEvent { event, .. } => match event {
                        WindowEvent::CloseRequested => elwt.exit(),
                        WindowEvent::Resized(new_size) => {
                            size = new_size;
                            self.layout_dirty = true;
                            window.request_redraw();
                        }
                        WindowEvent::ScaleFactorChanged { .. } => {
                            size = window.inner_size();
                        }
                        WindowEvent::RedrawRequested => {
                            self.render_loop(&mut surf, &size, &cursor);
                        }
                        WindowEvent::CursorMoved {
                            device_id: _,
                            position,
                        } => {
                            cursor = Position {
                                x: position.x as i32,
                                y: position.y as i32,
                            };
                            self.apply_hovering(&cursor);
                        }
                        WindowEvent::MouseInput {
                            device_id: _,
                            state,
                            button,
                        } => match (button, state) {
                            (MouseButton::Left, ElementState::Released) => self.on_click().unwrap(),
                            _ => {}
                        },
                        WindowEvent::MouseWheel {
                            device_id: _,
                            delta,
                            phase: _,
                        } => {
                            match delta {
                                MouseScrollDelta::LineDelta(_, y) => {
                                    self.scroll_y_by(y * 140.);
                                }
                                _ => {}
                            };
                        }
                        WindowEvent::KeyboardInput {
                            device_id: _,
                            event,
                            is_synthetic: _,
                        } => {
                            if event.state == ElementState::Released {
                                self.handle_keyup(event);
                            }
                        }
                        _ => {}
                    },
                    Event::AboutToWait => match self.pump_js_event_loop_once() {
                        Ok(js_pending) => {
                            let dom_pending =
                                self.renderer.as_ref().unwrap().borrow().pending_dom_update;

                            if dom_pending {
                                self.execute_dom_update();
                            }

                            if js_pending {
                                elwt.set_control_flow(ControlFlow::WaitUntil(
                                    Instant::now() + Duration::from_millis(16),
                                ));
                            } else {
                                elwt.set_control_flow(ControlFlow::Wait);
                            }
                        }
                        Err(err) => {
                            eprintln!("JS event loop error: {err:?}");
                            elwt.set_control_flow(ControlFlow::Wait);
                        }
                    },
                    _ => {}
                }
            })
            .context("Event loop failed")?;

        Ok(())
    }

    pub fn scroll_y_by(&mut self, y: f32) {
        let scrollable_idx = {
            let mut renderer = self.renderer.as_mut().unwrap().borrow_mut();
            let size = self.window.as_ref().unwrap().inner_size();
            let (scrollable_idx, scrollable_height) = renderer.get_scrollable_height();
            let max_scroll = (scrollable_height as f32 - size.height as f32).max(0.);
            let scroll_y = renderer.scroll_y.get(&scrollable_idx).cloned().unwrap_or(0);
            if let Some(Animation::ScrollAnimation(existing_animation)) = renderer
                .animations
                .iter_mut()
                .find(|a| matches!(a, Animation::ScrollAnimation(_)))
            {
                let target_scroll =
                    (existing_animation.end as f32 + y).min(0.).max(-max_scroll) as i32;
                if target_scroll == scroll_y {
                    return;
                }
                existing_animation.start_at = SystemTime::now();
                existing_animation.start = scroll_y;
                existing_animation.end = target_scroll;
            } else {
                let target_scroll = (scroll_y as f32 + y).min(0.).max(-max_scroll) as i32;
                if target_scroll == scroll_y {
                    return;
                }
                renderer
                    .animations
                    .push(Animation::ScrollAnimation(ScrollAnimation {
                        start: scroll_y,
                        end: target_scroll,
                        start_at: SystemTime::now(),
                        duration: Duration::from_millis(60),
                        node_idx: scrollable_idx,
                    }));
            }
            scrollable_idx
        };
        let code = format!(
            r#"
        (() => {{
            const event = new MouseEvent("scroll")
            event.target = __elementFromNodeIdx({})
            runEventListeners('window:scroll', event)
        }})()
        "#,
            scrollable_idx
        );
        self.execute_host_script("script onscroll", code).unwrap();
        if let Some(window) = self.window.as_mut() {
            window.request_redraw();
        }
    }

    fn handle_keyup(&mut self, event: KeyEvent) {
        let focusable = self.renderer.as_ref().unwrap().borrow().focusable;
        if let Some(focusable) = focusable
            && let Some(text) = event.text
        {
            let new_text = {
                let mut renderer = self.renderer.as_ref().unwrap().borrow_mut();
                if let Some(Node::Element(element)) = renderer.nodes.get_mut(&focusable) {
                    let entry = element.attributes.entry("value".to_string()).or_default();
                    *entry += text.as_str();
                    Some(entry.clone())
                } else {
                    None
                }
            };

            if let Some(text) = new_text {
                self.renderer
                    .as_ref()
                    .unwrap()
                    .borrow_mut()
                    .schedule_dom_update();

                self.execute_host_script(
                    "input event handler",
                    format!(
                        r#"
                (() => {{
                    const event = new InputEvent("{}")
                    __elementFromNodeIdx({}).dispatchEvent(event)
                    return event.defaultPrevented
                }})()
                "#,
                        text, focusable
                    ),
                )
                .unwrap();
            }
        }
    }
}

fn main() -> Result<()> {
    let _ = rustls::crypto::aws_lc_rs::default_provider().install_default();

    let hover_debugging = env::args().any(|arg| arg == "--hover-debugging");
    let mut browser = Browser::new("https://slack.com/".to_string(), hover_debugging);
    // let mut browser = Browser::new("http://localhost:5173".to_string());
    // let mut browser = Browser::new("file:///home/pontus/browser/pages/test.html".to_string(), hover_debugging);

    let params = browser.open()?;
    browser.start_event_loop(params)?;
    Ok(())
}

fn clear_buffer(buffer: &mut [u32], color: u32) {
    buffer.fill(color);
}

fn build_children_index(
    nodes: &HashMap<usize, Node>,
    node_idxs: &Vec<usize>,
) -> HashMap<usize, Vec<usize>> {
    let mut children_index = HashMap::new();

    for idx in node_idxs.iter() {
        if let Some(parent_idx) = nodes.get(idx).unwrap().get_parent() {
            let entry: &mut Vec<usize> = children_index.entry(parent_idx).or_default();
            entry.push(*idx);
        }
    }

    // Insert something for everyone
    for idx in node_idxs.iter() {
        if !children_index.contains_key(idx) {
            children_index.insert(*idx, vec![]);
        }
    }

    children_index
}

fn get_node_text_representation(
    node_idx: usize,
    nodes: &HashMap<usize, Node>,
    layout_node_mapping: &HashMap<usize, usize>,
    layout_table: &HashMap<usize, LayoutBox>,
    node_styles: &HashMap<usize, Style>,
) -> String {
    let mut label = match &nodes.get(&node_idx).unwrap() {
        Node::Element(element) => format_element_tree_label(element),
        Node::Text(text) => match collapse_whitespace(&text.text) {
            Some(text) => format!("Node::Text \"{text}\""),
            None => format!("Node::Text EMPTY"),
        },
        Node::Comment(element) => format!("Node::Comment \"{}\"", element.comment),
    };
    label.push_str(&format!(" [idx={}]", node_idx));
    match layout_node_mapping
        .get(&node_idx)
        .and_then(|idx| layout_table.get(idx).and_then(|layout| Some((idx, layout))))
    {
        Some((layout_idx, info)) => {
            label.push_str(&format!(
                " [layout_idx={} layout={:?} x={} y={} width={} height={}]",
                layout_idx, info.kind, info.rect.x, info.rect.y, info.rect.width, info.rect.height
            ));
        }
        None => label.push_str(" [layout=none]"),
    }
    label.push_str(&format!(
        " [style={:?}]",
        node_styles.get(&node_idx).unwrap()
    ));
    label
}

fn format_element_tree_label(element: &Element) -> String {
    let mut label = format!("Node::Element: {}", element.tag.clone());

    let mut attributes = element.attributes.iter().collect::<Vec<_>>();
    attributes.sort_by(|(left_key, _), (right_key, _)| left_key.cmp(right_key));

    for (key, value) in attributes {
        label.push(' ');
        label.push_str(key);
        label.push_str("=\"");
        label.push_str(value);
        label.push('"');
    }

    label
}

fn collapse_whitespace(text: &str) -> Option<String> {
    let normalized = text.split_whitespace().collect::<Vec<_>>().join(" ");
    if normalized.is_empty() {
        None
    } else {
        Some(normalized)
    }
}

struct GlyphPosition {
    x: f32,
    y: f32,
    glyph: OutlinedGlyph,
}

fn text_to_buffer(
    font_handler: &Rc<FontHandler>,
    color: u32,
    text: &String,
    font_px: u32,
    max_width: Option<u32>,
) -> Option<(Pixmap, u32, u32)> {
    let scaled_font = font_handler.font.as_scaled(font_px as f32);
    let mut width = 0f32;
    let x = 0;
    let y = 0;
    let mut pen_x: f32 = x as f32;
    let mut pen_y: f32 = y as f32;
    let mut previous = None;

    let mut glyph_positions = vec![];

    let line_height = scaled_font.height() + scaled_font.line_gap();
    for ch in text.chars() {
        let glyph_id = font_handler.font.glyph_id(ch);
        if let Some(previous_id) = previous {
            pen_x += scaled_font.kern(previous_id, glyph_id);
        }
        if let Some(glyph) = font_handler.outline_glyph_for(ch, font_px as f32) {
            glyph_positions.push(GlyphPosition {
                x: pen_x,
                y: pen_y,
                glyph,
            });
        }
        let advance = scaled_font.h_advance(glyph_id);
        // Line break
        if max_width.is_some_and(|max_width| pen_x + advance >= max_width as f32) && ch == ' ' {
            pen_x = x as f32;
            pen_y += line_height;
        } else {
            pen_x += advance;
            width = width.max(pen_x)
        }
        previous = Some(glyph_id);
    }
    let width = width as u32;
    let height = (pen_y + line_height) as u32;
    let mut buffer = vec![0x00_00_00_00; (width * height) as usize];
    for glyph_pos in glyph_positions {
        draw_glyph(
            &mut buffer,
            width,
            height,
            glyph_pos.x as i32,
            (glyph_pos.y + scaled_font.ascent() + glyph_pos.glyph.px_bounds().min.y) as i32,
            &glyph_pos.glyph,
            color,
        );
    }
    let pixmap = Pixmap::from_vec(
        rgba_buffer_to_premul_bytes(&buffer),
        IntSize::from_wh(width, height)?,
    )?;
    Some((pixmap, width, height))
}

fn with_coverage(color: u32, c: f32) -> u32 {
    let alpha = color & 0xFF;
    let covered_alpha = ((alpha as f32) * c.clamp(0.0, 1.0)).round() as u32;

    (color & 0xFFFF_FF00) | covered_alpha
}

fn draw_glyph(
    buffer: &mut [u32],
    width: u32,
    height: u32,
    x: i32,
    y: i32,
    glyph: &OutlinedGlyph,
    color: u32,
) {
    glyph.draw(|glyph_x, glyph_y, c| {
        draw_rect_filled(
            buffer,
            true,
            width,
            height,
            x + glyph_x as i32,
            y + glyph_y as i32,
            1,
            1,
            with_coverage(color, c),
        );
    });
}

fn rgba_to_premul_tuple(src: u32) -> (u8, u8, u8, u8) {
    let [r, g, b, a] = src.to_be_bytes();
    let r = (r as u32 * a as u32 / 255) as u8;
    let g = (g as u32 * a as u32 / 255) as u8;
    let b = (b as u32 * a as u32 / 255) as u8;
    (r, g, b, a)
}

fn rgba_buffer_to_premul_bytes(buffer: &[u32]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(buffer.len() * 4);

    for pixel in buffer {
        let (r, g, b, a) = rgba_to_premul_tuple(*pixel);

        bytes.extend_from_slice(&[r, g, b, a]);
    }

    bytes
}

fn rgb_to_premul_tuple(src: u32) -> (u8, u8, u8, u8) {
    let [_, r, g, b] = src.to_be_bytes();
    let a = 255;
    let r = (r as u32 * a as u32 / 255) as u8;
    let g = (g as u32 * a as u32 / 255) as u8;
    let b = (b as u32 * a as u32 / 255) as u8;
    (r, g, b, a)
}

#[allow(dead_code)]
fn rgb_buffer_to_premul_bytes(buffer: &[u32]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(buffer.len() * 4);

    for pixel in buffer {
        let (r, g, b, a) = rgb_to_premul_tuple(*pixel);

        bytes.extend_from_slice(&[r, g, b, a]);
    }

    bytes
}

#[allow(dead_code)]
fn pixmaps_are_equal(first: &Pixmap, second: &Pixmap) -> bool {
    if first.width() != second.width() {
        return false;
    }
    if first.height() != second.height() {
        return false;
    }
    for (px_one, px_two) in first.data().iter().zip(second.data()) {
        if px_one != px_two {
            return false;
        }
    }
    true
}

fn draw_rect_filled(
    buffer: &mut [u32],
    buffer_rgba: bool,
    width: u32,
    height: u32,
    x: i32,
    y: i32,
    w: u32,
    h: u32,
    color: u32,
) {
    let max_x = width as i32;
    let max_y = height as i32;
    let start_x = x.max(0);
    let start_y = y.max(0);
    let end_x = (x + w as i32).min(max_x);
    let end_y = (y + h as i32).min(max_y);
    let stride = width as usize;

    let color_tuple = rgba_to_premul_tuple(color);
    for py in start_y..end_y {
        let row = &mut buffer[py as usize * stride..(py as usize + 1) * stride];
        for px in start_x..end_x {
            if buffer_rgba {
                row[px as usize] = blend_rgba_with_rgba(row[px as usize], color_tuple);
            } else {
                row[px as usize] = blend_rgb_with_rgba(row[px as usize], color_tuple);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::{Context, Result, anyhow};
    use resvg::tiny_skia::{IntSize, Pixmap};
    use std::{
        ops::Add,
        path::Path,
        time::{Duration, Instant},
    };
    use winit::dpi::PhysicalSize;

    use crate::{
        Browser, RendererProxy, pixmaps_are_equal, rgb_buffer_to_premul_bytes,
        style::{
            CalcExpression, StyleCalcOperator, StyleSize, parse_calc, split_ignoring_parentheses,
        },
    };

    fn ensure_snapshot_matches(
        buffer: &[u32],
        name: &'static str,
        width: u32,
        height: u32,
    ) -> Result<()> {
        let snapshot_path = format!("snapshots/{}.png", name);
        let snapshot_path = Path::new(&snapshot_path);
        let pixmap = Pixmap::from_vec(
            rgb_buffer_to_premul_bytes(&buffer),
            IntSize::from_wh(width, height).with_context(|| "Failed to create IntSize")?,
        )
        .with_context(|| "Failed to create pixmap")?;
        match Path::exists(snapshot_path) {
            true => {
                let snapshot = Pixmap::load_png(snapshot_path)?;
                if pixmaps_are_equal(&pixmap, &snapshot) {
                    Ok(())
                } else {
                    let invalid_path = format!("snapshots/{}.invalid.png", name);
                    let invalid_path = Path::new(&invalid_path);
                    pixmap.save_png(invalid_path)?;
                    Err(anyhow!(
                        "Pixmap did not match saved snapshot. Saved invalid file in {:?}",
                        invalid_path
                    ))
                }
            }
            false => {
                pixmap.save_png(snapshot_path)?;
                Err(anyhow!("No snapshot existed. Created one now."))
            }
        }
    }

    #[test]
    fn renders_google() -> Result<()> {
        let (tx, _rx) = std::sync::mpsc::channel();
        let mut browser = Browser::new("https://www.google.com".to_string(), false);
        let params = browser.open()?;
        browser.set_up_without_event_loop(
            params,
            PhysicalSize::new(1920, 1080),
            RendererProxy::FrameLoop(tx),
        )?;
        browser.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        let mut buffer = vec![0; 1920 * 1080];
        browser.render_into(&mut buffer, 1920, 1080, true);
        ensure_snapshot_matches(&buffer, "googlecom", 1920, 1080)
    }

    #[test]
    fn render_vite_dev() -> Result<()> {
        let (tx, _rx) = std::sync::mpsc::channel();
        let mut browser = Browser::new("https://vite.dev".to_string(), false);
        let params = browser.open()?;
        browser.set_up_without_event_loop(
            params,
            PhysicalSize::new(1920, 4320),
            RendererProxy::FrameLoop(tx),
        )?;
        browser.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        let mut buffer = vec![0; 1920 * 4320];
        browser.render_into(&mut buffer, 1920, 4320, true);
        ensure_snapshot_matches(&buffer, "vitedev", 1920, 4320)
    }

    #[test]
    fn render_time_tracker() -> Result<()> {
        let (tx, _rx) = std::sync::mpsc::channel();
        let mut browser = Browser::new("https://pixel-time-tracker.pages.dev/".to_string(), false);
        let params = browser.open()?;
        browser.set_up_without_event_loop(
            params,
            PhysicalSize::new(1920, 1080),
            RendererProxy::FrameLoop(tx),
        )?;
        browser.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        let mut buffer = vec![0; 1920 * 1080];
        browser.render_into(&mut buffer, 1920, 1080, true);
        ensure_snapshot_matches(&buffer, "pixeltimetracker", 1920, 1080)
    }

    #[test]
    fn render_slack() -> Result<()> {
        let (tx, _rx) = std::sync::mpsc::channel();
        let mut browser = Browser::new("https://slack.com/".to_string(), false);
        let params = browser.open()?;
        browser.set_up_without_event_loop(
            params,
            PhysicalSize::new(1920, 1080),
            RendererProxy::FrameLoop(tx),
        )?;
        browser.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        let mut buffer = vec![0; 1920 * 1080];
        browser.render_into(&mut buffer, 1920, 1080, true);
        ensure_snapshot_matches(&buffer, "slackcom", 1920, 1080)
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

    #[test]
    fn test_parse_calc() -> Result<()> {
        assert_eq!(
            parse_calc("15px * 4rem + (4px + 2em)")?,
            StyleSize::Calc(vec![
                CalcExpression::Size(StyleSize::Px(15.)),
                CalcExpression::Operator(StyleCalcOperator::Multiply),
                CalcExpression::Size(StyleSize::Rem(4.)),
                CalcExpression::Operator(StyleCalcOperator::Plus),
                CalcExpression::Nesting(vec![
                    CalcExpression::Size(StyleSize::Px(4.)),
                    CalcExpression::Operator(StyleCalcOperator::Plus),
                    CalcExpression::Size(StyleSize::Em(2.)),
                ]),
            ])
        );
        Ok(())
    }
}
