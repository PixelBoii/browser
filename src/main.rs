mod css;
mod parser;
mod style;
mod loader;

use deno_web::{BlobStore, InMemoryBroadcastChannel};
use image::{DynamicImage, ImageReader};
use parser::{Element, HtmlParser, Node};
use reqwest::cookie::{CookieStore, Jar};
use resvg::tiny_skia::{IntSize, Pixmap};
use style::{
    Style, StyleBackground, StyleDisplay, StyleFlexDirection, StyleJustifyContent, StylePosition,
    StyleSize, get_base_style, parse_style,
};

use std::cell::{RefCell};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::future::poll_fn;
use std::io::Cursor;
use std::num::NonZeroU32;
use std::rc::Rc;
use std::sync::Arc;
use std::task::Poll;
use std::time::{Duration, Instant};
use std::{env, fs, u32};

use anyhow::{Context, Result, anyhow};
use bytes::{Bytes};
use deno_core::{JsRuntime, OpState, extension, op2, v8};
use deno_core::error::JsError;
use raw_window_handle::{DisplayHandle, HasDisplayHandle, HasWindowHandle, WindowHandle};
use reqwest::{Url as ReqwestUrl};
use resvg::{tiny_skia, usvg};
use softbuffer::{Context as SoftContext, Surface};
use winit::dpi::PhysicalSize;
use winit::event::{ElementState, Event, MouseButton, MouseScrollDelta, WindowEvent};
use winit::event_loop::{ControlFlow, EventLoopBuilder, EventLoopProxy};
use winit::window::{Window, WindowBuilder};
use ab_glyph::{Font, FontRef, Glyph, OutlinedGlyph, ScaleFont};

use crate::css::{ClassName, ClassNamePart, CssParser, MediaQuery, Node as CssNode, Overflow, PseudoClass, parse_media_query_parts, selector_to_parts};
use crate::loader::HttpModuleLoader;
use crate::parser::{CommentElement, TextElement};
use crate::style::{CalcExpression, GridColumnSize, GridTemplateColumns, GridTemplateColumnsValue, StyleAlign, StyleBorderStyle, StyleCalcOperator, StyleSizeAndColor, build_css_children_index, element_matched_attributes, get_chain_order, get_class_list, get_parent_chain, get_parent_layer, get_specificity_order, media_query_matches};

const WINDOW_WIDTH: u32 = 1920;
const WINDOW_HEIGHT: u32 = 1080;

// Many websites rely on the user-agent to be one of the major browsers, so we don't use our own for now
const USER_AGENT: &str =
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36";

#[derive(Debug, Clone)]
struct RectBorderSide {
    size: u32,
    color: u32,
}

impl RectBorderSide {
    pub fn parse_from_style(style: &StyleSizeAndColor, font_size: u32, available_size: &Size, window_size: &PhysicalSize<u32>) -> Option<RectBorderSide> {
        match style.style {
            StyleBorderStyle::Solid => Some(Self {
                size: get_specified_size(font_size, &style.size, Some(available_size.width), None, window_size)? as u32,
                color: match style.color {
                    StyleBackground::Hex(hex) => hex,
                    StyleBackground::Transparent => 0xFF_FF_FF_00,
                    StyleBackground::DataUrl(_) => {
                        return None;
                    },
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
    color: StyleBackground,
    font_size: Option<u32>,
    border: RectBorder,
}

#[derive(Debug, Clone)]
struct RenderableText {
    text: String,
    glyphs: Vec<Option<OutlinedGlyph>>,
    width: u32,
    height: u32,
    line_height: f32,
}

#[derive(Debug, Clone)]
enum LayoutKind {
    Element,
    PixMap(tiny_skia::Pixmap),
    Text(RenderableText),
}

#[derive(Debug, Clone)]
struct LayoutBox {
    rect: Rect,
    kind: LayoutKind,
    children: Vec<usize>,
    node_idx: usize,
    allow_overflow: bool,
}

#[derive(Debug, Clone)]
enum RequestCacheEntry {
    PngData(Bytes),
    SvgData(String),
    CssData(String),
    JpegData(Bytes),
    Unsupported,
}

#[derive(Debug)]
struct DomIndexes {
    class_elements: HashMap<String, HashSet<usize>>,
    tag_elements: HashMap<String, HashSet<usize>>,
    id_elements: HashMap<String, HashSet<usize>>,
    children_index: HashMap<usize, Vec<usize>>,
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
            buffer: vec![0xFF_FF_FF; width as usize * height as usize],
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
    rendered_nodes_ordered: Vec<usize>,
    pub hovering: Option<usize>,
    tokio: Rc<RefCell<tokio::runtime::Runtime>>,
    resolved_font_sizes: HashMap<usize, u32>,
    resolved_pixmaps: HashMap<String, tiny_skia::Pixmap>,
    window_size: PhysicalSize<u32>,
    font_handler: Rc<FontHandler>,
    pending_dom_update: bool,
    scroll_y: i32,
    layout_roots: Vec<usize>,
    resolved_specified_heights: HashMap<usize, Option<u32>>,
    resolved_specified_widths: HashMap<usize, Option<u32>>,
    dom_indexes: DomIndexes,
    canvas_buffers: HashMap<usize, CanvasBuffer>,
    network_fetch: Rc<RefCell<NetworkFetch>>,
    cached_rasterizations: CachedRasterizations,
}

#[derive(Debug, Clone)]
struct LayoutDumpInfo {
    kind: &'static str,
    rect: Rect,
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
        self.container_width_non_filling.unwrap_or(self.clamp_width(used_width) + self.padding_x)
    }
}

impl ContainingNode {
    pub fn layout_waiters(&mut self, renderer: &mut Renderer, height: u32, width: u32, children: &mut Vec<usize>) -> Result<()> {
        for waiter in &self.waiters {
            let style = renderer.node_styles.get(&waiter.node_idx).unwrap().clone();
            let mut forced_size = OptionalSize { height: None, width: None };
            let resolved_parent_font_size = renderer.get_parent_font_size(waiter.node_idx);
            let font_size = get_specified_size(resolved_parent_font_size, &style.font_size, Some(resolved_parent_font_size), None, &renderer.window_size).with_context(|| "Failed to get specific size")? as u32;
            renderer.resolved_font_sizes.insert(waiter.node_idx, font_size as u32);
            let top = get_specified_size(font_size, &style.top, Some(waiter.available_size.height), None, &renderer.window_size);
            let right = get_specified_size(font_size, &style.right, Some(waiter.available_size.width), None, &renderer.window_size);
            let bottom = get_specified_size(font_size, &style.bottom, Some(waiter.available_size.height), None, &renderer.window_size);
            let left = get_specified_size(font_size, &style.left, Some(waiter.available_size.width), None, &renderer.window_size);

            let margin_right = get_specified_size(font_size, &style.margin_right, Some(waiter.available_size.width), None, &renderer.window_size);
            let margin_left = get_specified_size(font_size, &style.margin_left, Some(waiter.available_size.width), None, &renderer.window_size);

            if style.position == StylePosition::Absolute && style.width == StyleSize::Auto && left.is_some() && right.is_some() {
                forced_size.width = Some((width as i32 - left.unwrap() - right.unwrap()) as u32);
            }
            if style.position == StylePosition::Absolute && style.height == StyleSize::Auto && top.is_some() && bottom.is_some() {
                forced_size.height = Some((height as i32 - top.unwrap() - bottom.unwrap()) as u32);
            }

            if let Some(layout_idx) = renderer.layout_node(
                waiter.node_idx,
                waiter.cursor,
                waiter.available_size,
                forced_size,
                self.node_idx,
                true,
                true,
            ) {
                let waiter_layout_box = renderer.layout_table.get(&layout_idx).unwrap().clone();

                if style.position == StylePosition::Absolute {
                    if style.width == StyleSize::Auto && left.is_some() && right.is_some() {
                        // Width is taken care of above, so just move by left
                        renderer.move_entire_box(layout_idx, left.unwrap(), 0);
                    } else if right.is_some() {
                        let move_by = width as i32 - waiter_layout_box.rect.width as i32 - right.unwrap() - margin_right.unwrap_or(0);
                        renderer.move_entire_box(layout_idx, move_by, 0);
                    } else if left.is_some() {
                        renderer.move_entire_box(layout_idx, left.unwrap() - margin_left.unwrap_or(0), 0);
                    } else if style.margin_left == StyleSize::Auto && style.margin_right == StyleSize::Auto {
                        let free_space = width.saturating_sub(waiter_layout_box.rect.width);
                        renderer.move_entire_box(layout_idx, (free_space / 2) as i32, 0);
                    }

                    if top.is_some() && bottom.is_some() {
                        // Height is taken care of above, so just move by top
                        renderer.move_entire_box(layout_idx, 0, top.unwrap());
                    } else if top.is_some() {
                        renderer.move_entire_box(layout_idx, 0, top.unwrap());
                    } else if bottom.is_some() {
                        let move_by = height as i32 - waiter_layout_box.rect.height as i32 - bottom.unwrap();
                        renderer.move_entire_box(layout_idx, 0, move_by);
                    }
                }

                // If the waiter's parent is us, we haven't been laid out yet, so just add to children vector
                if waiter.parent_idx == self.node_idx {
                    children.push(layout_idx);
                } else {
                    let parent_layout_idx = renderer.node_layout_mapping.get(&waiter.parent_idx).unwrap();
                    renderer.layout_table.get_mut(parent_layout_idx).unwrap().children.push(layout_idx);
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
    window_size: &PhysicalSize<u32>
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
        // TODO: Make this handle order of operations
        StyleSize::Calc(calc) => {
            let mut value = match &calc[0] {
                CalcExpression::Size(size) => get_specified_size(font_size, &size, available_size, auto_size, window_size)?,
                _ => panic!("Expected first calc expression to be value"),
            };
            let mut exp_idx = 1;
            while exp_idx < calc.len() {
                let loop_operator = match &calc[exp_idx] {
                    CalcExpression::Operator(operator) => operator,
                    _ => panic!("Expected calc expression to be operator"),
                };
                let loop_value = match &calc[exp_idx + 1] {
                    CalcExpression::Size(size) => get_specified_size(font_size, &size, available_size, auto_size, window_size)?,
                    _ => panic!("Expected calc expression to be size. Got: {:?} [{}]", calc, exp_idx + 1),
                };
                value = match loop_operator {
                    StyleCalcOperator::Plus => value + loop_value,
                    StyleCalcOperator::Minus => value - loop_value,
                    StyleCalcOperator::Divide => value / loop_value,
                    StyleCalcOperator::Multiply => value * loop_value,
                };
                exp_idx += 2;
            };
            Some(value)
        },
        StyleSize::Em(em) => {
            Some((*em * font_size as f32) as i32)
        },
        // TODO: This should actually be the font-size of the root element, so figure that out
        StyleSize::Rem(rem) => {
            Some((*rem * 16 as f32) as i32)
        },
    }
}

fn infer_image_size(base_size: Size, input_w: Option<u32>, input_h: Option<u32>) -> (u32, u32) {
    let (target_h, target_w) = match (input_h, input_w) {
        (None, None) => (base_size.height, base_size.width),
        (Some(height), None) => (height, (base_size.width as f32 * (height as f32 / base_size.height as f32)) as u32),
        (None, Some(width)) => ((base_size.height as f32 * (width as f32 / base_size.width as f32)) as u32, width),
        (Some(height), Some(width)) => (height, width),
    };

    (target_h, target_w)
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

fn rasterize_svg(svg_data: &[u8], input_w: Option<u32>, input_h: Option<u32>, max_w: u32, max_h: u32, style: &Style) -> Result<(tiny_skia::Pixmap, u32, u32)> {
    let mut opt = usvg::Options::default();
    let color_hex = match style.color {
        StyleBackground::Hex(hex) => hex,
        _ => 0x00_FF_FF_FF,
    };
    opt.style_sheet = Some(format!("svg {{ color: #{:08X}; fill: currentColor }}", color_hex).into());

    let tree = usvg::Tree::from_data(&svg_data, &opt)?;
    let svg_size = tree.size().to_int_size();

    let (mut target_h, mut target_w) = infer_image_size(Size { height: svg_size.height(), width: svg_size.width() }, input_w, input_h);
    (target_h, target_w) = clamp_with_ratio(target_h, max_h, target_w);
    (target_w, target_h) = clamp_with_ratio(target_w, max_w, target_h);

    let mut pixmap = tiny_skia::Pixmap::new(target_w.max(1), target_h.max(1))
        .context("failed to allocate svg pixmap")?;

    let scale = f32::min(
        target_w as f32 / svg_size.width() as f32,
        target_h as f32 / svg_size.height() as f32,
    );

    let tx = (target_w as f32 - svg_size.width() as f32 * scale) * 0.5;
    let ty = (target_h as f32 - svg_size.height() as f32 * scale) * 0.5;

    let transform = tiny_skia::Transform::from_row(scale, 0.0, 0.0, scale, tx, ty);
    resvg::render(&tree, transform, &mut pixmap.as_mut());

    Ok((pixmap, target_h, target_w))
}

fn rasterize_png(cached_rasterizations: &mut CachedRasterizations, src: &String, bytes: &[u8], input_w: Option<u32>, input_h: Option<u32>, max_w: u32, max_h: u32) -> Result<(tiny_skia::Pixmap, u32, u32)> {
    let pixmap = if let Some(cached) = cached_rasterizations.decoded_pngs.get(src) {
        cached
    } else {
        cached_rasterizations.decoded_pngs.insert(src.clone(), tiny_skia::Pixmap::decode_png(bytes)?);
        cached_rasterizations.decoded_pngs.get(src).unwrap()
    };
    if input_w.is_some_and(|v| v == pixmap.width()) && input_h.is_some_and(|v| v == pixmap.height()) {
        return Ok((pixmap.clone(), input_h.unwrap(), input_w.unwrap()));
    }

    let (mut target_h, mut target_w) = infer_image_size(Size { height: pixmap.height(), width: pixmap.width() }, input_w, input_h);
    (target_h, target_w) = clamp_with_ratio(target_h, max_h, target_w);
    (target_w, target_h) = clamp_with_ratio(target_w, max_w, target_h);

    let mut dst = tiny_skia::Pixmap::new(target_w.max(1), target_h.max(1))
        .context("failed to allocate png pixmap")?;

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

    Ok((dst, target_h, target_w))
}

fn rasterize_jpeg(cached_rasterizations: &mut CachedRasterizations, src: &String, bytes: &[u8], input_w: Option<u32>, input_h: Option<u32>, max_w: u32, max_h: u32) -> Result<(tiny_skia::Pixmap, u32, u32)> {
    let result = if let Some(cached) = cached_rasterizations.decoded_jpegs.get(src) {
        cached
    } else {
        let mut reader = ImageReader::new(Cursor::new(bytes));
        reader.set_format(image::ImageFormat::Jpeg);
        cached_rasterizations.decoded_jpegs.insert(src.clone(), reader.decode()?);
        cached_rasterizations.decoded_jpegs.get(src).unwrap()
    };

    let (mut target_h, mut target_w) = infer_image_size(Size { height: result.height(), width: result.width() }, input_w, input_h);
    (target_h, target_w) = clamp_with_ratio(target_h, max_h, target_w);
    (target_w, target_h) = clamp_with_ratio(target_w, max_w, target_h);

    let key = (src.clone(), target_h, target_w);
    let pixmap = if let Some(cached) = cached_rasterizations.jpegs.get(&key) {
        cached
    } else {
        let result = result.resize(target_w, target_h, image::imageops::FilterType::Lanczos3);
        let rgba = result.to_rgba8();

        let width = rgba.width();
        let height = rgba.height();
        let value = Pixmap::from_vec(
            rgba.to_owned().into_raw(),
            IntSize::from_wh(width, height).with_context(|| "Failed to create IntSize")?
        ).with_context(|| "Failed to convert to pixmap")?;
        cached_rasterizations.jpegs.insert(key.clone(), value);
        cached_rasterizations.jpegs.get(&key).unwrap()
    };

    Ok((pixmap.clone(), target_h, target_w))
}

fn resolve_url(href: &str, base_url: Option<&ReqwestUrl>) -> Result<ReqwestUrl> {
    if let Ok(url) = ReqwestUrl::parse(href) {
        return Ok(url);
    }

    let base_url = base_url.context(format!("relative URL without base: {href}"))?;
    Ok(base_url.join(href)?)
}

async fn fetch_link_strings(base_url: &String, network_fetch: &Rc<RefCell<NetworkFetch>>, links: &Vec<&String>, map_fn: impl Fn(String) -> RequestCacheEntry) -> Result<Vec<String>> {
    let mut results = vec![];
    for link in links.iter() {
        // TODO: Don't hardcode this
        let base = ReqwestUrl::parse(base_url)?;
        let url = resolve_url(link, Some(&base))?;

        if let Some(cache) = network_fetch.borrow_mut().request_cache.get(&url) {
            results.push(cache.clone());
        } else {
            let resp = network_fetch.borrow_mut().client.get(url.clone()).send().await?.text().await?;
            let cache_entry = map_fn(resp);
            network_fetch.borrow_mut().request_cache.insert(url, cache_entry.clone());

            results.push(cache_entry);
        }
    }
    let strings = results.iter().map(|r| match r {
        RequestCacheEntry::CssData(data) => Some(data.clone()),
        _ => None,
    }).flatten().collect::<Vec<String>>();

    Ok(strings)
}

fn combine_css_nodes(base_url: &String, tokio: &Rc<RefCell<tokio::runtime::Runtime>>, network_fetch: &Rc<RefCell<NetworkFetch>>, nodes: &HashMap<usize, Node>, node_idxs: &Vec<usize>, children_index: &HashMap<usize, Vec<usize>>) -> Result<Vec<String>> {
    let mut css_nodes: Vec<String> = node_idxs
        .iter()
        .filter(|idx| match nodes.get(*idx).unwrap() {
            Node::Element(element) => element.tag == "style",
            _ => false,
        })
        .map(|idx| -> Option<String> {
            let children = &children_index.get(idx).unwrap();
            if children.len() != 1 {
                println!("Unexpected children count: {}", children.len());
                return None;
            }
            let child = children.first().unwrap();
            let child_node = &nodes.get(child).unwrap();

            let text = match child_node {
                Node::Element(element) => {
                    println!("Got element when expecting CSS text {:?}", element);
                    return None;
                }
                Node::Text(element) => Some(element.text.clone()),
                Node::Comment(_) => {
                    return None;
                },
            };

            text
        })
        .flatten()
        .collect();

    let stylesheet_links: Vec<&String> = node_idxs
        .iter()
        .filter(|idx| match nodes.get(*idx).unwrap() {
            Node::Element(element) => {
                element.tag == "link"
                    && element.attributes.contains_key("href")
                    && element
                        .attributes
                        .get("rel")
                        .is_some_and(|v| {
                            let rels: Vec<&str> = v.split(" ").collect();
                            rels.contains(&"stylesheet")
                        })
            }
            _ => false,
        })
        .map(|idx| match nodes.get(idx).unwrap() {
            Node::Element(element) => element.attributes.get("href"),
            _ => None,
        })
        .flatten()
        .collect();

    let mut fetched_nodes = if stylesheet_links.len() > 0 {
        tokio.borrow_mut().block_on(fetch_link_strings(base_url, &network_fetch, &stylesheet_links, |str| RequestCacheEntry::CssData(str)))?
    } else {
        vec![]
    };
    println!("Fetched {} CSS nodes", fetched_nodes.len());

    css_nodes.append(&mut fetched_nodes);

    Ok(css_nodes)
}

fn compute_node_style(
    node_styles: &mut HashMap<usize, Style>,
    resolved_font_sizes: &mut HashMap<usize, u32>,
    nodes: &HashMap<usize, Node>,
    node_idx: usize,
    children_index: &HashMap<usize, Vec<usize>>,
    css_nodes: &Vec<CssNode>,
    parent_style: Option<usize>,
    parent_variables: &HashMap<String, String>,
    parent_font_size: Option<u32>,
    collected_class_nodes: &HashMap<usize, Vec<usize>>,
    css_children_index: &HashMap<usize, Vec<usize>>,
    window_size: &PhysicalSize<u32>,
    css_node_ranking: &[usize],
) {
    let mut variables = parent_variables.clone();
    let parent_style = parent_style.and_then(|idx| Some(node_styles.get(&idx).unwrap()));
    let mut style = match &nodes.get(&node_idx).unwrap() {
        Node::Element(element) => parse_style(node_idx, element, css_nodes, parent_style, &mut variables, collected_class_nodes, css_children_index, css_node_ranking).unwrap(),
        node => get_base_style(node, parent_style),
    };

    let resolved_font_size = get_specified_size(parent_font_size.unwrap_or(16), &style.font_size, Some(parent_font_size.unwrap_or(16)), None, window_size).unwrap_or_else(|| {
        println!("Failed to get font size for node idx {}", node_idx);
        16
    });
    resolved_font_sizes.insert(node_idx, resolved_font_size as u32);

    // Set to resolved size in px so that ems dont stack on top of each other
    style.font_size = StyleSize::Px(resolved_font_size as f32);

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
            &variables,
            Some(resolved_font_size as u32),
            collected_class_nodes,
            css_children_index,
            window_size,
            css_node_ranking,
        );
    }
}

fn parse_css_nodes(css_nodes: &Vec<String>) -> Result<Vec<CssNode>> {
    let joined = css_nodes.join("\n");
    let mut parser = CssParser::new(&joined.as_str());
    parser.parse()?;

    Ok(parser.nodes)
}

fn move_up_ancestor_chain(
    element: usize,
    html_nodes: &HashMap<usize, &Node>,
    css_nodes: &Vec<(usize, &CssNode)>,
    class_elements: &HashMap<String, HashSet<usize>>, 
    css_node: &CssNode,
    window_size: &PhysicalSize<u32>,
    require_immediate_match: bool,
    walk_up_parent: bool,
    dom_indexes: &DomIndexes,
) -> bool {
    let parent = css_node.get_parent();
    if let Some(parent) = parent {
        let parent_node = css_nodes[parent].1;
        // Media queries should not cause a walk up a HTML parent
        // I think this happens at the right time, but might be worth double-checking later
        let walk_up_html_parent_immediately = walk_up_parent && !matches!(parent_node, CssNode::MediaQuery(_) | CssNode::Layer(_));
        if let CssNode::ClassName(parent_node_class) = parent_node {
            let mut is_match = false;
            let el = if walk_up_html_parent_immediately { get_parent_html_idx(element, html_nodes) } else { Some(element) };
            if let Some(el) = el {
                for (name_part_idx, _) in parent_node_class.name_parts.iter().enumerate() {
                    is_match |= narrow_elements_by_ancestors(el, css_nodes, html_nodes, class_elements, parent, name_part_idx, 0, window_size, require_immediate_match, dom_indexes);
                }
            }
            return is_match;
        } else {
            let el = if walk_up_html_parent_immediately { get_parent_html_idx(element, html_nodes) } else { Some(element) };
            if let Some(el) = el {
                return narrow_elements_by_ancestors(el, css_nodes, html_nodes, class_elements, parent, 0, 0, window_size, require_immediate_match, dom_indexes);
            } else {
                return false;
            }
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
    class_elements: &HashMap<String, HashSet<usize>>,
    parts: &Vec<ClassNamePart>,
    css_node: usize,
    nested_part_idx: usize,
    name_part_idx: usize,
    window_size: &PhysicalSize<u32>,
    walk_up_parent: bool,
    require_immediate_match: bool,
    dom_indexes: &DomIndexes,
) -> bool {
    let node = css_nodes[css_node].1;
    // If we've reached the beginning, that means this node is done, so move up the chain
    if nested_part_idx == parts.len() - 1 {
        return move_up_ancestor_chain(element, html_nodes, css_nodes, class_elements, node, window_size, require_immediate_match, walk_up_parent, dom_indexes);
    } else {
        let walk_el = if walk_up_parent { get_parent_html_idx(element, html_nodes) } else { Some(element) };
        if let Some(walk_el) = walk_el {
            return narrow_elements_by_ancestors(walk_el, css_nodes, html_nodes, class_elements, css_node, name_part_idx, nested_part_idx + 1, window_size, require_immediate_match, dom_indexes);
        } else {
            return false;
        }
    }
}

fn walk_for_html_match<F>(element: usize, html_nodes: &HashMap<usize, &Node>, match_fn: F, quota: Option<i32>) -> Option<usize>
where
    F: Fn(usize) -> bool
{
    // If we're not allowed to walk anymore, give up
    if quota.is_some_and(|quota| quota == 0) {
        None
    } else if match_fn(element) {
        Some(element)
    } else if let Some(parent) = html_nodes.get(&element).unwrap().get_parent() {
        walk_for_html_match(parent, html_nodes, match_fn, quota.and_then(|quota| Some(quota - 1)))
    } else {
        None
    }
}

fn element_matches_class_part(
    part: &ClassNamePart,
    element: usize,
    html_nodes: &HashMap<usize, &Node>,
    class_elements: &HashMap<String, HashSet<usize>>,
    dom_indexes: &DomIndexes,
) -> bool {
    match part {
        ClassNamePart::Class(class) => {
            if let Some(elements_to_keep) = class_elements.get(class) {
                elements_to_keep.contains(&element)
            } else {
                false
            }
        },
        ClassNamePart::Id(id) => {
            match html_nodes.get(&element).unwrap() {
                Node::Element(walk_element) => walk_element.attributes.get("id").is_some_and(|el_id| *el_id == *id),
                _ => false,
            }
        },
        ClassNamePart::ArrowRight | ClassNamePart::Ampersand => {
            true
        },
        ClassNamePart::PseudoClass(class) => {
            match class {
                // All elements are children of root
                PseudoClass::Root => true,
                PseudoClass::Not(selector) => {
                    let negative_matches = query_selector_all(&html_nodes, selector.clone(), &PhysicalSize { width: 0, height: 0 }, dom_indexes);
                    !negative_matches.contains(&element)
                },
                _ => false,
            }
        },
        ClassNamePart::Tag(tag) => {
            match html_nodes.get(&element).unwrap() {
                Node::Element(walk_element) => walk_element.tag == *tag,
                _ => false,
            }
        },
        ClassNamePart::Attributes(attributes) => {
            match html_nodes.get(&element).unwrap() {
                Node::Element(walk_element) => element_matched_attributes(walk_element, attributes),
                _ => false,
            }
        },
        ClassNamePart::Combined(combined) => {
            combined.iter().all(|part| element_matches_class_part(part, element, html_nodes, class_elements, dom_indexes))
        }
    }
}

fn narrow_elements_by_ancestors(
    element: usize,
    css_nodes: &Vec<(usize, &CssNode)>,
    html_nodes: &HashMap<usize, &Node>,
    class_elements: &HashMap<String, HashSet<usize>>,
    css_node: usize,
    name_part_idx: usize,
    nested_part_idx: usize,
    window_size: &PhysicalSize<u32>,
    require_immediate_match: bool,
    dom_indexes: &DomIndexes,
) -> bool {
    let walk_quota = if require_immediate_match { Some(1) } else { None };
    let node = css_nodes[css_node].1;
    match node {
        CssNode::ClassName(classes) => {
            let parts = &classes.name_parts[name_part_idx];
            let part = &parts[parts.len() - 1 - nested_part_idx];
            let walk_result = walk_for_html_match(element, html_nodes, |idx| element_matches_class_part(part, idx, html_nodes, class_elements, dom_indexes), walk_quota);
            let (walk_up_parent, require_immediate_match) = match part {
                ClassNamePart::Class(_) | ClassNamePart::Id(_) | ClassNamePart::PseudoClass(_) | ClassNamePart::Tag(_) | ClassNamePart::Attributes(_) | ClassNamePart::Combined(_) => (true, false),
                ClassNamePart::Ampersand => (false, require_immediate_match),
                ClassNamePart::ArrowRight => (false, true),
            };
            if let Some(html_match) = walk_result {
                return move_up_class_part(html_match, css_nodes, html_nodes, class_elements, parts, css_node, nested_part_idx, name_part_idx, window_size, walk_up_parent, require_immediate_match, dom_indexes);
            } else {
                return false;
            }
        },
        CssNode::MediaQuery(query) => {
            if media_query_matches(query, window_size) {
                return move_up_ancestor_chain(element, html_nodes, css_nodes, class_elements, node, window_size, false, true, dom_indexes);
            } else {
                return false;
            }
        },
        // Layers always pass through, they just affect sorting
        CssNode::Layer(_) => {
            return move_up_ancestor_chain(element, html_nodes, css_nodes, class_elements, node, window_size, false, true, dom_indexes);
        },
        _ => {
            return false;
        },
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
) -> (HashMap<usize, Vec<usize>>, HashMap<usize, [i32; 3]>) {
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
            },
            _ => {},
        };
    }
    search_elements_for_css_nodes(to_resolve, css_nodes, &filter_to_elements(raw_html_nodes), window_size, dom_indexes)
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
            ClassNamePart::Attributes(_) | ClassNamePart::PseudoClass(_) | ClassNamePart::Class(_) => tuple[1] += 1,
            ClassNamePart::Tag(_) => tuple[2] += 1,
            ClassNamePart::Combined(combined) => {
                let specificity = get_specificity_tuple(combined);
                for (idx, value) in specificity.iter().enumerate() {
                    tuple[idx] += value;
                }
            },
            _ => {},
        };
    }
    tuple
}

// It is assumed that html_nodes only contains Node::Element here
fn search_elements_for_css_nodes(
    to_resolve: HashSet<usize>,
    css_nodes: &Vec<(usize, &CssNode)>,
    html_nodes: &HashMap<usize, &Node>,
    window_size: &PhysicalSize<u32>,
    dom_indexes: &DomIndexes,
) -> (HashMap<usize, Vec<usize>>, HashMap<usize, [i32; 3]>) {
    let class_elements = &dom_indexes.class_elements;
    let id_elements = &dom_indexes.id_elements;
    let tag_elements = &dom_indexes.tag_elements;

    let mut matches: HashMap<usize, Vec<usize>> = HashMap::new();
    let mut specificity: HashMap<usize, [i32; 3]> = HashMap::new();

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

                    let elements: Option<HashSet<usize>> = match last_part {
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
                                        .collect::<HashSet<usize>>();
                                    Some(elements)
                                },
                                _ => None,
                            }
                        },
                        ClassNamePart::Tag(tag) => tag_elements.get(tag).cloned(),
                        ClassNamePart::Combined(combined) => {
                            let last_part_combined = combined.last().unwrap();
                            let (indexed, base_elements) = match last_part_combined {
                                ClassNamePart::Tag(tag) => (true, tag_elements.get(tag).cloned().unwrap_or(HashSet::new())),
                                ClassNamePart::Class(class) => (true, class_elements.get(class).cloned().unwrap_or(HashSet::new())),
                                ClassNamePart::Id(id) => (true, id_elements.get(id).cloned().unwrap_or(HashSet::new())),
                                _ => (false, html_nodes.iter().map(|(idx, _)| idx).cloned().collect::<HashSet<usize>>()),
                            };
                            let rules_to_apply = if indexed { &combined[..combined.len() - 1].to_vec() } else { combined };

                            let mut filtered_elements = HashSet::new();
                            for el in base_elements.into_iter() {
                                let matched_all = rules_to_apply.iter().all(|part| element_matches_class_part(part, el, &html_nodes, &class_elements, dom_indexes));
                                if matched_all {
                                    filtered_elements.insert(el);
                                }
                            }
                            Some(filtered_elements)
                        },
                        // This is not super efficient, but it's not used all that much so should be okay for now
                        ClassNamePart::Attributes(attributes) => {
                            let filtered_elements = html_nodes
                                .iter()
                                .filter(|(_, node)| match node {
                                    Node::Element(element) => element_matched_attributes(element, attributes),
                                    _ => false,
                                })
                                .map(|(idx, _)| idx)
                                .cloned()
                                .collect();
                            Some(filtered_elements)
                        },
                        // TODO: Implement remaining name part logic
                        _ => None,
                    };

                    if let Some(elements) = elements {
                        for el in elements.to_owned() {
                            // If there's only a single part, we've already completed this class name by doing the last one
                            let is_match = if parts.len() == 1 {
                                move_up_ancestor_chain(el, &html_nodes, css_nodes, &class_elements, node, window_size, false, true, dom_indexes)
                            } else {
                                if let Some(parent_el) = get_parent_html_idx(el, &html_nodes) {
                                    narrow_elements_by_ancestors(parent_el, css_nodes, &html_nodes, &class_elements, css_node_idx, name_part_idx, 1, window_size, false, dom_indexes)
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
            },
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
                        let is_match = move_up_ancestor_chain(*el, &html_nodes, css_nodes, &class_elements, node, window_size, false, true, dom_indexes);

                        if is_match {
                            matches.entry(*el).or_default().push(css_node_idx);
                        }
                    }
                }
            },
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
                    let is_match = move_up_ancestor_chain(*el, &html_nodes, css_nodes, &class_elements, node, window_size, false, true, dom_indexes);

                    if is_match {
                        matches.entry(*el).or_default().push(css_node_idx);
                    }
                }
            },
            _ => println!("Unexpected node appeared: {:?}", node),
        }
    }

    (matches, specificity)
}

fn compute_css_node_ranking(raw_nodes: &Vec<CssNode>, class_node_specificity: &HashMap<usize, [i32; 3]>) -> Vec<usize> {
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
        let a_layer = get_parent_layer(&nodes, **a);
        let b_layer = get_parent_layer(&nodes, **b);

        let layer_ordering = a_layer.cmp(&b_layer);

        if layer_ordering != Ordering::Equal {
            return layer_ordering;
        }

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
                let a_chain = chains.get(a).unwrap();
                let b_chain = chains.get(b).unwrap();

                let a_parent = if a_chain.len() >= 2 { Some(a_chain[1]) } else { None };
                let b_parent = if b_chain.len() >= 2 { Some(b_chain[1]) } else { None };

                let a_specificity = a_parent.and_then(|parent| class_node_specificity.get(&parent)).unwrap_or(&[0; 3]);
                let b_specificity = b_parent.and_then(|parent| class_node_specificity.get(&parent)).unwrap_or(&[0; 3]);

                let specificity_order = get_specificity_order(a_specificity, b_specificity);

                match specificity_order {
                    Ordering::Equal => get_chain_order(a_chain, b_chain),
                    ordering => ordering
                }
            },
            ordering => ordering,
        }
    });
    let mut rankings = vec![0; raw_nodes.len()];
    for (ranking, idx) in sorted_idxs.into_iter().enumerate() {
        rankings[*idx] = ranking;
    }
    rankings
}

fn compute_node_styles(
    base_url: &String,
    tokio: &Rc<RefCell<tokio::runtime::Runtime>>,
    network_fetch: &Rc<RefCell<NetworkFetch>>,
    nodes: &HashMap<usize, Node>,
    node_idxs: &Vec<usize>,
    window_size: &PhysicalSize<u32>,
    dom_indexes: &DomIndexes,
) -> (HashMap<usize, Style>, HashMap<usize, u32>) {
    let css_nodes = combine_css_nodes(base_url, tokio, network_fetch, nodes, node_idxs, &dom_indexes.children_index).unwrap();
    let parsed_css_nodes = parse_css_nodes(&css_nodes).unwrap();

    let css_children_index = build_css_children_index(&parsed_css_nodes.iter().enumerate().collect());

    let start = Instant::now();
    let (collected_class_nodes, class_node_specificity) = collect_class_nodes_for_elements(&parsed_css_nodes.iter().enumerate().collect(), &nodes, window_size, dom_indexes);
    println!("collect_class_nodes_for_elements took {}ms", Instant::now().duration_since(start).as_millis());

    let start = Instant::now();
    let css_node_ranking = compute_css_node_ranking(&parsed_css_nodes, &class_node_specificity);

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
        &HashMap::new(),
        None,
        &collected_class_nodes,
        &css_children_index,
        window_size,
        &css_node_ranking,
    );
    println!("computing styles took {}ms", Instant::now().duration_since(start).as_millis());
    (node_styles, resolved_font_sizes)
}

#[derive(Debug, Clone)]
enum UserEvent {
    DomUpdated,
    Navigate((String, bool)),
}

#[derive(Debug, Clone)]
struct JsHostState {
    renderer: Rc<RefCell<Renderer>>,
    proxy: EventLoopProxy<UserEvent>
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
fn op_set_location_href(state: &mut OpState, #[string] href: String, reload: bool) -> Result<(), JsError> {
    let host = state.borrow::<JsHostState>();

    host.proxy.send_event(UserEvent::Navigate((href, reload))).unwrap();

    Ok(())
}

// TODO: Somehow hook this into fetch as well
#[op2(fast)]
fn op_set_cookie(state: &mut OpState, #[string] url: String, #[string] cookie: String) -> Result<(), JsError> {
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
    renderer.push_node(Node::Element(Element { tag, attributes: HashMap::new(), parent: None }));
    renderer.recompute_dom_indexes();
    let node_idx = renderer.node_idx_cursor;
    Ok(node_idx as i32)
}

#[op2(fast)]
fn op_create_text_element(state: &mut OpState, #[string] text: String) -> Result<i32, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    renderer.push_node(Node::Text(TextElement { text, parent: None }));
    renderer.recompute_dom_indexes();
    let node_idx = renderer.node_idx_cursor;
    Ok(node_idx as i32)
}

#[op2(fast)]
fn op_create_comment_element(state: &mut OpState, #[string] comment: String) -> Result<i32, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    renderer.push_node(Node::Comment(CommentElement { comment, parent: None }));
    renderer.recompute_dom_indexes();
    let node_idx = renderer.node_idx_cursor;
    Ok(node_idx as i32)
}

#[op2]
#[serde]
// TODO: Implement before_reference_idx
fn op_append_child(state: &mut OpState, #[number] parent_idx: usize, #[number] node_idx: usize, #[number] before_reference_idx: Option<usize>) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    renderer.nodes.get_mut(&node_idx).unwrap().set_parent(Some(parent_idx));
    renderer.recompute_dom_indexes();
    renderer.schedule_dom_update(&host.proxy);
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
    host.renderer.borrow_mut().remove_node(child_idx, true);
    Ok(())
}

#[op2]
fn op_get_element_by_id(state: &mut OpState, #[string] id: String) -> Result<Option<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let node_idx = renderer.nodes_idxs.iter().find(|idx| match renderer.nodes.get(*idx).unwrap() {
        Node::Element(element) => element.attributes.get("id").is_some_and(|v| *v == id),
        Node::Text(_) | Node::Comment(_) => false,
    });
    let node = node_idx.and_then(|idx| Some((*idx, renderer.nodes.get(idx).unwrap().clone())));
    Ok(node)
}

#[op2]
fn op_get_elements_by_tag_name(state: &mut OpState, #[string] tag: String) -> Result<Vec<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let nodes: Vec<(usize, Node)> = renderer.nodes_idxs
        .iter()
        .filter(|idx| match renderer.nodes.get(*idx).unwrap() {
            Node::Element(element) => element.tag == tag,
            Node::Text(_) | Node::Comment(_) => false,
        })
        .map(|idx| (*idx, renderer.nodes.get(idx).unwrap().clone()))
        .collect();
    Ok(nodes)
}

#[op2]
fn op_query_selector(state: &mut OpState, #[string] selector: String, #[number] required_parent: Option<usize>) -> Result<Option<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let mut node_idxs: Vec<usize> = query_selector_all(&filter_to_elements(&renderer.nodes), selector_to_parts(&selector), &renderer.window_size, &renderer.dom_indexes);
    if let Some(required_parent) = required_parent {
        node_idxs = node_idxs.into_iter().filter(|idx| has_parent(&renderer.nodes, *idx, required_parent)).collect();
    }
    let node = node_idxs.first();
    let owned = node.cloned().map(|idx| (idx, renderer.nodes.get(&idx).unwrap().clone()));
    Ok(owned)
}

fn has_parent(nodes_table: &HashMap<usize, Node>, node_idx: usize, target_parent: usize) -> bool {
    if node_idx == target_parent {
        return true;
    }

    if let Some(parent) = nodes_table.get(&node_idx).unwrap().get_parent() {
        has_parent(nodes_table, parent, target_parent)
    } else {
        false
    }
}

#[op2]
fn op_query_selector_all(state: &mut OpState, #[string] selector: String, #[number] required_parent: Option<usize>) -> Result<Vec<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let node_idxs: Vec<usize> = query_selector_all(&filter_to_elements(&renderer.nodes), selector_to_parts(&selector), &renderer.window_size, &renderer.dom_indexes);
    let mut owned: Vec<(usize, Node)> = node_idxs.into_iter().map(|idx| (idx, renderer.nodes.get(&idx).unwrap().clone())).collect();
    if let Some(required_parent) = required_parent {
        owned = owned.into_iter().filter(|(idx, _)| has_parent(&renderer.nodes, *idx, required_parent)).collect();
    }
    Ok(owned)
}

#[op2(fast)]
fn op_set_inner_html(state: &mut OpState, #[number] node_idx: usize, #[string] html: String) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let children = renderer.dom_indexes.children_index.get(&node_idx).unwrap_or(&vec![]).clone();
    for child in children {
        renderer.remove_node(child, true);
    }
    renderer.create_children_from_html(node_idx, html);
    renderer.recompute_dom_indexes();
    renderer.schedule_dom_update(&host.proxy);
    Ok(())
}

#[op2(fast)]
fn op_set_text_content(state: &mut OpState, #[number] node_idx: usize, #[string] text: String) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let children = renderer.dom_indexes.children_index.get(&node_idx).unwrap_or(&vec![]).clone();
    for child in children {
        renderer.remove_node(child, true);
    }
    renderer.push_node(Node::Text(TextElement { text, parent: Some(node_idx) }));
    renderer.recompute_dom_indexes();
    renderer.schedule_dom_update(&host.proxy);
    Ok(())
}

#[op2]
#[string]
fn op_get_text_content(state: &mut OpState, #[number] node_idx: usize) -> Result<String, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let text = host.renderer.borrow_mut().get_element_text_content(node_idx);
    Ok(text)
}

#[op2(fast)]
fn op_media_query_matches(state: &mut OpState, #[string] query: String) -> Result<bool, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow_mut();
    let matches = media_query_matches(&MediaQuery {
        criterias: parse_media_query_parts(query.as_str()),
        parent: None,
    }, &renderer.window_size);
    Ok(matches)
}

#[op2]
fn op_get_child_nodes(state: &mut OpState, #[number] node_idx: usize) -> Result<Vec<(usize, Node)>, JsError> {
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
fn op_get_parent_node(state: &mut OpState, #[number] node_idx: usize) -> Result<(usize, Node), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow_mut();
    let parent_idx = renderer.nodes.get(&node_idx).unwrap().get_parent().unwrap();
    let parent = (parent_idx, renderer.nodes.get(&parent_idx).unwrap().clone());
    Ok(parent)
}

#[op2]
#[serde]
fn op_update_attributes(state: &mut OpState, #[number] node_idx: usize, #[serde] attributes: HashMap<String, String>) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    match renderer.nodes.get_mut(&node_idx).unwrap() {
        Node::Element(element) => {
            for (key, value) in attributes {
                element.attributes.insert(key, value);
            }
        },
        _ => {},
    };
    renderer.schedule_dom_update(&host.proxy);
    Ok(())
}

fn get_canvas_wh(node: &Node) -> (Option<u32>, Option<u32>) {
    match node {
        Node::Element(element) => (
            element.attributes.get("width").and_then(|v| v.parse::<u32>().ok()).or(Some(150)),
            element.attributes.get("height").and_then(|v| v.parse::<u32>().ok()).or(Some(150)),
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

    let canvas = renderer.canvas_buffers
        .entry(node_idx)
        .or_insert_with(|| CanvasBuffer::new(node_width, node_height));
    canvas.resize_if_needed(node_width, node_height);

    draw_rect_filled(&mut canvas.buffer, node_width, node_height, x, y, width, height, 0x00_00_00_FF);

    renderer.schedule_dom_update(&host.proxy);

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

    let canvas = renderer.canvas_buffers
        .entry(node_idx)
        .or_insert_with(|| CanvasBuffer::new(node_width, node_height));
    canvas.resize_if_needed(node_width, node_height);

    draw_rect_filled(&mut canvas.buffer, node_width, node_height, x, y, line_width, height, 0x00_00_00_FF); // Left
    draw_rect_filled(&mut canvas.buffer, node_width, node_height, x, y, width, line_width, 0x00_00_00_FF); // Top
    draw_rect_filled(&mut canvas.buffer, node_width, node_height, x + width as i32 - line_width as i32, y, line_width, height, 0x00_00_00_FF); // Right
    draw_rect_filled(&mut canvas.buffer, node_width, node_height, x, y + height as i32 - line_width as i32, width, line_width, 0x00_00_00_FF); // Bottom

    renderer.schedule_dom_update(&host.proxy);

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

    let canvas = renderer.canvas_buffers
        .entry(node_idx)
        .or_insert_with(|| CanvasBuffer::new(node_width, node_height));

    let mut cursor = Position { x: path[0][0] as i32, y: path[0][1] as i32 };
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
                    let px = (start_x + idx as f64 * x_ratio + wxidx as f64).round().min(node_width as f64) as i32;
                    let py = (start_y + idx as f64 * y_ratio + wyidx as f64).round().min(node_height as f64) as i32;

                    let row = &mut canvas.buffer[py as usize * stride..(py as usize + 1) * stride];
                    row[px as usize] = blend_rgb_with_rgba(row[px as usize], color_tuple);
                }
            }
        }

        cursor.x = x.round() as i32;
        cursor.y = y.round() as i32;
    }

    renderer.schedule_dom_update(&host.proxy);

    Ok(())
}

// This should walk the tree to be fully correct I think
fn query_selector_all(nodes_table: &HashMap<usize, &Node>, selector: Vec<ClassNamePart>, window_size: &PhysicalSize<u32>, dom_indexes: &DomIndexes) -> Vec<usize> {
    let class = CssNode::ClassName(ClassName {
        name: vec![],
        name_parts: vec![selector],
        parent: None,
    });
    let css_vec = vec![class];
    let css_nodes: Vec<(usize, &CssNode)> = css_vec.iter().enumerate().collect();
    let mut to_resolve = HashSet::new();
    to_resolve.insert(0);
    let (collected, _) = search_elements_for_css_nodes(to_resolve, &css_nodes, nodes_table, window_size, dom_indexes);

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
    op_get_inner_html,
    op_get_text_content,
    op_tls_peer_certificate,
    op_fill_canvas_rect,
    op_stroke_canvas_rect,
    op_canvas_path_stroke,
    op_set_cookie,
    op_get_cookie,
    op_set_location_href,
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
  esm = [
    "ext:deno_node/internal/crypto/constants.ts" = {
      source = "export const kKeyObject = Symbol('kKeyObject');"
    },
  ],
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
}

fn sorted_node_idxs(nodes: &HashMap<usize, Node>) -> Vec<usize> {
    let mut node_idxs: Vec<usize> = nodes.keys().copied().collect();
    node_idxs.sort_unstable();
    node_idxs
}

fn get_dom_indexes(html_nodes: &HashMap<usize, Node>) -> DomIndexes {
    let nodes_idxs = sorted_node_idxs(html_nodes);
    let mut class_elements: HashMap<String, HashSet<usize>> = HashMap::new();
    for (html_node_idx, html_node) in html_nodes.iter() {
        match html_node {
            Node::Element(element) => {
                let class_list = get_class_list(element);
                for class in class_list {
                    class_elements.entry(class).or_default().insert(*html_node_idx);
                }
            },
            _ => {},
        };
    }

    let mut id_elements: HashMap<String, HashSet<usize>> = HashMap::new();
    for (html_node_idx, html_node) in html_nodes.iter() {
        match html_node {
            Node::Element(element) => {
                if let Some(id) = element.attributes.get("id") {
                    id_elements.entry(id.clone()).or_default().insert(*html_node_idx);

                }
            },
            _ => {},
        };
    }

    let mut tag_elements: HashMap<String, HashSet<usize>> = HashMap::new();
    for (html_node_idx, html_node) in html_nodes.iter() {
        match html_node {
            Node::Element(element) => {
                tag_elements.entry(element.tag.clone()).or_default().insert(*html_node_idx);
            },
            _ => {},
        };
    }

    let children_index = build_children_index(&html_nodes, &nodes_idxs);

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

    DomIndexes {
        class_elements,
        tag_elements,
        id_elements,
        children_index,
        root_indice
    }
}

#[derive(Debug)]
struct CachedRasterizations {
    decoded_pngs: HashMap<String, Pixmap>,
    decoded_jpegs: HashMap<String, DynamicImage>,
    jpegs: HashMap<(String, u32, u32), Pixmap>,
}

impl CachedRasterizations {
    pub fn new() -> Self {
        Self {
            decoded_pngs: HashMap::new(),
            decoded_jpegs: HashMap::new(),
            jpegs: HashMap::new(),
        }
    }
}

impl Renderer {
    fn new(url: String, tokio: Rc<RefCell<tokio::runtime::Runtime>>, nodes_table: HashMap<usize, Node>, window_size: PhysicalSize<u32>, font_handler: Rc<FontHandler>, network_fetch: Rc<RefCell<NetworkFetch>>, dom_indexes: DomIndexes) -> Self {
        let request_cache = HashMap::new();

        let layout_table = HashMap::new();
        let containing_nodes = HashMap::new();
        let node_layout_mapping = HashMap::new();

        let rendered_nodes_ordered = vec![];
        let hovering = None;

        let nodes_idxs = sorted_node_idxs(&nodes_table);

        let (node_styles, resolved_font_sizes) = compute_node_styles(&url, &tokio, &network_fetch, &nodes_table, &nodes_idxs, &window_size, &dom_indexes);

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
            scroll_y: 0,
            layout_roots: vec![],
            resolved_specified_heights: HashMap::new(),
            resolved_specified_widths: HashMap::new(),
            dom_indexes,
            canvas_buffers: HashMap::new(),
            network_fetch,
            cached_rasterizations: CachedRasterizations::new(),
        }
    }

    pub fn get_scripts(&mut self) -> Vec<Script> {
        let mut scripts: Vec<Script> = self.nodes_idxs
            .iter()
            .filter(|node_idx| match self.nodes.get(*node_idx).unwrap() {
                Node::Element(element) => element.tag == "script",
                _ => false,
            })
            .map(|idx| -> Option<Script> {
                match self.nodes.get(idx).unwrap() {
                    Node::Element(element) => {
                        let script_type = match element.attributes.get("type").map(|v| v.trim().to_ascii_lowercase()) {
                            None => ScriptType::Classic,
                            Some(script_type) if script_type.is_empty() => ScriptType::Classic,
                            Some(script_type) if script_type == "text/javascript" => ScriptType::Classic,
                            Some(script_type) if script_type == "application/javascript" => ScriptType::Classic,
                            Some(script_type) if script_type == "text/ecmascript" => ScriptType::Classic,
                            Some(script_type) if script_type == "application/ecmascript" => ScriptType::Classic,
                            Some(script_type) if script_type == "module" => ScriptType::Module,
                            _ => return None,
                        };
                        let src = element.attributes.get("src");
                        if let Some(src) = src {
                            return Some(Script { content: ScriptContent::Link(src.to_string()), script_type, node_idx: Some(*idx) });
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
                            Node::Text(element) => Some(Script { content: ScriptContent::Code(element.text.clone()), script_type, node_idx: Some(*idx) }),
                            Node::Comment(_) => {
                                return None;
                            },
                        };

                        text
                    }
                    Node::Text(_) | Node::Comment(_) => None,
                }
            })
            .flatten()
            .collect();

        scripts.sort_by(|a, b| {
            (a.script_type.clone() as u32).cmp(&(b.script_type.clone() as u32))
        });

        scripts
    }

    fn apply_overflow_constraints_inner(&mut self, layout_box_id: usize, mut overflow_box: Option<(u32, u32, u32, u32)>) {
        let layout_box = self.layout_table.get_mut(&layout_box_id).unwrap();

        if let Some((start_x, start_y, end_x, end_y)) = overflow_box {
            layout_box.rect.x = layout_box.rect.x.max(start_x as i32);
            layout_box.rect.y = layout_box.rect.y.max(start_y as i32);
            let target_end_x = layout_box.rect.x + layout_box.rect.width as i32;
            let overflow_right = target_end_x - end_x as i32;
            layout_box.rect.width = layout_box.rect.width.saturating_sub_signed(overflow_right.max(0));
            let target_end_y = layout_box.rect.y + layout_box.rect.height as i32;
            let overflow_bottom = target_end_y - end_y as i32;
            layout_box.rect.height = layout_box.rect.height.saturating_sub_signed(overflow_bottom.max(0));
        }

        if !layout_box.allow_overflow {
            let rect = &layout_box.rect;
            overflow_box = Some((rect.x as u32, rect.y as u32, (rect.x + rect.width as i32) as u32, (rect.y + rect.height as i32) as u32));
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
            self.layout_roots = self.build_layout(width, height);
            self.apply_overflow_constraints();
        }
        let mut new_rendered_nodes_ordered = vec![];
        for layout_box_idx in self.layout_roots.iter() {
            self.paint_layout_box(*layout_box_idx, buffer, width, height, self.scroll_y, &mut new_rendered_nodes_ordered);
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
                content_type => Err(anyhow!("Failed to handle image content-type: {}", content_type)),
            }
        }.await;

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
        let requests: Vec<(ReqwestUrl, &'static str)> = self.nodes
            .values()
            .filter_map(|n| match n {
                Node::Element(element) if element.tag == "img" => {
                    element.attributes.get("src").map(|src| src.as_str())
                },
                _ => None
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
                    self.request_cache.insert(url, RequestCacheEntry::Unsupported);
                }
            }
        }
    }

    fn build_layout(&mut self, width: u32, height: u32) -> Vec<usize> {
        let mut layout_roots = Vec::new();

        self.node_layout_mapping.clear();

        self.prefetch_images();

        // Create initial containing node
        self.containing_nodes.insert(self.dom_indexes.root_indice, ContainingNode {
            node_idx: self.dom_indexes.root_indice,
            waiters: vec![],
        });
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
        ) {
            layout_roots.push(layout_box_idx);
        }

        layout_roots
    }

    fn inject_css_variables_into_str(&self, str: &mut String, variables: &HashMap<String, String>) {
        // Return early if string doesn't need any vars
        if !str.contains("var(") {
            return;
        }
        for (variable, value) in variables.iter() {
            *str = str.replace(&format!("var({})", variable), value);
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
            },
            Node::Element(_) => {
                for child_idx in self.dom_indexes.children_index.get(&node_idx).unwrap() {
                    str += &self.get_text_content(*child_idx);
                }
            },
            Node::Comment(_) => {},
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
            },
            Node::Comment(element) => {
                str += &format!("<!--{}-->", element.comment);
            },
        }
        str
    }

    async fn get_img_src_data(&mut self, src: &str) -> Result<RequestCacheEntry> {
        let base = ReqwestUrl::parse(&self.url)?;
        let url = resolve_url(src, Some(&base))?;
        let src_extension = Self::img_src_extension(src).with_context(|| format!("Unsupported img extension: {}", src))?;
        if let Some(cache) = self.request_cache.get(&url) {
            match cache {
                RequestCacheEntry::Unsupported => Err(anyhow!("Unsupported image")),
                v => Ok(v.clone())
            }
        } else {
            let (url, cache_entry) = Self::fetch_img_src_data_url(self.network_fetch.borrow().client.clone(), url, src_extension).await;
            if let Ok(ref entry) = cache_entry {
                self.request_cache.insert(url, entry.clone());
            } else {
                self.request_cache.insert(url, RequestCacheEntry::Unsupported);
            }
            cache_entry
        }
    }

    fn register_layout_box(
        &mut self,
        layout_box: LayoutBox,
        save_as_final: bool,
    ) -> usize {
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
        let resolved_parent_font_size = self.resolved_font_sizes
            .get(&self.nodes.get(&node_idx).unwrap().get_parent().unwrap_or(node_idx))
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
    ) -> Option<usize> {
        let style = self.node_styles.get(&node_idx).unwrap().clone();

        let resolved_font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();

        match self.nodes.get(&node_idx).unwrap().clone() {
            Node::Comment(_) => None,
            Node::Text(text) => {
                let text = collapse_whitespace(&text.text).unwrap_or("".to_string());
                let renderable_text = self.font_handler
                    .get_renderable_text(text.clone(), resolved_font_size as i32, Some(available_size.width))
                    .inspect_err(|err| println!("Failed to get renderable text for {} {:?}", text, err))
                    .ok()?;
                let width = forced_size.width.unwrap_or(renderable_text.width);
                let height = forced_size.height.unwrap_or(renderable_text.height);

                Some(self.register_layout_box(LayoutBox {
                    rect: Rect {
                        x: cursor.x,
                        y: cursor.y,
                        width,
                        height,
                        background: StyleBackground::Transparent,
                        color: style.color,
                        font_size: Some(resolved_font_size),
                        border: RectBorder::new_empty(),
                    },
                    kind: LayoutKind::Text(renderable_text),
                    children: vec![],
                    node_idx,
                    allow_overflow: style.overflow == Overflow::Visible,
                }, save_as_final))
            }
            Node::Element(element) => {
                if element.tag == "svg" || element.tag == "img" || element.tag == "canvas" {
                    let style = self.node_styles.get(&node_idx).unwrap().clone();
                    if let StyleDisplay::None = style.display {
                        return None;
                    }
                    let container_size = self.get_container_sizes(node_idx, &OptionalSize { height: None, width: None }, &style, &available_size);
                    let (containing_block_height, containing_block_width) = self.get_containing_block_size(containing_node_idx, node_idx, &style);
                    let max_h = get_specified_size(resolved_font_size as u32, &style.max_height, containing_block_height, None, &self.window_size).unwrap_or(available_size.height as i32) as u32;
                    let max_w = get_specified_size(resolved_font_size as u32, &style.max_width, containing_block_width, None, &self.window_size).unwrap_or(available_size.width as i32) as u32;
                    let (pixmap, height, width) = match element.tag.as_str() {
                        "canvas" => {
                            let (Some(canvas_width), Some(canvas_height)) = (match self.nodes.get(&node_idx).unwrap() {
                                Node::Element(element) => (
                                    element.attributes.get("width").and_then(|v| v.parse::<u32>().ok()).or(Some(150)),
                                    element.attributes.get("height").and_then(|v| v.parse::<u32>().ok()).or(Some(150)),
                                ),
                                _ => (None, None),
                            }) else {
                                return None;
                            };
                            let canvas = self.canvas_buffers.entry(node_idx).or_insert_with(|| CanvasBuffer::new(canvas_width, canvas_height));
                            canvas.resize_if_needed(canvas_width, canvas_height);
                            let data = rgb_buffer_to_premul_bytes(&canvas.buffer);
                            let pixmap = tiny_skia::Pixmap::from_vec(data, IntSize::from_wh(canvas_width, canvas_height)?)?;
                            (pixmap, container_size.container_height, container_size.container_width)
                        },
                        "svg" => {
                            let mut svg_data = self.get_element_html(node_idx);
                            self.inject_css_variables_into_str(&mut svg_data, &style.variables);
                            let result = rasterize_svg(svg_data.as_bytes(), container_size.container_width_non_filling, container_size.container_height_non_filling, max_w, max_h, &style);
                            match result {
                                Err(err) => {
                                    println!("Failed to rasterize SVG data: {}", err);
                                    return None;
                                },
                                Ok(res) => res,
                            }
                        },
                        "img" => {
                            let src = element.attributes.get("src")?;
                            if src.starts_with("data:") {
                                if let Some(data) = src.strip_prefix("data:image/svg+xml,") {
                                    let mut decoded = percent_encoding::percent_decode_str(data).decode_utf8().ok()?.to_string();
                                    self.inject_css_variables_into_str(&mut decoded, &style.variables);
                                    let result = rasterize_svg(decoded.as_bytes(), container_size.container_width_non_filling, container_size.container_height_non_filling, max_w, max_h, &style);
                                    match result {
                                        Err(err) => {
                                            println!("Failed to rasterize SVG data: {}", err);
                                            return None;
                                        },
                                        Ok(res) => res,
                                    }
                                } else {
                                    return None
                                }
                            } else {
                                let img_data = self.tokio.clone().borrow_mut().block_on(self.get_img_src_data(src)).ok()?;
                                let result = match img_data {
                                    RequestCacheEntry::PngData(bytes) => {
                                        rasterize_png(&mut self.cached_rasterizations, src, &bytes, container_size.container_width_non_filling, container_size.container_height_non_filling, max_w, max_h).unwrap()
                                    },
                                    RequestCacheEntry::JpegData(bytes) => {
                                        rasterize_jpeg(&mut self.cached_rasterizations, &src, &bytes, container_size.container_width_non_filling, container_size.container_height_non_filling, max_w, max_h).unwrap()
                                    },
                                    RequestCacheEntry::SvgData(svg_data) => {
                                        let mut injected = svg_data.clone();
                                        self.inject_css_variables_into_str(&mut injected, &style.variables);
                                        let result = rasterize_svg(injected.as_bytes(), container_size.container_width_non_filling, container_size.container_height_non_filling, max_w, max_h, &style);
                                        match result {
                                            Err(err) => {
                                                println!("Failed to rasterize SVG data: {}", err);
                                                return None;
                                            },
                                            Ok(res) => res,
                                        }
                                    },
                                    _ => panic!(),
                                };
                                result
                            }
                        },
                        _ => panic!(),
                    };

                    Some(self.register_layout_box(LayoutBox {
                        rect: Rect {
                            x: cursor.x,
                            y: cursor.y,
                            width,
                            height,
                            background: StyleBackground::Transparent,
                            color: StyleBackground::Transparent,
                            font_size: None,
                            border: RectBorder::new_empty(),
                        },
                        kind: LayoutKind::PixMap(pixmap),
                        children: vec![],
                        node_idx,
                        allow_overflow: style.overflow == Overflow::Visible,
                    }, save_as_final))
                } else {
                    let layout = match style.display {
                        StyleDisplay::Block | StyleDisplay::InlineBlock | StyleDisplay::Inline => self.layout_block(
                            node_idx,
                            cursor,
                            &style,
                            available_size,
                            forced_size,
                            containing_node_idx,
                            allow_fill,
                            save_as_final,
                        ),
                        StyleDisplay::Flex | StyleDisplay::InlineFlex => self.layout_flex(
                            node_idx,
                            cursor,
                            &style,
                            available_size,
                            forced_size,
                            containing_node_idx,
                            allow_fill,
                            save_as_final,
                        ),
                        StyleDisplay::Grid => self.layout_grid(
                            node_idx,
                            cursor,
                            &style,
                            available_size,
                            forced_size,
                            containing_node_idx,
                            allow_fill,
                            save_as_final,
                        ),
                        StyleDisplay::None => None,
                    };

                    if let Some((width, height, children)) = layout {
                        let border = RectBorder {
                            left: RectBorderSide::parse_from_style(&style.border_left, resolved_font_size as u32, &available_size, &self.window_size),
                            top: RectBorderSide::parse_from_style(&style.border_top, resolved_font_size as u32, &available_size, &self.window_size),
                            right: RectBorderSide::parse_from_style(&style.border_right, resolved_font_size as u32, &available_size, &self.window_size),
                            bottom: RectBorderSide::parse_from_style(&style.border_bottom, resolved_font_size as u32, &available_size, &self.window_size),
                        };

                        if let StyleBackground::DataUrl((format, data)) = &style.background {
                            let container_size = self.get_container_sizes(node_idx, &OptionalSize { height: None, width: None }, &style, &available_size);
                            let _ = self.resolve_background_data_url(node_idx, format, data, &container_size, &style)
                                .inspect_err(|err| eprintln!("An error occured while resolving background data url: {}", err));
                        }

                        Some(self.register_layout_box(LayoutBox {
                            rect: Rect {
                                x: cursor.x,
                                y: cursor.y,
                                width,
                                height,
                                background: style.background,
                                color: style.color,
                                font_size: None,
                                border,
                            },
                            kind: LayoutKind::Element,
                            children,
                            node_idx,
                            allow_overflow: style.overflow == Overflow::Visible,
                        }, save_as_final))
                    } else {
                        None
                    }
                }
            }
        }
    }

    fn resolve_background_data_url(&mut self, node_idx: usize, format: &String, data: &String, container_size: &ContainerSizes, style: &Style) -> Result<()> {
        match format.as_str() {
            "image/svg+xml" => {
                let mut svg_data = percent_encoding::percent_decode_str(data).decode_utf8()?.to_string();
                self.inject_css_variables_into_str(&mut svg_data, &style.variables);
                let result = rasterize_svg(svg_data.as_bytes(), Some(container_size.container_width), Some(container_size.container_height), container_size.container_width, container_size.container_height, &style);
                match result {
                    Err(err) => {
                        println!("Failed to rasterize SVG data: {}", err);
                    },
                    Ok((pixmap, _, _)) => {
                        self.resolved_pixmaps.insert(node_idx.to_string(), pixmap);
                    },
                };
            },
            format => panic!("Unsupported background data format: {}", format),
        };
        Ok(())
    }

    fn get_margin_free_space_to_give(&self, free_space: u32, first_margin: &StyleSize, last_margin: &StyleSize) -> u32 {
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

    fn divide_free_space_for_margin(&mut self, children_rows: &MarginRows, container_width: i32, free_space_y: u32) {
        let mut free_space_to_give_y = 0;
        // TODO: I don't think this is 100% accurate
        if let (Some(first_child), Some(last_child)) = (children_rows.rows.first().and_then(|v| v.first()), children_rows.rows.last().and_then(|v| v.last())) {
            let first_child_style = &self.node_styles.get(&self.layout_to_node_idx(first_child)).unwrap();
            let last_child_style = &self.node_styles.get(&self.layout_to_node_idx(last_child)).unwrap();
            free_space_to_give_y = self.get_margin_free_space_to_give(free_space_y, &first_child_style.margin_top, &last_child_style.margin_bottom);
        }
        for row in children_rows.rows.iter() {
            let first_child = row.first().unwrap();
            let last_child = row.last().unwrap();

            let first_child_style = &self.node_styles.get(&self.layout_to_node_idx(first_child)).unwrap();
            let last_child_style = &self.node_styles.get(&self.layout_to_node_idx(last_child)).unwrap();

            let mut used_space = 0i32;
            for child in row.iter() {
                let child_box = &self.layout_table.get(child).unwrap();
                used_space += child_box.rect.width as i32;
            }
            let free_space_x = (container_width - used_space).max(0) as u32;

            let mut first_margin = first_child_style.margin_left.clone();
            let mut last_margin = last_child_style.margin_right.clone();
            // If the text-align isn't left, and all children in this row are the same, use that instead of the margin
            if first_child_style.text_align != StyleAlign::Left && row.iter().all(|c| self.node_styles.get(&self.layout_to_node_idx(c)).unwrap().text_align == first_child_style.text_align) {
                (first_margin, last_margin) = match first_child_style.text_align {
                    StyleAlign::Left => panic!(),
                    StyleAlign::Center => (StyleSize::Auto, StyleSize::Auto),
                    StyleAlign::Right => (StyleSize::Auto, StyleSize::Px(0.)),
                };
            }

            let free_space_to_give_x = self.get_margin_free_space_to_give(free_space_x, &first_margin, &last_margin);
            for child in row {
                let already_moved_x = children_rows.alignment_movements.get(child).unwrap();
                // TODO: Maybe do this for Y too
                self.move_entire_box(*child, free_space_to_give_x as i32 - already_moved_x, free_space_to_give_y as i32);
            }
        }
    }

    fn get_container_sizes(&self, node_idx: usize, forced_size: &OptionalSize, style: &Style, available_size: &Size) -> ContainerSizes {
        let (padding_left_size, padding_right_size, padding_top_size, padding_bottom_size) =
            self.get_paddings(node_idx, style, *available_size);
        let (border_left_size, border_right_size, border_top_size, border_bottom_size) =
            self.get_border_sizes(node_idx, style, *available_size);

        let resolved_font_size = self.resolved_font_sizes.get(&node_idx).unwrap();

        let min_height = get_specified_size(*resolved_font_size, &style.min_height, Some(available_size.height), None, &self.window_size)
            .and_then(|v| Some(v as u32));
        let max_height = get_specified_size(*resolved_font_size, &style.max_height, Some(available_size.height), None, &self.window_size)
            .and_then(|v| Some(v as u32));
        let min_width = get_specified_size(*resolved_font_size, &style.min_width, Some(available_size.width), None, &self.window_size)
            .and_then(|v| Some(v as u32));
        let max_width = get_specified_size(*resolved_font_size, &style.max_width, Some(available_size.width), None, &self.window_size)
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
        let container_width_non_filling = specified_width
            .and_then(|v| Some(
                v
                .min(max_width.unwrap_or(u32::MAX))
                .max(min_width.unwrap_or(u32::MIN))
            ));
        let container_width = specified_width
            .unwrap_or(available_size.width)
            .min(max_width.unwrap_or(u32::MAX))
            .max(min_width.unwrap_or(u32::MIN));
        let inner_width = container_width.saturating_sub((padding_left_size + padding_right_size + border_left_size + border_right_size) as u32);
        // TODO: Container heights should probably respect min and max height
        let container_height_non_filling = specified_height;
        let container_height = specified_height
            .unwrap_or(available_size.height);
        let inner_height = container_height
            .saturating_sub((padding_top_size + padding_bottom_size + border_top_size + border_bottom_size) as u32);

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

    fn create_input_text_box(&mut self, node_idx: usize, input_value: String, cursor: &mut Position, font_size: u32, save_as_final: bool) -> Result<usize> {
        let style = &self.node_styles.get(&node_idx).unwrap();
        let text = collapse_whitespace(&input_value).unwrap();
        let renderable_text = self.font_handler.get_renderable_text(text, font_size as i32, None).with_context(|| "Failed to compute renderable text")?;

        let layout_box = self.register_layout_box(LayoutBox {
            rect: Rect {
                x: cursor.x,
                y: cursor.y,
                width: renderable_text.width,
                height: renderable_text.height,
                background: StyleBackground::Transparent,
                color: style.color.clone(),
                font_size: Some(font_size as u32),
                border: RectBorder::new_empty(),
            },
            kind: LayoutKind::Text(renderable_text),
            children: vec![],
            node_idx,
            allow_overflow: style.overflow == Overflow::Visible,
        }, save_as_final);
        Ok(layout_box)
    }

    fn get_grid_column(&self, current_column: i32, template_columns: &Vec<GridTemplateColumnsValue>) -> bool {
        // Are we out of columns?
        current_column >= template_columns.len() as i32
    }

    fn layout_grid(
        &mut self,
        node_idx: usize,
        cursor: Position,
        style: &Style,
        available_size: Size,
        forced_size: OptionalSize,
        mut containing_node_idx: usize,
        allow_fill: bool,
        save_as_final: bool,
    ) -> Option<(u32, u32, Vec<usize>)> {
        let container_sizes = self.get_container_sizes(node_idx, &forced_size, style, &available_size);
        if style.position == StylePosition::Relative {
            self.containing_nodes.insert(node_idx, ContainingNode {
                node_idx,
                waiters: vec![],
            });
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
        let (containing_block_height, containing_block_width) = self.get_containing_block_size(containing_node_idx, node_idx, style);
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
        self.resolved_specified_heights.insert(node_idx, specified_height);
        self.resolved_specified_widths.insert(node_idx, specified_width);
        let mut max_child_height = 0;
        let mut longest_row_width = 0;
        let width_to_distribute = container_sizes.inner_width;
        let children_idxs = self.dom_indexes.children_index.get(&node_idx).cloned().unwrap();
        let mut current_column = 0;
        let mut definitely_used_width = 0;
        let mut max_total_fractions = 0;
        if let GridTemplateColumns::Values(template_columns) = style.grid_template_columns.clone() {
            for value in template_columns.iter() {
                match value {
                    GridTemplateColumnsValue::Size(size) => {
                        definitely_used_width += match size {
                            GridColumnSize::Px(px) => *px,
                            // TODO: This is probably not entirely correct, so come back to this
                            GridColumnSize::Fraction(_) => panic!(),
                        };
                    },
                    GridTemplateColumnsValue::MinMax((_, max)) => {
                        if let GridColumnSize::Fraction(fraction) = max {
                            max_total_fractions += fraction;
                        }
                    },
                };
            }
        }
        let dynamic_space_to_give = width_to_distribute - definitely_used_width as u32;
        for child_idx in children_idxs.iter() {
            let wrap = if let GridTemplateColumns::Values(template_columns) = style.grid_template_columns.clone() {
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
            let specified_column_size = if let GridTemplateColumns::Values(template_columns) = style.grid_template_columns.clone() {
                match &template_columns[current_column as usize] {
                    GridTemplateColumnsValue::Size(size) => {
                        match size {
                            GridColumnSize::Px(px) => *px,
                            // TODO: This is probably not entirely correct, so come back to this
                            GridColumnSize::Fraction(_) => panic!(),
                        }
                    },
                    GridTemplateColumnsValue::MinMax((min, max)) => {
                        let min_parsed = match min {
                            GridColumnSize::Px(px) => *px,
                            GridColumnSize::Fraction(_) => panic!(),
                        };
                        let max_parsed = match max {
                            GridColumnSize::Px(px) => *px,
                            GridColumnSize::Fraction(fraction) => (dynamic_space_to_give as f32 * (*fraction as f32 / max_total_fractions as f32)) as i32,
                        };

                        // TODO: Take min into account
                        max_parsed
                    },
                }
            } else {
                available_size.width as i32
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
                // Inline-block doesn't fill the width, so instruct children to not do that either
                match style.display {
                    StyleDisplay::InlineBlock | StyleDisplay::Inline => false,
                    _ => allow_fill,
                },
                save_as_final,
            ) {
                let child_box = self.layout_table.get(&child).unwrap();
                content_position.x += specified_column_size;
                longest_row_width = longest_row_width.max(content_position.x - original_content_position.x);
                current_column += 1;
                max_child_height = max_child_height.max(child_box.rect.height as i32);
                children.push(child);
            }
        }
        let content_height = (content_position.y - original_content_position.y).max(max_child_height);
        let height = specified_height
            .unwrap_or(content_height as u32)
            .min(container_sizes.max_height.unwrap_or(u32::MAX))
            .max(container_sizes.min_height.unwrap_or(u32::MIN));
        let width = if allow_fill { container_sizes.container_width } else { container_sizes.compute_actual_container_width(longest_row_width as u32) };
        Some((width as u32, height as u32, children))
    }

    fn get_containing_block_size(&self, containing_node_idx: usize, node_idx: usize, style: &Style) -> (Option<u32>, Option<u32>) {
        // This is the parent which this node uses for % sizing, and possibly more later on
        let containing_block = match style.position {
            StylePosition::Absolute | StylePosition::Fixed => Some(containing_node_idx),
            StylePosition::Relative | StylePosition::Static => self.nodes.get(&node_idx).unwrap().get_parent(),
        };
        let containing_block_height = containing_block.and_then(|idx| self.resolved_specified_heights.get(&idx).unwrap().clone());
        let containing_block_width = containing_block.and_then(|idx| self.resolved_specified_widths.get(&idx).unwrap().clone());

        (containing_block_height, containing_block_width)
    }

    fn layout_block(
        &mut self,
        node_idx: usize,
        cursor: Position,
        style: &Style,
        available_size: Size,
        forced_size: OptionalSize,
        mut containing_node_idx: usize,
        allow_fill: bool,
        save_as_final: bool,
    ) -> Option<(u32, u32, Vec<usize>)> {
        let (padding_left_size, padding_right_size, padding_top_size, padding_bottom_size) =
            self.get_paddings(node_idx, style, available_size);

        let mut content_position = Position {
            x: cursor.x + padding_left_size as i32,
            y: cursor.y + padding_top_size as i32,
        };
        let original_cursor = content_position.clone();
        let mut children = Vec::new();

        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();

        let (containing_block_height, containing_block_width) = self.get_containing_block_size(containing_node_idx, node_idx, style);

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

        self.resolved_specified_heights.insert(node_idx, specified_height);
        self.resolved_specified_widths.insert(node_idx, specified_width);

        let container_sizes = self.get_container_sizes(node_idx, &forced_size, style, &available_size);

        let children_idxs: Vec<usize> = self.dom_indexes.children_index.get(&node_idx).unwrap().clone();

        let immediate_children: Vec<&usize> = children_idxs.iter().filter(|c| {
            let style = &self.node_styles.get(*c).unwrap();
            !style.position.is_free()
        }).collect();
        let free_children: Vec<&usize> = children_idxs.iter().filter(|c| {
            let style = &self.node_styles.get(*c).unwrap();
            style.position.is_free()
        }).collect();

        if style.position == StylePosition::Relative {
            self.containing_nodes.insert(node_idx, ContainingNode {
                node_idx,
                waiters: vec![],
            });
            containing_node_idx = node_idx;
        }

        for child_idx in free_children {
            let containing_node = self.containing_nodes
                .get_mut(&containing_node_idx)
                .unwrap();

            containing_node
                .waiters
                .push(ResumableNode { parent_idx: node_idx, node_idx: *child_idx, available_size, cursor: content_position });
        }

        let mut max_child_width: u32 = 0;
        let mut max_child_height: u32 = 0;
        let mut child_width_buffer = 0;

        let mut children_rows = MarginRows::new();

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
                // Inline-block doesn't fill the width, so instruct children to not do that either
                match style.display {
                    StyleDisplay::InlineBlock | StyleDisplay::Inline => false,
                    _ => allow_fill,
                },
                save_as_final,
            ) {
                let child_box = self.layout_table.get(&child).unwrap();
                let prev_child_display: Option<StyleDisplay> = prev_child_idx.and_then(|idx| Some(self.node_styles.get(idx).unwrap().display));
                let next_child_display: Option<StyleDisplay> = next_child_idx.and_then(|idx| Some(self.node_styles.get(idx).unwrap().display));
                if child_style.display.is_inline() && prev_child_display.is_none_or(|v| v.is_inline()) && next_child_display.is_none_or(|v| v.is_inline()) {
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
            let layout_box = self.create_input_text_box(node_idx, input_value.unwrap().clone(), &mut content_position, font_size, save_as_final).unwrap();
            max_child_width = self.layout_table.get(&layout_box).unwrap().rect.width;
            children.push(layout_box);
        }

        let content_height = (content_position.y - original_cursor.y).max(max_child_height as i32).max(0) as u32;
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

        // By default block elements fill their available width, but if it's a child of a flex, it only uses what it needs
        let wants_to_fill = style.display != StyleDisplay::InlineBlock && style.display != StyleDisplay::Inline;
        let width = if allow_fill && wants_to_fill { container_sizes.container_width } else { container_sizes.compute_actual_container_width(max_child_width) };

        // Margin: auto
        let free_space_y = (container_sizes.inner_height as i32 - content_height as i32).max(0) as u32;
        self.divide_free_space_for_margin(&children_rows, width as i32 - padding_left_size - padding_right_size, free_space_y);

        if containing_node_idx == node_idx {
            let mut containing_node = self.containing_nodes.get_mut(&containing_node_idx).unwrap().clone();
            containing_node.layout_waiters(self, height, width, &mut children).ok()?;
            self.containing_nodes.insert(containing_node_idx, containing_node);
        }

        Some((width, height, children))
    }

    fn calculate_cross_offset(&self, item: &FlexItem, parent_style: &Style, has_definite_height: bool, allow_fill: bool, container_sizes: &ContainerSizes) -> u32 {
        let align = match self.node_styles.get(&item.node_idx).unwrap().align_self {
            StyleJustifyContent::Auto => parent_style.align_items,
            v => v,
        };
        let used_cross = item.cross_size.round() as u32;
        let cross_free_space = match parent_style.flex_direction {
            StyleFlexDirection::Column if allow_fill => container_sizes.inner_width.saturating_sub(used_cross),
            StyleFlexDirection::Column => 0,
            StyleFlexDirection::Row if has_definite_height => { container_sizes.inner_height.saturating_sub(used_cross) }
            StyleFlexDirection::Row => 0,
        };
        let cross_offset = match align {
            StyleJustifyContent::Auto | StyleJustifyContent::FlexStart => 0,
            StyleJustifyContent::FlexEnd => cross_free_space,
            StyleJustifyContent::Center => cross_free_space / 2,
            StyleJustifyContent::SpaceBetween => 0,
            StyleJustifyContent::Stretch => 0,
            StyleJustifyContent::SpaceEvenly => 0,
        };
        cross_offset
    }

    fn layout_flex(
        &mut self,
        node_idx: usize,
        cursor: Position,
        style: &Style,
        available_size: Size,
        forced_size: OptionalSize,
        mut containing_node_idx: usize,
        allow_fill: bool,
        save_as_final: bool,
    ) -> Option<(u32, u32, Vec<usize>)> {
        let (padding_left_size, padding_right_size, padding_top_size, padding_bottom_size) =
            self.get_paddings(node_idx, style, available_size);

        let mut content_position = Position {
            x: cursor.x + padding_left_size as i32,
            y: cursor.y + padding_top_size as i32,
        };
        let original_content_cursor = content_position.clone();
        let mut base_items = Vec::new();
        let mut children = Vec::new();

        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();

        let container_sizes = self.get_container_sizes(node_idx, &forced_size, style, &available_size);
        let (containing_block_height, containing_block_width) = self.get_containing_block_size(containing_node_idx, node_idx, style);

        let specified_height = get_specified_size(
            font_size,
            &style.height,
            containing_block_height,
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32));
        let specified_width = get_specified_size(
            font_size,
            &style.width,
            containing_block_width,
            None,
            &self.window_size,
        )
        .and_then(|v| Some(v as u32));
        let has_definite_height = forced_size.height.is_some() || specified_height.is_some();
        self.resolved_specified_heights.insert(node_idx, specified_height);
        self.resolved_specified_widths.insert(node_idx, specified_width);

        if style.position == StylePosition::Relative {
            self.containing_nodes.insert(node_idx, ContainingNode {
                node_idx,
                waiters: vec![],
            });
            containing_node_idx = node_idx;
        }

        for child_idx in self.dom_indexes.children_index.get(&node_idx).unwrap().clone() {
            if let Some(child) = self.layout_node(
                child_idx,
                Position { x: 0, y: 0 },
                Size {
                    width: container_sizes.inner_width,
                    height: container_sizes.inner_height,
                },
                OptionalSize {
                    height: None,
                    width: None,
                },
                containing_node_idx,
                false,
                false,
            ) {
                let child_style: &Style = &self.node_styles.get(&child_idx).unwrap();
                let child_box = self.layout_table.get(&child).unwrap();
                let size = match style.flex_direction {
                    StyleFlexDirection::Row => child_box.rect.width,
                    StyleFlexDirection::Column => child_box.rect.height,
                };
                let cross_size = match style.flex_direction {
                    StyleFlexDirection::Row => child_box.rect.height,
                    StyleFlexDirection::Column => child_box.rect.width,
                };
                base_items.push(FlexItem {
                    node_idx: child_idx,
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
            StyleFlexDirection::Column => container_sizes.inner_height,
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
        if style.align_items == StyleJustifyContent::Stretch {
            for item in &mut base_items {
                let child_style: &Style = &self.node_styles.get(&item.node_idx).unwrap();
                if child_style.width == StyleSize::Auto {
                    item.cross_size = cross_available_size as f32;
                }
            }
        }

        // Justify-content
        let authored_gap = get_specified_size(font_size, &style.gap, Some(flex_available_size), None, &self.window_size).unwrap_or(0);
        let gap_total = authored_gap.saturating_mul(base_items.len().saturating_sub(1) as i32);

        let used_main: u32 = base_items
            .iter()
            .map(|i| i.target_size.round() as u32)
            .sum::<u32>()
            + gap_total as u32;
        let main_free_space = match style.flex_direction {
            StyleFlexDirection::Row if allow_fill => container_sizes.inner_width.saturating_sub(used_main),
            StyleFlexDirection::Row => 0,
            StyleFlexDirection::Column if has_definite_height => { container_sizes.inner_height.saturating_sub(used_main) }
            StyleFlexDirection::Column => 0,
        };

        let (main_start_offset, main_distributed_gap) = match style.justify_content {
            StyleJustifyContent::Auto | StyleJustifyContent::FlexStart | StyleJustifyContent::Stretch => (0, 0),
            StyleJustifyContent::FlexEnd => (main_free_space, 0),
            StyleJustifyContent::Center => (main_free_space / 2, 0),
            StyleJustifyContent::SpaceBetween if base_items.len() > 1 => {
                (0, main_free_space / (base_items.len() as u32 - 1))
            }
            StyleJustifyContent::SpaceBetween => (0, 0),
            StyleJustifyContent::SpaceEvenly if !base_items.is_empty() => {
                let slot = main_free_space / (base_items.len() as u32 + 1);
                (slot, slot)
            }
            StyleJustifyContent::SpaceEvenly => (0, 0),
        };

        let main_gap = main_distributed_gap + authored_gap as u32;

        let (width, mut height) = match style.flex_direction {
            StyleFlexDirection::Row => {
                let mut max_child_height = 0u32;
                content_position.x = original_content_cursor.x + main_start_offset as i32;

                let mut children_rows = MarginRows::new();

                for (item_idx, item) in base_items.iter().enumerate() {
                    let cross_offset = self.calculate_cross_offset(&item, &style, has_definite_height, allow_fill, &container_sizes);
                    let child_style = self.node_styles.get(&item.node_idx).unwrap().clone();
                    let (margin_left_size, margin_right_size, margin_top_size, _) =
                        self.get_margins(item.node_idx, &child_style, available_size);
                    // Re-compute cursor for each child so that align-self works
                    content_position.y = original_content_cursor.y + cross_offset as i32 + margin_top_size;
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
                            height: None,
                            width: Some(item.target_size as u32),
                        },
                        containing_node_idx,
                        allow_fill,
                        save_as_final,
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
                let width = if allow_fill && wants_to_fill { container_sizes.container_width } else { container_sizes.compute_actual_container_width((content_position.x - original_content_cursor.x) as u32) };

                // Margin: auto
                let free_space_y = (container_sizes.inner_height as i32 - max_child_height as i32).max(0) as u32;
                self.divide_free_space_for_margin(&children_rows, width as i32 - padding_left_size - padding_right_size, free_space_y);

                (width, height)
            }
            StyleFlexDirection::Column => {
                content_position.y = original_content_cursor.y + main_start_offset as i32;

                let mut max_affecting_child_width = 0;
                let mut children_rows = MarginRows::new();

                for (item_idx, item) in base_items.iter().enumerate() {
                    let cross_offset = self.calculate_cross_offset(&item, &style, has_definite_height, allow_fill, &container_sizes);
                    let child_style = self.node_styles.get(&item.node_idx).unwrap().clone();
                    let (margin_left_size, _, margin_top_size, margin_bottom_size) =
                        self.get_margins(item.node_idx, &child_style, available_size);
                    content_position.x = original_content_cursor.x + cross_offset as i32 + margin_left_size;
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
                    ) {
                        let child_box = self.layout_table.get(&child).unwrap();
                        if !child_style.position.is_free() {
                            max_affecting_child_width = max_affecting_child_width.max(child_box.rect.width);
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
                let width = if allow_fill && wants_to_fill { container_sizes.container_width } else { container_sizes.compute_actual_container_width(max_affecting_child_width) };

                // Margin: auto
                let free_space_y = (container_sizes.inner_height as i32 - content_height as i32).max(0) as u32;
                self.divide_free_space_for_margin(&children_rows, width as i32 - padding_left_size - padding_right_size, free_space_y);

                (width, height)
            }
        };

        height = height.min(container_sizes.max_height.unwrap_or(u32::MAX)).max(container_sizes.min_height.unwrap_or(u32::MIN));

        Some((width, height, children))
    }

    fn blend_premul_over_rgb(&self, dst: u32, src: tiny_skia::PremultipliedColorU8) -> u32 {
        blend_rgb_with_rgba(dst, (src.red(), src.green(), src.blue(), src.alpha()))
    }

    fn compute_hovering(&mut self, position: Position) {
        let hovering = self.rendered_nodes_ordered
            .iter()
            .rev()
            .find(|idx| {
                let layout_box = self.layout_table.get(*idx).unwrap();
                let end_x = layout_box.rect.x + layout_box.rect.width as i32;
                let end_y = layout_box.rect.y + layout_box.rect.height as i32;

                position.x > layout_box.rect.x &&
                    position.x < end_x &&
                    position.y > layout_box.rect.y + self.scroll_y &&
                    position.y < end_y + self.scroll_y
            });
        self.hovering = hovering.copied();
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
        pixmap_buffer: &tiny_skia::Pixmap
    ) {
        let pixels = pixmap_buffer.pixels();
        let pixmap_width = layout_box.rect.width.min(pixmap_buffer.width());
        let pixmap_height = layout_box.rect.height.min(pixmap_buffer.height());
        let end_x = pixmap_width.min((width as i32 - layout_box.rect.x).max(0) as u32);
        let end_y = pixmap_height.min(height);
        for pixel_x in 0..end_x {
            for pixel_y in 0..end_y {
                let pixel = pixels[(pixel_x + pixel_y * pixmap_width) as usize];
                let dist = container_start_y * width as i32
                    + layout_box.rect.x
                    + pixel_x as i32
                    + pixel_y as i32 * width as i32;
                if dist > 0 && dist < buffer.len() as i32 {
                    buffer[dist as usize] = self.blend_premul_over_rgb(buffer[dist as usize], pixel);
                }
            }
        }
    }

    fn paint_layout_box(
        &self,
        layout_box_idx: usize,
        buffer: &mut [u32],
        width: u32,
        height: u32,
        offset_y: i32,
        rendered_nodes_ordered: &mut Vec<usize>,
    ) {
        rendered_nodes_ordered.push(layout_box_idx);
        let layout_box = self.layout_table.get(&layout_box_idx).unwrap();
        let container_start_y = layout_box.rect.y + offset_y;
        let container_end_y = container_start_y + layout_box.rect.height as i32;
        // If outside viewport, don't render
        // This is a bit naive but should be okay for now
        if container_start_y > height as i32 || container_end_y < 0 {
            return;
        }
        match &layout_box.kind {
            LayoutKind::Element => {
                let left_border_size = layout_box.rect.border.left.as_ref().and_then(|v| Some(v.size)).unwrap_or(0) as i32;
                let top_border_size = layout_box.rect.border.top.as_ref().and_then(|v| Some(v.size)).unwrap_or(0) as i32;
                let right_border_size = layout_box.rect.border.right.as_ref().and_then(|v| Some(v.size)).unwrap_or(0) as i32;
                let bottom_border_size = layout_box.rect.border.bottom.as_ref().and_then(|v| Some(v.size)).unwrap_or(0) as i32;
                match &layout_box.rect.background {
                    StyleBackground::Hex(code) => {
                        draw_rect_filled(
                            buffer,
                            width,
                            height,
                            layout_box.rect.x + left_border_size,
                            container_start_y + top_border_size,
                            (layout_box.rect.width as i32 - left_border_size - right_border_size).max(0) as u32,
                            (layout_box.rect.height as i32 - top_border_size - bottom_border_size).max(0) as u32,
                            code.clone(),
                        );
                    },
                    StyleBackground::DataUrl(_) => {
                        if let Some(pixmap) = self.resolved_pixmaps.get(&layout_box.node_idx.to_string()) {
                            self.apply_pixmap_on_buffer(layout_box, buffer, width, height, container_start_y, pixmap);
                        }
                    },
                    _ => {},
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
                        width,
                        height,
                        layout_box.rect.x,
                        container_start_y,
                        layout_box.rect.width,
                        layout_box.rect.height,
                        bg,
                    );
                }
                let text_hex: Option<u32> = match layout_box.rect.color {
                    StyleBackground::Hex(code) => Some(code),
                    _ => None,
                };
                if let Some(color) = text_hex {
                    draw_text(
                        &self.font_handler,
                        buffer,
                        width,
                        height,
                        layout_box.rect.x as i32,
                        container_start_y as i32,
                        text,
                        color,
                        layout_box.rect.font_size.unwrap(),
                    );
                }
            }
            LayoutKind::PixMap(pixmap_buffer) => {
                self.apply_pixmap_on_buffer(layout_box, buffer, width, height, container_start_y, pixmap_buffer);
            }
        }

        for &child in &layout_box.children {
            self.paint_layout_box(child, buffer, width, height, offset_y, rendered_nodes_ordered);
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

    pub fn get_parent_link(&self, idx: usize) -> Option<usize> {
        let is_link = match &self.nodes.get(&idx)? {
            Node::Element(element) => element.tag == "a",
            Node::Text(_) | Node::Comment(_) => false,
        };

        if is_link {
            Some(idx)
        } else {
            let parent = self.nodes.get(&idx).unwrap().get_parent();
            if let Some(parent) = parent {
                self.get_parent_link(parent)
            } else {
                None
            }
        }
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
        for child in self.dom_indexes.children_index.get(&node_idx).unwrap().clone() {
            self.remove_node(child, false);
        }

        // Remove from parent
        if remove_from_parent {
            if let Some(parent) = self.nodes.get(&node_idx).unwrap().get_parent() {
                let children = self.dom_indexes.children_index.get(&parent).unwrap();
                let filtered: Vec<usize> = children.into_iter().filter(|idx| **idx != node_idx).cloned().collect();
                self.dom_indexes.children_index.insert(parent, filtered);
            }
        }

        // Remove node itself
        self.nodes_idxs = self.nodes_idxs.iter().filter(|idx| **idx != node_idx).cloned().collect();
        self.nodes.remove(&node_idx);
        self.node_layout_mapping.remove(&node_idx);
        self.dom_indexes.children_index.remove(&node_idx);
    }

    pub fn recompute_dom_indexes(&mut self) {
        self.dom_indexes = get_dom_indexes(&self.nodes);
    }

    pub fn recompute_nodes(&mut self) {
        self.recompute_dom_indexes();
        (self.node_styles, self.resolved_font_sizes) = compute_node_styles(&self.url, &self.tokio, &self.network_fetch, &self.nodes, &self.nodes_idxs, &self.window_size, &self.dom_indexes);
    }

    pub fn get_paddings(&self, node_idx: usize, style: &Style, available_size: Size) -> (i32, i32, i32, i32) {
        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();
        let padding_left_size =
            get_specified_size(font_size, &style.padding_left, Some(available_size.width), None, &self.window_size).unwrap_or(0);
        let padding_right_size =
            get_specified_size(font_size, &style.padding_right, Some(available_size.width), None, &self.window_size).unwrap_or(0);
        let padding_top_size =
            get_specified_size(font_size, &style.padding_top, Some(available_size.height), None, &self.window_size).unwrap_or(0);
        let padding_bottom_size =
            get_specified_size(font_size, &style.padding_bottom, Some(available_size.height), None, &self.window_size).unwrap_or(0);

        (
            padding_left_size,
            padding_right_size,
            padding_top_size,
            padding_bottom_size,
        )
    }

    pub fn get_border_sizes(&self, node_idx: usize, style: &Style, available_size: Size) -> (i32, i32, i32, i32) {
        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();
        let left_size =
            get_specified_size(font_size, &style.border_left.size, Some(available_size.width), None, &self.window_size).unwrap_or(0);
        let right_size =
            get_specified_size(font_size, &style.border_right.size, Some(available_size.width), None, &self.window_size).unwrap_or(0);
        let top_size =
            get_specified_size(font_size, &style.border_top.size, Some(available_size.height), None, &self.window_size).unwrap_or(0);
        let bottom_size =
            get_specified_size(font_size, &style.border_bottom.size, Some(available_size.height), None, &self.window_size).unwrap_or(0);

        (
            left_size,
            right_size,
            top_size,
            bottom_size,
        )
    }

    pub fn get_margins(&self, node_idx: usize, style: &Style, available_size: Size) -> (i32, i32, i32, i32) {
        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();
        let margin_left_size =
            get_specified_size(font_size, &style.margin_left, Some(available_size.width), None, &self.window_size).unwrap_or(0);
        let margin_right_size =
            get_specified_size(font_size, &style.margin_right, Some(available_size.width), None, &self.window_size).unwrap_or(0);
        let margin_top_size =
            get_specified_size(font_size, &style.margin_top, Some(available_size.height), None, &self.window_size).unwrap_or(0);
        let margin_bottom_size =
            get_specified_size(font_size, &style.margin_bottom, Some(available_size.height), None, &self.window_size).unwrap_or(0);

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

    pub fn schedule_dom_update(&mut self, proxy: &EventLoopProxy<UserEvent>) {
        if !self.pending_dom_update {
            proxy.send_event(UserEvent::DomUpdated).unwrap();
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
        Ok(Self {
            font,
        })
    }

    pub fn get_renderable_text(&self, text: String, font_px: i32, max_width: Option<u32>) -> Result<RenderableText> {
        let scaled_font = self.font.as_scaled(font_px as f32);
        let mut glyphs = vec![];
        let mut width = 0f32;
        let mut width_buffer = 0f32;
        let mut lines = 1;
        for char in text.chars() {
            let glyph = self.outline_glyph_for(char, font_px as f32);
            glyphs.push(glyph);
            let advance = scaled_font.h_advance(self.font.glyph_id(char));
            if max_width.is_some_and(|max_width| width + advance >= max_width as f32) && char == ' ' {
                width_buffer = 0f32;
                lines += 1;
            } else {
                width_buffer += advance;
                width = width.max(width_buffer)
            }
        }
        let line_height = scaled_font.height() + scaled_font.line_gap();
        let height = (line_height * lines as f32) as u32;
        Ok(RenderableText {
            text,
            glyphs,
            width: width as u32,
            height,
            line_height,
        })
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
}

impl Browser {
    fn new(url: String) -> Self {
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
        }
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

    pub fn dump_tree(&mut self) -> Result<()> {
        self.register_tokio_runtime()?;
        self.navigate(self.url.clone())?;
        self.install_js_host();
        let event_loop = EventLoopBuilder::with_user_event().build().expect("Failed to create event loop");
        let nodes_table = self.html_parser.as_ref().unwrap().nodes.clone().into_iter().enumerate().collect();
        let dom_indexes = get_dom_indexes(&nodes_table);
        self.renderer = Some(Rc::new(RefCell::new(Renderer::new(
            self.url.clone(),
            self.tokio.as_ref().unwrap().clone(),
            nodes_table,
            PhysicalSize { width: WINDOW_WIDTH, height: WINDOW_HEIGHT },
            Rc::clone(&self.font_handler),
            Rc::clone(&self.network_fetch),
            dom_indexes,
        ))));
        self.js_runtime.as_mut().unwrap().borrow_mut().op_state().borrow_mut().put(JsHostState {
            renderer: self.renderer.as_mut().cloned().unwrap(),
            proxy: event_loop.create_proxy(),
        });
        self.setup_js_dom()?;

        let js_result = self.run_js();
        println!("Finished running JS code: {:?}", js_result);

        self.pump_js_event_loop_once()?;

        self.renderer.as_ref().unwrap().borrow_mut().recompute_nodes();

        print!("{}", format_tree(&mut self.renderer.as_mut().unwrap().borrow_mut(), WINDOW_WIDTH, WINDOW_HEIGHT));
        Ok(())
    }

    pub fn install_js_host(&mut self) {
        let blob_store = Arc::new(BlobStore::default());
        let broadcast_channel = InMemoryBroadcastChannel::default();
        self.js_runtime = Some(
            Rc::new(RefCell::new(deno_core::JsRuntime::new(deno_core::RuntimeOptions {
                module_loader: Some(Rc::new(HttpModuleLoader::new())),
                extensions: vec![
                    browser::init(),
                    deno_webidl::deno_webidl::init(),
                    deno_web::deno_web::init(
                        blob_store,
                        None,
                        broadcast_channel,
                    ),
                    deno_net::deno_net::init(None, None),
                    deno_fetch_without_telemetry(),
                    deno_node_crypto_shim::init(),
                    deno_crypto::deno_crypto::init(None),
                ],
                ..Default::default()
            })))
        );
    }

    fn drain_microtasks(runtime: &mut JsRuntime) {
        deno_core::scope!(scope, runtime);
        scope.perform_microtask_checkpoint();
    }

    fn pump_js_event_loop_once(&mut self) -> Result<bool> {
        let mut runtime = self.js_runtime.as_mut().unwrap().borrow_mut();

        self.tokio.as_ref().unwrap().clone().borrow_mut().block_on(async {
            poll_fn(|cx| {
                match runtime.poll_event_loop(cx, Default::default()) {
                    Poll::Ready(Ok(())) => Poll::Ready(Ok(false)),
                    Poll::Ready(Err(err)) => Poll::Ready(Err(err.into())),
                    Poll::Pending => Poll::Ready(Ok(true)),
                }
            }).await
        })
    }

    async fn execute_js(&mut self, scripts: Vec<Script>) -> Result<()> {
        let mut runtime = self.js_runtime.as_mut().unwrap().borrow_mut();
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
                    runtime.execute_script(format!("injected code {} ({})", idx, code_context), code.clone())?;
                    Self::drain_microtasks(&mut runtime);
                }
                ScriptContent::Link(link) => {
                    let base = ReqwestUrl::parse(&self.url)?;
                    let url = resolve_url(&link, Some(&base))?;
                    match js.script_type {
                        ScriptType::Classic => {
                            let code = self.network_fetch.borrow_mut().client.get(url.clone()).send().await?.text().await?;
                            runtime.execute_script(url.to_string(), code)?;
                            Self::drain_microtasks(&mut runtime);
                        }
                        ScriptType::Module => {
                            let module_id = runtime.load_side_es_module(&url).await?;
                            let result = runtime.mod_evaluate(module_id);
                            runtime.with_event_loop_promise(result, Default::default()).await?;
                        }
                    }
                }
            };

            // Run onload handlers
            if let Some(node_idx) = js.node_idx {
                let code = format!(r#"
                    if (__EVENT_LISTENERS[`${{{}}}:load`]) {{
                        __EVENT_LISTENERS[`${{{}}}:load`]?.forEach(cb => {{
                            cb()
                        }})
                    }}
                "#, node_idx, node_idx);
                runtime.execute_script("script onload", code.clone())?;
                Self::drain_microtasks(&mut runtime);
            }
        }

        Ok(())
    }

    pub fn run_js(&mut self) -> Result<()> {
        let scripts = self.renderer.as_ref().unwrap().borrow_mut().get_scripts();

        println!("Running {} JS scripts", scripts.len());

        self.tokio.as_ref().unwrap().clone().borrow_mut().block_on(self.execute_js(scripts))?;

        Ok(())
    }

    fn detect_html_redirect_walk_inner(&mut self, node_idx: usize) -> Option<Result<()>> {
        let nodes = &self.html_parser.as_ref().unwrap().nodes;
        let node = &nodes[node_idx];

        let Node::Element(element) = node else {
            return None;
        };
        if element.tag == "meta" && element.attributes.get("http-equiv").is_some_and(|v| v.to_lowercase() == "refresh") {
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

    fn detect_html_redirect_walk(&mut self, node_idx: usize, dom_indexes: &DomIndexes) -> Option<Result<()>> {
        let html_tag = match self.html_parser.as_ref().unwrap().nodes.get(node_idx).unwrap() {
            Node::Element(element) => Some(element.tag.clone()),
            _ => None,
        };
        if let Some(result) = self.detect_html_redirect_walk_inner(node_idx) {
            return Some(result);
        } else if html_tag.is_none_or(|v| v != "noscript") {
            let children = dom_indexes
                .children_index
                .get(&node_idx)
                .unwrap()
                .clone();
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
        let (input, final_url) = self.tokio.as_ref().unwrap().borrow_mut().block_on(self.get_html(href))?;
        println!("Changing url to {}", final_url);
        self.url = final_url;

        self.html_parser = Some(HtmlParser::new(input));
        self.html_parser.as_mut().unwrap().parse().expect(&format!(
            "Failed to parse. Context: {}",
            self.html_parser.as_mut().unwrap().get_context()
        ));

        if self.renderer.is_some() {
            self.setup_js_dom()?;
            let js_result = self.run_js();
            println!("Finished running JS code: {:?}", js_result);
        }
        if let Some(window) = self.window.as_mut() {
            self.layout_dirty = true;
            window.request_redraw();
        }
        Ok(())
    }

    pub fn register_tokio_runtime(&mut self) -> Result<()> {
        self.tokio = Some(
            Rc::new(RefCell::new(tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()?))
        );
        Ok(())
    }

    pub fn open(&mut self) -> Result<()> {
        self.register_tokio_runtime()?;
        self.navigate(self.url.clone())?;
        self.install_js_host();
        let nodes_table = self.html_parser.as_mut().unwrap().nodes.clone().into_iter().enumerate().collect();
        let dom_indexes = get_dom_indexes(&nodes_table);
        self.detect_html_redirect(&dom_indexes);
        self.start_event_loop(nodes_table, dom_indexes)
    }

    fn on_click(&mut self) -> Result<()> {
        let (href, link_node_idx, code): (Option<String>, Option<usize>, Option<String>) = {
            let renderer_ref = self.renderer.as_ref().unwrap().clone();
            let renderer = renderer_ref.borrow();
            let hovering = renderer.hovering;
            if let Some(hovering) = hovering {
                // Run event listeners
                let hovering_node_idx = renderer.layout_to_node_idx(&hovering);
                println!("Clicked on {}", hovering_node_idx);
                let parents: Vec<String> = renderer.get_parents(hovering_node_idx).into_iter().map(|idx| idx.to_string()).collect();
                let code = format!(r#"
                    (() => {{
                        const event = new MouseEvent("click")
                        // TODO: Use real tag name here
                        event.target = new HTMLElement("div")
                        for (const idx of [{}]) {{
                            event.target.__node_idx = idx
                            if (__EVENT_LISTENERS[`${{idx}}:click`]) {{
                                __EVENT_LISTENERS[`${{idx}}:click`]?.forEach(cb => {{
                                    cb(event)
                                }})
                            }}
                        }}
                        return event.defaultPrevented
                    }})()
                "#, parents.join(", "));

                let parent_link = renderer.get_parent_link(hovering_node_idx);
                if let Some(parent) = parent_link {
                    match &renderer.nodes.get(&parent).unwrap() {
                        Node::Element(element) => (element.attributes.get("href").cloned(), Some(parent), Some(code)),
                        _ => (None, Some(parent), Some(code)),
                    }
                } else {
                    (None, None, Some(code))
                }
            } else {
                (None, None, None)
            }
        };

        let default_prevented = if let Some(code) = code {
            let mut runtime = self.js_runtime.as_mut().unwrap().borrow_mut();
            let value = runtime.execute_script("click handler", code.clone())?;
            let future = runtime.run_event_loop(Default::default());
            self.tokio.as_ref().unwrap().clone().borrow_mut().block_on(future)?;

            deno_core::scope!(scope, &mut *runtime);
            let value = deno_core::v8::Local::new(scope, value);
            value.boolean_value(scope)
        } else {
            false
        };

        println!("default prevented {}", default_prevented);

        if let (Some(href), Some(_link_node_idx)) = (href, link_node_idx) {
            if !default_prevented {
                let current_url = url::Url::parse(&self.url)?;
                let resolved_url = current_url.join(&href)?;
                self.navigate(resolved_url.to_string()).unwrap();
            }
        }

        Ok(())
    }

    fn setup_js_dom(&mut self) -> Result<()> {
        let code = ScriptContent::Code(format!(r#"
            document.documentElement = document.querySelector("html");
            document.body = document.querySelector("body");
            document.head = document.querySelector("head");

            navigator.userAgent = "{}";

            window.__init_location("{}");
        "#, USER_AGENT, self.url).to_string());
        self.tokio.as_ref().unwrap().clone().borrow_mut().block_on(self.execute_js(vec![
            Script { content: code, script_type: ScriptType::Classic, node_idx: None }
        ]))?;
        Ok(())
    }

    fn refresh_renderer(&mut self, nodes_table: HashMap<usize, Node>, dom_indexes: DomIndexes) {
        let size = self.window.as_ref().unwrap().inner_size();
        self.renderer = Some(Rc::new(RefCell::new(Renderer::new(
            self.url.clone(),
            self.tokio.as_ref().unwrap().clone(),
            nodes_table,
            size,
            Rc::clone(&self.font_handler),
            Rc::clone(&self.network_fetch),
            dom_indexes,
        ))));
    }

    fn render(&mut self, surf: &mut Surface<DisplayHandle, WindowHandle>, size: &PhysicalSize<u32>, cursor: &Position) -> bool {
        let start = Instant::now();

        let width = NonZeroU32::new(size.width.max(1)).expect("Non-zero width");
        let height = NonZeroU32::new(size.height.max(1)).expect("Non-zero height");
        surf.resize(width, height).expect("Resize failed");

        let mut buffer = surf.buffer_mut().expect("Failed to get back buffer");
        let mut renderer = self.renderer.as_mut().unwrap().borrow_mut();
        renderer.render_into(&mut buffer, size.width, size.height, self.layout_dirty);
        self.layout_dirty = false;
        renderer.compute_hovering(*cursor);
        buffer.present().expect("Failed to present");

        println!("Render took {} microseconds", Instant::now().duration_since(start).as_micros());

        if !self.layout_booted {
            self.layout_booted = true;
            true
        } else {
            false
        }
    }

    fn execute_dom_update(&mut self) {
        println!("DOM UPDATED");
        let window = self.window.as_ref().unwrap();
        self.renderer.as_ref().unwrap().borrow_mut().pending_dom_update = false;
        self.renderer.as_ref().unwrap().borrow_mut().recompute_nodes();
        self.layout_dirty = true;
        window.request_redraw();
        let js_result = self.run_js();
        println!("Finished running JS code: {:?}", js_result);

        // If the JS caused another update, execute it immediately
        if self.renderer.as_ref().unwrap().borrow_mut().pending_dom_update {
            self.execute_dom_update();
        }
    }

    fn start_event_loop(&mut self, nodes_table: HashMap<usize, Node>, dom_indexes: DomIndexes) -> Result<()> {
        let event_loop = EventLoopBuilder::with_user_event().build().expect("Failed to create event loop");
        let window = Arc::new(WindowBuilder::new()
            .with_title("XML demo")
            .with_inner_size(PhysicalSize::new(WINDOW_WIDTH, WINDOW_HEIGHT))
            .build(&event_loop)
            .expect("Failed to create window"));
        self.window = Some(Arc::clone(&window));
        let mut size = window.inner_size();

        let ctx = SoftContext::new(window.display_handle().expect("Display handle"))
                .expect("Softbuffer context failed");
        let mut surf = Surface::new(&ctx, window.window_handle().expect("Window handle"))
                .expect("Softbuffer surface failed");

        self.refresh_renderer(nodes_table, dom_indexes);

        self.js_runtime.as_mut().unwrap().borrow_mut().op_state().borrow_mut().put(JsHostState {
            renderer: self.renderer.as_mut().cloned().unwrap(),
            proxy: event_loop.create_proxy(),
        });

        self.setup_js_dom()?;

        let mut cursor = Position { x: 0, y: 0 };

        event_loop
            .run(move |event, elwt| {
                let window = self.window.as_ref().unwrap();
                match event {
                    Event::UserEvent(UserEvent::DomUpdated) => {
                        self.execute_dom_update()
                    },
                    Event::UserEvent(UserEvent::Navigate((href, reload))) => {
                        let current_url = url::Url::parse(&self.url).unwrap();
                        let resolved_url = current_url.join(&href).unwrap();
                        if reload {
                            if let Err(err) = self.navigate(resolved_url.to_string()) {
                                eprintln!("Navigation failed: {err:?}");
                            }
                        } else {
                            self.url = resolved_url.to_string();
                            self.renderer.as_mut().unwrap().borrow_mut().url = resolved_url.to_string();
                            self.setup_js_dom().unwrap();
                        }
                    },
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
                            let first_boot = self.render(&mut surf, &size, &cursor);
                            if first_boot {
                                let js_result = self.run_js();
                                println!("Finished running JS code: {:?}", js_result);
                            }
                        }
                        WindowEvent::CursorMoved { device_id: _, position } => {
                            cursor = Position {
                                x: position.x as i32,
                                y: position.y as i32,
                            };
                            self.renderer.as_mut().unwrap().borrow_mut().compute_hovering(cursor);
                        }
                        WindowEvent::MouseInput { device_id: _, state, button } => {
                            match (button, state) {
                                (MouseButton::Left, ElementState::Released) => self.on_click().unwrap(),
                                _ => {},
                            }
                        }
                        WindowEvent::MouseWheel { device_id: _, delta, phase: _ } => {
                            match delta {
                                MouseScrollDelta::LineDelta(_, y) => {
                                    self.scroll_y_by(y * 80.);
                                }
                                _ => {}
                            };
                        }
                        _ => {}
                    }
                    Event::AboutToWait => {
                        match self.pump_js_event_loop_once() {
                            Ok(js_pending) => {
                                let dom_pending = self.renderer
                                    .as_ref()
                                    .unwrap()
                                    .borrow()
                                    .pending_dom_update;

                                if dom_pending {
                                    self.execute_dom_update();
                                }

                                if js_pending {
                                    elwt.set_control_flow(
                                        ControlFlow::WaitUntil(Instant::now() + Duration::from_millis(16))
                                    );
                                } else {
                                    elwt.set_control_flow(ControlFlow::Wait);
                                }
                            }
                            Err(err) => {
                                eprintln!("JS event loop error: {err:?}");
                                elwt.set_control_flow(ControlFlow::Wait);
                            }
                        }
                    }
                    _ => {}
                }
            })
            .context("Event loop failed")?;

        Ok(())
    }

    pub fn scroll_y_by(&mut self, y: f32) {
        let mut renderer = self.renderer.as_mut().unwrap().borrow_mut();
        let root_height = renderer.layout_table
            .get(&renderer.layout_roots[0])
            .and_then(|l| Some(l.rect.height))
            .unwrap_or(0);
        let size = self.window.as_ref().unwrap().inner_size();
        renderer.scroll_y = ((renderer.scroll_y as f32 + y)).min(0.).max(-(root_height as f32 - size.height as f32)) as i32;
        if let Some(window) = self.window.as_mut() {
            window.request_redraw();
        }
    }
}

fn main() -> Result<()> {
    let _ = rustls::crypto::aws_lc_rs::default_provider().install_default();

    let dump_tree = env::args().any(|arg| arg == "--dump-tree");
    let mut browser = Browser::new("https://vite.dev".to_string());
    // let mut browser = Browser::new("http://localhost:5173".to_string());
    // let mut browser = Browser::new("file:///home/pontus/browser/pages/test.html".to_string());

    if dump_tree {
        browser.dump_tree()
    } else {
        browser.open()
    }
}

fn clear_buffer(buffer: &mut [u32], color: u32) {
    buffer.fill(color);
}

fn build_children_index(nodes: &HashMap<usize, Node>, node_idxs: &Vec<usize>) -> HashMap<usize, Vec<usize>> {
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

fn format_tree(renderer: &mut Renderer, width: u32, height: u32) -> String {
    let layout_roots = renderer.build_layout(width, height);
    let mut layout_info = HashMap::new();
    collect_layout_info(&layout_roots, &mut layout_info, &renderer.layout_table);
    let mut out = String::new();

    write_tree(
        &renderer.nodes,
        &renderer.dom_indexes.children_index,
        &renderer.node_styles,
        &renderer.node_layout_mapping,
        &layout_info,
        renderer.dom_indexes.root_indice,
        0,
        &mut out,
    );

    out
}

fn collect_layout_info(layout_boxes: &[usize], layout_info: &mut HashMap<usize, LayoutDumpInfo>, layout_table: &HashMap<usize, LayoutBox>) {
    for layout_box_idx in layout_boxes {
        if let Some(layout_box) = layout_table.get(&layout_box_idx) {
            layout_info.insert(*layout_box_idx, LayoutDumpInfo {
                kind: layout_kind_label(&layout_box.kind),
                rect: layout_box.rect.clone(),
            });
            collect_layout_info(&layout_box.children, layout_info, layout_table);
        }
    }
}

fn layout_kind_label(kind: &LayoutKind) -> &'static str {
    match kind {
        LayoutKind::Element => "element",
        LayoutKind::PixMap(_) => "pixmap",
        LayoutKind::Text(_) => "text",
    }
}

fn write_tree(
    nodes: &HashMap<usize, Node>,
    children_index: &HashMap<usize, Vec<usize>>,
    node_styles: &HashMap<usize, Style>,
    layout_node_mapping: &HashMap<usize, usize>,
    layout_info: &HashMap<usize, LayoutDumpInfo>,
    node_idx: usize,
    depth: usize,
    out: &mut String,
) {
    let mut label = match &nodes.get(&node_idx).unwrap() {
        Node::Element(element) => format_element_tree_label(element),
        Node::Text(text) => match collapse_whitespace(&text.text) {
            Some(text) => format!("Node::Text \"{text}\""),
            None => return,
        },
        Node::Comment(element) => format!("Node::Comment \"{}\"", element.comment),
    };
    label.push_str(&format!(" [idx={}]", node_idx));
    match layout_node_mapping.get(&node_idx).and_then(|idx| layout_info.get(idx).and_then(|layout| Some((idx, layout)))) {
        Some((layout_idx, info)) => {
            label.push_str(&format!(
                " [layout_idx={} layout={} x={} y={} width={} height={}]",
                layout_idx, info.kind, info.rect.x, info.rect.y, info.rect.width, info.rect.height
            ));
        }
        None => label.push_str(" [layout=none]"),
    }
    label.push_str(&format!(" [style={:?}]", node_styles.get(&node_idx).unwrap()));

    out.push_str(&"  ".repeat(depth));
    out.push_str(&label);
    out.push('\n');

    for &child_idx in children_index.get(&node_idx).unwrap() {
        write_tree(
            nodes,
            children_index,
            node_styles,
            layout_node_mapping,
            layout_info,
            child_idx,
            depth + 1,
            out,
        );
    }
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

fn draw_text(
    font_handler: &Rc<FontHandler>,
    buffer: &mut [u32],
    width: u32,
    height: u32,
    x: i32,
    y: i32,
    renderable_text: &RenderableText,
    color: u32,
    font_px: u32,
) {
    let scaled_font = font_handler.font.as_scaled(font_px as f32);
    let mut pen_x: f32 = x as f32;
    let mut pen_y: f32 = y as f32;
    let mut previous = None;

    for (ch, glyph) in renderable_text.text.chars().zip(renderable_text.glyphs.clone()) {
        let glyph_id = font_handler.font.glyph_id(ch);
        if let Some(previous_id) = previous {
            pen_x += scaled_font.kern(previous_id, glyph_id);
        }
        if let Some(glyph) = glyph {
            draw_glyph(buffer, width, height, pen_x as i32, (pen_y + scaled_font.ascent() + glyph.px_bounds().min.y) as i32, glyph, color);
        }
        let advance = scaled_font.h_advance(glyph_id);
        // Line break
        if pen_x - x as f32 + advance > renderable_text.width as f32 && ch == ' ' {
            pen_x = x as f32;
            pen_y += renderable_text.line_height;
        } else {
            pen_x += advance;
        }
        previous = Some(glyph_id);
    }
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
    glyph: OutlinedGlyph,
    color: u32,
) {
    glyph.draw(|glyph_x, glyph_y, c| {
        draw_rect_filled(buffer, width, height, x + glyph_x as i32, y + glyph_y as i32, 1, 1, with_coverage(color, c));
    });
}

fn rgba_to_premul_tuple(src: u32) -> (u8, u8, u8, u8) {
    let [r, g, b, a] = src.to_be_bytes();
    let r = (r as u32 * a as u32 / 255) as u8;
    let g = (g as u32 * a as u32 / 255) as u8;
    let b = (b as u32 * a as u32 / 255) as u8;
    (r, g, b, a)
}

fn rgb_buffer_to_premul_bytes(buffer: &[u32]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(buffer.len() * 4);

    for pixel in buffer {
        let r = ((pixel >> 16) & 0xFF) as u8;
        let g = ((pixel >> 8) & 0xFF) as u8;
        let b = (pixel & 0xFF) as u8;

        bytes.extend_from_slice(&[r, g, b, 0xFF]);
    }

    bytes
}

fn draw_rect_filled(
    buffer: &mut [u32],
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
            row[px as usize] = blend_rgb_with_rgba(row[px as usize], color_tuple);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::clamp_with_ratio;

    use crate::css::{CssParser, Node as CssNode, Overflow};
    use crate::parser::Element;
    use crate::style::{
        GridTemplateColumns, Style, StyleAlign, StyleBackground, StyleBorderStyle, StyleDisplay, StyleFlexDirection, StyleJustifyContent, StylePosition, StyleSize, StyleSizeAndColor, parse_style
    };
    use crate::{FontHandler, HtmlParser, NetworkFetch, Renderer, get_dom_indexes};
    use anyhow::{Context, Result};
    use winit::dpi::PhysicalSize;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::fs;
    use std::rc::Rc;

    const SAMPLE_PAGE_PATH: &str = "pages/google_real.html";

    #[test]
    fn clamps_with_ratio() {
        assert_eq!(clamp_with_ratio(200, 100, 80), (100, 40));
    }

    #[test]
    fn test_parse_svg() -> Result<()> {
        let svg_input = r#"<svg class="lnXdpd" aria-label="Google" height="92" role="img" viewBox="0 0 272 92" width="272" xmlns="http://www.w3.org/2000/svg"><path d="M115.75 47.18c0 12.77-9.99 22.18-22.25 22.18s-22.25-9.41-22.25-22.18C71.25 34.32 81.24 25 93.5 25s22.25 9.32 22.25 22.18zm-9.74 0c0-7.98-5.79-13.44-12.51-13.44S80.99 39.2 80.99 47.18c0 7.9 5.79 13.44 12.51 13.44s12.51-5.55 12.51-13.44zm57.74 0c0 12.77-9.99 22.18-22.25 22.18s-22.25-9.41-22.25-22.18c0-12.85 9.99-22.18 22.25-22.18s22.25 9.32 22.25 22.18zm-9.74 0c0-7.98-5.79-13.44-12.51-13.44s-12.51 5.46-12.51 13.44c0 7.9 5.79 13.44 12.51 13.44s12.51-5.55 12.51-13.44zm55.74-20.84v39.82c0 16.38-9.66 23.07-21.08 23.07-10.75 0-17.22-7.19-19.66-13.07l8.48-3.53c1.51 3.61 5.21 7.87 11.17 7.87 7.31 0 11.84-4.51 11.84-13v-3.19h-.34c-2.18 2.69-6.38 5.04-11.68 5.04-11.09 0-21.25-9.66-21.25-22.09 0-12.52 10.16-22.26 21.25-22.26 5.29 0 9.49 2.35 11.68 4.96h.34v-3.61h9.25zm-8.56 20.92c0-7.81-5.21-13.52-11.84-13.52-6.72 0-12.35 5.71-12.35 13.52 0 7.73 5.63 13.36 12.35 13.36 6.63 0 11.84-5.63 11.84-13.36zM225 3v65h-9.5V3h9.5zm37.02 51.48l7.56 5.04c-2.44 3.61-8.32 9.83-18.48 9.83-12.6 0-22.01-9.74-22.01-22.18 0-13.19 9.49-22.18 20.92-22.18 11.51 0 17.14 9.16 18.98 14.11l1.01 2.52-29.65 12.28c2.27 4.45 5.8 6.72 10.75 6.72 4.96 0 8.4-2.44 10.92-6.14zm-23.27-7.98l19.82-8.23c-1.09-2.77-4.37-4.7-8.23-4.7-4.95 0-11.84 4.37-11.59 12.93zM35.29 41.41V32H67c.31 1.64.47 3.58.47 5.68 0 7.06-1.93 15.79-8.15 22.01-6.05 6.3-13.78 9.66-24.02 9.66C16.32 69.35.36 53.89.36 34.91.36 15.93 16.32.47 35.3.47c10.5 0 17.98 4.12 23.6 9.49l-6.64 6.64c-4.03-3.78-9.49-6.72-16.97-6.72-13.86 0-24.7 11.17-24.7 25.03 0 13.86 10.84 25.03 24.7 25.03 8.99 0 14.11-3.61 17.39-6.89 2.66-2.66 4.41-6.46 5.1-11.65l-22.49.01z" fill="\#FFF"></path></svg>"#;
        let input = format!(
            r#"<html style="width:100%;height:100%;background-color:#FFFFFF;">{}</html>"#,
            svg_input
        );
        let mut parser: HtmlParser = HtmlParser::new(input.to_string());
        parser.parse().expect("Failed to parse");

        let tokio = Rc::new(RefCell::new(tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .ok()
            .with_context(|| "Failed to construct tokio")?));

        let nodes_table = parser.nodes.clone().into_iter().enumerate().collect();
        let dom_indexes = get_dom_indexes(&nodes_table);
        let renderer = Renderer::new("http://localhost:5173".to_string(), tokio, nodes_table, PhysicalSize { width: 1920, height: 1080 }, Rc::new(FontHandler::new().unwrap()), Rc::new(RefCell::new(NetworkFetch::new())), dom_indexes);
        assert_eq!(renderer.get_element_html(1), svg_input);

        Ok(())
    }

    #[test]
    fn test_self_closing() {
        let input = r#"<html><img src="test.png"><p>Haha</p></html>"#;
        let mut parser: HtmlParser = HtmlParser::new(input.to_string());
        parser.parse().expect("Failed to parse");

        println!("{:?}", parser.nodes);
    }

    #[test]
    fn test_parse_style() -> Result<()> {
        let mut attributes = HashMap::new();
        attributes.insert(
            "style".to_string(),
            "width:100%;height:100%;background-color:#FFFFFF;".to_string(),
        );
        let parsed = parse_style(
            0,
            &Element {
                tag: "div".to_string(),
                attributes,
                parent: None,
            },
            &vec![],
            None,
            &mut HashMap::new(),
            &mut HashMap::new(),
            &HashMap::new(),
            &[],
        )?;

        assert_eq!(
            Style {
                width: StyleSize::Percent(100.),
                height: StyleSize::Percent(100.),
                background: StyleBackground::Hex(0x00_FF_FF_FF),
                display: StyleDisplay::Block,
                flex_shrink: 1,
                flex_grow: 0,
                justify_content: StyleJustifyContent::FlexStart,
                align_items: StyleJustifyContent::FlexStart,
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
                color: StyleBackground::Transparent,
                min_height: StyleSize::Auto,
                max_height: StyleSize::Auto,
                min_width: StyleSize::Auto,
                max_width: StyleSize::Auto,
                position: StylePosition::Static,
                text_align: StyleAlign::Left,
                variables: HashMap::new(),
                font_size: StyleSize::Px(16.),
                align_self: StyleJustifyContent::Auto,
                border_left: StyleSizeAndColor { color: StyleBackground::Hex(0xFF_FF_00_00), size: StyleSize::Px(3.), style: StyleBorderStyle::None },
                border_top: StyleSizeAndColor { color: StyleBackground::Hex(0xFF_FF_00_00), size: StyleSize::Px(3.), style: StyleBorderStyle::None },
                border_right: StyleSizeAndColor { color: StyleBackground::Hex(0xFF_FF_00_00), size: StyleSize::Px(3.), style: StyleBorderStyle::None },
                border_bottom: StyleSizeAndColor { color: StyleBackground::Hex(0xFF_FF_00_00), size: StyleSize::Px(3.), style: StyleBorderStyle::None },
                grid_template_columns: GridTemplateColumns::None,
                overflow: Overflow::Visible,
            },
            parsed
        );

        Ok(())
    }

    #[test]
    fn test_parse_google() -> Result<()> {
        let input = fs::read_to_string(SAMPLE_PAGE_PATH)
            .with_context(|| format!("Failed to read sample page at {SAMPLE_PAGE_PATH}"))?;

        let mut parser: HtmlParser = HtmlParser::new(input.to_string());
        parser.parse().expect("Failed to parse");

        println!("{:?}", parser.nodes);

        Ok(())
    }

    #[test]
    fn test_parse_css() -> Result<()> {
        let input = r#"
.test {
    display: block;
    background-color: #D2E3FC;
}

.haha {
    display: block;
    background-color: #FFF;
}

.hmm, .lol {
    display: 'flex';
    background-color: #D2E3FC;
}

.Qwbd3:hover {
    background:rgba(136,170,187,0.04);
    color:rgb(210,227,252);
    border:1px solid rgb(60,64,67)
}

.lJ9FBc input[type="submit"],.gbqfba{background-color:#303134;border:1px solid #303134;border-radius:8px;}
"#;
        let mut parser: CssParser = CssParser::new(&input);
        parser.parse().expect("Failed to parse");

        println!("{:?}", parser.nodes);

        Ok(())
    }

    #[test]
    fn test_parse_complex_css() -> Result<()> {
        let input = fs::read_to_string("pages/complex.css")
            .with_context(|| format!("Failed to read complex css at pages/complex.css"))?;

        let mut parser: CssParser = CssParser::new(&input);
        parser.parse().expect("Failed to parse");

        let body_css = parser
            .nodes
            .iter()
            .filter(|n| match n {
                CssNode::ClassName(class) => class.name.contains(&"body".to_string()),
                _ => false,
            })
            .collect::<Vec<&CssNode>>();

        println!("{:?}", parser.nodes);
        assert!(body_css.len() > 0);

        Ok(())
    }

    #[test]
    fn test_parse_inline_style() -> Result<()> {
        let input = r#"<g-snackbar jsname="PWj1Zb" jscontroller="OZLguc" style="display:none" jsshadow="" id="ow15" __is_owner="true"></g-snackbar>"#;
        let mut parser: HtmlParser = HtmlParser::new(input.to_string());
        parser.parse().expect("Failed to parse");

        let tokio = Rc::new(RefCell::new(tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .ok()
            .with_context(|| "Failed to construct tokio")?));

        let nodes_table = parser.nodes.clone().into_iter().enumerate().collect();
        let dom_indexes = get_dom_indexes(&nodes_table);
        let mut renderer = Renderer::new("http://localhost:5173".to_string(), tokio, nodes_table, PhysicalSize { width: 1920, height: 1080 }, Rc::new(FontHandler::new().unwrap()), Rc::new(RefCell::new(NetworkFetch::new())), dom_indexes);
        let width = 1280;
        let height = 720;
        let mut buffer = vec![0; width * height];
        renderer.render_into(&mut buffer, width as u32, height as u32, true);

        // Ensure all white, meaning nothing was painted
        assert!(buffer.iter().all(|p| *p == 0xFF_FF_FF_FF));

        Ok(())
    }

    #[test]
    fn test_parse_complex_css_selelctor() -> Result<()> {
        let input = r#"<html><style>.test input[type="submit"] { background-color: #ff0000; width: 100%; height: 100%; }</style><input class="test" type="submit"></html>"#;
        let mut parser: HtmlParser = HtmlParser::new(input.to_string());
        parser.parse().expect("Failed to parse");

        let tokio = Rc::new(RefCell::new(tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .ok()
            .with_context(|| "Failed to construct tokio")?));

        let nodes_table = parser.nodes.clone().into_iter().enumerate().collect();
        let dom_indexes = get_dom_indexes(&nodes_table);
        let mut renderer = Renderer::new("http://localhost:5173".to_string(), tokio, nodes_table, PhysicalSize { width: 1920, height: 1080 }, Rc::new(FontHandler::new().unwrap()), Rc::new(RefCell::new(NetworkFetch::new())), dom_indexes);
        let width = 1280;
        let height = 720;
        let mut buffer = vec![0; width * height];
        renderer.render_into(&mut buffer, width as u32, height as u32, true);

        // Ensure all red, meaning nothing was painted
        assert!(buffer.iter().all(|p| *p == 0xFF_00_00));

        Ok(())
    }

    #[test]
    fn test_parse_css_links() -> Result<()> {
        let input = r#"<html><head><link rel="stylesheet" href="https://pastebin.com/raw/rTDWxgsa"></head><input class="test" type="submit"></html>"#;
        let mut parser: HtmlParser = HtmlParser::new(input.to_string());
        parser.parse().expect("Failed to parse");

        let tokio = Rc::new(RefCell::new(tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .ok()
            .with_context(|| "Failed to construct tokio")?));

        let nodes_table = parser.nodes.clone().into_iter().enumerate().collect();
        let dom_indexes = get_dom_indexes(&nodes_table);
        let mut renderer = Renderer::new("http://localhost:5173".to_string(), tokio, nodes_table, PhysicalSize { width: 1920, height: 1080 }, Rc::new(FontHandler::new().unwrap()), Rc::new(RefCell::new(NetworkFetch::new())), dom_indexes);
        let width = 1280;
        let height = 720;
        let mut buffer = vec![0; width * height];
        renderer.render_into(&mut buffer, width as u32, height as u32, true);

        // Ensure all red, meaning nothing was painted
        assert!(buffer.iter().all(|p| *p == 0xFF_00_00));

        Ok(())
    }
}
