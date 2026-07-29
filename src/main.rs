mod css;
mod loader;
mod parser;
mod style;
mod ui;

use deno_core::serde::Deserialize;
use deno_error::JsErrorBox;
use deno_web::{BlobStore, InMemoryBroadcastChannel};
use fixedbitset::FixedBitSet;
use image::{DynamicImage, ImageReader};
use parser::{Element, HtmlParser, Node};
use reqwest::cookie::{CookieStore, Jar};
use resvg::tiny_skia::{IntSize, Pixmap};
use resvg::usvg::Tree;
use serde::Serialize;
use style::{
    Style, StyleBackground, StyleDisplay, StyleFlexDirection, StyleJustifyContent, StylePosition,
    StyleSize, StyleTransform, StyleTransformOperation, StyleVisibility, get_base_style,
    parse_style,
};

use std::borrow::Cow;
use std::cell::{Ref, RefCell, RefMut};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::io::Cursor;
use std::num::NonZeroU32;
use std::ops::Mul;
use std::path::Path;
use std::rc::Rc;
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, Mutex, Once};
use std::time::{Duration, Instant, SystemTime};
use std::{env, fs, u32};

use ab_glyph::{Font, FontRef, Glyph, OutlinedGlyph, ScaleFont};
use anyhow::{Context, Result, anyhow};
use bytes::Bytes;
use deno_core::error::JsError;
use deno_core::{JsRuntime, OpState, ToV8, extension, op2, v8};
use raw_window_handle::{HasDisplayHandle, HasWindowHandle};
use reqwest::Url as ReqwestUrl;
use resvg::{tiny_skia, usvg};
use softbuffer::{Context as SoftContext, Surface};
use winit::dpi::PhysicalSize;
use winit::event::{ElementState, Event, KeyEvent, MouseButton, MouseScrollDelta, WindowEvent};
use winit::event_loop::{EventLoopBuilder, EventLoopProxy};
use winit::window::{Window, WindowBuilder};

use crate::css::{
    ClassIndexes, ClassName, ClassNamePart, ClassNamePartAttribute, CssParser, MediaQuery,
    Node as CssNode, PropertyValue, PseudoClass, parse_media_query_parts, selector_to_parts,
};
use crate::loader::HttpModuleLoader;
use crate::parser::{Attributes, CommentElement, TextElement};
use crate::style::{
    CalcExpression, GridColumnSize, GridTemplateColumns, GridTemplateColumnsValue, StyleAlign,
    StyleBorderStyle, StyleCalcOperator, StylePointerEvents, StyleSizeAndColor, StyleZIndex,
    build_css_children_index, element_matched_attributes, format_css_number, get_chain_order,
    get_class_list, get_parent_chain, get_parent_layer, get_specificity_order, media_query_matches,
    split_ignoring_parentheses,
};
use crate::ui::{Typeable, UiBuilder, UiRuntime};

const WINDOW_WIDTH: u32 = 1920;
const WINDOW_HEIGHT: u32 = 1080;
const HEADER_HEIGHT: u32 = 100;
const ANIMATION_FRAME_INTERVAL: Duration = Duration::from_nanos(16_666_667);

// Many websites rely on the user-agent to be one of the major frames, so we don't use our own for now
const USER_AGENT: &str = "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36";

fn js_string_literal(value: &str) -> String {
    deno_core::serde_json::to_string(value).expect("serializing a string literal cannot fail")
}

fn run_v8_source<'s>(
    scope: &mut v8::PinScope<'s, '_>,
    name: &str,
    source: &str,
) -> Result<(), JsErrorBox> {
    v8::tc_scope!(let tc_scope, scope);

    let source = v8::String::new(tc_scope, source)
        .ok_or_else(|| JsErrorBox::generic(format!("Failed to allocate JS source for {name}")))?;
    let Some(script) = v8::Script::compile(tc_scope, source, None) else {
        if let Some(exception) = tc_scope.exception() {
            let err = deno_core::exception_to_err(tc_scope, exception, false, true);
            return Err(JsErrorBox::generic(err.to_string()));
        }
        return Err(JsErrorBox::generic(format!("Failed to compile {name}")));
    };

    if script.run(tc_scope).is_none() {
        if let Some(exception) = tc_scope.exception() {
            let err = deno_core::exception_to_err(tc_scope, exception, false, true);
            return Err(JsErrorBox::generic(err.to_string()));
        }
        return Err(JsErrorBox::generic(format!("Failed to run {name}")));
    }

    Ok(())
}

#[derive(Debug, Clone)]
struct RectBorderSide {
    size: u32,
    color: u32,
}

impl RectBorderSide {
    pub fn parse_from_style(
        style: &StyleSizeAndColor,
        node_style: &Style,
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
                    &SizeUnit::Px,
                )? as u32,
                color: match style.color {
                    StyleBackground::Hex(hex) => hex,
                    StyleBackground::Transparent => 0xFF_FF_FF_00,
                    StyleBackground::DataUrl(_) => {
                        return None;
                    }
                    StyleBackground::CurrentColor => match node_style.color {
                        StyleBackground::Hex(hex) => hex,
                        _ => {
                            return None;
                        }
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
pub struct BorderRadius {
    top_left: u32,
    top_right: u32,
    bottom_right: u32,
    bottom_left: u32,
}

impl BorderRadius {
    pub fn new_empty() -> Self {
        Self {
            top_left: 0,
            top_right: 0,
            bottom_right: 0,
            bottom_left: 0,
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
    border_radius: BorderRadius,
}

#[derive(Debug, Clone, Copy)]
struct PaintClip {
    start_x: i32,
    start_y: i32,
    end_x: i32,
    end_y: i32,
}

impl PaintClip {
    fn viewport(width: u32, height: u32) -> Self {
        Self {
            start_x: 0,
            start_y: 0,
            end_x: i32::try_from(width).unwrap_or(i32::MAX),
            end_y: i32::try_from(height).unwrap_or(i32::MAX),
        }
    }

    fn intersect_x(mut self, start_x: i32, end_x: i32) -> Self {
        self.start_x = self.start_x.max(start_x);
        self.end_x = self.end_x.min(end_x);
        self
    }

    fn intersect_y(mut self, start_y: i32, end_y: i32) -> Self {
        self.start_y = self.start_y.max(start_y);
        self.end_y = self.end_y.min(end_y);
        self
    }

    fn is_empty(self) -> bool {
        self.start_x >= self.end_x || self.start_y >= self.end_y
    }
}

#[derive(Debug, Clone, Copy)]
struct ClippedBlit {
    src_x: u32,
    src_y: u32,
    dst_x: u32,
    dst_y: u32,
    width: u32,
    height: u32,
}

fn clipped_blit(
    dst_width: u32,
    dst_height: u32,
    src_width: u32,
    src_height: u32,
    dst_x: i32,
    dst_y: i32,
    clip: PaintClip,
) -> Option<ClippedBlit> {
    if dst_width == 0 || dst_height == 0 || src_width == 0 || src_height == 0 || clip.is_empty() {
        return None;
    }

    let start_x = dst_x.max(0).max(clip.start_x);
    let start_y = dst_y.max(0).max(clip.start_y);
    let end_x = dst_x
        .saturating_add_unsigned(src_width)
        .min(i32::try_from(dst_width).unwrap_or(i32::MAX))
        .min(clip.end_x);
    let end_y = dst_y
        .saturating_add_unsigned(src_height)
        .min(i32::try_from(dst_height).unwrap_or(i32::MAX))
        .min(clip.end_y);
    if start_x >= end_x || start_y >= end_y {
        return None;
    }

    Some(ClippedBlit {
        src_x: (start_x - dst_x) as u32,
        src_y: (start_y - dst_y) as u32,
        dst_x: start_x as u32,
        dst_y: start_y as u32,
        width: (end_x - start_x) as u32,
        height: (end_y - start_y) as u32,
    })
}

#[derive(Debug, Clone)]
enum LayoutKind {
    Element,
    PixMap((tiny_skia::Pixmap, bool)),
    Canvas,
    Text(tiny_skia::Pixmap),
    Iframe,
}

#[derive(Debug, Clone)]
struct LayoutBox {
    rect: Rect,
    kind: LayoutKind,
    children: Vec<usize>,
    node_idx: usize,
    content_height: u32,
    z_index: i32,
}

#[derive(Debug, Clone)]
enum RequestCacheEntry {
    PngData(Bytes),
    SvgData(String),
    CssData(String),
    JpegData(Bytes),
    GifData(Bytes),
    WebpData(Bytes),
    Unsupported,
}

fn sniff_image_data(bytes: Vec<u8>) -> Option<RequestCacheEntry> {
    if bytes.starts_with(&[0x89, b'P', b'N', b'G', 0x0d, 0x0a, 0x1a, 0x0a]) {
        Some(RequestCacheEntry::PngData(bytes.into()))
    } else if bytes.len() >= 12 && &bytes[..4] == b"RIFF" && &bytes[8..12] == b"WEBP" {
        Some(RequestCacheEntry::WebpData(bytes.into()))
    } else if bytes.starts_with(&[0xff, 0xd8, 0xff]) {
        Some(RequestCacheEntry::JpegData(bytes.into()))
    } else if bytes.starts_with(b"GIF87a") || bytes.starts_with(b"GIF89a") {
        Some(RequestCacheEntry::GifData(bytes.into()))
    } else {
        let text = String::from_utf8(bytes).ok()?;
        let text_start = text.trim_start();
        if text_start.starts_with("<svg") || text_start.starts_with("<?xml") {
            Some(RequestCacheEntry::SvgData(text))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum LayoutMode {
    BaseCalculation,
    Complete,
}

#[derive(Debug, Default)]
struct DomIndexes {
    class_elements: Vec<FixedBitSet>,
    tag_elements: HashMap<String, FixedBitSet>,
    id_elements: HashMap<String, FixedBitSet>,
    children_index: HashMap<usize, Vec<usize>>,
    attribute_elements: HashMap<String, FixedBitSet>,
    root_indice: usize,
}

impl DomIndexes {
    pub fn recompute_class_elements(
        &mut self,
        html_nodes: &NodesTable,
        nodes_idxs: &Vec<usize>,
        class_indexes: &mut ClassIndexes,
    ) {
        self.class_elements = get_dom_indexes_classes(html_nodes, nodes_idxs, class_indexes);
    }

    pub fn remove_id_node(&mut self, id: &String, node_idx: usize) {
        if let Some(existing) = self.id_elements.get_mut(id) {
            existing.remove(node_idx);
        }
    }

    pub fn add_id_node(&mut self, id: &String, node_idx: usize) {
        if let Some(existing) = self.id_elements.get_mut(id) {
            existing.grow_and_insert(node_idx);
        } else {
            let mut elements = FixedBitSet::with_capacity(0);
            elements.grow_and_insert(node_idx);
            self.id_elements.insert(id.clone(), elements);
        }
    }

    pub fn remove_class_node(
        &mut self,
        class: &str,
        node_idx: usize,
        class_indexes: &mut ClassIndexes,
    ) {
        for class in class.split_whitespace() {
            if let Some(class_idx) = class_indexes.class_to_idx.get(class) {
                if let Some(existing) = self.class_elements.get_mut(*class_idx) {
                    existing.remove(node_idx);
                }
            }
        }
    }

    pub fn add_class_node(
        &mut self,
        class: &str,
        node_idx: usize,
        class_indexes: &mut ClassIndexes,
    ) {
        for class in class.split_whitespace() {
            let (new, class_idx) = class_indexes.upsert_definition(class.to_string());
            if new {
                self.class_elements
                    .resize(class_indexes.len(), FixedBitSet::with_capacity(0));
            }
            if let Some(existing) = self.class_elements.get_mut(class_idx) {
                existing.grow_and_insert(node_idx);
            }
        }
    }

    pub fn add_attribute_node(&mut self, attribute: &str, node_idx: usize) {
        if let Some(existing) = self.attribute_elements.get_mut(attribute) {
            existing.grow_and_insert(node_idx);
        } else {
            let mut elements = FixedBitSet::with_capacity(0);
            elements.grow_and_insert(node_idx);
            self.attribute_elements
                .insert(attribute.to_string(), elements);
        }
    }

    pub fn remove_attribute_node(&mut self, attribute: &str, node_idx: usize) {
        if let Some(existing) = self.attribute_elements.get_mut(attribute) {
            existing.remove(node_idx);
        }
    }
}

type CanvasImageKey = (usize, Option<u32>, Option<u32>);

type CanvasClipMask = Rc<[u8]>;

#[derive(Clone, Debug, Default)]
struct CanvasState {
    transform: Option<Matrixf32>,
    clip_mask: Option<CanvasClipMask>,
}

#[derive(Clone, Copy, Debug)]
struct CanvasSpan {
    y: usize,
    start_x: usize,
    end_x: usize,
}

fn multiply_coverage(first: u8, second: u8) -> u8 {
    ((u16::from(first) * u16::from(second) + 127) / 255) as u8
}

fn clipped_coverage(clip_mask: Option<&[u8]>, pixel_idx: usize, coverage: u8) -> u8 {
    match clip_mask {
        Some(mask) => multiply_coverage(coverage, mask[pixel_idx]),
        None => coverage,
    }
}

fn blend_canvas_pixel(
    buffer: &mut [u32],
    clip_mask: Option<&[u8]>,
    pixel_idx: usize,
    source: (u8, u8, u8, u8),
    coverage: u8,
) {
    let coverage = clipped_coverage(clip_mask, pixel_idx, coverage);
    if coverage == 0 {
        return;
    }

    let source = if coverage == u8::MAX {
        source
    } else {
        (
            multiply_coverage(source.0, coverage),
            multiply_coverage(source.1, coverage),
            multiply_coverage(source.2, coverage),
            multiply_coverage(source.3, coverage),
        )
    };
    buffer[pixel_idx] = blend_rgba_with_rgba(buffer[pixel_idx], source);
}

fn clear_canvas_pixel(
    buffer: &mut [u32],
    clip_mask: Option<&[u8]>,
    pixel_idx: usize,
    coverage: u8,
) {
    let coverage = clipped_coverage(clip_mask, pixel_idx, coverage);
    if coverage == 0 {
        return;
    }
    if coverage == u8::MAX {
        buffer[pixel_idx] = 0;
        return;
    }

    let remaining = u8::MAX - coverage;
    let [red, green, blue, alpha] = buffer[pixel_idx].to_be_bytes();
    buffer[pixel_idx] = u32::from_be_bytes([
        multiply_coverage(red, remaining),
        multiply_coverage(green, remaining),
        multiply_coverage(blue, remaining),
        multiply_coverage(alpha, remaining),
    ]);
}

#[derive(Debug)]
struct CanvasBuffer {
    buffer: Vec<u32>,
    width: u32,
    height: u32,
    images: HashMap<CanvasImageKey, Pixmap>,
    commands: Vec<CanvasPathCommand>,
    current_path: Vec<CanvasPathCommand>,
    state: CanvasState,
    state_stack: Vec<CanvasState>,
    dirty: bool,
}

impl CanvasBuffer {
    fn new(width: u32, height: u32) -> Self {
        Self {
            buffer: vec![0x00_00_00_00; width as usize * height as usize],
            width,
            height,
            images: HashMap::new(),
            commands: vec![],
            current_path: vec![],
            state: CanvasState::default(),
            state_stack: vec![],
            dirty: false,
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
        self.buffer = vec![0; width as usize * height as usize];
        self.commands.clear();
        self.current_path.clear();
        self.state = CanvasState::default();
        self.state_stack.clear();
        self.dirty = true;
    }

    fn update_if_needed(&mut self) {
        if self.dirty {
            self.update_buffer();
            self.dirty = false;
        }
    }

    fn rect_bounds(&self, x: i32, y: i32, width: u32, height: u32) -> (usize, usize, usize, usize) {
        let canvas_width = i64::from(self.width);
        let canvas_height = i64::from(self.height);
        let start_x = i64::from(x).clamp(0, canvas_width) as usize;
        let start_y = i64::from(y).clamp(0, canvas_height) as usize;
        let end_x = (i64::from(x) + i64::from(width)).clamp(0, canvas_width) as usize;
        let end_y = (i64::from(y) + i64::from(height)).clamp(0, canvas_height) as usize;
        (start_x, start_y, end_x, end_y)
    }

    fn blend_pixel(&mut self, x: i32, y: i32, source: (u8, u8, u8, u8), coverage: u8) {
        if x < 0 || y < 0 || x >= self.width as i32 || y >= self.height as i32 {
            return;
        }

        let pixel_idx = y as usize * self.width as usize + x as usize;
        blend_canvas_pixel(
            &mut self.buffer,
            self.state.clip_mask.as_deref(),
            pixel_idx,
            source,
            coverage,
        );
    }

    fn fill_rect(&mut self, x: i32, y: i32, width: u32, height: u32, color: u32) {
        let (start_x, start_y, end_x, end_y) = self.rect_bounds(x, y, width, height);
        let stride = self.width as usize;
        let source = rgba_to_premul_tuple(color);
        for py in start_y..end_y {
            for px in start_x..end_x {
                let pixel_idx = py * stride + px;
                blend_canvas_pixel(
                    &mut self.buffer,
                    self.state.clip_mask.as_deref(),
                    pixel_idx,
                    source,
                    u8::MAX,
                );
            }
        }
    }

    fn clear_rect(&mut self, x: i32, y: i32, width: u32, height: u32) {
        let (start_x, start_y, end_x, end_y) = self.rect_bounds(x, y, width, height);
        let stride = self.width as usize;
        for py in start_y..end_y {
            for px in start_x..end_x {
                let pixel_idx = py * stride + px;
                clear_canvas_pixel(
                    &mut self.buffer,
                    self.state.clip_mask.as_deref(),
                    pixel_idx,
                    u8::MAX,
                );
            }
        }
    }

    fn update_buffer(&mut self) {
        let commands = std::mem::take(&mut self.commands);
        for cmd in commands {
            match cmd {
                CanvasPathCommand::Transform { matrix } => {
                    self.state.transform = Some(match self.state.transform.take() {
                        Some(current) => current.multiply(&matrix).unwrap(),
                        None => matrix,
                    });
                }
                CanvasPathCommand::ResetTransform => {
                    self.state.transform = None;
                }
                CanvasPathCommand::Save => {
                    self.state_stack.push(self.state.clone());
                }
                CanvasPathCommand::Restore => {
                    if let Some(saved) = self.state_stack.pop() {
                        self.state = saved;
                    }
                }
                CanvasPathCommand::BeginPath => {
                    self.current_path.clear();
                }
                CanvasPathCommand::MoveTo { point: _ }
                | CanvasPathCommand::Point { point: _ }
                | CanvasPathCommand::BezierCurve {
                    cp1: _,
                    cp2: _,
                    endpoint: _,
                }
                | CanvasPathCommand::Close => {
                    self.current_path.push(cmd);
                }
                CanvasPathCommand::FillRect {
                    x,
                    y,
                    width,
                    height,
                } => {
                    self.fill_rect(x, y, width, height, 0x00_00_00_FF);
                }
                CanvasPathCommand::StrokeRect {
                    x,
                    y,
                    width,
                    height,
                    line_width,
                } => {
                    let line_width = line_width as u32;
                    self.fill_rect(x, y, line_width, height, 0x00_00_00_FF); // Left
                    self.fill_rect(x, y, width, line_width, 0x00_00_00_FF); // Top
                    self.fill_rect(
                        x + width as i32 - line_width as i32,
                        y,
                        line_width,
                        height,
                        0x00_00_00_FF,
                    ); // Right
                    self.fill_rect(
                        x,
                        y + height as i32 - line_width as i32,
                        width,
                        line_width,
                        0x00_00_00_FF,
                    ); // Bottom
                }
                CanvasPathCommand::ClearRect {
                    x,
                    y,
                    width,
                    height,
                } => {
                    self.clear_rect(x, y, width, height);
                }
                CanvasPathCommand::DrawImage {
                    image_node_idx,
                    image_width,
                    image_height,
                    x,
                    y,
                } => {
                    if let Some(image) =
                        self.images
                            .get(&(image_node_idx, image_width, image_height))
                    {
                        let image_width = image.width() as usize;
                        let image_height = image.height() as usize;
                        let canvas_width = self.width as usize;
                        let pixels = image.pixels();

                        let mut top_left = [x as f64, y as f64];
                        let mut top_right = [x as f64 + image_width as f64, y as f64];
                        let mut bottom_left = [x as f64, y as f64 + image_height as f64];
                        let mut bottom_right = [
                            x as f64 + image_width as f64,
                            y as f64 + image_height as f64,
                        ];
                        if let Some(transform) = &self.state.transform {
                            top_left = self.compute_point_transform(&top_left, &transform).unwrap();
                            top_right = self
                                .compute_point_transform(&top_right, &transform)
                                .unwrap();
                            bottom_left = self
                                .compute_point_transform(&bottom_left, &transform)
                                .unwrap();
                            bottom_right = self
                                .compute_point_transform(&bottom_right, &transform)
                                .unwrap();
                        }

                        let inverse_transform = match &self.state.transform {
                            None => None,
                            Some(transform) => match transform.inverse_affine() {
                                Some(inverse) => Some(inverse),
                                None => continue,
                            },
                        };

                        let min_x = top_left[0]
                            .min(top_right[0])
                            .min(bottom_left[0])
                            .min(bottom_right[0])
                            .floor() as i32;

                        let max_x = top_left[0]
                            .max(top_right[0])
                            .max(bottom_left[0])
                            .max(bottom_right[0])
                            .ceil() as i32;

                        let min_y = top_left[1]
                            .min(top_right[1])
                            .min(bottom_left[1])
                            .min(bottom_right[1])
                            .floor() as i32;

                        let max_y = top_left[1]
                            .max(top_right[1])
                            .max(bottom_left[1])
                            .max(bottom_right[1])
                            .ceil() as i32;

                        let start_x = min_x.max(0);
                        let start_y = min_y.max(0);
                        let end_x = max_x.min(self.width as i32);
                        let end_y = max_y.min(self.height as i32);

                        for destination_y in start_y..end_y {
                            for destination_x in start_x..end_x {
                                let destination_point =
                                    [destination_x as f64 + 0.5, destination_y as f64 + 0.5];
                                let user_point = match &inverse_transform {
                                    Some(inverse) => self
                                        .compute_point_transform(&destination_point, inverse)
                                        .unwrap(),
                                    None => destination_point,
                                };

                                let source_x = user_point[0] - x as f64;
                                let source_y = user_point[1] - y as f64;

                                if source_x < 0.0
                                    || source_x >= image_width as f64
                                    || source_y < 0.0
                                    || source_y >= image_height as f64
                                {
                                    continue;
                                }

                                let source_x = source_x.floor() as usize;
                                let source_y = source_y.floor() as usize;

                                let source = pixels[source_y * image_width + source_x];
                                let destination_idx =
                                    destination_y as usize * canvas_width + destination_x as usize;
                                blend_canvas_pixel(
                                    &mut self.buffer,
                                    self.state.clip_mask.as_deref(),
                                    destination_idx,
                                    (source.red(), source.green(), source.blue(), source.alpha()),
                                    u8::MAX,
                                );
                            }
                        }
                    }
                }
                CanvasPathCommand::Stroke { line_width, color } => {
                    let current_path = self.current_path.clone();
                    let transform = self.state.transform.clone();
                    self.apply_stroke(&current_path, line_width, &transform, color)
                        .unwrap();
                }
                CanvasPathCommand::StrokePath {
                    path,
                    line_width,
                    color,
                } => {
                    let transform = self.state.transform.clone();
                    self.apply_stroke(&path, line_width, &transform, color)
                        .unwrap();
                }
                CanvasPathCommand::Fill { color, fill_rule } => {
                    let current_path = self.current_path.clone();
                    let transform = self.state.transform.clone();
                    self.apply_fill(&current_path, &transform, color, &fill_rule)
                        .unwrap();
                }
                CanvasPathCommand::FillPath {
                    path,
                    color,
                    fill_rule,
                } => {
                    let transform = self.state.transform.clone();
                    self.apply_fill(&path, &transform, color, &fill_rule)
                        .unwrap();
                }
                CanvasPathCommand::Clip { fill_rule } => {
                    let current_path = self.current_path.clone();
                    let transform = self.state.transform.clone();
                    self.apply_clip(&current_path, &transform, &fill_rule)
                        .unwrap();
                }
                CanvasPathCommand::ClipPath { path, fill_rule } => {
                    let transform = self.state.transform.clone();
                    self.apply_clip(&path, &transform, &fill_rule).unwrap();
                }
            }
        }
    }

    fn compute_point_transform(&self, point: &[f64; 2], transform: &Matrixf32) -> Result<[f64; 2]> {
        Ok([
            (transform.get(0, 0) * point[0] as f32
                + transform.get(0, 1) * point[1] as f32
                + transform.get(0, 2)) as f64,
            (transform.get(1, 0) * point[0] as f32
                + transform.get(1, 1) * point[1] as f32
                + transform.get(1, 2)) as f64,
        ])
    }

    fn rasterize_path_spans(
        &self,
        queued_commands: &[CanvasPathCommand],
        transform: &Option<Matrixf32>,
        fill_rule: &CanvasFillRule,
    ) -> Result<Vec<CanvasSpan>> {
        let mut cursor = Position { x: 0, y: 0 };
        let mut subpath_start: Option<[f64; 2]> = None;
        let mut y_pixels = vec![vec![]; self.height as usize];
        for cmd in queued_commands {
            match cmd {
                &CanvasPathCommand::MoveTo { mut point } => {
                    if let Some(transform) = transform {
                        point = self.compute_point_transform(&point, transform)?;
                    }
                    cursor.x = point[0].round() as i32;
                    cursor.y = point[1].round() as i32;
                    subpath_start = Some(point);
                }
                &CanvasPathCommand::Point { mut point } => {
                    if let Some(transform) = transform {
                        point = self.compute_point_transform(&point, transform)?;
                    }
                    let x = point[0];
                    let y = point[1];

                    if subpath_start.is_none() {
                        cursor.x = x as i32;
                        cursor.y = y as i32;
                        subpath_start = Some(point);
                        continue;
                    }

                    let start_x = cursor.x as f64;
                    let start_y = cursor.y as f64;
                    let x_delta = x - cursor.x as f64;
                    let y_delta = y - cursor.y as f64;

                    let steps = y_delta.abs().ceil().max(1.) as usize;

                    let x_ratio = x_delta / steps as f64;
                    let y_ratio = y_delta / steps as f64;

                    for idx in 0..steps {
                        let px = (start_x + idx as f64 * x_ratio).round() as i32;
                        let py = (start_y + idx as f64 * y_ratio).round() as i32;

                        if px < 0 || py < 0 || py >= self.height as i32 {
                            continue;
                        }

                        y_pixels[py as usize].push(px as usize);
                    }

                    cursor.x = x.round() as i32;
                    cursor.y = y.round() as i32;
                }
                &CanvasPathCommand::BezierCurve {
                    mut cp1,
                    mut cp2,
                    mut endpoint,
                } => {
                    if let Some(transform) = transform {
                        cp1 = self.compute_point_transform(&cp1, transform)?;
                        cp2 = self.compute_point_transform(&cp2, transform)?;
                        endpoint = self.compute_point_transform(&endpoint, transform)?;
                    }
                    let steps = (distance((cursor.x as f64, cursor.y as f64), (cp1[0], cp1[1]))
                        + distance((cp1[0], cp1[1]), (cp2[0], cp2[1]))
                        + distance((cp2[0], cp2[1]), (endpoint[0], endpoint[1])))
                    .ceil()
                    // TODO: Multiplying by 3 here is a dirty fix, come back to this
                    .mul(3.)
                    .max(1.) as usize;
                    let mut last_y = None;
                    for t_idx in 0..=steps {
                        let x = cubic_bezier(
                            t_idx as f32 / steps as f32,
                            cursor.x,
                            cp1[0] as i32,
                            cp2[0] as i32,
                            endpoint[0] as i32,
                        );
                        let y = cubic_bezier(
                            t_idx as f32 / steps as f32,
                            cursor.y,
                            cp1[1] as i32,
                            cp2[1] as i32,
                            endpoint[1] as i32,
                        );

                        if x >= 0
                            && x < self.width as i32
                            && y >= 0
                            && y < self.height as i32
                            && last_y.is_none_or(|last| last != y)
                        {
                            y_pixels[y as usize].push(x as usize);
                            last_y = Some(y);
                        }
                    }

                    cursor.x = endpoint[0].round() as i32;
                    cursor.y = endpoint[1].round() as i32;
                }
                CanvasPathCommand::Close => {
                    let Some([x, y]) = subpath_start else {
                        continue;
                    };
                    let x_delta = x - cursor.x as f64;
                    let y_delta = y - cursor.y as f64;
                    let steps = y_delta.abs().max(1.) as usize;
                    if steps > 0 {
                        for step in 0..=steps {
                            let px = (cursor.x as f64 + x_delta * step as f64 / steps as f64)
                                .round() as usize;
                            let py = (cursor.y as f64 + y_delta * step as f64 / steps as f64)
                                .round() as usize;
                            if px < self.width as usize && py < self.height as usize {
                                y_pixels[py].push(px);
                            }
                        }
                    }
                    cursor.x = x.round() as i32;
                    cursor.y = y.round() as i32;
                }
                _ => {}
            };
        }

        let width = self.width as usize;
        let mut spans = vec![];
        if width == 0 {
            return Ok(spans);
        }

        for (py, edges) in y_pixels.iter_mut().enumerate() {
            edges.sort_unstable();
            match fill_rule {
                CanvasFillRule::NonZero => {
                    let Some(min) = edges.first() else {
                        continue;
                    };
                    let Some(max) = edges.last() else {
                        continue;
                    };
                    let min = (*min).min(width - 1);
                    let max = (*max).min(width - 1);
                    if min < max {
                        spans.push(CanvasSpan {
                            y: py,
                            start_x: min,
                            end_x: max,
                        });
                    }
                }
                CanvasFillRule::EvenOdd => {
                    for edge_pair in edges.chunks_exact(2) {
                        let edge_start = edge_pair[0].min(width - 1);
                        let edge_end = edge_pair[1].min(width - 1);
                        if edge_start < edge_end {
                            spans.push(CanvasSpan {
                                y: py,
                                start_x: edge_start,
                                end_x: edge_end,
                            });
                        }
                    }
                }
            }
        }

        Ok(spans)
    }

    fn apply_fill(
        &mut self,
        queued_commands: &[CanvasPathCommand],
        transform: &Option<Matrixf32>,
        color: u32,
        fill_rule: &CanvasFillRule,
    ) -> Result<()> {
        let spans = self.rasterize_path_spans(queued_commands, transform, fill_rule)?;
        let source = rgba_to_premul_tuple(color);
        let stride = self.width as usize;
        for span in spans {
            for x in span.start_x..span.end_x {
                blend_canvas_pixel(
                    &mut self.buffer,
                    self.state.clip_mask.as_deref(),
                    span.y * stride + x,
                    source,
                    u8::MAX,
                );
            }
        }

        Ok(())
    }

    fn apply_clip(
        &mut self,
        queued_commands: &[CanvasPathCommand],
        transform: &Option<Matrixf32>,
        fill_rule: &CanvasFillRule,
    ) -> Result<()> {
        let spans = self.rasterize_path_spans(queued_commands, transform, fill_rule)?;
        let stride = self.width as usize;
        let mut mask = vec![0; stride * self.height as usize];
        for span in spans {
            mask[span.y * stride + span.start_x..span.y * stride + span.end_x].fill(u8::MAX);
        }
        if let Some(current_clip) = &self.state.clip_mask {
            for (coverage, current_coverage) in mask.iter_mut().zip(current_clip.iter()) {
                *coverage = multiply_coverage(*coverage, *current_coverage);
            }
        }
        self.state.clip_mask = Some(Rc::from(mask));

        Ok(())
    }

    fn apply_stroke(
        &mut self,
        queued_commands: &[CanvasPathCommand],
        line_width: f64,
        transform: &Option<Matrixf32>,
        color: u32,
    ) -> Result<()> {
        let mut cursor = Position { x: 0, y: 0 };
        let mut subpath_start: Option<[f64; 2]> = None;
        let color_tuple = rgba_to_premul_tuple(color);
        let line_width_offset = -line_width as i32 / 2;
        let line_width_end = line_width as i32 / 2;
        for cmd in queued_commands {
            match cmd {
                &CanvasPathCommand::MoveTo { mut point } => {
                    if let Some(transform) = transform {
                        point = self.compute_point_transform(&point, transform)?;
                    }
                    cursor.x = point[0].round() as i32;
                    cursor.y = point[1].round() as i32;
                    subpath_start = Some(point);
                }
                &CanvasPathCommand::Point { mut point } => {
                    if let Some(transform) = transform {
                        point = self.compute_point_transform(&point, transform)?;
                    }
                    let x = point[0];
                    let y = point[1];

                    if subpath_start.is_none() {
                        cursor.x = x as i32;
                        cursor.y = y as i32;
                        subpath_start = Some(point);
                        continue;
                    }

                    let start_x = cursor.x as f64;
                    let start_y = cursor.y as f64;
                    let x_delta = x - cursor.x as f64;
                    let y_delta = y - cursor.y as f64;

                    let hyp = (x_delta.powi(2) + y_delta.powi(2)).sqrt().round() as i32;
                    if hyp > 0 {
                        let x_ratio = x_delta / hyp as f64;
                        let y_ratio = y_delta / hyp as f64;

                        for idx in 0..hyp {
                            for wxidx in line_width_offset..line_width_end {
                                for wyidx in line_width_offset..line_width_end {
                                    let px = (start_x + idx as f64 * x_ratio + wxidx as f64).round()
                                        as i32;
                                    let py = (start_y + idx as f64 * y_ratio + wyidx as f64).round()
                                        as i32;
                                    self.blend_pixel(px, py, color_tuple, u8::MAX);
                                }
                            }
                        }
                    }

                    cursor.x = x.round() as i32;
                    cursor.y = y.round() as i32;
                }
                &CanvasPathCommand::BezierCurve {
                    mut cp1,
                    mut cp2,
                    mut endpoint,
                } => {
                    if let Some(transform) = transform {
                        cp1 = self.compute_point_transform(&cp1, transform)?;
                        cp2 = self.compute_point_transform(&cp2, transform)?;
                        endpoint = self.compute_point_transform(&endpoint, transform)?;
                    }
                    let steps = (distance((cursor.x as f64, cursor.y as f64), (cp1[0], cp1[1]))
                        + distance((cp1[0], cp1[1]), (cp2[0], cp2[1]))
                        + distance((cp2[0], cp2[1]), (endpoint[0], endpoint[1])))
                    .ceil()
                    .max(1.) as usize;
                    for x_idx in 0..=steps {
                        let x = cubic_bezier(
                            x_idx as f32 / steps as f32,
                            cursor.x,
                            cp1[0] as i32,
                            cp2[0] as i32,
                            endpoint[0] as i32,
                        );
                        let y = cubic_bezier(
                            x_idx as f32 / steps as f32,
                            cursor.y,
                            cp1[1] as i32,
                            cp2[1] as i32,
                            endpoint[1] as i32,
                        );

                        for wxidx in line_width_offset..line_width_end {
                            for wyidx in line_width_offset..line_width_end {
                                self.blend_pixel(x + wxidx, y + wyidx, color_tuple, u8::MAX);
                            }
                        }
                    }

                    cursor.x = endpoint[0].round() as i32;
                    cursor.y = endpoint[1].round() as i32;
                }
                CanvasPathCommand::Close => {
                    let Some([x, y]) = subpath_start else {
                        continue;
                    };
                    let x_delta = x - cursor.x as f64;
                    let y_delta = y - cursor.y as f64;
                    let steps = (x_delta.powi(2) + y_delta.powi(2)).sqrt().ceil() as i32;
                    if steps > 0 {
                        for step in 0..=steps {
                            let x = (cursor.x as f64 + x_delta * step as f64 / steps as f64).round()
                                as i32;
                            let y = (cursor.y as f64 + y_delta * step as f64 / steps as f64).round()
                                as i32;
                            for wxidx in line_width_offset..line_width_end {
                                for wyidx in line_width_offset..line_width_end {
                                    self.blend_pixel(x + wxidx, y + wyidx, color_tuple, u8::MAX);
                                }
                            }
                        }
                    }
                    cursor.x = x.round() as i32;
                    cursor.y = y.round() as i32;
                }
                _ => {}
            }
        }

        Ok(())
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
struct Matrixf32 {
    data: Vec<f32>,
    rows: usize,
    columns: usize,
}

impl Matrixf32 {
    pub fn new(data: Vec<f32>, rows: usize, columns: usize) -> Self {
        Self {
            data,
            rows,
            columns,
        }
    }

    fn get(&self, row: usize, column: usize) -> f32 {
        self.data[row * self.columns + column]
    }

    fn multiply_into(&self, other: &Self, out: &mut Self) -> Result<()> {
        if self.columns != other.rows || out.rows != self.rows || out.columns != other.columns {
            return Err(anyhow!("Invalid shape"));
        }
        let compatibility = self.columns;
        for row in 0..self.rows {
            for column in 0..other.columns {
                let mut value = 0.;
                for inner in 0..compatibility {
                    value += self.get(row, inner) * other.get(inner, column);
                }
                out.data[row * other.columns + column] = value;
            }
        }
        Ok(())
    }

    fn multiply(&self, other: &Self) -> Option<Self> {
        let mut out = Self::new(
            vec![0.; self.rows * other.columns],
            self.rows,
            other.columns,
        );
        self.multiply_into(other, &mut out).ok()?;
        Some(out)
    }

    fn inverse_affine(&self) -> Option<Self> {
        let a = self.get(0, 0);
        let c = self.get(0, 1);
        let e = self.get(0, 2);
        let b = self.get(1, 0);
        let d = self.get(1, 1);
        let f = self.get(1, 2);

        let determinant = a * d - b * c;
        if !determinant.is_finite() || determinant.abs() <= f32::EPSILON {
            return None;
        }

        Some(Self::new(
            vec![
                d / determinant,
                -c / determinant,
                (c * f - d * e) / determinant,
                -b / determinant,
                a / determinant,
                (b * e - a * f) / determinant,
                0.0,
                0.0,
                1.0,
            ],
            3,
            3,
        ))
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
enum FrameDomCommand {
    QuerySelector {
        selector: String,
        required_parent: Option<usize>,
        reply: std::sync::mpsc::Sender<Result<Option<(usize, Node)>, String>>,
    },
    QuerySelectorAll {
        selector: String,
        required_parent: Option<usize>,
        reply: std::sync::mpsc::Sender<Result<Vec<(usize, Node)>, String>>,
    },
    ReplaceInnerHtml {
        node_idx: usize,
        html: String,
        reply: std::sync::mpsc::Sender<()>,
    },
    GetInnerHtml {
        node_idx: usize,
        reply: std::sync::mpsc::Sender<String>,
    },
    GetComputedStyle {
        node_idx: usize,
        reply: std::sync::mpsc::Sender<HashMap<String, String>>,
    },
    CreateElement {
        tag: String,
        reply: std::sync::mpsc::Sender<usize>,
    },
    GetElementsByTagName {
        tag: String,
        required_parent: Option<usize>,
        reply: std::sync::mpsc::Sender<Vec<(usize, Node)>>,
    },
    GetElementsByName {
        name: String,
        required_parent: Option<usize>,
        reply: std::sync::mpsc::Sender<Vec<(usize, Node)>>,
    },
    GetElementsByClassName {
        class_names: String,
        required_parent: Option<usize>,
        reply: std::sync::mpsc::Sender<Vec<(usize, Node)>>,
    },
    UpdateElementAttributes {
        node_idx: usize,
        attributes: Attributes,
        reply: std::sync::mpsc::Sender<Result<()>>,
    },
}

#[derive(Debug)]
enum FrameCommand {
    Render,
    UserEvent(UserEvent),
    Dom(FrameDomCommand),
    Resized(PhysicalSize<u32>),
}

#[derive(Debug)]
struct FrameHandle {
    surface: Arc<Mutex<Vec<u32>>>,
    tx: std::sync::mpsc::Sender<FrameCommand>,
}

#[derive(Debug, Clone)]
enum RendererProxy {
    WindowLoop {
        proxy: EventLoopProxy<UserEvent>,
        tab_idx: usize,
    },
    FrameLoop(std::sync::mpsc::Sender<FrameCommand>),
}

impl RendererProxy {
    fn fire_user_event(&self, event: UserEvent) -> Result<()> {
        match self {
            RendererProxy::FrameLoop(tx) => tx.send(FrameCommand::UserEvent(event))?,
            RendererProxy::WindowLoop { proxy, .. } => proxy.send_event(event)?,
        };
        Ok(())
    }

    fn fire_tab_url_updated(&self, url: String) -> Result<()> {
        if let RendererProxy::WindowLoop { proxy, tab_idx } = self {
            proxy.send_event(UserEvent::TabUrlUpdated {
                tab_idx: *tab_idx,
                url,
            })?;
        }
        Ok(())
    }

    fn fire_tab_updated(&self, buffer: Vec<u32>) -> Result<()> {
        if let RendererProxy::WindowLoop { proxy, tab_idx } = self {
            proxy.send_event(UserEvent::TabUpdated {
                tab_idx: *tab_idx,
                buffer,
            })?;
        }
        Ok(())
    }
}

#[derive(Debug)]
struct RenderedNode {
    layout_box_idx: usize,
    offset_x: i32,
    offset_y: i32,
    clip: PaintClip,
}

type DeferredPaint = (usize, i32, i32, PaintClip);

#[derive(Debug)]
struct NodesTable {
    data: Vec<Option<Node>>,
    cursor: usize,
}

impl NodesTable {
    pub fn new_from_nodes(data: Vec<Node>) -> Self {
        Self {
            cursor: data.len(),
            data: data.into_iter().map(|v| Some(v)).collect(),
        }
    }

    pub fn get(&self, idx: usize) -> Option<&Node> {
        let value = self.data.get(idx)?.as_ref();
        value
    }

    pub fn get_mut(&mut self, idx: usize) -> Option<&mut Node> {
        let value = self.data.get_mut(idx)?.as_mut();
        value
    }

    pub fn keys(&self) -> impl Iterator<Item = usize> + '_ {
        self.data.iter().enumerate().filter_map(
            |(idx, v)| {
                if v.is_some() { Some(idx) } else { None }
            },
        )
    }

    pub fn iter(&self) -> impl Iterator<Item = (usize, &Node)> + '_ {
        self.data
            .iter()
            .enumerate()
            .filter_map(|(idx, e)| e.as_ref().and_then(|e| Some((idx, e))))
    }

    pub fn remove(&mut self, idx: usize) {
        self.data[idx] = None;
    }

    pub fn insert(&mut self, idx: usize, value: Node) {
        if idx >= self.data.len() {
            self.data.resize(idx + 1, None);
        }
        self.data[idx] = Some(value);
    }

    pub fn contains_key(&self, idx: usize) -> bool {
        self.data.get(idx).is_some_and(|v| v.is_some())
    }
}

#[derive(Debug)]
struct Renderer {
    url: String,
    pub nodes_idxs: Vec<usize>,
    pub nodes: NodesTable,
    node_styles: HashMap<usize, Style>,
    layout_table: HashMap<usize, LayoutBox>,
    node_layout_mapping: HashMap<usize, usize>,
    containing_nodes: HashMap<usize, ContainingNode>,
    request_cache: HashMap<ReqwestUrl, RequestCacheEntry>,
    pending_image_fetches: HashSet<ReqwestUrl>,
    rendered_nodes_ordered: Vec<RenderedNode>,
    pub hovering: Option<usize>,
    pub focusable: Option<usize>,
    tokio: Rc<RefCell<tokio::runtime::Runtime>>,
    resolved_font_sizes: HashMap<usize, u32>,
    resolved_pixmaps: HashMap<String, tiny_skia::Pixmap>,
    window_size: PhysicalSize<u32>,
    font_handler: Rc<FontHandler>,
    pending_dom_update: bool,
    event_loop_notify: Rc<tokio::sync::Notify>,
    scroll_y: HashMap<usize, i32>,
    layout_roots: Vec<usize>,
    resolved_specified_heights: HashMap<usize, Option<u32>>,
    resolved_specified_widths: HashMap<usize, Option<u32>>,
    resolved_content_sizes: HashMap<usize, OptionalSize>,
    resolved_heights: HashMap<usize, u32>,
    resolved_widths: HashMap<usize, u32>,
    dom_indexes: DomIndexes,
    canvas_buffers: HashMap<usize, CanvasBuffer>,
    pending_canvas_update: bool,
    network_fetch: Rc<RefCell<NetworkFetch>>,
    cached_rasterizations: CachedRasterizations,
    animations: Vec<Animation>,
    cached_text_buffers: HashMap<(String, u32, Option<u32>, Option<u32>, u32), (Pixmap, u32, u32)>,
    css_parse_cache: HashMap<ExpandableCssNode, Vec<CssNode>>,
    flattened_css_cache: Option<(String, Vec<ExpandableCssNode>, Vec<CssNode>)>,
    variable_definitions: VariableDefinitions,
    event_loop_proxy: Option<RendererProxy>,
    hovering_impact: HashSet<usize>,
    frames: HashMap<usize, FrameHandle>,
    css_parser: CssParser,
    workers: HashMap<String, WorkerHandle>,
    tracking_intersection: Vec<usize>,
    nodes_intersecting: HashSet<usize>,
    blob_store: Arc<BlobStore>,
    images_nodes_loaded: HashMap<usize, (u32, u32)>,
}

#[derive(Debug, Clone)]
struct WorkerHandle {}

#[derive(Debug, Clone)]
struct FlexItem {
    node_idx: usize,
    target_size: f32,
    base_size: f32,
    main_margin: i32,
    max_size: f32,
    cross_size: f32,
    max_cross_size: f32,
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
enum SizeDependentStaticOffset {
    CenterY(u32),
    EndY(u32),
}

#[derive(Debug, Clone, Copy)]
struct StaticPositionOffset {
    offset: Position,
    size_dependent_offset: Option<SizeDependentStaticOffset>,
}

#[derive(Debug, Clone, Copy)]
struct ResumableNode {
    node_idx: usize,
    static_position_offset: Option<StaticPositionOffset>,
}

#[derive(Debug, Clone)]
struct ContainingNode {
    node_idx: usize,
    cursor: Position,
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
    has_specified_height: bool,
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

    pub fn image_placeholder_size(&self, max_width: u32, max_height: u32) -> (u32, u32) {
        let (height, width) = match (
            self.container_height_non_filling,
            self.container_width_non_filling,
        ) {
            (Some(height), Some(width)) => (height, width),
            (Some(height), None) => (height, height.saturating_mul(2)),
            (None, Some(width)) => (width / 2, width),
            (None, None) => (150, 300),
        };
        (
            height.max(self.min_height.unwrap_or(0)).min(max_height),
            width.max(self.min_width.unwrap_or(0)).min(max_width),
        )
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
            let positioning_width = if style.position == StylePosition::Fixed {
                renderer.window_size.width
            } else {
                width
            };
            let positioning_height = if style.position == StylePosition::Fixed {
                renderer.window_size.height
            } else {
                height
            };
            let available_size = Size {
                width: positioning_width,
                height: positioning_height,
            };
            let resolved_parent_font_size = renderer.get_parent_font_size(waiter.node_idx);
            let font_size = get_specified_size(
                resolved_parent_font_size,
                &style.font_size,
                Some(resolved_parent_font_size),
                None,
                &renderer.window_size,
                &SizeUnit::Px,
            )
            .with_context(|| "Failed to get specific size")? as u32;
            renderer
                .resolved_font_sizes
                .insert(waiter.node_idx, font_size as u32);
            let top = get_specified_size(
                font_size,
                &style.top,
                Some(positioning_height),
                None,
                &renderer.window_size,
                &SizeUnit::Px,
            );
            let right = get_specified_size(
                font_size,
                &style.right,
                Some(positioning_width),
                None,
                &renderer.window_size,
                &SizeUnit::Px,
            );
            let bottom = get_specified_size(
                font_size,
                &style.bottom,
                Some(positioning_height),
                None,
                &renderer.window_size,
                &SizeUnit::Px,
            );
            let left = get_specified_size(
                font_size,
                &style.left,
                Some(positioning_width),
                None,
                &renderer.window_size,
                &SizeUnit::Px,
            );
            let auto_left = left.is_none() && right.is_none();
            let auto_top = top.is_none() && bottom.is_none();
            let static_position_offset = (style.position == StylePosition::Absolute)
                .then_some(waiter.static_position_offset)
                .flatten();
            let static_offset = static_position_offset
                .map(|position| position.offset)
                .unwrap_or(Position { x: 0, y: 0 });
            let cursor = if style.position == StylePosition::Fixed {
                Position { x: 0, y: 0 }
            } else {
                Position {
                    x: self.cursor.x + if auto_left { static_offset.x } else { 0 },
                    y: self.cursor.y + if auto_top { static_offset.y } else { 0 },
                }
            };

            let margin_right = get_specified_size(
                font_size,
                &style.margin_right,
                Some(positioning_width),
                None,
                &renderer.window_size,
                &SizeUnit::Px,
            );
            let margin_left = get_specified_size(
                font_size,
                &style.margin_left,
                Some(positioning_width),
                None,
                &renderer.window_size,
                &SizeUnit::Px,
            );

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
                cursor,
                available_size,
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

                    if auto_top
                        && let Some(size_dependent_offset) =
                            static_position_offset.and_then(|offset| offset.size_dependent_offset)
                    {
                        let (_, _, margin_top, margin_bottom) =
                            renderer.get_margins(waiter.node_idx, &style, available_size);
                        let margin_y = (margin_top + margin_bottom).max(0) as u32;
                        let used_height = waiter_layout_box.rect.height.saturating_add(margin_y);
                        let offset_y = match size_dependent_offset {
                            SizeDependentStaticOffset::CenterY(available) => {
                                available.saturating_sub(used_height) / 2
                            }
                            SizeDependentStaticOffset::EndY(available) => {
                                available.saturating_sub(used_height)
                            }
                        };
                        renderer.move_entire_box(
                            layout_idx,
                            0,
                            offset_y as i32 + margin_top.max(0),
                        );
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

                children.push(layout_idx);
            }
        }
        self.waiters.clear();
        Ok(())
    }
}

enum SizeUnit {
    Px,
    Em,
}

fn get_specified_size(
    font_size: u32,
    value: &StyleSize,
    available_size: Option<u32>,
    auto_size: Option<i32>,
    window_size: &PhysicalSize<u32>,
    default_unit: &SizeUnit,
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
            let min = get_specified_size(
                font_size,
                min,
                available_size,
                auto_size,
                window_size,
                default_unit,
            )?;
            let value = get_specified_size(
                font_size,
                value,
                available_size,
                auto_size,
                window_size,
                default_unit,
            )?;
            let max = get_specified_size(
                font_size,
                max,
                available_size,
                auto_size,
                window_size,
                default_unit,
            )?;
            Some(value.min(max).max(min))
        }
        StyleSize::Calc(calc) => solve_calc(
            calc,
            font_size,
            available_size,
            auto_size,
            window_size,
            default_unit,
        ),
        StyleSize::Em(em) => Some(unit_to_px(*em, &SizeUnit::Em, font_size) as i32),
        // TODO: This should actually be the font-size of the root element, so figure that out
        StyleSize::Rem(rem) => Some((*rem * 16 as f32) as i32),
        StyleSize::FitContent | StyleSize::MinContent | StyleSize::MaxContent => None,
    }
}

fn get_calc_exp_value(
    exp: &CalcExpression,
    font_size: u32,
    available_size: Option<u32>,
    auto_size: Option<i32>,
    window_size: &PhysicalSize<u32>,
    default_unit: &SizeUnit,
) -> Option<i32> {
    match exp {
        CalcExpression::Size(size) => get_specified_size(
            font_size,
            &size,
            available_size,
            auto_size,
            window_size,
            default_unit,
        ),
        CalcExpression::Nesting(nesting) => solve_calc(
            nesting,
            font_size,
            available_size,
            auto_size,
            window_size,
            default_unit,
        ),
        CalcExpression::Solved(value) => Some(*value as i32),
        _ => panic!("Expected calc expression to be value"),
    }
}

fn solve_calc(
    calc: &Vec<CalcExpression>,
    font_size: u32,
    available_size: Option<u32>,
    auto_size: Option<i32>,
    window_size: &PhysicalSize<u32>,
    default_unit: &SizeUnit,
) -> Option<i32> {
    let mut calc = calc.clone();
    let has_unit = calc.iter().any(|c| matches!(c, CalcExpression::Size(..)));
    while calc.len() > 1 {
        let exp = calc
            .iter()
            .position(|exp| {
                matches!(
                    exp,
                    CalcExpression::Operator(
                        StyleCalcOperator::Multiply | StyleCalcOperator::Divide
                    )
                )
            })
            .or_else(|| {
                calc.iter().position(|exp| {
                    matches!(
                        exp,
                        CalcExpression::Operator(
                            StyleCalcOperator::Plus | StyleCalcOperator::Minus
                        )
                    )
                })
            });

        if let Some(exp) = exp
            && exp > 0
            && exp < calc.len() - 1
        {
            let prev = &calc[exp - 1];
            let curr = &calc[exp];
            let next = &calc[exp + 1];

            let prev_value = get_calc_exp_value(
                prev,
                font_size,
                available_size,
                auto_size,
                window_size,
                default_unit,
            )?;
            let next_value = get_calc_exp_value(
                next,
                font_size,
                available_size,
                auto_size,
                window_size,
                default_unit,
            )?;

            let CalcExpression::Operator(operator) = curr else {
                unreachable!();
            };

            let value = match operator {
                StyleCalcOperator::Plus => prev_value + next_value,
                StyleCalcOperator::Minus => prev_value - next_value,
                StyleCalcOperator::Divide => prev_value / next_value.max(1),
                StyleCalcOperator::Multiply => prev_value * next_value,
            };

            calc.splice(exp - 1..=exp + 1, [CalcExpression::Solved(value as f32)]);
        } else {
            break;
        }
    }

    let mut value = if calc.len() == 1
        && let CalcExpression::Solved(value) = calc[0]
    {
        Some(value as i32)
    } else if calc.len() == 1
        && let CalcExpression::Size(StyleSize::Px(size)) = calc[0]
    {
        Some(size as i32)
    } else {
        None
    };

    if !has_unit && let Some(inner) = &mut value {
        *inner = unit_to_px(*inner as f32, default_unit, font_size) as i32;
    }

    value
}

fn unit_to_px(value: f32, unit: &SizeUnit, font_size: u32) -> f32 {
    match unit {
        SizeUnit::Px => value,
        SizeUnit::Em => value * font_size as f32,
    }
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
    let da = dst & 0xFF;

    let r = src.0 as u32 + (dr * inv_a + 127) / 255;
    let g = src.1 as u32 + (dg * inv_a + 127) / 255;
    let b = src.2 as u32 + (db * inv_a + 127) / 255;

    let output_alpha = a + (da * inv_a + 127) / 255;

    (r << 24) | (g << 16) | (b << 8) | output_alpha
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
    max_w: Option<u32>,
    max_h: Option<u32>,
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
        opt.style_sheet = Some(
            format!(
                "svg {{ color: #{:08X} !important; fill: currentColor }}",
                color_hex
            )
            .into(),
        );

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
    if let Some(max_h) = max_h {
        (target_h, target_w) = clamp_with_ratio(target_h, max_h, target_w);
    }
    if let Some(max_w) = max_w {
        (target_w, target_h) = clamp_with_ratio(target_w, max_w, target_h);
    }

    let key = (svg_str.clone(), color_hex, target_h, target_w);
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
    src: &str,
    bytes: &[u8],
    input_w: Option<u32>,
    input_h: Option<u32>,
    max_w: Option<u32>,
    max_h: Option<u32>,
    mode: &LayoutMode,
) -> Result<(tiny_skia::Pixmap, u32, u32, bool)> {
    let pixmap = if let Some(cached) = cached_rasterizations.decoded_pngs.get(src) {
        cached
    } else {
        cached_rasterizations
            .decoded_pngs
            .insert(src.to_string(), tiny_skia::Pixmap::decode_png(bytes)?);
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
    if let Some(max_h) = max_h {
        (target_h, target_w) = clamp_with_ratio(target_h, max_h, target_w);
    }
    if let Some(max_w) = max_w {
        (target_w, target_h) = clamp_with_ratio(target_w, max_w, target_h);
    }

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
    src: &str,
    bytes: &[u8],
    input_w: Option<u32>,
    input_h: Option<u32>,
    max_w: Option<u32>,
    max_h: Option<u32>,
) -> Result<(u32, u32)> {
    let result = if let Some(cached) = cached_rasterizations.decoded_jpegs.get(src) {
        cached
    } else {
        let mut reader = ImageReader::new(Cursor::new(bytes));
        reader.set_format(image::ImageFormat::Jpeg);
        cached_rasterizations
            .decoded_jpegs
            .insert(src.to_string(), reader.decode()?);
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
    if let Some(max_h) = max_h {
        (target_h, target_w) = clamp_with_ratio(target_h, max_h, target_w);
    }
    if let Some(max_w) = max_w {
        (target_w, target_h) = clamp_with_ratio(target_w, max_w, target_h);
    }

    Ok((target_h, target_w))
}

fn rasterize_jpeg(
    cached_rasterizations: &mut CachedRasterizations,
    src: &str,
    target_w: u32,
    target_h: u32,
) -> Result<tiny_skia::Pixmap> {
    let decoded = cached_rasterizations.decoded_jpegs.get(src).unwrap();
    let key = (src.to_string(), target_h, target_w);
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

fn prepare_gif(
    cached_rasterizations: &mut CachedRasterizations,
    src: &str,
    bytes: &[u8],
    input_w: Option<u32>,
    input_h: Option<u32>,
    max_w: Option<u32>,
    max_h: Option<u32>,
) -> Result<(u32, u32)> {
    let result = if let Some(cached) = cached_rasterizations.decoded_gifs.get(src) {
        cached
    } else {
        let mut reader = ImageReader::new(Cursor::new(bytes));
        reader.set_format(image::ImageFormat::Gif);
        cached_rasterizations
            .decoded_gifs
            .insert(src.to_string(), reader.decode()?);
        cached_rasterizations.decoded_gifs.get(src).unwrap()
    };

    let (mut target_h, mut target_w) = infer_image_size(
        Size {
            height: result.height(),
            width: result.width(),
        },
        input_w,
        input_h,
    );
    if let Some(max_h) = max_h {
        (target_h, target_w) = clamp_with_ratio(target_h, max_h, target_w);
    }
    if let Some(max_w) = max_w {
        (target_w, target_h) = clamp_with_ratio(target_w, max_w, target_h);
    }

    Ok((target_h, target_w))
}

fn rasterize_gif(
    cached_rasterizations: &mut CachedRasterizations,
    src: &str,
    target_w: u32,
    target_h: u32,
) -> Result<tiny_skia::Pixmap> {
    let decoded = cached_rasterizations.decoded_gifs.get(src).unwrap();
    let key = (src.to_string(), target_h, target_w);
    let pixmap = if let Some(cached) = cached_rasterizations.gifs.get(&key) {
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
        cached_rasterizations.gifs.insert(key.clone(), value);
        cached_rasterizations.gifs.get(&key).unwrap()
    };

    Ok(pixmap.clone())
}

fn prepare_webp(
    cached_rasterizations: &mut CachedRasterizations,
    src: &str,
    bytes: &[u8],
    input_w: Option<u32>,
    input_h: Option<u32>,
    max_w: Option<u32>,
    max_h: Option<u32>,
) -> Result<(u32, u32)> {
    let result = if let Some(cached) = cached_rasterizations.decoded_webps.get(src) {
        cached
    } else {
        let mut reader = ImageReader::new(Cursor::new(bytes));
        reader.set_format(image::ImageFormat::WebP);
        cached_rasterizations
            .decoded_webps
            .insert(src.to_string(), reader.decode()?);
        cached_rasterizations.decoded_webps.get(src).unwrap()
    };

    let (mut target_h, mut target_w) = infer_image_size(
        Size {
            height: result.height(),
            width: result.width(),
        },
        input_w,
        input_h,
    );
    if let Some(max_h) = max_h {
        (target_h, target_w) = clamp_with_ratio(target_h, max_h, target_w);
    }
    if let Some(max_w) = max_w {
        (target_w, target_h) = clamp_with_ratio(target_w, max_w, target_h);
    }

    Ok((target_h, target_w))
}

fn rasterize_webp(
    cached_rasterizations: &mut CachedRasterizations,
    src: &str,
    target_w: u32,
    target_h: u32,
) -> Result<tiny_skia::Pixmap> {
    let decoded = cached_rasterizations.decoded_webps.get(src).unwrap();
    let key = (src.to_string(), target_h, target_w);
    let pixmap = if let Some(cached) = cached_rasterizations.webps.get(&key) {
        cached
    } else {
        let result =
            decoded.resize_exact(target_w, target_h, image::imageops::FilterType::Triangle);
        let mut rgba = result.to_rgba8().into_raw();
        for pixel in rgba.chunks_exact_mut(4) {
            let alpha = pixel[3] as u16;
            pixel[0] = ((pixel[0] as u16 * alpha + 127) / 255) as u8;
            pixel[1] = ((pixel[1] as u16 * alpha + 127) / 255) as u8;
            pixel[2] = ((pixel[2] as u16 * alpha + 127) / 255) as u8;
        }

        let value = Pixmap::from_vec(
            rgba,
            IntSize::from_wh(target_w, target_h).context("Failed to create WebP image size")?,
        )
        .context("Failed to convert WebP to pixmap")?;
        cached_rasterizations.webps.insert(key.clone(), value);
        cached_rasterizations.webps.get(&key).unwrap()
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
    nodes: &NodesTable,
    children_index: &HashMap<usize, Vec<usize>>,
    idx: usize,
) {
    let Some(Node::Element(element)) = nodes.get(idx) else {
        return;
    };
    if element.tag == "style" {
        let children = &children_index.get(&idx).unwrap();
        if children.len() != 1 {
            println!("Unexpected children count: {}", children.len());
            return;
        }
        let child = children.first().unwrap();
        let child_node = &nodes.get(*child).unwrap();
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
        && let Some(href) = element.attributes.get_str("href")
        && element.attributes.get_str("rel").is_some_and(|v| {
            let rels: Vec<&str> = v.split(" ").collect();
            rels.contains(&"stylesheet")
        })
    {
        expandable.push(ExpandableCssNode::Link(href.into_owned()));
    } else if element.tag != "noscript" {
        let children = &children_index.get(&idx).unwrap();
        for child in children.iter() {
            get_expandable_css_nodes_walk(expandable, nodes, children_index, *child);
        }
    }
}

fn get_expandable_css_nodes(
    nodes: &NodesTable,
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
    nodes: &NodesTable,
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
    ancestor_hidden: bool,
) {
    // Keep cached descendants until their hidden ancestor can render again.
    if ancestor_hidden && node_styles.contains_key(&node_idx) {
        return;
    }
    let parent_style = parent_style.and_then(|idx| Some(node_styles.get(&idx).unwrap()));
    let node = &nodes.get(node_idx).unwrap();
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
        &SizeUnit::Px,
    )
    .unwrap_or_else(|| {
        println!("Failed to get font size for node idx {}", node_idx);
        16
    });
    resolved_font_sizes.insert(node_idx, resolved_font_size as u32);

    // Set to resolved size in px so that ems dont stack on top of each other
    style.font_size = StyleSize::Px(resolved_font_size as f32);

    let subtree_hidden = ancestor_hidden || style.display == StyleDisplay::None;
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
            subtree_hidden,
        );
    }
}

fn parse_css_nodes(parser: &mut CssParser, css_nodes: &Vec<String>) -> Result<()> {
    let joined = css_nodes.join("\n");
    parser.parse(joined.as_str())?;
    Ok(())
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
    html_nodes: &NodesTable,
    css_nodes: &Vec<(usize, &CssNode)>,
    class_elements: &Vec<FixedBitSet>,
    css_node: &CssNode,
    window_size: &PhysicalSize<u32>,
    require_immediate_match: bool,
    walk_up_parent: bool,
    dom_indexes: &DomIndexes,
    hovering_chain: &Vec<usize>,
    hovering_has_impact: &mut HashSet<usize>,
    precomputed_selectors: &Vec<FixedBitSet>,
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
                        precomputed_selectors,
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
                precomputed_selectors,
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
    html_nodes: &NodesTable,
    class_elements: &Vec<FixedBitSet>,
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
    precomputed_selectors: &Vec<FixedBitSet>,
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
            precomputed_selectors,
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
                precomputed_selectors,
            );
        } else {
            return false;
        }
    }
}

fn walk_for_html_match<F>(
    mut element: usize,
    html_nodes: &NodesTable,
    match_fn: &mut F,
    mut quota: Option<i32>,
) -> Option<usize>
where
    F: FnMut(usize) -> bool,
{
    loop {
        // If we're not allowed to walk anymore, give up
        if quota.is_some_and(|quota| quota == 0) {
            return None;
        }
        if match_fn(element) {
            return Some(element);
        }
        if let Some(parent) = html_nodes.get(element).unwrap().get_parent() {
            element = parent;
            quota = quota.map(|quota| quota - 1);
        } else {
            return None;
        }
    }
}

#[inline(never)]
fn class_name_part_match_class<T>(f: impl FnOnce() -> T) -> T {
    f()
}

#[inline(never)]
fn class_name_part_match_id<T>(f: impl FnOnce() -> T) -> T {
    f()
}

#[inline(never)]
fn class_name_part_match_pseudo<T>(f: impl FnOnce() -> T) -> T {
    f()
}

#[inline(never)]
fn class_name_part_match_tag<T>(f: impl FnOnce() -> T) -> T {
    f()
}

#[inline(never)]
fn class_name_part_match_attributes<T>(f: impl FnOnce() -> T) -> T {
    f()
}

#[inline(never)]
fn class_name_part_match_combined<T>(f: impl FnOnce() -> T) -> T {
    f()
}

fn element_matches_class_part(
    part: &ClassNamePart,
    element: usize,
    html_nodes: &NodesTable,
    class_elements: &Vec<FixedBitSet>,
    dom_indexes: &DomIndexes,
    hovering_chain: &Vec<usize>,
    hovering_has_impact: &mut HashSet<usize>,
    precomputed_selectors: &Vec<FixedBitSet>,
) -> bool {
    match part {
        ClassNamePart::Class(class) => class_name_part_match_class(|| {
            if let Some(elements_to_keep) = class_elements.get(*class) {
                elements_to_keep.contains(element)
            } else {
                false
            }
        }),
        ClassNamePart::Id(id) => {
            class_name_part_match_id(|| match html_nodes.get(element).unwrap() {
                Node::Element(walk_element) => walk_element
                    .attributes
                    .get_str("id")
                    .is_some_and(|el_id| el_id.as_ref() == id),
                _ => false,
            })
        }
        ClassNamePart::ArrowRight
        | ClassNamePart::Ampersand
        | ClassNamePart::Tilde
        | ClassNamePart::AdjacentSibling => true,
        ClassNamePart::PseudoClass(class) => class_name_part_match_pseudo(|| {
            match class {
                // All elements are children of root
                PseudoClass::Root => true,
                PseudoClass::IndexedNot(selector) => {
                    let negative_matches = &precomputed_selectors[*selector];
                    !negative_matches.contains(element)
                }
                PseudoClass::IndexedIs(selectors) | PseudoClass::IndexedWhere(selectors) => {
                    selectors.iter().any(|selector| {
                        precomputed_selectors[*selector].contains(element)
                    })
                }
                PseudoClass::Not(_)
                | PseudoClass::Is(_)
                | PseudoClass::Where(_) => unreachable!("selectors must be indexed before matching"),
                PseudoClass::Hover => {
                    hovering_has_impact.insert(element);
                    hovering_chain.contains(&element)
                }
                PseudoClass::FirstChild => html_nodes
                    .get(element)
                    .and_then(|node| node.get_parent())
                    .and_then(|parent| dom_indexes.children_index.get(&parent))
                    .is_some_and(|siblings| siblings.first().is_some_and(|idx| *idx == element)),
                PseudoClass::NthChild(n) => n.parse::<usize>().ok().is_some_and(|target| {
                    html_nodes
                        .get(element)
                        .and_then(|node| node.get_parent())
                        .and_then(|parent| dom_indexes.children_index.get(&parent))
                        .and_then(|siblings| siblings.iter().position(|idx| *idx == element))
                        .is_some_and(|pos| pos + 1 == target)
                }),
                PseudoClass::FirstOfType => html_nodes.get(element).is_some_and(|node| {
                    let Node::Element(element_node) = node else {
                        return false;
                    };
                    node.get_parent()
                        .and_then(|parent| dom_indexes.children_index.get(&parent))
                        .and_then(|siblings| {
                            siblings.iter().find(|idx| {
                                matches!(html_nodes.get(**idx), Some(Node::Element(sibling)) if sibling.tag == element_node.tag)
                            })
                        })
                        .is_some_and(|idx| *idx == element)
                }),
                PseudoClass::NthOfType(n) => n.parse::<usize>().ok().is_some_and(|target| {
                    let Some(Node::Element(element_node)) = html_nodes.get(element) else {
                        return false;
                    };
                    html_nodes
                        .get(element)
                        .and_then(|node| node.get_parent())
                        .and_then(|parent| dom_indexes.children_index.get(&parent))
                        .and_then(|siblings| {
                            siblings
                                .iter()
                                .filter(|idx| {
                                    matches!(html_nodes.get(**idx), Some(Node::Element(sibling)) if sibling.tag == element_node.tag)
                                })
                                .position(|idx| *idx == element)
                        })
                        .is_some_and(|pos| pos + 1 == target)
                }),
                PseudoClass::NthLastChild(n) => n.parse::<usize>().ok().is_some_and(|target| {
                    html_nodes
                        .get(element)
                        .and_then(|node| node.get_parent())
                        .and_then(|parent| dom_indexes.children_index.get(&parent))
                        .and_then(|siblings| siblings.iter().rev().position(|idx| *idx == element))
                        .is_some_and(|pos| pos + 1 == target)
                }),
                PseudoClass::LastChild => html_nodes
                    .get(element)
                    .and_then(|node| node.get_parent())
                    .and_then(|parent| dom_indexes.children_index.get(&parent))
                    .is_some_and(|siblings| siblings.last().is_some_and(|idx| *idx == element)),
                PseudoClass::OnlyChild => html_nodes
                    .get(element)
                    .and_then(|node| node.get_parent())
                    .and_then(|parent| dom_indexes.children_index.get(&parent))
                    .is_some_and(|siblings| siblings.len() == 1 && siblings[0] == element),
                PseudoClass::Empty => dom_indexes
                    .children_index
                    .get(&element)
                    .is_none_or(|children| children.is_empty()),
                PseudoClass::Link => match html_nodes.get(element).unwrap() {
                    Node::Element(el) => el.tag == "a" && el.attributes.contains_key("href"),
                    _ => false,
                },
                PseudoClass::Visited => false,
                PseudoClass::Disabled => match html_nodes.get(element).unwrap() {
                    Node::Element(el) => el.attributes.contains_key("disabled"),
                    _ => false,
                },
                PseudoClass::Checked => match html_nodes.get(element).unwrap() {
                    Node::Element(el) => el.attributes.contains_key("checked"),
                    _ => false,
                },
                PseudoClass::Lang(target) => {
                    let lang = walk_for_html_match(
                        element,
                        html_nodes,
                        &mut |idx| match html_nodes.get(idx).unwrap() {
                            Node::Element(el) => el.attributes.contains_key("lang"),
                            _ => false,
                        },
                        None,
                    )
                    .and_then(|idx| match html_nodes.get(idx).unwrap() {
                        Node::Element(el) => el.attributes.get_str("lang"),
                        _ => None,
                    });
                    lang.is_some_and(|lang| {
                        lang.eq_ignore_ascii_case(target)
                            || lang
                                .strip_prefix(target)
                                .is_some_and(|rest| rest.starts_with('-'))
                    })
                }
                _ => false,
            }
        }),
        ClassNamePart::Tag(tag) => {
            class_name_part_match_tag(|| match html_nodes.get(element).unwrap() {
                Node::Element(walk_element) => tag == "*" || walk_element.tag == *tag,
                _ => false,
            })
        }
        ClassNamePart::Attributes(attributes) => {
            class_name_part_match_attributes(|| match html_nodes.get(element).unwrap() {
                Node::Element(walk_element) => element_matched_attributes(walk_element, attributes),
                _ => false,
            })
        }
        ClassNamePart::Combined(combined) => class_name_part_match_combined(|| {
            combined.iter().all(|part| {
                element_matches_class_part(
                    part,
                    element,
                    html_nodes,
                    class_elements,
                    dom_indexes,
                    hovering_chain,
                    hovering_has_impact,
                    precomputed_selectors,
                )
            })
        }),
    }
}

fn narrow_elements_by_ancestors(
    element: usize,
    css_nodes: &Vec<(usize, &CssNode)>,
    html_nodes: &NodesTable,
    class_elements: &Vec<FixedBitSet>,
    css_node: usize,
    name_part_idx: usize,
    nested_part_idx: usize,
    window_size: &PhysicalSize<u32>,
    require_immediate_match: bool,
    dom_indexes: &DomIndexes,
    hovering_chain: &Vec<usize>,
    hovering_has_impact: &mut HashSet<usize>,
    precomputed_selectors: &Vec<FixedBitSet>,
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
            if let ClassNamePart::AdjacentSibling = part {
                let Some(parent) = html_nodes.get(element).and_then(|v| v.get_parent()) else {
                    return false;
                };
                let Some(siblings) = dom_indexes.children_index.get(&parent) else {
                    return false;
                };
                let Some(pos) = siblings.iter().position(|sibling| *sibling == element) else {
                    return false;
                };
                let Some(previous_element) = siblings[..pos].iter().rev().find(|sibling_idx| {
                    matches!(html_nodes.get(**sibling_idx), Some(Node::Element(_)))
                }) else {
                    return false;
                };
                return move_up_class_part(
                    *previous_element,
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
                    precomputed_selectors,
                );
            }
            if let ClassNamePart::Tilde = part {
                let Some(parent) = html_nodes.get(element).and_then(|v| v.get_parent()) else {
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
                    .filter(|idx| *idx.1 != element && html_nodes.contains_key(*idx.1))
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
                                precomputed_selectors,
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
                        precomputed_selectors,
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
                ClassNamePart::AdjacentSibling => (false, false),
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
                    precomputed_selectors,
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
                    precomputed_selectors,
                );
            } else {
                return false;
            }
        }
        // Layers and supports always pass through, they just affect sorting
        CssNode::Layer(_) | CssNode::Supports(_) => {
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
                precomputed_selectors,
            );
        }
        _ => {
            return false;
        }
    };
}

fn get_parent_html_idx(node_idx: usize, html_nodes: &NodesTable) -> Option<usize> {
    html_nodes.get(node_idx).unwrap().get_parent()
}

// Wrapper around search_elements_for_css_nodes that narrows the css_nodes down to only nodes that have property/variable children
// Query selectors skip this step
fn collect_class_nodes_for_elements(
    css_nodes: &mut Vec<CssNode>,
    raw_html_nodes: &NodesTable,
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
    for (idx, n) in css_nodes.iter().enumerate() {
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
        raw_html_nodes,
        window_size,
        dom_indexes,
        hovering_chain,
    )
}

fn filter_to_elements(html_nodes: &NodesTable) -> Vec<usize> {
    html_nodes
        .iter()
        .filter(|(_, value)| matches!(value, Node::Element(_)))
        .map(|(key, _)| key)
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
            ClassNamePart::Tag(tag) if tag != "*" => tuple[2] += 1,
            ClassNamePart::Tag(_) => {}
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

#[inline(never)]
fn get_base_elements_by_attributes(
    html_nodes: &NodesTable,
    dom_indexes: &DomIndexes,
    attributes: &Vec<ClassNamePartAttribute>,
) -> FixedBitSet {
    let mut base_items = FixedBitSet::with_capacity(html_nodes.keys().max().unwrap_or(0));
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
            ClassNamePartAttribute::KeyValue((key, _, _, _)) => {
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
        .filter(|idx| match html_nodes.get(*idx).unwrap() {
            Node::Element(element) => element_matched_attributes(element, attributes),
            _ => false,
        })
        .collect();
    filtered_elements
}

fn walk_into_part(part: &ClassNamePart) -> bool {
    !matches!(part, ClassNamePart::Tilde | ClassNamePart::AdjacentSibling)
}

fn selector_index(
    selectors: &mut Vec<Vec<ClassNamePart>>,
    selector_indexes: &mut HashMap<Vec<ClassNamePart>, usize>,
    selector: &Vec<ClassNamePart>,
) -> usize {
    if let Some(idx) = selector_indexes.get(selector) {
        *idx
    } else {
        let idx = selectors.len();
        selector_indexes.insert(selector.clone(), idx);
        selectors.push(selector.clone());
        idx
    }
}

fn walk_selectors(
    selectors: &mut Vec<Vec<ClassNamePart>>,
    selector_indexes: &mut HashMap<Vec<ClassNamePart>, usize>,
    part: &mut ClassNamePart,
) {
    match part {
        ClassNamePart::PseudoClass(pseudo_class) => match pseudo_class {
            PseudoClass::Is(nested_selectors) => {
                let mut indexes = vec![];
                for selector in nested_selectors {
                    indexes.push(selector_index(selectors, selector_indexes, selector));
                    for part in selector {
                        walk_selectors(selectors, selector_indexes, part);
                    }
                }
                *pseudo_class = PseudoClass::IndexedIs(indexes);
            }
            // TODO: Consider whether this needs to be a vector of selectors instead
            PseudoClass::Not(selector) => {
                let index = selector_index(selectors, selector_indexes, selector);
                for part in selector {
                    walk_selectors(selectors, selector_indexes, part);
                }
                *pseudo_class = PseudoClass::IndexedNot(index);
            }
            PseudoClass::Where(nested_selectors) => {
                let mut indexes = vec![];
                for selector in nested_selectors {
                    indexes.push(selector_index(selectors, selector_indexes, selector));
                    for part in selector {
                        walk_selectors(selectors, selector_indexes, part);
                    }
                }
                *pseudo_class = PseudoClass::IndexedWhere(indexes);
            }
            _ => {}
        },
        ClassNamePart::Combined(combined) => {
            for part in combined {
                walk_selectors(selectors, selector_indexes, part);
            }
        }
        _ => {}
    }
}

fn search_elements_for_css_nodes(
    to_resolve: HashSet<usize>,
    css_nodes: &mut Vec<CssNode>,
    html_nodes: &NodesTable,
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

    let mut unique_selectors = vec![];
    let mut selector_indexes = HashMap::new();
    for node in css_nodes.iter_mut() {
        match node {
            CssNode::ClassName(class) => {
                for selector in &mut class.name_parts {
                    for part in selector {
                        walk_selectors(&mut unique_selectors, &mut selector_indexes, part);
                    }
                }
            }
            _ => {}
        }
    }
    let element_indexes = filter_to_elements(html_nodes);
    let max_element_idx = element_indexes
        .iter()
        .max()
        .cloned()
        .map(|v| v + 1)
        .unwrap_or(0);

    let mut precomputed_selectors: Vec<FixedBitSet> = vec![];
    for selector in &unique_selectors {
        let mut results = FixedBitSet::with_capacity(max_element_idx);
        for idx in query_selector_all(
            html_nodes,
            selector.clone(),
            &PhysicalSize {
                width: 0,
                height: 0,
            },
            dom_indexes,
            hovering_chain,
            None,
        ) {
            results.insert(idx);
        }
        precomputed_selectors.push(results);
    }
    let css_nodes: Vec<(usize, &CssNode)> = css_nodes.iter().enumerate().collect();
    let css_nodes = &css_nodes;

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
                        let mut bitset = FixedBitSet::with_capacity(max_element_idx);
                        for idx in element_indexes.iter().copied() {
                            bitset.insert(idx);
                        }
                        bitset
                    };

                    let elements: Option<FixedBitSet> = match last_part {
                        ClassNamePart::Class(class) => class_elements.get(*class).cloned(),
                        ClassNamePart::Id(id) => id_elements.get(id).cloned(),
                        ClassNamePart::PseudoClass(class) => {
                            match class {
                                // No parent means it's a root element
                                PseudoClass::Root => {
                                    let mut bitset = FixedBitSet::with_capacity(max_element_idx);
                                    for idx in element_indexes.iter() {
                                        if html_nodes
                                            .get(*idx)
                                            .is_some_and(|node| node.get_parent().is_none())
                                        {
                                            bitset.insert(*idx);
                                        }
                                    }
                                    Some(bitset)
                                }
                                PseudoClass::IndexedNot(selector) => {
                                    let negative_matches = &precomputed_selectors[*selector];
                                    let mut bitset = FixedBitSet::with_capacity(max_element_idx);
                                    for idx in element_indexes.iter() {
                                        if !negative_matches.contains(*idx) {
                                            bitset.insert(*idx);
                                        }
                                    }
                                    Some(bitset)
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
                            let mut base: Option<(usize, FixedBitSet, usize)> = None;
                            for (part_idx, part) in combined.iter().enumerate() {
                                let candidate = match part {
                                    ClassNamePart::Tag(tag) if tag != "*" => {
                                        tag_elements.get(tag).cloned()
                                    }
                                    ClassNamePart::Class(class) => {
                                        class_elements.get(*class).cloned()
                                    }
                                    ClassNamePart::Id(id) => id_elements.get(id).cloned(),
                                    ClassNamePart::Attributes(attributes) => {
                                        Some(get_base_elements_by_attributes(
                                            html_nodes,
                                            dom_indexes,
                                            attributes,
                                        ))
                                    }
                                    _ => None,
                                };
                                let Some(candidate) = candidate else {
                                    continue;
                                };
                                let candidate_count = candidate.count_ones(..);
                                if base
                                    .as_ref()
                                    .is_none_or(|(_, _, best)| candidate_count < *best)
                                {
                                    base = Some((part_idx, candidate, candidate_count));
                                }
                                if candidate_count == 0 {
                                    break;
                                }
                            }

                            let (base_part_idx, base_elements) = base
                                .map(|(part_idx, elements, _)| (part_idx, elements))
                                .unwrap_or_else(|| (usize::MAX, all_elements()));
                            let mut filtered_elements = FixedBitSet::with_capacity(max_element_idx);
                            for el in base_elements.ones() {
                                let matched_all =
                                    combined.iter().enumerate().all(|(part_idx, part)| {
                                        part_idx == base_part_idx
                                            || element_matches_class_part(
                                                part,
                                                el,
                                                &html_nodes,
                                                &class_elements,
                                                dom_indexes,
                                                hovering_chain,
                                                &mut hovering_has_impact,
                                                &precomputed_selectors,
                                            )
                                    });
                                if matched_all {
                                    filtered_elements.insert(el);
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
                                    &precomputed_selectors,
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
                                        &precomputed_selectors,
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
                    let elements: Vec<usize> = html_nodes
                        .iter()
                        .filter_map(|(idx, node)| match node {
                            Node::Element(_) => Some(idx),
                            _ => None,
                        })
                        .collect();

                    for el in elements {
                        // If there's only a single part, we've already completed this class name by doing the last one
                        let is_match = move_up_ancestor_chain(
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
                            &precomputed_selectors,
                        );

                        if is_match {
                            matches.entry(el).or_default().push(css_node_idx);
                        }
                    }
                }
            }
            // Layers and supports always pass through, they just affect sorting
            CssNode::Layer(_) | CssNode::Supports(_) => {
                let elements: Vec<usize> = html_nodes
                    .iter()
                    .filter_map(|(idx, node)| match node {
                        Node::Element(_) => Some(idx),
                        _ => None,
                    })
                    .collect();

                for el in elements {
                    // If there's only a single part, we've already completed this class name by doing the last one
                    let is_match = move_up_ancestor_chain(
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
                        &precomputed_selectors,
                    );

                    if is_match {
                        matches.entry(el).or_default().push(css_node_idx);
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
    raw_nodes: &[CssNode],
    class_node_specificity: &HashMap<usize, [i32; 3]>,
) -> Vec<usize> {
    let nodes: Vec<(usize, &CssNode)> = raw_nodes.into_iter().enumerate().collect();
    let node_idxs: Vec<usize> = nodes
        .iter()
        .filter(|(_, node)| matches!(node, CssNode::Property(_) | CssNode::Variable(_)))
        .map(|(idx, _)| *idx)
        .collect();
    let mut chains = vec![Vec::new(); raw_nodes.len()];
    let mut important_scores = vec![0; raw_nodes.len()];
    let mut parent_layers = vec![None; raw_nodes.len()];
    let mut specificities = vec![[0; 3]; raw_nodes.len()];

    for idx in node_idxs.iter().copied() {
        get_parent_chain(&nodes, idx, &mut chains[idx]);

        important_scores[idx] = match nodes[idx].1 {
            CssNode::Property(property) => property.important as i32,
            _ => 0i32,
        };
        parent_layers[idx] = get_parent_layer(&nodes, idx);
        if let Some(specificity) = chains[idx]
            .get(1)
            .and_then(|parent| class_node_specificity.get(parent))
        {
            specificities[idx] = *specificity;
        }
    }

    let mut sorted_idxs = node_idxs;
    sorted_idxs.sort_unstable_by(|a, b| {
        match important_scores[*a].cmp(&important_scores[*b]) {
            Ordering::Equal => {
                let layer_ordering = match (parent_layers[*a], parent_layers[*b]) {
                    (Some(a), Some(b)) => a.cmp(&b),
                    (None, Some(_)) => Ordering::Greater,
                    (Some(_), None) => Ordering::Less,
                    (None, None) => Ordering::Equal,
                };

                if layer_ordering != Ordering::Equal {
                    // TODO: Might want to flip this if both nodes have !important
                    return layer_ordering;
                }

                let specificity_order =
                    get_specificity_order(&specificities[*a], &specificities[*b]);

                match specificity_order {
                    Ordering::Equal => get_chain_order(&chains[*a], &chains[*b]),
                    ordering => ordering,
                }
            }
            ordering => ordering,
        }
    });
    let mut rankings = vec![0; raw_nodes.len()];
    for (ranking, idx) in sorted_idxs.into_iter().enumerate() {
        rankings[idx] = ranking;
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
    nodes: &NodesTable,
    root_indice: usize,
    dom_indexes: &DomIndexes,
    css_parse_cache: &mut HashMap<ExpandableCssNode, Vec<CssNode>>,
    flattened_css_cache: &mut Option<(String, Vec<ExpandableCssNode>, Vec<CssNode>)>,
    css_parser: &mut CssParser,
) -> Vec<CssNode> {
    let expandable = get_expandable_css_nodes(nodes, root_indice, &dom_indexes.children_index);
    if let Some((cached_base_url, cached_expandable, cached_nodes)) = flattened_css_cache
        && cached_base_url == base_url
        && cached_expandable == &expandable
    {
        return cached_nodes.clone();
    }
    let mut parsed_css_chunks = vec![];
    let mut needs_fetching = vec![];
    for (idx, exp) in expandable.iter().enumerate() {
        if let Some(cached_nodes) = css_parse_cache.get(&exp) {
            parsed_css_chunks.push((idx, cached_nodes.clone()));
        } else {
            match exp {
                ExpandableCssNode::Link(link) => needs_fetching.push((idx, link, exp)),
                ExpandableCssNode::Inline(text) => {
                    parse_css_nodes(css_parser, &vec![text.clone()]).unwrap();
                    let nodes = css_parser.drain_result();
                    css_parse_cache.insert(exp.clone(), nodes.clone());
                    parsed_css_chunks.push((idx, nodes));
                }
            };
        }
    }
    if needs_fetching.len() > 0 {
        let fetched =
            fetch_expandable_css(base_url, tokio, network_fetch, &needs_fetching).unwrap();
        for (str, (idx, _, exp)) in fetched.into_iter().zip(needs_fetching) {
            parse_css_nodes(css_parser, &vec![str]).unwrap();
            let nodes = css_parser.drain_result();
            css_parse_cache.insert(exp.clone(), nodes.clone());
            parsed_css_chunks.push((idx, nodes));
        }
    }
    let parsed_css_nodes = flatten_css_chunks(parsed_css_chunks);
    *flattened_css_cache = Some((base_url.clone(), expandable, parsed_css_nodes.clone()));
    parsed_css_nodes
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
    nodes: &NodesTable,
    nodes_idxs: &Vec<usize>,
    root_indice: usize,
    window_size: &PhysicalSize<u32>,
    dom_indexes: &mut DomIndexes,
    css_parse_cache: &mut HashMap<ExpandableCssNode, Vec<CssNode>>,
    flattened_css_cache: &mut Option<(String, Vec<ExpandableCssNode>, Vec<CssNode>)>,
    hovering_chain: &Vec<usize>,
    css_parser: &mut CssParser,
    mut node_styles: HashMap<usize, Style>,
    mut resolved_font_sizes: HashMap<usize, u32>,
) -> (
    HashMap<usize, Style>,
    HashMap<usize, u32>,
    VariableDefinitions,
    HashSet<usize>,
) {
    node_styles.retain(|idx, _| nodes.contains_key(*idx));
    resolved_font_sizes.retain(|idx, _| nodes.contains_key(*idx));
    let start = Instant::now();
    let mut parsed_css_nodes = get_css_nodes(
        base_url,
        tokio,
        network_fetch,
        nodes,
        root_indice,
        dom_indexes,
        css_parse_cache,
        flattened_css_cache,
        css_parser,
    );
    println!(
        "Retrieved parsed css nodes in {}ms",
        Instant::now().duration_since(start).as_millis()
    );
    dom_indexes.recompute_class_elements(nodes, nodes_idxs, &mut css_parser.class_definitions);

    let css_children_index =
        build_css_children_index(&parsed_css_nodes.iter().enumerate().collect());

    let start = Instant::now();
    let (collected_class_nodes, class_node_specificity, hovering_impact) =
        collect_class_nodes_for_elements(
            &mut parsed_css_nodes,
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
        false,
    );
    println!(
        "computing styles took {} microseconds",
        Instant::now().duration_since(start).as_micros()
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
    Form(FormNavigation),
}

#[derive(Debug, Clone, PartialEq)]
enum FormMethod {
    Get,
    Post,
}

#[derive(Debug, Clone, PartialEq)]
struct FormNavigation {
    url: ReqwestUrl,
    method: FormMethod,
    body: Option<String>,
}

#[derive(Debug, Clone)]
enum UserEvent {
    DomUpdated,
    ImagesPrefetched(Vec<(ReqwestUrl, RequestCacheEntry)>),
    Navigate((UserNavigateUrl, bool)),
    FrameUpdated,
    CanvasUpdated,
    TabUpdated { tab_idx: usize, buffer: Vec<u32> },
    TabUrlUpdated { tab_idx: usize, url: String },
    ChildMessage(String),
    ParentMessage(String),
    Hover(Position),
    Click,
    Keyup(KeyEvent),
    ScrollBy((f32, f32)),
    FrameLoaded(usize),
    AnimationFrameRequested,
    IntersectionTracked,
}

#[derive(Debug, Clone)]
struct JsHostState {
    renderer: Rc<RefCell<Renderer>>,
    proxy: RendererProxy,
    executed_scripts: Rc<RefCell<ExecutedScripts>>,
    is_top: bool,
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

#[op2(fast)]
fn op_request_animation_frame(state: &mut OpState) -> Result<(), JsError> {
    let host = state.borrow::<JsHostState>();
    host.proxy
        .fire_user_event(UserEvent::AnimationFrameRequested)
        .unwrap();
    host.renderer.borrow().event_loop_notify.notify_one();
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

#[op2]
fn op_create_element(
    state: &mut OpState,
    #[string] tag: String,
    #[number] frame_id: Option<usize>,
) -> Result<i32, JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let node_idx = if let Some(frame_id) = frame_id {
        js_send_onetime_to_frame(&renderer, frame_id, |reply| {
            FrameCommand::Dom(FrameDomCommand::CreateElement { tag, reply })
        })?
    } else {
        renderer.create_element(tag)
    };
    Ok(node_idx as i32)
}

#[op2(fast)]
fn op_create_text_element(state: &mut OpState, #[string] text: String) -> Result<i32, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    renderer.push_node(Node::Text(TextElement { text, parent: None }));
    let node_idx = renderer.nodes.cursor;
    renderer.dom_indexes.children_index.insert(node_idx, vec![]);
    Ok(node_idx as i32)
}

#[op2]
fn op_get_attribute<'s>(
    scope: &mut v8::PinScope<'s, '_>,
    state: &mut OpState,
    #[number] node_idx: usize,
    #[string] attribute: String,
) -> Result<Option<v8::Local<'s, v8::Value>>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow_mut();
    let value = renderer
        .nodes
        .get(node_idx)
        .and_then(|node| match node {
            Node::Element(element) => element.attributes.values.get(&attribute),
            _ => None,
        })
        .and_then(|v| v.clone().to_v8(scope).ok());
    Ok(value)
}

#[op2]
#[string]
fn op_spawn_frame(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[string] url: Option<String>,
) -> Result<(), JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    if renderer.frames.contains_key(&node_idx) {
        return Ok(());
    }
    let handle = renderer
        .spawn_frame(url, PhysicalSize::new(300, 150), node_idx)
        .map_err(|err| JsErrorBox::generic(format!("Failed to spawn frame: {err}")))?;
    renderer.frames.insert(node_idx, handle);
    Ok(())
}

// TODO: Maybe we want to copy the text children no matter what the deep parameter says, but idk
fn clone_node(
    renderer: &mut RefMut<'_, Renderer>,
    node_idx: usize,
    new_parent: Option<usize>,
    deep: bool,
) -> Result<usize> {
    let mut node = renderer
        .nodes
        .get(node_idx)
        .with_context(|| "Could not find node by idx")?
        .clone();
    node.set_parent(new_parent);
    renderer.push_node(node);
    let new_node_idx = renderer.nodes.cursor;
    if deep {
        let old_children = renderer
            .dom_indexes
            .children_index
            .get(&node_idx)
            .unwrap()
            .clone();
        for c in old_children {
            clone_node(renderer, c, Some(new_node_idx), true)?;
        }
    }
    Ok(new_node_idx)
}

#[op2(fast)]
fn op_clone_node(
    state: &mut OpState,
    #[number] node_idx: usize,
    deep: bool,
) -> Result<u32, JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let new_node_idx = clone_node(&mut renderer, node_idx, None, deep)
        .or_else(|err| Err(JsErrorBox::generic(err.root_cause().to_string())))?;
    renderer.recompute_dom_indexes();
    Ok(new_node_idx as u32)
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

#[op2(fast)]
fn op_is_top(state: &mut OpState) -> bool {
    let host = state.borrow::<JsHostState>();
    host.is_top
}

#[op2(fast)]
fn op_post_message_to_frame(
    state: &mut OpState,
    #[string] message: String,
    #[number] frame_id: usize,
) -> Result<(), JsErrorBox> {
    println!("test");
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let Some(frame) = renderer.frames.get(&frame_id) else {
        return Err(JsErrorBox::generic("Failed to get frame by idx"));
    };
    let _ = frame
        .tx
        .send(FrameCommand::UserEvent(UserEvent::ParentMessage(message)));
    Ok(())
}

fn get_offset_y_walk(renderer: &Ref<'_, Renderer>, node_idx: usize, mut parent_offset: i32) -> i32 {
    if let Some(scroll_y) = renderer.scroll_y.get(&node_idx) {
        parent_offset += scroll_y;
    }

    if let Some(parent) = renderer
        .nodes
        .get(node_idx)
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
fn op_get_attributes(
    state: &mut OpState,
    #[number] node_idx: usize,
) -> Result<Option<Attributes>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow_mut();
    let value = renderer
        .nodes
        .get(node_idx)
        .and_then(|node| match node {
            Node::Element(element) => Some(element.attributes.clone()),
            _ => None,
        })
        .clone();
    Ok(value)
}

fn style_border_to_properties(
    properties: &mut HashMap<String, String>,
    side: &str,
    border: &StyleSizeAndColor,
) {
    properties.insert(format!("border-{side}-width"), border.size.to_string());
    properties.insert(format!("border-{side}-color"), border.color.to_css_color());
    properties.insert(format!("border-{side}-style"), border.style.to_string());
}

fn computed_style_properties(renderer: &Renderer, node_idx: usize) -> HashMap<String, String> {
    let Some(style) = renderer.node_styles.get(&node_idx) else {
        return HashMap::new();
    };

    let mut properties = HashMap::from([
        ("width".to_string(), style.width.to_string()),
        ("height".to_string(), style.height.to_string()),
        ("min-width".to_string(), style.min_width.to_string()),
        ("max-width".to_string(), style.max_width.to_string()),
        ("min-height".to_string(), style.min_height.to_string()),
        ("max-height".to_string(), style.max_height.to_string()),
        (
            "background-color".to_string(),
            style.background.to_css_color(),
        ),
        (
            "background-image".to_string(),
            style.background.to_css_image(),
        ),
        ("display".to_string(), style.display.to_string()),
        ("flex-grow".to_string(), style.flex_grow.to_string()),
        ("flex-shrink".to_string(), style.flex_shrink.to_string()),
        ("flex-basis".to_string(), style.flex_basis.to_string()),
        ("order".to_string(), style.order.to_string()),
        (
            "justify-content".to_string(),
            style.justify_content.to_string(),
        ),
        ("justify-items".to_string(), style.justify_items.to_string()),
        ("align-items".to_string(), style.align_items.to_string()),
        ("align-self".to_string(), style.align_self.to_string()),
        (
            "flex-direction".to_string(),
            style.flex_direction.to_string(),
        ),
        ("gap".to_string(), style.gap.to_string()),
        ("margin-left".to_string(), style.margin_left.to_string()),
        ("margin-right".to_string(), style.margin_right.to_string()),
        ("margin-top".to_string(), style.margin_top.to_string()),
        ("margin-bottom".to_string(), style.margin_bottom.to_string()),
        ("padding-left".to_string(), style.padding_left.to_string()),
        ("padding-right".to_string(), style.padding_right.to_string()),
        ("padding-top".to_string(), style.padding_top.to_string()),
        (
            "padding-bottom".to_string(),
            style.padding_bottom.to_string(),
        ),
        ("color".to_string(), style.color.to_css_color()),
        ("position".to_string(), style.position.to_string()),
        ("left".to_string(), style.left.to_string()),
        ("right".to_string(), style.right.to_string()),
        ("top".to_string(), style.top.to_string()),
        ("bottom".to_string(), style.bottom.to_string()),
        ("text-align".to_string(), style.text_align.to_string()),
        ("font-size".to_string(), style.font_size.to_string()),
        (
            "line-height".to_string(),
            match style.line_height {
                StyleSize::Auto => "normal".to_string(),
                _ => style.line_height.to_string(),
            },
        ),
        ("overflow-x".to_string(), style.overflow_x.to_string()),
        ("overflow-y".to_string(), style.overflow_y.to_string()),
        ("z-index".to_string(), style.z_index.to_string()),
        (
            "pointer-events".to_string(),
            style.pointer_events.to_string(),
        ),
        ("opacity".to_string(), format_css_number(style.opacity)),
        ("visibility".to_string(), style.visibility.to_string()),
        ("transform".to_string(), style.transform.to_string()),
        (
            "border-top-left-radius".to_string(),
            style.border_radius_top_left.to_string(),
        ),
        (
            "border-top-right-radius".to_string(),
            style.border_radius_top_right.to_string(),
        ),
        (
            "border-bottom-right-radius".to_string(),
            style.border_radius_bottom_right.to_string(),
        ),
        (
            "border-bottom-left-radius".to_string(),
            style.border_radius_bottom_left.to_string(),
        ),
    ]);

    style_border_to_properties(&mut properties, "left", &style.border_left);
    style_border_to_properties(&mut properties, "top", &style.border_top);
    style_border_to_properties(&mut properties, "right", &style.border_right);
    style_border_to_properties(&mut properties, "bottom", &style.border_bottom);

    for (variable_idx, value) in style.variables.iter() {
        if let Some(definition) = renderer.variable_definitions.data.get(variable_idx) {
            properties.insert(definition.property.clone(), value.clone());
        }
    }

    properties
}

#[op2]
#[serde]
fn op_get_computed_style(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[number] frame_id: Option<usize>,
) -> Result<HashMap<String, String>, JsErrorBox> {
    let host = state.borrow::<JsHostState>();
    let renderer = host.renderer.borrow();
    if let Some(frame_id) = frame_id {
        js_send_onetime_to_frame(&renderer, frame_id, |reply| {
            FrameCommand::Dom(FrameDomCommand::GetComputedStyle { node_idx, reply })
        })
    } else {
        Ok(computed_style_properties(&renderer, node_idx))
    }
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
    let node_idx = renderer.nodes.cursor;
    renderer.dom_indexes.children_index.insert(node_idx, vec![]);
    Ok(node_idx as i32)
}

#[op2(reentrant)]
fn op_append_child<'s>(
    scope: &mut v8::PinScope<'s, '_>,
    state: Rc<RefCell<OpState>>,
    #[number] parent_idx: usize,
    #[number] node_idx: usize,
    #[number] before_reference_idx: Option<usize>,
) -> Result<(), JsErrorBox> {
    let (renderer, executed_scripts) = {
        let state = state.borrow();
        let host = state.borrow::<JsHostState>();
        (host.renderer.clone(), host.executed_scripts.clone())
    };

    let script_to_run = {
        let mut renderer = renderer.borrow_mut();
        if before_reference_idx.is_some_and(|idx| idx == node_idx) {
            return Ok(());
        }
        if let Some(old_parent_idx) = renderer.nodes.get(node_idx).unwrap().get_parent() {
            if let Some(children) = renderer.dom_indexes.children_index.get_mut(&old_parent_idx) {
                children.retain(|idx| *idx != node_idx);
            }
        }
        renderer
            .nodes
            .get_mut(node_idx)
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
        renderer.schedule_dom_update();

        match renderer.extract_script_from_idx(node_idx) {
            Some(Script {
                script_type: ScriptType::Classic,
                content: ScriptContent::Code(code),
                ..
            }) => {
                let mut executed_scripts = executed_scripts.borrow_mut();
                if executed_scripts.nodes.contains(&node_idx) {
                    None
                } else {
                    executed_scripts.nodes.push(node_idx);
                    Some(code)
                }
            }
            _ => None,
        }
    };

    if let Some(code) = script_to_run {
        run_v8_source(
            scope,
            "set current script",
            &format!("__set_current_script_node_idx({node_idx})"),
        )?;
        let script_result = run_v8_source(scope, "dynamic inline script", &code);
        let clear_result = run_v8_source(
            scope,
            "clear current script",
            "__set_current_script_node_idx(null)",
        );

        clear_result?;
        script_result?;
    }

    Ok(())
}

#[op2]
#[string]
fn op_get_inner_html(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[number] frame_id: Option<usize>,
) -> Result<String, JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow_mut();
    let html = if let Some(frame_id) = frame_id {
        js_send_onetime_to_frame(&renderer, frame_id, |reply| {
            FrameCommand::Dom(FrameDomCommand::GetInnerHtml { node_idx, reply })
        })?
    } else {
        renderer.get_element_inner_html(node_idx)
    };
    Ok(html)
}

#[op2(fast)]
fn op_remove_child(state: &mut OpState, #[number] child_idx: usize) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    renderer.detach_node(child_idx);
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
        .get(idx)
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
    let node = node_idx.and_then(|idx| Some((idx, renderer.nodes.get(idx).unwrap().clone())));
    Ok(node)
}

#[op2]
fn op_get_elements_by_tag_name(
    state: &mut OpState,
    #[string] tag: String,
    #[number] required_parent: Option<usize>,
    #[number] frame_id: Option<usize>,
) -> Result<Vec<(usize, Node)>, JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    if let Some(frame_id) = frame_id {
        js_send_onetime_to_frame(&renderer, frame_id, |reply| {
            FrameCommand::Dom(FrameDomCommand::GetElementsByTagName {
                tag,
                reply,
                required_parent,
            })
        })
    } else {
        Ok(renderer.get_elements_by_tag_name(&tag, required_parent))
    }
}

#[op2]
fn op_get_elements_by_name(
    state: &mut OpState,
    #[string] name: String,
    #[number] required_parent: Option<usize>,
    #[number] frame_id: Option<usize>,
) -> Result<Vec<(usize, Node)>, JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    if let Some(frame_id) = frame_id {
        js_send_onetime_to_frame(&renderer, frame_id, |reply| {
            FrameCommand::Dom(FrameDomCommand::GetElementsByName {
                name,
                reply,
                required_parent,
            })
        })
    } else {
        Ok(renderer.get_elements_by_name(&name, required_parent))
    }
}

#[op2]
fn op_get_elements_by_class_name(
    state: &mut OpState,
    #[string] class_names: String,
    #[number] required_parent: Option<usize>,
    #[number] frame_id: Option<usize>,
) -> Result<Vec<(usize, Node)>, JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    if let Some(frame_id) = frame_id {
        js_send_onetime_to_frame(&renderer, frame_id, |reply| {
            FrameCommand::Dom(FrameDomCommand::GetElementsByClassName {
                class_names,
                reply,
                required_parent,
            })
        })
    } else {
        Ok(renderer.get_elements_by_class_name(&class_names, required_parent))
    }
}

#[op2]
fn op_query_selector(
    state: &mut OpState,
    #[string] selector: String,
    #[number] required_parent: Option<usize>,
    #[number] frame_id: Option<usize>,
) -> Result<Option<(usize, Node)>, JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    if let Some(frame_id) = frame_id {
        js_send_onetime_to_frame(&renderer, frame_id, |reply| {
            FrameCommand::Dom(FrameDomCommand::QuerySelector {
                selector,
                required_parent,
                reply,
            })
        })?
        .map_err(|err| JsErrorBox::generic(err))
    } else {
        Ok(renderer.query_selector_node(selector, required_parent))
    }
}

fn walk_closest(buffer: &mut Vec<usize>, nodes: &NodesTable, node_idx: usize) {
    buffer.push(node_idx);
    if let Some(parent) = nodes.get(node_idx).and_then(|node| node.get_parent()) {
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
    let mut renderer = host.renderer.borrow_mut();
    let selector = selector_to_parts(&selector, &mut renderer.css_parser.class_definitions);
    let matched_idxs: Vec<usize> = query_selector_all(
        &renderer.nodes,
        selector,
        &renderer.window_size,
        &renderer.dom_indexes,
        &renderer.get_hover_chain(),
        None,
    );
    let mut allowed_idxs = vec![];
    walk_closest(&mut allowed_idxs, &renderer.nodes, node_idx);
    let mut allowed_matched_idxs: Vec<usize> = matched_idxs
        .into_iter()
        .filter_map(|idx| allowed_idxs.iter().position(|lidx| idx == *lidx))
        .collect();
    allowed_matched_idxs.sort();
    let most_applicable = allowed_matched_idxs.first().map(|lidx| allowed_idxs[*lidx]);
    let owned = most_applicable.map(|idx| (idx, renderer.nodes.get(idx).unwrap().clone()));
    Ok(owned)
}

fn has_parent(nodes_table: &NodesTable, node_idx: usize, target_parent: usize) -> bool {
    if node_idx == target_parent {
        return true;
    }

    if let Some(parent) = nodes_table.get(node_idx).and_then(|v| v.get_parent()) {
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
    #[number] frame_id: Option<usize>,
) -> Result<Vec<(usize, Node)>, JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    if let Some(frame_id) = frame_id {
        js_send_onetime_to_frame(&renderer, frame_id, |reply| {
            FrameCommand::Dom(FrameDomCommand::QuerySelectorAll {
                selector,
                required_parent,
                reply,
            })
        })?
        .map_err(|err| JsErrorBox::generic(err))
    } else {
        Ok(renderer.query_selector_all_nodes(selector, required_parent))
    }
}

fn js_send_onetime_to_frame<T>(
    renderer: &Renderer,
    frame_id: usize,
    build_command: impl FnOnce(std::sync::mpsc::Sender<T>) -> FrameCommand,
) -> Result<T, JsErrorBox> {
    let handle = renderer
        .frames
        .get(&frame_id)
        .ok_or_else(|| JsErrorBox::generic("Failed to get frame"))?;
    let (reply_tx, reply_rx) = std::sync::mpsc::channel();

    handle
        .tx
        .send(build_command(reply_tx))
        .map_err(|err| JsErrorBox::generic(format!("Failed to query frame: {err}")))?;

    reply_rx
        .recv_timeout(Duration::from_secs(1))
        .map_err(|err| JsErrorBox::generic(format!("Frame query timed out: {err}")))
}

#[op2]
fn op_set_inner_html(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[string] html: String,
    #[number] frame_id: Option<usize>,
) -> Result<(), JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    if let Some(frame_id) = frame_id {
        js_send_onetime_to_frame(&renderer, frame_id, |reply| {
            FrameCommand::Dom(FrameDomCommand::ReplaceInnerHtml {
                node_idx,
                html,
                reply,
            })
        })
    } else {
        renderer.replace_inner_html(node_idx, html);
        Ok(())
    }
}

#[op2(fast)]
fn op_set_text_content(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[string] text: String,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();

    let needs_index_rebuild = match renderer.nodes.get_mut(node_idx).unwrap() {
        Node::Text(element) => {
            element.text = text;
            false
        }
        Node::Comment(element) => {
            element.comment = text;
            false
        }
        Node::Element(_) => {
            let children = renderer
                .dom_indexes
                .children_index
                .get(&node_idx)
                .cloned()
                .unwrap_or_default();
            let had_children = !children.is_empty();
            for child in children {
                renderer.remove_node(child, true);
            }
            renderer.push_node(Node::Text(TextElement {
                text,
                parent: Some(node_idx),
            }));
            let text_idx = renderer.nodes.cursor;
            renderer
                .dom_indexes
                .children_index
                .insert(node_idx, vec![text_idx]);
            renderer.dom_indexes.children_index.insert(text_idx, vec![]);
            had_children
        }
    };

    // Text nodes are absent from the tag/class/id/attribute indexes, and the new parent-child
    // relationship was recorded above. Only removed descendants can invalidate those indexes.
    if needs_index_rebuild {
        renderer.recompute_dom_indexes();
    }
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
        .map(|idx| (*idx, renderer.nodes.get(*idx).unwrap().clone()))
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
    let parent_idx = if let Some(parent) = renderer.nodes.get(node_idx).and_then(|v| v.get_parent())
    {
        parent
    } else {
        return Ok(None);
    };
    let parent = (parent_idx, renderer.nodes.get(parent_idx).unwrap().clone());
    Ok(Some(parent))
}

#[op2]
fn op_update_attributes<'s>(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[serde] attributes: HashMap<String, String>,
    #[number] frame_id: Option<usize>,
) -> Result<(), JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let attributes = Attributes::from_hash_map(attributes);
    if let Some(frame_id) = frame_id {
        js_send_onetime_to_frame(&renderer, frame_id, |reply| {
            FrameCommand::Dom(FrameDomCommand::UpdateElementAttributes {
                node_idx,
                attributes,
                reply,
            })
        })?
        .map_err(|err| JsErrorBox::generic(err.root_cause().to_string()))
    } else {
        renderer
            .update_element_attributes(node_idx, attributes)
            .map_err(|err| JsErrorBox::generic(err.root_cause().to_string()))
    }
}

#[op2(fast)]
fn op_remove_attribute(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[string] attribute: String,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let removed = match renderer.nodes.get_mut(node_idx).unwrap() {
        Node::Element(element) => element.attributes.remove(&attribute),
        _ => None,
    };
    let Some(removed) = removed else {
        return Ok(());
    };

    if attribute == "id" {
        renderer.dom_indexes.remove_id_node(&removed, node_idx);
    } else if attribute == "class" {
        let Renderer {
            dom_indexes,
            css_parser,
            ..
        } = &mut *renderer;
        dom_indexes.remove_class_node(&removed, node_idx, &mut css_parser.class_definitions);
    }
    renderer
        .dom_indexes
        .remove_attribute_node(&attribute, node_idx);
    renderer.schedule_dom_update();
    Ok(())
}

fn get_canvas_wh(node: &Node) -> (Option<u32>, Option<u32>) {
    match node {
        Node::Element(element) => (
            element
                .attributes
                .get_str("width")
                .and_then(|v| v.parse::<u32>().ok())
                .or(Some(150)),
            element
                .attributes
                .get_str("height")
                .and_then(|v| v.parse::<u32>().ok())
                .or(Some(150)),
        ),
        _ => (None, None),
    }
}

#[op2]
fn op_canvas_record_command(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[serde] command: CanvasPathCommand,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let node = renderer.nodes.get(node_idx).unwrap();
    let (Some(node_width), Some(node_height)) = get_canvas_wh(node) else {
        return Ok(());
    };

    let canvas = renderer
        .canvas_buffers
        .entry(node_idx)
        .or_insert_with(|| CanvasBuffer::new(node_width, node_height));
    canvas.resize_if_needed(node_width, node_height);

    canvas.commands.push(command);

    Ok(())
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
enum CanvasFillRule {
    NonZero,
    EvenOdd,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "camelCase")]
enum CanvasPathCommand {
    MoveTo {
        point: [f64; 2],
    },
    Point {
        point: [f64; 2],
    },
    BezierCurve {
        cp1: [f64; 2],
        cp2: [f64; 2],
        endpoint: [f64; 2],
    },
    Close,
    Fill {
        color: u32,
        fill_rule: CanvasFillRule,
    },
    Stroke {
        line_width: f64,
        color: u32,
    },
    StrokePath {
        path: Vec<CanvasPathCommand>,
        line_width: f64,
        color: u32,
    },
    FillPath {
        path: Vec<CanvasPathCommand>,
        color: u32,
        fill_rule: CanvasFillRule,
    },
    Clip {
        fill_rule: CanvasFillRule,
    },
    ClipPath {
        path: Vec<CanvasPathCommand>,
        fill_rule: CanvasFillRule,
    },
    FillRect {
        x: i32,
        y: i32,
        width: u32,
        height: u32,
    },
    StrokeRect {
        x: i32,
        y: i32,
        width: u32,
        height: u32,
        line_width: f64,
    },
    Transform {
        matrix: Matrixf32,
    },
    ResetTransform,
    Save,
    Restore,
    BeginPath,
    ClearRect {
        x: i32,
        y: i32,
        width: u32,
        height: u32,
    },
    DrawImage {
        image_node_idx: usize,
        image_width: Option<u32>,
        image_height: Option<u32>,
        x: i32,
        y: i32,
    },
}

#[derive(Debug, Deserialize)]
struct CanvasDrawImageRequest {
    x: f64,
    y: f64,
    width: Option<f64>,
    height: Option<f64>,
}

fn cubic_bezier(t: f32, p0: i32, p1: i32, p2: i32, p3: i32) -> i32 {
    let result = (1. - t).powi(3) * p0 as f32
        + 3. * (1. - t).powi(2) * t * p1 as f32
        + 3. * (1. - t) * t.powi(2) * p2 as f32
        + t.powi(3) * p3 as f32;
    result.round() as i32
}

fn distance(a: (f64, f64), b: (f64, f64)) -> f64 {
    let dx = b.0 - a.0;
    let dy = b.1 - a.1;
    (dx * dx + dy * dy).sqrt()
}

#[op2]
fn op_canvas_draw_image(
    state: &mut OpState,
    #[number] canvas_node_idx: usize,
    #[number] image_node_idx: usize,
    #[serde] request: CanvasDrawImageRequest,
) -> Result<bool, JsErrorBox> {
    if !request.x.is_finite() || !request.y.is_finite() {
        return Ok(false);
    }

    let (input_width, input_height) = match (request.width, request.height) {
        (None, None) => (None, None),
        (Some(width), Some(height))
            if width.is_finite()
                && height.is_finite()
                && width > 0.0
                && height > 0.0
                && width <= u32::MAX as f64
                && height <= u32::MAX as f64 =>
        {
            (
                Some(width.round().max(1.0) as u32),
                Some(height.round().max(1.0) as u32),
            )
        }
        _ => return Ok(false),
    };

    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    if !renderer.nodes.contains_key(image_node_idx) {
        return Ok(false);
    }
    let (Some(canvas_width), Some(canvas_height)) = renderer
        .nodes
        .get(canvas_node_idx)
        .map(get_canvas_wh)
        .unwrap_or((None, None))
    else {
        return Ok(false);
    };

    let canvas = renderer
        .canvas_buffers
        .entry(canvas_node_idx)
        .or_insert_with(|| CanvasBuffer::new(canvas_width, canvas_height));
    canvas.resize_if_needed(canvas_width, canvas_height);
    canvas.commands.push(CanvasPathCommand::DrawImage {
        image_node_idx,
        image_width: input_width,
        image_height: input_height,
        x: request.x.round() as i32,
        y: request.y.round() as i32,
    });

    Ok(true)
}

#[op2]
fn op_canvas_path_stroke(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[serde] path: Option<Vec<CanvasPathCommand>>,
    line_width: f64,
    #[string] stroke_style: String,
) -> Result<(), JsErrorBox> {
    let color = match style::parse_color(stroke_style)
        .map_err(|err| JsErrorBox::generic(err.to_string()))?
    {
        StyleBackground::Hex(color) => color,
        StyleBackground::Transparent => 0,
        _ => return Err(JsErrorBox::generic("Unsupported canvas strokeStyle")),
    };

    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let node = renderer.nodes.get(node_idx).unwrap();
    let (Some(node_width), Some(node_height)) = get_canvas_wh(node) else {
        return Ok(());
    };

    let canvas = renderer
        .canvas_buffers
        .entry(node_idx)
        .or_insert_with(|| CanvasBuffer::new(node_width, node_height));
    canvas.resize_if_needed(node_width, node_height);

    match path {
        Some(path) => canvas.commands.push(CanvasPathCommand::StrokePath {
            path,
            line_width,
            color,
        }),
        None => canvas
            .commands
            .push(CanvasPathCommand::Stroke { line_width, color }),
    }

    Ok(())
}

#[op2]
fn op_canvas_path_fill(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[serde] path: Option<Vec<CanvasPathCommand>>,
    #[string] fill_style: String,
    #[serde] fill_rule: CanvasFillRule,
) -> Result<(), JsErrorBox> {
    let color =
        match style::parse_color(fill_style).map_err(|err| JsErrorBox::generic(err.to_string()))? {
            StyleBackground::Hex(color) => color,
            StyleBackground::Transparent => 0,
            _ => return Err(JsErrorBox::generic("Unsupported canvas fillStyle")),
        };

    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let node = renderer.nodes.get(node_idx).unwrap();
    let (Some(node_width), Some(node_height)) = get_canvas_wh(node) else {
        return Ok(());
    };

    let canvas = renderer
        .canvas_buffers
        .entry(node_idx)
        .or_insert_with(|| CanvasBuffer::new(node_width, node_height));
    canvas.resize_if_needed(node_width, node_height);

    match path {
        Some(path) => canvas.commands.push(CanvasPathCommand::FillPath {
            path,
            color,
            fill_rule,
        }),
        None => canvas
            .commands
            .push(CanvasPathCommand::Fill { color, fill_rule }),
    }

    Ok(())
}

#[op2]
fn op_canvas_path_clip(
    state: &mut OpState,
    #[number] node_idx: usize,
    #[serde] path: Option<Vec<CanvasPathCommand>>,
    #[serde] fill_rule: CanvasFillRule,
) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let node = renderer.nodes.get(node_idx).unwrap();
    let (Some(node_width), Some(node_height)) = get_canvas_wh(node) else {
        return Ok(());
    };

    let canvas = renderer
        .canvas_buffers
        .entry(node_idx)
        .or_insert_with(|| CanvasBuffer::new(node_width, node_height));
    canvas.resize_if_needed(node_width, node_height);

    match path {
        Some(path) => canvas
            .commands
            .push(CanvasPathCommand::ClipPath { path, fill_rule }),
        None => canvas.commands.push(CanvasPathCommand::Clip { fill_rule }),
    }

    Ok(())
}

#[op2(fast)]
fn op_canvas_paint(state: &mut OpState, #[number] node_idx: usize) -> Result<(), JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();

    let canvas = renderer
        .canvas_buffers
        .get_mut(&node_idx)
        .ok_or_else(|| JsErrorBox::generic("Failed to get canvas in op_canvas_paint"))?;

    canvas.dirty = true;

    renderer.schedule_canvas_update();

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
        let Some(Node::Element(element)) = renderer.nodes.get(*input) else {
            continue;
        };
        let Some(name) = element.attributes.get_str("name") else {
            continue;
        };
        data.insert(name.into_owned(), form_control_value(element));
    }
    data
}

#[op2(fast)]
fn op_track_intersection(state: &mut OpState, #[number] node_idx: usize) -> Result<(), JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    renderer.track_intersection(node_idx);
    Ok(())
}

#[op2(fast)]
fn op_untrack_intersection(
    state: &mut OpState,
    #[number] node_idx: usize,
) -> Result<(), JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    renderer.untrack_intersection(node_idx);
    Ok(())
}

#[op2(fast)]
fn op_spawn_worker(state: &mut OpState, #[string] src: &str) -> Result<(), JsErrorBox> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    renderer
        .spawn_worker(src)
        .map_err(|err| JsErrorBox::generic(format!("Failed to spawn worker: {err}")))?;
    Ok(())
}

// This should walk the tree to be fully correct I think
fn query_selector_all(
    nodes_table: &NodesTable,
    selector: Vec<ClassNamePart>,
    window_size: &PhysicalSize<u32>,
    dom_indexes: &DomIndexes,
    hovering_chain: &Vec<usize>,
    required_parent: Option<usize>,
) -> Vec<usize> {
    let class = CssNode::ClassName(ClassName {
        name: vec![],
        name_parts: vec![selector],
        parent: None,
    });
    let mut css_vec = vec![class];
    let mut to_resolve = HashSet::new();
    to_resolve.insert(0);
    let (collected, _, _) = search_elements_for_css_nodes(
        to_resolve,
        &mut css_vec,
        nodes_table,
        window_size,
        dom_indexes,
        hovering_chain,
    );

    let mut node_idxs: Vec<usize> = collected.keys().cloned().collect();
    node_idxs.sort();

    if let Some(required_parent) = required_parent {
        node_idxs = node_idxs
            .into_iter()
            .filter(|idx| has_parent(nodes_table, *idx, required_parent))
            .collect();
        node_idxs.sort();
    }

    node_idxs
}

extension!(
  browser_worker,
  ops = [
    op_tls_peer_certificate,
  ],
  esm_entry_point = "ext:browser_worker/runtime_worker.js",
  esm = [dir "src", "runtime_worker.js", "runtime_fetch.js", "xml_http_request.js", "event_target.js"],
  state = |state| {
    let parser = Arc::new(deno_permissions::RuntimePermissionDescriptorParser::new(
      sys_traits::impls::RealSys,
    ));
    state.put(deno_permissions::PermissionsContainer::allow_all(parser));
  },
);

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
    op_get_elements_by_name,
    op_get_elements_by_class_name,
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
    op_canvas_record_command,
    op_canvas_draw_image,
    op_canvas_path_stroke,
    op_canvas_path_fill,
    op_canvas_path_clip,
    op_canvas_paint,
    op_set_cookie,
    op_get_cookie,
    op_set_location_href,
    op_is_top,
    op_get_node,
    op_get_closest,
    op_get_attribute,
    op_get_attributes,
    op_get_computed_style,
    op_post_message_to_parent,
    op_post_message_to_frame,
    op_get_offset_y,
    op_collect_data_for_form,
    op_clone_node,
    op_spawn_frame,
    op_spawn_worker,
    op_track_intersection,
    op_untrack_intersection,
    op_request_animation_frame,
  ],
  esm_entry_point = "ext:browser/runtime.js",
  esm = [dir "src", "runtime.js", "runtime_fetch.js", "xml_http_request.js", "event_target.js"],
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
    let mut extension = deno_fetch::deno_fetch::init(deno_fetch::Options {
        user_agent: USER_AGENT.to_string(),
        ..Default::default()
    });
    extension.esm_files.to_mut().retain(|source| {
        !matches!(
            source.specifier,
            "ext:deno_fetch/26_fetch.js" | "ext:deno_fetch/27_eventsource.js"
        )
    });
    extension
}

fn install_default_crypto_provider() {
    static INSTALL: Once = Once::new();
    INSTALL.call_once(|| {
        let _ = rustls::crypto::aws_lc_rs::default_provider().install_default();
    });
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

#[derive(Debug, Clone, PartialEq)]
pub enum ScriptType {
    Classic,
    Module,
}

fn parse_script_type_attr(value: Option<&str>) -> Option<ScriptType> {
    let script_type = value.unwrap_or("").trim().to_ascii_lowercase();
    let script_type = script_type
        .rsplit_once('-')
        .map_or(script_type.as_str(), |(_, script_type)| script_type);

    match script_type {
        ""
        | "text/javascript"
        | "application/javascript"
        | "text/ecmascript"
        | "application/ecmascript" => Some(ScriptType::Classic),
        "module" => Some(ScriptType::Module),
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub struct Script {
    content: ScriptContent,
    script_type: ScriptType,
    node_idx: Option<usize>,
    defer: bool,
    is_async: bool,
}

fn sorted_node_idxs(nodes: &NodesTable) -> Vec<usize> {
    let mut node_idxs: Vec<usize> = nodes.keys().collect();
    node_idxs.sort_unstable();
    node_idxs
}

fn get_dom_indexes_classes(
    html_nodes: &NodesTable,
    nodes_idxs: &Vec<usize>,
    class_indexes: &mut ClassIndexes,
) -> Vec<FixedBitSet> {
    let bitset_capacity = nodes_idxs.iter().max().map_or(0, |idx| idx + 1);
    let mut class_elements = vec![FixedBitSet::with_capacity(bitset_capacity); class_indexes.len()];
    for (html_node_idx, html_node) in html_nodes.iter() {
        match html_node {
            Node::Element(element) => {
                let class_list = get_class_list(element);
                for class in class_list {
                    let (new, class_idx) = class_indexes.upsert_definition(class);
                    if new {
                        class_elements.resize(
                            class_indexes.len(),
                            FixedBitSet::with_capacity(bitset_capacity),
                        );
                    }
                    class_elements[class_idx].insert(html_node_idx);
                }
            }
            _ => {}
        };
    }
    class_elements
}

fn get_dom_indexes_attributes(
    html_nodes: &NodesTable,
    nodes_idxs: &Vec<usize>,
) -> HashMap<String, FixedBitSet> {
    let bitset_capacity = nodes_idxs.iter().max().map_or(0, |idx| idx + 1);
    let mut attribute_elements: HashMap<String, FixedBitSet> = HashMap::new();
    for (html_node_idx, html_node) in html_nodes.iter() {
        let Node::Element(element) = html_node else {
            continue;
        };

        for key in element.attributes.keys() {
            attribute_elements
                .entry(key.clone())
                .or_insert_with(|| FixedBitSet::with_capacity(bitset_capacity))
                .insert(html_node_idx);
        }
    }
    attribute_elements
}

fn get_dom_indexes_ids(
    html_nodes: &NodesTable,
    nodes_idxs: &Vec<usize>,
) -> HashMap<String, FixedBitSet> {
    let bitset_capacity = nodes_idxs.iter().max().map_or(0, |idx| idx + 1);
    let mut id_elements: HashMap<String, FixedBitSet> = HashMap::new();
    for (html_node_idx, html_node) in html_nodes.iter() {
        match html_node {
            Node::Element(element) => {
                if let Some(id) = element.attributes.get_str("id") {
                    id_elements
                        .entry(id.into_owned())
                        .or_insert_with(|| FixedBitSet::with_capacity(bitset_capacity))
                        .insert(html_node_idx);
                }
            }
            _ => {}
        };
    }
    id_elements
}

fn get_dom_indexes(
    html_nodes: &NodesTable,
    nodes_idxs: &Vec<usize>,
    class_indexes: &mut ClassIndexes,
) -> DomIndexes {
    let bitset_capacity = nodes_idxs.iter().max().map_or(0, |idx| idx + 1);

    let class_elements = get_dom_indexes_classes(html_nodes, nodes_idxs, class_indexes);
    let id_elements = get_dom_indexes_ids(html_nodes, nodes_idxs);

    let mut tag_elements: HashMap<String, FixedBitSet> = HashMap::new();
    for (html_node_idx, html_node) in html_nodes.iter() {
        match html_node {
            Node::Element(element) => {
                tag_elements
                    .entry(element.tag.clone())
                    .or_insert_with(|| FixedBitSet::with_capacity(bitset_capacity))
                    .insert(html_node_idx);
            }
            _ => {}
        };
    }

    let children_index = build_children_index(&html_nodes, nodes_idxs);

    let mut root_indices: Vec<usize> = html_nodes
        .iter()
        .filter_map(|(idx, node)| node.get_parent().is_none().then_some(idx))
        .filter(|idx| match html_nodes.get(*idx).unwrap() {
            Node::Element(_) | Node::Text(_) => true,
            Node::Comment(_) => false,
        })
        .collect();
    root_indices.sort_unstable();
    let root_indice = root_indices
        .iter()
        .find(|idx| match html_nodes.get(**idx).unwrap() {
            Node::Element(element) => element.tag == "html",
            Node::Text(_) | Node::Comment(_) => false,
        })
        .or(root_indices.first())
        .copied()
        .expect("Expected at least one root index");

    let attribute_elements = get_dom_indexes_attributes(html_nodes, nodes_idxs);

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
    decoded_gifs: HashMap<String, DynamicImage>,
    decoded_webps: HashMap<String, DynamicImage>,
    decoded_svgs: HashMap<(String, u32), Tree>,
    jpegs: HashMap<(String, u32, u32), Pixmap>,
    gifs: HashMap<(String, u32, u32), Pixmap>,
    webps: HashMap<(String, u32, u32), Pixmap>,
    svgs: HashMap<(String, u32, u32, u32), Pixmap>,
}

impl CachedRasterizations {
    pub fn new() -> Self {
        Self {
            decoded_pngs: HashMap::new(),
            decoded_jpegs: HashMap::new(),
            decoded_gifs: HashMap::new(),
            decoded_webps: HashMap::new(),
            decoded_svgs: HashMap::new(),
            jpegs: HashMap::new(),
            gifs: HashMap::new(),
            webps: HashMap::new(),
            svgs: HashMap::new(),
        }
    }
}

#[derive(Debug)]
struct GridBaseItem {
    node_idx: usize,
    base_width: u32,
    target_width: u32,
    base_height: u32,
    target_height: u32,
    column: i32,
    column_span: i32,
    row: i32,
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
        return match element.attributes.get_str("type") {
            // If type="submit", only include its value if it was clicked
            Some(input_type) if input_type.eq_ignore_ascii_case("submit") => {
                submitted_by.is_some_and(|v| v == node_idx)
            }
            _ => true,
        };
    }
    if element.tag == "button"
        && element.attributes.contains_key("name")
        && is_submit_button(element)
    {
        return submitted_by.is_some_and(|v| v == node_idx);
    }
    false
}

fn form_control_value(element: &Element) -> String {
    element
        .attributes
        .get_str("value")
        .map(|value| value.into_owned())
        .unwrap_or_default()
}

fn is_submit_button(element: &Element) -> bool {
    match element.tag.as_str() {
        "input" | "button" => element
            .attributes
            .get_str("type")
            .is_some_and(|v| v.eq_ignore_ascii_case("submit")),
        _ => false,
    }
}

fn serialize_form_entries(entries: &[(String, String)]) -> String {
    let mut serializer = url::form_urlencoded::Serializer::new(String::new());
    for (name, value) in entries {
        serializer.append_pair(name, value);
    }
    serializer.finish()
}

fn build_form_navigation(
    current_url: &str,
    action: Option<&str>,
    method: Option<&str>,
    entries: &[(String, String)],
) -> Result<FormNavigation> {
    let base_url = ReqwestUrl::parse(current_url)?;
    let action = action.unwrap_or(current_url);
    let mut parsed_url = resolve_url(action, Some(&base_url))?;
    let method = match method {
        Some(method) if method.eq_ignore_ascii_case("post") => FormMethod::Post,
        _ => FormMethod::Get,
    };

    let body = match method {
        FormMethod::Get => {
            let mut query_parms = parsed_url.query_pairs_mut();
            for (name, value) in entries {
                query_parms.append_pair(name, value);
            }
            None
        }
        FormMethod::Post => Some(serialize_form_entries(entries)),
    };

    Ok(FormNavigation {
        url: parsed_url,
        method,
        body,
    })
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
    clip: PaintClip,
) {
    let Some(blit) = clipped_blit(
        dst_width, dst_height, src_width, src_height, dst_x, dst_y, clip,
    ) else {
        return;
    };

    for row in 0..blit.height {
        let src_start = ((blit.src_y + row) * src_width + blit.src_x) as usize;
        let dst_start = ((blit.dst_y + row) * dst_width + blit.dst_x) as usize;

        let src_row = &src[src_start..src_start + blit.width as usize];
        let dst_row = &mut dst[dst_start..dst_start + blit.width as usize];

        dst_row.copy_from_slice(src_row);
    }
}

#[derive(Debug, PartialEq)]
enum LoadPhase {
    JsDone,
    IframeDone,
}

impl Renderer {
    fn new(
        url: String,
        tokio: Rc<RefCell<tokio::runtime::Runtime>>,
        nodes_table: NodesTable,
        window_size: PhysicalSize<u32>,
        font_handler: Rc<FontHandler>,
        network_fetch: Rc<RefCell<NetworkFetch>>,
        mut dom_indexes: DomIndexes,
        nodes_idxs: Vec<usize>,
        blob_store: Arc<BlobStore>,
    ) -> Self {
        let request_cache = HashMap::new();

        let layout_table = HashMap::new();
        let containing_nodes = HashMap::new();
        let node_layout_mapping = HashMap::new();

        let rendered_nodes_ordered = vec![];
        let hovering = None;

        let mut css_parse_cache = HashMap::new();
        let mut flattened_css_cache = None;
        let mut css_parser = CssParser::new();

        let (node_styles, resolved_font_sizes, variable_definitions, hovering_impact) =
            compute_node_styles(
                &url,
                &tokio,
                &network_fetch,
                &nodes_table,
                &nodes_idxs,
                dom_indexes.root_indice,
                &window_size,
                &mut dom_indexes,
                &mut css_parse_cache,
                &mut flattened_css_cache,
                &vec![],
                &mut css_parser,
                HashMap::new(),
                HashMap::new(),
            );

        Self {
            url,
            nodes_idxs,
            nodes: nodes_table,
            node_styles,
            layout_table,
            node_layout_mapping,
            containing_nodes,
            request_cache,
            pending_image_fetches: HashSet::new(),
            rendered_nodes_ordered,
            hovering,
            tokio,
            resolved_font_sizes,
            resolved_pixmaps: HashMap::new(),
            window_size,
            font_handler,
            pending_dom_update: false,
            event_loop_notify: Rc::new(tokio::sync::Notify::new()),
            scroll_y: HashMap::new(),
            layout_roots: vec![],
            resolved_specified_heights: HashMap::new(),
            resolved_specified_widths: HashMap::new(),
            resolved_content_sizes: HashMap::new(),
            resolved_heights: HashMap::new(),
            resolved_widths: HashMap::new(),
            dom_indexes,
            canvas_buffers: HashMap::new(),
            pending_canvas_update: false,
            network_fetch,
            cached_rasterizations: CachedRasterizations::new(),
            animations: vec![],
            cached_text_buffers: HashMap::new(),
            css_parse_cache,
            flattened_css_cache,
            variable_definitions,
            focusable: None,
            event_loop_proxy: None,
            hovering_impact,
            frames: HashMap::new(),
            css_parser,
            workers: HashMap::new(),
            tracking_intersection: vec![],
            nodes_intersecting: HashSet::new(),
            blob_store,
            images_nodes_loaded: HashMap::new(),
        }
    }

    fn track_intersection(&mut self, node_idx: usize) {
        self.tracking_intersection.push(node_idx);
        let _ = self
            .event_loop_proxy
            .as_ref()
            .unwrap()
            .fire_user_event(UserEvent::IntersectionTracked);
    }

    fn untrack_intersection(&mut self, node_idx: usize) {
        self.tracking_intersection.retain(|idx| *idx != node_idx);
        self.nodes_intersecting.remove(&node_idx);
    }

    fn layout_inside_viewport(&self, layout: &LayoutBox, layout_box_id: usize) -> bool {
        let rendered_node = self
            .rendered_nodes_ordered
            .iter()
            .find(|n| n.layout_box_idx == layout_box_id);
        let offset_x = layout.rect.x + rendered_node.map(|n| n.offset_x).unwrap_or(0);
        let offset_y = layout.rect.y + rendered_node.map(|n| n.offset_y).unwrap_or(0);
        let clip = rendered_node.map(|node| node.clip).unwrap_or_else(|| {
            PaintClip::viewport(self.window_size.width, self.window_size.height)
        });
        offset_x + layout.rect.width as i32 > clip.start_x
            && offset_x < clip.end_x
            && offset_y + layout.rect.height as i32 >= clip.start_y
            && offset_y < clip.end_y
    }

    fn compute_intersections(&mut self) -> (Vec<usize>, Vec<usize>) {
        let mut intersecting = vec![];
        let mut not_intersecting = vec![];
        for node_idx in self.tracking_intersection.iter() {
            let Some(layout_idx) = self.node_layout_mapping.get(node_idx) else {
                continue;
            };
            let Some(layout) = self.layout_table.get(layout_idx) else {
                let changed = self.nodes_intersecting.remove(node_idx);
                if changed {
                    not_intersecting.push(*node_idx);
                }
                continue;
            };
            if !self.layout_inside_viewport(layout, *layout_idx) {
                let changed = self.nodes_intersecting.remove(node_idx);
                if changed {
                    not_intersecting.push(*node_idx);
                }
                continue;
            }
            let new = self.nodes_intersecting.insert(*node_idx);
            if new {
                intersecting.push(*node_idx);
            }
        }
        (intersecting, not_intersecting)
    }

    fn element_has_loaded(&self, node_idx: usize, phase: &LoadPhase) -> bool {
        let Some(node) = self.nodes.get(node_idx) else {
            return false;
        };
        match node {
            Node::Element(element) => {
                if element.tag == "iframe" {
                    *phase == LoadPhase::IframeDone
                } else if element.tag == "img" {
                    self.images_nodes_loaded.contains_key(&node_idx)
                } else {
                    *phase == LoadPhase::JsDone
                }
            }
            _ => *phase == LoadPhase::JsDone,
        }
    }

    fn query_selector_all(
        &mut self,
        selector: String,
        required_parent: Option<usize>,
    ) -> Vec<usize> {
        let mut matches = Vec::new();
        for selector in split_ignoring_parentheses(selector, ',', &[]) {
            let selector = selector_to_parts(
                &selector.trim().to_string(),
                &mut self.css_parser.class_definitions,
            );
            matches.extend(query_selector_all(
                &self.nodes,
                selector,
                &self.window_size,
                &self.dom_indexes,
                &self.get_hover_chain(),
                required_parent,
            ));
        }
        matches.sort_unstable();
        matches.dedup();
        matches
    }

    fn query_selector_all_nodes(
        &mut self,
        selector: String,
        required_parent: Option<usize>,
    ) -> Vec<(usize, Node)> {
        let node_idxs = self.query_selector_all(selector, required_parent);
        let owned = node_idxs
            .into_iter()
            .map(|idx| (idx, self.nodes.get(idx).unwrap().clone()))
            .collect();
        owned
    }

    fn query_selector_node(
        &mut self,
        selector: String,
        required_parent: Option<usize>,
    ) -> Option<(usize, Node)> {
        let node_idxs = self.query_selector_all(selector, required_parent);
        let node = node_idxs.first();
        let owned = node
            .cloned()
            .map(|idx| (idx, self.nodes.get(idx).unwrap().clone()));
        owned
    }

    fn replace_inner_html(&mut self, node_idx: usize, html: String) {
        self.remove_children(node_idx);
        self.create_children_from_html(node_idx, html);
        self.recompute_dom_indexes();
        self.schedule_dom_update();
    }

    fn create_element(&mut self, tag: String) -> usize {
        self.push_node(Node::Element(Element {
            tag,
            attributes: Attributes::new(),
            parent: None,
        }));
        let node_idx = self.nodes.cursor;
        self.dom_indexes.children_index.insert(node_idx, vec![]);
        node_idx
    }

    fn get_elements_by_tag_name(
        &self,
        tag: &String,
        required_parent: Option<usize>,
    ) -> Vec<(usize, Node)> {
        let tag = tag.to_ascii_lowercase();
        let mut nodes: Vec<(usize, Node)> = if tag == "*" {
            self.nodes_idxs
                .iter()
                .filter_map(|idx| {
                    let node = self.nodes.get(*idx)?;
                    matches!(node, Node::Element(_)).then(|| (*idx, node.clone()))
                })
                .filter(|(idx, node)| {
                    node.get_parent().is_some() || *idx == self.dom_indexes.root_indice
                })
                .collect()
        } else if let Some(idxs) = self.dom_indexes.tag_elements.get(&tag) {
            idxs.ones()
                .map(|idx| (idx, self.nodes.get(idx).unwrap().clone()))
                .filter(|(idx, node)| {
                    node.get_parent().is_some() || *idx == self.dom_indexes.root_indice
                })
                .collect()
        } else {
            vec![]
        };
        if let Some(required_parent) = required_parent {
            nodes = nodes
                .into_iter()
                .filter(|(idx, _)| has_parent(&self.nodes, *idx, required_parent))
                .collect();
        }
        nodes
    }

    fn get_elements_by_name(
        &self,
        name: &str,
        required_parent: Option<usize>,
    ) -> Vec<(usize, Node)> {
        let mut nodes: Vec<(usize, Node)> =
            if let Some(idxs) = self.dom_indexes.attribute_elements.get("name") {
                idxs.ones()
                    .filter_map(|idx| match self.nodes.get(idx) {
                        Some(Node::Element(element))
                            if element
                                .attributes
                                .get_str("name")
                                .is_some_and(|element_name| element_name == name) =>
                        {
                            Some((idx, self.nodes.get(idx).unwrap().clone()))
                        }
                        _ => None,
                    })
                    .filter(|(idx, node)| {
                        node.get_parent().is_some() || *idx == self.dom_indexes.root_indice
                    })
                    .collect()
            } else {
                vec![]
            };
        if let Some(required_parent) = required_parent {
            nodes = nodes
                .into_iter()
                .filter(|(idx, _)| has_parent(&self.nodes, *idx, required_parent))
                .collect();
        }
        nodes
    }

    fn get_elements_by_class_name(
        &self,
        class_names: &String,
        required_parent: Option<usize>,
    ) -> Vec<(usize, Node)> {
        let classes = class_names.split_whitespace().collect::<Vec<_>>();
        if classes.is_empty() {
            return vec![];
        }

        let class_indexes = classes
            .iter()
            .map(|class| {
                self.css_parser
                    .class_definitions
                    .class_to_idx
                    .get(*class)
                    .copied()
            })
            .collect::<Option<Vec<_>>>();
        let Some(class_indexes) = class_indexes else {
            return vec![];
        };

        let class_bitsets = class_indexes
            .iter()
            .map(|idx| self.dom_indexes.class_elements.get(*idx))
            .collect::<Option<Vec<_>>>();
        let Some(class_bitsets) = class_bitsets else {
            return vec![];
        };

        let required_parent = required_parent.unwrap_or(self.dom_indexes.root_indice);
        let mut valid_idxs = class_bitsets[0].clone();
        for bitset in class_bitsets.iter().skip(1) {
            valid_idxs.intersect_with(bitset);
        }
        valid_idxs
            .ones()
            .filter(|idx| has_parent(&self.nodes, *idx, required_parent))
            .map(|idx| (idx, self.nodes.get(idx).unwrap().clone()))
            .collect()
    }

    fn update_element_attributes(&mut self, node_idx: usize, attributes: Attributes) -> Result<()> {
        let mut changed = false;
        match self
            .nodes
            .get_mut(node_idx)
            .with_context(|| "Failed to get node")?
        {
            Node::Element(element) => {
                for (key, value) in attributes.values {
                    if element
                        .attributes
                        .values
                        .get(&key)
                        .is_some_and(|current| current == &value)
                    {
                        continue;
                    }
                    if key == "id" {
                        if let Some(existing_id) = element.attributes.get_str("id") {
                            self.dom_indexes
                                .remove_id_node(&existing_id.into_owned(), node_idx);
                        }
                        self.dom_indexes.add_id_node(&value, node_idx);
                    }
                    if key == "class" {
                        if let Some(existing_id) = element.attributes.get_str("class") {
                            self.dom_indexes.remove_class_node(
                                &existing_id.into_owned(),
                                node_idx,
                                &mut self.css_parser.class_definitions,
                            );
                        }
                        self.dom_indexes.add_class_node(
                            &value,
                            node_idx,
                            &mut self.css_parser.class_definitions,
                        );
                    }
                    if !element.attributes.contains_key(&key) {
                        self.dom_indexes.add_attribute_node(&key, node_idx);
                    }
                    element.attributes.insert(key, value);
                    changed = true;
                }
            }
            _ => {}
        };
        if changed {
            self.schedule_dom_update();
        }
        Ok(())
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
        self.resolved_content_sizes.clear();
        self.resolved_heights.clear();
        self.resolved_widths.clear();
    }

    fn replace_document(&mut self, url: String, nodes_table: NodesTable, nodes_idxs: Vec<usize>) {
        self.url = url;
        self.nodes = nodes_table;
        self.nodes_idxs = nodes_idxs;
        self.hovering = None;
        self.pending_dom_update = false;
        self.scroll_y.clear();
        self.canvas_buffers.clear();
        self.pending_canvas_update = false;
        self.animations.clear();
        self.clear_layout_state();
        self.recompute_nodes();
    }

    fn get_implicit_click_events(&self, node_idx: usize) -> Vec<(usize, HtmlEvent)> {
        let Some(node) = self.nodes.get(node_idx) else {
            return vec![];
        };
        let mut events = vec![];
        if let Node::Element(element) = node {
            if element.tag == "label" {
                if let Some(for_attr) = element.attributes.get_str("for") {
                    if let Some(for_elements) = self.dom_indexes.id_elements.get(for_attr.as_ref())
                    {
                        for el in for_elements.ones() {
                            let node = self.nodes.get(el).unwrap();
                            if let Node::Element(element) = node {
                                if element.tag == "input"
                                    && element
                                        .attributes
                                        .get_str("type")
                                        .is_some_and(|v| v == "radio")
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

    fn get_scrollable_dimensions(&self) -> Option<(usize, u32, u32)> {
        if let Some(hovering) = self.get_scrollable_node_idx() {
            let hovering_layout_idx = self.node_layout_mapping.get(&hovering).unwrap();
            if let Some(layout) = self.layout_table.get(hovering_layout_idx) {
                return Some((hovering, layout.content_height, layout.rect.height));
            }
        }
        // TODO: This might not cover all cases, like maybe the HTML tag can be larger than the window? Idk. Might wanna add some scroll logic that is independent from nodes.
        let layout_root_idx = self.layout_roots.first()?;
        let root_node_idx = self.layout_to_node_idx(&layout_root_idx);
        let root_height = self
            .layout_table
            .get(&layout_root_idx)
            .and_then(|l| Some(l.content_height))
            .unwrap();
        Some((root_node_idx, root_height, self.window_size.height))
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
        if style.is_some_and(|style| style.overflow_y.allows_user_scroll()) && allow_scroll {
            Some(node_idx)
        } else if let Some(parent) = self.nodes.get(node_idx).and_then(|n| n.get_parent()) {
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

    pub fn extract_script_from_idx(&self, idx: usize) -> Option<Script> {
        match self.nodes.get(idx).unwrap() {
            Node::Element(element) => {
                if element.tag != "script" || !self.node_is_connected(idx) {
                    return None;
                }

                let script_type =
                    parse_script_type_attr(element.attributes.get_str("type").as_deref())?;
                let src = element.attributes.get_str("src");
                let has_src = src.is_some();
                let is_async = has_src && element.attributes.get_str("async").is_some();
                let defer = has_src && !is_async && element.attributes.get_str("defer").is_some();
                if let Some(src) = src {
                    return Some(Script {
                        content: ScriptContent::Link(src.to_string()),
                        script_type,
                        node_idx: Some(idx),
                        defer,
                        is_async,
                    });
                }

                let children = &self.dom_indexes.children_index.get(&idx).unwrap();
                if children.len() != 1 {
                    println!("Unexpected children count: {}", children.len());
                    return None;
                }
                let child = children.first().unwrap();
                let child_node = &self.nodes.get(*child).unwrap();

                let text = match child_node {
                    Node::Element(element) => {
                        println!("Got element when expecting JS text {:?}", element);
                        return None;
                    }
                    Node::Text(text_element) => Some(Script {
                        content: ScriptContent::Code(text_element.text.clone()),
                        script_type,
                        node_idx: Some(idx),
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
    }

    fn node_is_connected(&self, idx: usize) -> bool {
        if idx == self.dom_indexes.root_indice {
            return true;
        }

        let Some(parent) = self.nodes.get(idx).and_then(|node| node.get_parent()) else {
            return false;
        };

        self.node_is_connected(parent)
    }

    pub fn get_scripts(&mut self) -> Vec<Script> {
        let mut scripts: Vec<Script> = self
            .nodes_idxs
            .iter()
            .filter(|node_idx| match self.nodes.get(**node_idx).unwrap() {
                Node::Element(element) => element.tag == "script",
                _ => false,
            })
            .map(|idx| -> Option<Script> { self.extract_script_from_idx(*idx) })
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
        if let Some(node) = self.nodes.get(idx) {
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
        if let Some(node) = self.nodes.get(node_idx) {
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
        let Some(Node::Element(element)) = self.nodes.get(form) else {
            return Err(anyhow!("Failed to get form node"));
        };
        let action = element.attributes.get_str("action").map(|v| v.into_owned());
        let method = element.attributes.get_str("method").map(|v| v.into_owned());
        let inputs = self.collect_inputs_in_form(form, submitted_by);
        let mut entries = vec![];
        for input in inputs {
            let Some(Node::Element(element)) = self.nodes.get(input) else {
                continue;
            };
            let Some(name) = element.attributes.get_str("name") else {
                continue;
            };
            entries.push((name.into_owned(), form_control_value(element)));
        }

        let navigation =
            build_form_navigation(&self.url, action.as_deref(), method.as_deref(), &entries)?;

        let proxy = self.event_loop_proxy.as_ref().unwrap();
        proxy
            .fire_user_event(UserEvent::Navigate((
                UserNavigateUrl::Form(navigation),
                true,
            )))
            .unwrap();

        Ok(())
    }

    fn resolve_pending_canvas_images(&mut self) {
        let dirty_canvas_idxs = self
            .canvas_buffers
            .iter()
            .filter_map(|(idx, canvas)| canvas.dirty.then_some(*idx))
            .collect::<Vec<_>>();

        for canvas_idx in dirty_canvas_idxs {
            let image_keys = self
                .canvas_buffers
                .get(&canvas_idx)
                .map(|canvas| {
                    canvas
                        .commands
                        .iter()
                        .filter_map(|command| match command {
                            CanvasPathCommand::DrawImage {
                                image_node_idx,
                                image_width,
                                image_height,
                                ..
                            } => Some((*image_node_idx, *image_width, *image_height)),
                            _ => None,
                        })
                        .collect::<HashSet<CanvasImageKey>>()
                })
                .unwrap_or_default();

            let resolved_images = image_keys
                .into_iter()
                .map(|image_key @ (image_node_idx, image_width, image_height)| {
                    let image = self
                        .decode_and_rasterize_img(
                            image_node_idx,
                            &LayoutMode::Complete,
                            image_height,
                            image_width,
                            None,
                            None,
                        )
                        .map(|(image, _, _, _)| image);
                    (image_key, image)
                })
                .collect::<Vec<_>>();

            if let Some(canvas) = self.canvas_buffers.get_mut(&canvas_idx) {
                for (image_key, image) in resolved_images {
                    if let Some(image) = image {
                        canvas.images.insert(image_key, image);
                    } else {
                        canvas.images.remove(&image_key);
                    }
                }
            }
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
        }
        self.resolve_pending_canvas_images();
        let mut new_rendered_nodes_ordered = vec![];
        let mut deferred_z_index = vec![];
        let viewport_clip = PaintClip::viewport(width, height);
        for layout_box_idx in self.layout_roots.clone().iter() {
            self.paint_layout_box(
                *layout_box_idx,
                buffer,
                width,
                height,
                0,
                0,
                viewport_clip,
                &mut new_rendered_nodes_ordered,
                &mut deferred_z_index,
                true,
            );
        }
        self.paint_deferred_z_index(
            &mut deferred_z_index,
            buffer,
            width,
            height,
            &mut new_rendered_nodes_ordered,
        );
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
        } else if src.ends_with(".gif") {
            Some("image/gif")
        } else if src.ends_with(".webp") {
            Some("image/webp")
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
                "image/gif" => Ok(RequestCacheEntry::GifData(resp.bytes().await?)),
                "image/webp" => Ok(RequestCacheEntry::WebpData(resp.bytes().await?)),
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
        let requests: Vec<(ReqwestUrl, &'static str)> = self
            .nodes
            .iter()
            .filter_map(|(idx, n)| match n {
                Node::Element(element)
                    if element.tag == "img"
                        && self
                            .node_styles
                            .get(&idx)
                            .is_some_and(|v| v.display != StyleDisplay::None) =>
                {
                    element
                        .attributes
                        .get_str("src")
                        .map(|src| src.into_owned())
                }
                _ => None,
            })
            .filter(|src| !src.starts_with("data:"))
            .filter_map(|src| {
                let src_extension = Self::img_src_extension(&src)?;
                let url = match resolve_url(&src, Some(&base)) {
                    Ok(url) => url,
                    Err(err) => {
                        println!("Failed to resolve image URL {}: {}", src, err);
                        return None;
                    }
                };
                if self.request_cache.contains_key(&url)
                    || !self.pending_image_fetches.insert(url.clone())
                {
                    return None;
                }

                Some((url, src_extension))
            })
            .collect();

        if requests.is_empty() {
            return;
        }

        println!("Pre-fetching {} images", requests.len());

        let cookie_jar = Arc::clone(&self.network_fetch.borrow().cookie_jar);
        let proxy = self.event_loop_proxy.clone();
        std::thread::spawn(move || {
            let runtime = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .expect("Failed to create tokio runtime for image prefetch");
            let client = reqwest::Client::builder()
                .cookie_provider(cookie_jar)
                .user_agent(USER_AGENT)
                .build()
                .expect("Failed to create HTTP client for image prefetch");

            let entries = runtime.block_on(async move {
                let mut join_set = tokio::task::JoinSet::new();
                for (url, src_extension) in requests {
                    let client = client.clone();
                    join_set.spawn(Self::fetch_img_src_data_url(client, url, src_extension));
                }

                let mut entries = Vec::new();
                while let Some(result) = join_set.join_next().await {
                    match result {
                        Ok((url, cache_entry)) => {
                            let entry = match cache_entry {
                                Ok(entry) => entry,
                                Err(err) => {
                                    println!("Failed to prefetch img src {}: {}", url, err);
                                    RequestCacheEntry::Unsupported
                                }
                            };
                            entries.push((url, entry));
                        }
                        Err(err) => println!("Failed to join image fetch task: {}", err),
                    }
                }
                entries
            });

            if entries.is_empty() {
                return;
            }
            if let Some(proxy) = proxy {
                let _ = proxy.fire_user_event(UserEvent::ImagesPrefetched(entries));
            }
        });
    }

    fn finish_image_prefetch(&mut self, entries: Vec<(ReqwestUrl, RequestCacheEntry)>) {
        for (url, entry) in entries {
            self.pending_image_fetches.remove(&url);
            self.request_cache.insert(url, entry);
        }
    }

    fn spawn_worker(&mut self, src: &str) -> Result<()> {
        let handle = WorkerHandle {};
        let url = self.url.clone();
        let inner_src = src.to_string();
        let network = NetworkFetch::new();
        std::thread::spawn(move || {
            let blob_store = Arc::new(BlobStore::default());
            let broadcast_channel = InMemoryBroadcastChannel::default();
            let mut runtime = deno_core::JsRuntime::new(deno_core::RuntimeOptions {
                module_loader: Some(Rc::new(HttpModuleLoader::new(network.client.clone()))),
                extensions: vec![
                    browser_worker::init(),
                    deno_webidl::deno_webidl::init(),
                    deno_web::deno_web::init(blob_store, None, broadcast_channel),
                    deno_net::deno_net::init(None, None),
                    deno_fetch_without_telemetry(),
                    deno_node_crypto_shim::init(),
                    deno_crypto::deno_crypto::init(None),
                ],
                ..Default::default()
            });
            let tokio = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .expect("Failed to create tokio runtime in worker thread");
            let Ok(base) = ReqwestUrl::parse(&url) else {
                return;
            };
            let Ok(url) = resolve_url(&inner_src, Some(&base)) else {
                return;
            };
            let fetch = async || -> Result<String> {
                if let Some(stripped) = url.as_str().strip_prefix("file://") {
                    let contents = fs::read_to_string(stripped)?;
                    Ok(contents)
                } else {
                    let code = network.client.get(url.clone()).send().await?.text().await?;
                    Ok(code)
                }
            };
            let code = match tokio.block_on(fetch()) {
                Ok(code) => code,
                Err(err) => {
                    eprintln!("Failed to fetch JS in worker thread: {}", err);
                    return;
                }
            };
            match runtime.execute_script(url, code) {
                Ok(_) => {}
                Err(err) => {
                    eprintln!("Failed to execute JS in worker thread: {}", err);
                    return;
                }
            };
            let future = runtime.run_event_loop(Default::default());
            let _ = tokio.block_on(future).inspect_err(|err| {
                eprintln!("Failed to run worker thread: {}", err);
            });
        });
        if self.workers.contains_key(src) {
            // TODO: Should kill the thread here
        }
        self.workers.insert(src.to_string(), handle);
        Ok(())
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
                cursor: Position { x: 0, y: 0 },
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

    fn decode_and_rasterize_img(
        &mut self,
        node_idx: usize,
        mode: &LayoutMode,
        input_h: Option<u32>,
        input_w: Option<u32>,
        max_h: Option<u32>,
        max_w: Option<u32>,
    ) -> Option<(Pixmap, u32, u32, bool)> {
        let Some(node) = self.nodes.get(node_idx) else {
            return None;
        };
        let Node::Element(element) = node else {
            return None;
        };
        let style = self
            .node_styles
            .get(&node_idx)
            .map(|style| Cow::Borrowed(style))
            .unwrap_or_else(|| Cow::Owned(get_base_style(node, None)));
        let src = if element.tag == "video" {
            element.attributes.get_str("poster")?
        } else {
            element.attributes.get_str("src")?
        };
        let entry = if src.starts_with("data:") {
            if let Some(data) = src.strip_prefix("data:image/svg+xml,") {
                let mut decoded = percent_encoding::percent_decode_str(data)
                    .decode_utf8()
                    .ok()?
                    .to_string();
                self.inject_css_variables_into_str(&mut decoded, &style.variables);
                Some(RequestCacheEntry::SvgData(decoded))
            } else {
                None
            }
        } else if src.starts_with("blob") {
            let url = url::Url::parse(&src).ok()?;
            let blob = self.blob_store.get_object_url(url)?;
            let bytes = self.tokio.borrow_mut().block_on(blob.read_all());
            sniff_image_data(bytes)
        } else {
            self.get_img_src_data(&src)
        };
        let result = match entry {
            Some(RequestCacheEntry::PngData(bytes)) => rasterize_png(
                &mut self.cached_rasterizations,
                &src,
                &bytes,
                input_w,
                input_h,
                max_w,
                max_h,
                mode,
            )
            .inspect_err(|err| println!("Failed to rasterize PNG: {}", err))
            .ok()?,
            Some(RequestCacheEntry::JpegData(bytes)) => {
                let (target_h, target_w) = prepare_jpeg(
                    &mut self.cached_rasterizations,
                    &src,
                    &bytes,
                    input_w,
                    input_h,
                    max_w,
                    max_h,
                )
                .inspect_err(|err| println!("Failed to rasterize JPEG: {}", err))
                .ok()?;
                let (target_h, target_w) = (target_h.max(1), target_w.max(1));
                if *mode == LayoutMode::Complete {
                    let pixmap =
                        rasterize_jpeg(&mut self.cached_rasterizations, &src, target_w, target_h)
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
            Some(RequestCacheEntry::SvgData(svg_data)) => {
                let mut injected = svg_data.clone();
                self.inject_css_variables_into_str(&mut injected, &style.variables);
                let result = rasterize_svg(
                    &mut self.cached_rasterizations,
                    &injected,
                    input_w,
                    input_h,
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
            Some(RequestCacheEntry::GifData(bytes)) => {
                let (target_h, target_w) = prepare_gif(
                    &mut self.cached_rasterizations,
                    &src,
                    &bytes,
                    input_w,
                    input_h,
                    max_w,
                    max_h,
                )
                .unwrap();
                let (target_h, target_w) = (target_h.max(1), target_w.max(1));
                if *mode == LayoutMode::Complete {
                    let pixmap =
                        rasterize_gif(&mut self.cached_rasterizations, &src, target_w, target_h)
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
            Some(RequestCacheEntry::WebpData(bytes)) => {
                let (target_h, target_w) = prepare_webp(
                    &mut self.cached_rasterizations,
                    &src,
                    &bytes,
                    input_w,
                    input_h,
                    max_w,
                    max_h,
                )
                .inspect_err(|err| println!("Failed to decode WebP: {}", err))
                .ok()?;
                let (target_h, target_w) = (target_h.max(1), target_w.max(1));
                if *mode == LayoutMode::Complete {
                    let pixmap =
                        rasterize_webp(&mut self.cached_rasterizations, &src, target_w, target_h)
                            .inspect_err(|err| println!("Failed to rasterize WebP: {}", err))
                            .ok()?;
                    let opaque = pixmap_is_opaque(&pixmap);
                    (pixmap, target_h, target_w, opaque)
                } else {
                    (
                        Pixmap::new(target_w, target_h).unwrap(),
                        target_h,
                        target_w,
                        false,
                    )
                }
            }
            _ => return None,
        };
        self.images_nodes_loaded
            .insert(node_idx, (result.1, result.2));
        Some(result)
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
        let node = &self.nodes.get(node_idx).unwrap();
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
        let node = &self.nodes.get(node_idx).unwrap();
        let mut str = String::new();
        match node {
            Node::Text(element) => {
                str += &element.text;
            }
            Node::Element(element) => {
                str += "<";
                str += &element.tag;
                for (key, value) in element.attributes.values.iter() {
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

    fn get_img_src_data(&self, src: &str) -> Option<RequestCacheEntry> {
        let base = ReqwestUrl::parse(&self.url).ok()?;
        let url = resolve_url(src, Some(&base)).ok()?;
        match self.request_cache.get(&url) {
            Some(RequestCacheEntry::Unsupported) | None => None,
            Some(entry) => Some(entry.clone()),
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
                    .get(node_idx)
                    .unwrap()
                    .get_parent()
                    .unwrap_or(node_idx),
            )
            .unwrap_or(&16);
        *resolved_parent_font_size
    }

    fn get_line_height(&self, style: &Style, font_size: u32) -> Option<u32> {
        get_specified_size(
            font_size,
            &style.line_height,
            Some(font_size),
            None,
            &self.window_size,
            &SizeUnit::Em,
        )
        .and_then(|value| (value > 0).then_some(value as u32))
    }

    fn resolve_transform_offset(&self, style: &Style, layout_box: &LayoutBox) -> (i32, i32) {
        let StyleTransform::Operations(operations) = &style.transform else {
            return (0, 0);
        };

        let font_size = self
            .resolved_font_sizes
            .get(&layout_box.node_idx)
            .cloned()
            .unwrap_or(16);
        let mut offset_x = 0;
        let mut offset_y = 0;
        for operation in operations {
            match operation {
                StyleTransformOperation::Translate { x, y } => {
                    offset_x += get_specified_size(
                        font_size,
                        x,
                        Some(layout_box.rect.width),
                        Some(0),
                        &self.window_size,
                        &SizeUnit::Px,
                    )
                    .unwrap_or(0);
                    offset_y += get_specified_size(
                        font_size,
                        y,
                        Some(layout_box.rect.height),
                        Some(0),
                        &self.window_size,
                        &SizeUnit::Px,
                    )
                    .unwrap_or(0);
                }
            }
        }

        (offset_x, offset_y)
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
        if *mode == LayoutMode::Complete {
            self.resolved_widths.remove(&node_idx);
            self.resolved_heights.remove(&node_idx);
        }

        match self.nodes.get(node_idx).unwrap().clone() {
            Node::Comment(_) => None,
            Node::Text(text) => {
                let style = self.node_styles.get(&node_idx).unwrap();
                let text = collapse_whitespace(&text.text).unwrap_or("".to_string());
                let text_hex = match style.color {
                    StyleBackground::Hex(code) => Some(code),
                    _ => None,
                }?;
                let max_width = Some(available_size.width);
                let line_height = self.get_line_height(style, resolved_font_size);
                let cache_key = (
                    text.clone(),
                    resolved_font_size,
                    max_width,
                    line_height,
                    text_hex,
                );
                let (buffer, width, height) =
                    if let Some(cached) = self.cached_text_buffers.get(&cache_key) {
                        cached
                    } else {
                        let result = text_to_buffer_with_line_height(
                            &self.font_handler,
                            text_hex,
                            &text.clone(),
                            resolved_font_size,
                            max_width,
                            line_height,
                        )?;
                        self.cached_text_buffers.insert(cache_key.clone(), result);
                        self.cached_text_buffers.get(&cache_key)?
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
                            border_radius: BorderRadius::new_empty(),
                        },
                        // TODO: Can probably avoid cloning here
                        kind: LayoutKind::Text(buffer.clone()),
                        children: vec![],
                        node_idx,
                        content_height: *height,
                        z_index: 0,
                    },
                    save_as_final,
                ))
            }
            Node::Element(element) => {
                if element.tag == "svg"
                    || element.tag == "img"
                    || element.tag == "video"
                    || element.tag == "canvas"
                {
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
                        containing_node_idx,
                    );
                    let (containing_block_height, containing_block_width) =
                        self.get_containing_block_size(containing_node_idx, node_idx, &style);
                    let max_h = get_specified_size(
                        resolved_font_size as u32,
                        &style.max_height,
                        containing_block_height,
                        None,
                        &self.window_size,
                        &SizeUnit::Px,
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
                        &SizeUnit::Px,
                    )
                    .map(|width| width as u32)
                    .unwrap_or(
                        container_size
                            .container_width_non_filling
                            .unwrap_or(available_size.width),
                    );
                    let (kind, height, width) = match element.tag.as_str() {
                        "canvas" => {
                            let (Some(canvas_width), Some(canvas_height)) =
                                (match self.nodes.get(node_idx).unwrap() {
                                    Node::Element(element) => (
                                        element
                                            .attributes
                                            .get_str("width")
                                            .and_then(|v| v.parse::<u32>().ok())
                                            .or(Some(150)),
                                        element
                                            .attributes
                                            .get_str("height")
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
                            (
                                LayoutKind::Canvas,
                                container_size.container_height,
                                container_size.container_width,
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
                                Some(max_w),
                                Some(max_h),
                                &style,
                                mode,
                            );
                            match result {
                                Err(err) => {
                                    println!("Failed to rasterize SVG data: {}", err);
                                    return None;
                                }
                                Ok((pixmap, height, width, opaque)) => {
                                    (LayoutKind::PixMap((pixmap, opaque)), height, width)
                                }
                            }
                        }
                        "img" | "video" => {
                            let result = self.decode_and_rasterize_img(
                                node_idx,
                                mode,
                                container_size.container_height_non_filling,
                                container_size.container_width_non_filling,
                                Some(max_h),
                                Some(max_w),
                            );
                            if result.is_none() && element.tag == "img" {
                                let (height, width) =
                                    container_size.image_placeholder_size(max_w, max_h);
                                (
                                    LayoutKind::PixMap((Pixmap::new(1, 1).unwrap(), false)),
                                    height,
                                    width,
                                )
                            } else {
                                let (pixmap, height, width, opaque) = result?;
                                (LayoutKind::PixMap((pixmap, opaque)), height, width)
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
                                border_radius: BorderRadius::new_empty(),
                            },
                            kind,
                            children: vec![],
                            node_idx,
                            content_height: height,
                            z_index,
                        },
                        save_as_final,
                    ))
                } else if element.tag == "iframe" {
                    let style = self.node_styles.get(&node_idx).unwrap();
                    if style.display == StyleDisplay::None {
                        return None;
                    }
                    let height = element
                        .attributes
                        .get_str("height")
                        .and_then(|v| v.parse::<f32>().ok())
                        .unwrap_or(150.) as u32;
                    let width = element
                        .attributes
                        .get_str("width")
                        .and_then(|v| v.parse::<f32>().ok())
                        .unwrap_or(300.) as u32;
                    let url = element.attributes.get_str("src");
                    let z_index = match style.z_index {
                        StyleZIndex::Auto => 0,
                        StyleZIndex::Number(value) => value,
                    };
                    if !self.frames.contains_key(&node_idx) {
                        let handle = self
                            .spawn_frame(
                                url.and_then(|v| Some(v.into_owned())),
                                PhysicalSize { width, height },
                                node_idx,
                            )
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
                                border_radius: BorderRadius::new_empty(),
                            },
                            kind: LayoutKind::Iframe,
                            children: vec![],
                            node_idx,
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
                        let border = RectBorder {
                            left: RectBorderSide::parse_from_style(
                                &style.border_left,
                                &style,
                                resolved_font_size,
                                &available_size,
                                &self.window_size,
                            ),
                            top: RectBorderSide::parse_from_style(
                                &style.border_top,
                                &style,
                                resolved_font_size,
                                &available_size,
                                &self.window_size,
                            ),
                            right: RectBorderSide::parse_from_style(
                                &style.border_right,
                                &style,
                                resolved_font_size,
                                &available_size,
                                &self.window_size,
                            ),
                            bottom: RectBorderSide::parse_from_style(
                                &style.border_bottom,
                                &style,
                                resolved_font_size,
                                &available_size,
                                &self.window_size,
                            ),
                        };
                        let z_index = match style.z_index {
                            StyleZIndex::Auto => 0,
                            StyleZIndex::Number(value) => value,
                        };

                        let border_radius = BorderRadius {
                            top_left: get_specified_size(
                                resolved_font_size,
                                &style.border_radius_top_left,
                                Some(available_size.width),
                                None,
                                &self.window_size,
                                &SizeUnit::Px,
                            )
                            .unwrap_or(0)
                            .max(0) as u32,
                            top_right: get_specified_size(
                                resolved_font_size,
                                &style.border_radius_top_right,
                                Some(available_size.width),
                                None,
                                &self.window_size,
                                &SizeUnit::Px,
                            )
                            .unwrap_or(0)
                            .max(0) as u32,
                            bottom_right: get_specified_size(
                                resolved_font_size,
                                &style.border_radius_bottom_right,
                                Some(available_size.width),
                                None,
                                &self.window_size,
                                &SizeUnit::Px,
                            )
                            .unwrap_or(0)
                            .max(0) as u32,
                            bottom_left: get_specified_size(
                                resolved_font_size,
                                &style.border_radius_bottom_left,
                                Some(available_size.width),
                                None,
                                &self.window_size,
                                &SizeUnit::Px,
                            )
                            .unwrap_or(0)
                            .max(0) as u32,
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
                                containing_node_idx,
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
                                    border_radius,
                                },
                                kind: LayoutKind::Element,
                                children,
                                node_idx,
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

    fn spawn_frame(
        &mut self,
        url: Option<String>,
        size: PhysicalSize<u32>,
        node_idx: usize,
    ) -> Result<FrameHandle> {
        let (tx, rx) = std::sync::mpsc::channel();
        let latest_bitmap = Arc::new(Mutex::new(vec![0; (size.width * size.height) as usize]));
        let bitmap_for_thread = Arc::clone(&latest_bitmap);
        let parent_proxy = self.event_loop_proxy.as_ref().unwrap().clone();
        tx.send(FrameCommand::Render).unwrap();
        let tx_proxy = RendererProxy::FrameLoop(tx.clone());
        std::thread::spawn(move || {
            let mut frame = Frame::new(
                url.clone().unwrap_or("about:blank".to_string()),
                false,
                size,
            );
            frame.is_top = false;

            let frame_result = frame.open();
            match frame_result {
                Ok(params) => {
                    let _ = frame
                        .set_up_without_event_loop(params, tx_proxy)
                        .inspect_err(|err| eprintln!("Failed to start iframe renderer: {:?}", err));
                }
                Err(err) => {
                    eprintln!("Failed to boot iframe frame: {:?}", err);
                    return;
                }
            }

            let start = Instant::now();
            let js_result = frame.run_js();
            println!(
                "Finished running JS code in {}ms: {:?}",
                Instant::now().duration_since(start).as_millis(),
                js_result
            );
            let _ = parent_proxy.fire_user_event(UserEvent::FrameLoaded(node_idx));

            let mut js_pending = true;
            loop {
                let cmd = if let Some(timeout) = frame.command_wait_timeout(js_pending) {
                    match rx.recv_timeout(timeout) {
                        Ok(cmd) => Some(cmd),
                        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => None,
                        Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => break,
                    }
                } else {
                    match rx.recv() {
                        Ok(cmd) => Some(cmd),
                        Err(_) => break,
                    }
                };
                let had_command = cmd.is_some();
                if let Some(cmd) = cmd {
                    frame.handle_frame_command(cmd, &parent_proxy, &size, &bitmap_for_thread);

                    while let Ok(cmd) = rx.try_recv() {
                        frame.handle_frame_command(cmd, &parent_proxy, &size, &bitmap_for_thread);
                    }
                }
                if had_command || js_pending {
                    js_pending = frame
                        .pump_js_event_loop_once()
                        .inspect_err(|err| {
                            eprintln!("Error occurred while pumping JS loop: {}", err)
                        })
                        .unwrap_or(false);
                }
                let _ = frame.run_animation_frame_if_due().inspect_err(|err| {
                    eprintln!("Error occurred while running animation frame: {}", err)
                });
            }
        });
        Ok(FrameHandle {
            surface: latest_bitmap,
            tx,
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
                    Some(container_size.container_width),
                    Some(container_size.container_height),
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
        containing_node_idx: usize,
    ) -> ContainerSizes {
        let (padding_left_size, padding_right_size, padding_top_size, padding_bottom_size) =
            self.get_paddings(node_idx, style, containing_node_idx);
        let (border_left_size, border_right_size, border_top_size, border_bottom_size) =
            self.get_border_sizes(node_idx, style, containing_node_idx);

        let (containing_block_height, containing_block_width) =
            self.get_containing_block_size(containing_node_idx, node_idx, &style);
        let containing_block_width = containing_block_width
            .filter(|width| *width > 0)
            .or(Some(available_size.width));
        let resolved_font_size = self.resolved_font_sizes.get(&node_idx).unwrap();

        let min_height = get_specified_size(
            *resolved_font_size,
            &style.min_height,
            containing_block_height,
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .and_then(|v| Some(v as u32));
        let max_height = get_specified_size(
            *resolved_font_size,
            &style.max_height,
            containing_block_height,
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .and_then(|v| Some(v as u32));
        let min_width = get_specified_size(
            *resolved_font_size,
            &style.min_width,
            containing_block_width,
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .and_then(|v| Some(v as u32));
        let max_width = get_specified_size(
            *resolved_font_size,
            &style.max_width,
            containing_block_width,
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .and_then(|v| Some(v as u32));

        let specified_width = forced_size.width.or(get_specified_size(
            *resolved_font_size,
            &style.width,
            containing_block_width,
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .and_then(|v| Some(v as u32)));
        let specified_height = forced_size.height.or(get_specified_size(
            *resolved_font_size,
            &style.height,
            containing_block_height,
            None,
            &self.window_size,
            &SizeUnit::Px,
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
        let container_height_non_filling = specified_height.map(|v| {
            v.min(max_height.unwrap_or(u32::MAX))
                .max(min_height.unwrap_or(u32::MIN))
        });
        let container_height = specified_height
            .or(min_height)
            .unwrap_or(available_size.height)
            .min(max_height.unwrap_or(u32::MAX))
            .max(min_height.unwrap_or(u32::MIN));
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
            has_specified_height: specified_height.is_some(),
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
        let cache_key = (text.clone(), font_size, None, None, text_hex);
        let (buffer, width, height) = if let Some(cached) = self.cached_text_buffers.get(&cache_key)
        {
            cached
        } else {
            let result = text_to_buffer(&self.font_handler, text_hex, &text, font_size, None)
                .with_context(|| "Failed to build pixmap for input text")?;
            self.cached_text_buffers.insert(cache_key.clone(), result);
            self.cached_text_buffers
                .get(&cache_key)
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
                    border_radius: BorderRadius::new_empty(),
                },
                // TODO: Could avoid a clone here
                kind: LayoutKind::Text(buffer.clone()),
                children: vec![],
                node_idx,
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
        column_span: i32,
        template_columns: &Vec<GridTemplateColumnsValue>,
    ) -> bool {
        // Are we out of columns?
        current_column + column_span > template_columns.len() as i32
    }

    fn calculate_grid_item_size(
        &self,
        template: &Vec<GridTemplateColumnsValue>,
        base_item_target: usize,
        to_distribute: u32,
        to_give: u32,
        max_total_fractions: i32,
        total_auto_columns: i32,
        max_sizes: &Vec<u32>,
    ) -> i32 {
        let Some(value) = &template.get(base_item_target) else {
            return 0;
        };
        match value {
            GridTemplateColumnsValue::Size(size) => match size {
                GridColumnSize::Px(px) => *px,
                GridColumnSize::Rem(rem) => (rem * 16.) as i32,
                GridColumnSize::Percent(percent) => {
                    (to_distribute as f32 * (*percent / 100.)) as i32
                }
                GridColumnSize::Fraction(fraction) => {
                    (to_give as f32 * (*fraction as f32 / max_total_fractions as f32)) as i32
                }
                GridColumnSize::Auto => {
                    if max_total_fractions == 0 {
                        to_give as i32 / total_auto_columns
                    } else {
                        max_sizes[base_item_target] as i32
                    }
                }
            },
            GridTemplateColumnsValue::MinMax((min, max)) => {
                let min_parsed = match min {
                    GridColumnSize::Px(px) => *px,
                    GridColumnSize::Rem(rem) => (rem * 16.) as i32,
                    GridColumnSize::Percent(percent) => {
                        (to_distribute as f32 * (*percent / 100.)) as i32
                    }
                    GridColumnSize::Fraction(_) => panic!(),
                    // TODO: I think this needs auto calculation too
                    GridColumnSize::Auto => 0,
                };
                let max_parsed = match max {
                    GridColumnSize::Px(px) => *px,
                    GridColumnSize::Rem(rem) => (rem * 16.) as i32,
                    GridColumnSize::Percent(percent) => {
                        (to_distribute as f32 * (*percent / 100.)) as i32
                    }
                    GridColumnSize::Fraction(fraction) => {
                        (to_give as f32 * (*fraction as f32 / max_total_fractions as f32)) as i32
                    }
                    // TODO: I think this needs auto calculation too
                    GridColumnSize::Auto => 0,
                };

                max_parsed.max(min_parsed)
            }
        }
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
        let container_sizes = self.get_container_sizes(
            node_idx,
            &forced_size,
            style,
            &available_size,
            containing_node_idx,
        );
        if style.position != StylePosition::Static {
            self.containing_nodes.insert(
                node_idx,
                ContainingNode {
                    node_idx,
                    cursor,
                    waiters: vec![],
                },
            );
            containing_node_idx = node_idx;
        }
        let mut children = vec![];
        let (padding_left_size, _, padding_top_size, _) =
            self.get_paddings(node_idx, style, containing_node_idx);
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
            &SizeUnit::Px,
        )
        .and_then(|v| Some(v as u32)));
        let specified_width = forced_size.width.or(get_specified_size(
            font_size,
            &style.width,
            containing_block_width,
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .and_then(|v| Some(v as u32)));
        self.resolved_specified_heights
            .insert(node_idx, specified_height);
        self.resolved_specified_widths
            .insert(node_idx, specified_width);
        self.resolved_content_sizes.insert(
            node_idx,
            OptionalSize {
                width: Some(container_sizes.inner_width),
                height: if container_sizes.has_specified_height {
                    Some(container_sizes.inner_height)
                } else {
                    None
                },
            },
        );
        let mut max_child_height = 0;
        let mut longest_row_width = 0;
        let width_to_distribute = container_sizes.inner_width;
        let height_to_distribute = container_sizes.inner_height;
        let children_idxs = self
            .dom_indexes
            .children_index
            .get(&node_idx)
            .cloned()
            .unwrap();
        let immediate_children: Vec<usize> = children_idxs
            .iter()
            .copied()
            .filter(|c| {
                let style = &self.node_styles.get(c);
                style.is_some_and(|style| !style.position.is_free())
            })
            .collect();
        let free_children: Vec<usize> = children_idxs
            .iter()
            .copied()
            .filter(|c| {
                let style = &self.node_styles.get(c);
                style.is_some_and(|style| style.position.is_free())
            })
            .collect();
        let mut current_column = 0;
        let mut definitely_used_width = 0;
        let mut definitely_used_height = 0;
        let mut max_column_fractions = 0;
        let mut max_row_fractions = 0;
        let mut total_auto_columns = 0;
        let mut total_auto_rows = 0;
        if let GridTemplateColumns::Values(template_columns) = style.grid_template_columns.clone() {
            for value in template_columns.iter() {
                match value {
                    GridTemplateColumnsValue::Size(size) => {
                        definitely_used_width += match size {
                            GridColumnSize::Px(px) => *px,
                            GridColumnSize::Rem(rem) => (rem * 16.) as i32,
                            GridColumnSize::Percent(percent) => {
                                (container_sizes.inner_width as f32 * (*percent / 100.)) as i32
                            }
                            GridColumnSize::Fraction(fraction) => {
                                max_column_fractions += fraction;
                                0
                            }
                            GridColumnSize::Auto => {
                                total_auto_columns += 1;
                                0
                            }
                        };
                    }
                    GridTemplateColumnsValue::MinMax((_, max)) => {
                        if let GridColumnSize::Fraction(fraction) = max {
                            max_column_fractions += fraction;
                        }
                    }
                };
            }
        }
        if let GridTemplateColumns::Values(template_rows) = style.grid_template_rows.clone() {
            for value in template_rows.iter() {
                match value {
                    GridTemplateColumnsValue::Size(size) => {
                        definitely_used_height += match size {
                            GridColumnSize::Px(px) => *px,
                            GridColumnSize::Rem(rem) => (rem * 16.) as i32,
                            GridColumnSize::Percent(percent) => {
                                (container_sizes.inner_height as f32 * (*percent / 100.)) as i32
                            }
                            GridColumnSize::Fraction(fraction) => {
                                max_row_fractions += fraction;
                                0
                            }
                            GridColumnSize::Auto => {
                                total_auto_rows += 1;
                                0
                            }
                        };
                    }
                    GridTemplateColumnsValue::MinMax((_, max)) => {
                        if let GridColumnSize::Fraction(fraction) = max {
                            max_row_fractions += fraction;
                        }
                    }
                };
            }
        }
        let mut dynamic_width_to_give = width_to_distribute - definitely_used_width as u32;
        let mut dynamic_height_to_give = height_to_distribute - definitely_used_height as u32;
        let justify_items = style.justify_items;
        let align_items = style.align_items;
        let child_allow_fill = if justify_items != StyleJustifyContent::Stretch {
            false
        } else {
            allow_fill
        };
        let grid_template_columns = style.grid_template_columns.clone();
        let grid_template_rows = style.grid_template_rows.clone();
        let mut base_items = vec![];
        let mut column_count = 1usize;
        let mut row_count = 1usize;
        let mut current_row: usize = 0;
        // Compute base items and their ideal sizes
        for child_idx in immediate_children.iter() {
            let column_span =
                self.node_styles
                    .get(child_idx)
                    .map_or(1, |style| style.grid_column_span.max(1)) as i32;
            let wrap = match grid_template_columns {
                GridTemplateColumns::Values(ref template_columns) => {
                    self.get_grid_column(current_column, column_span, &template_columns)
                }
                GridTemplateColumns::None => current_column >= 1,
            };
            if wrap {
                max_child_height = 0;
                current_column = 0;
                current_row += 1;
                row_count = row_count.max(current_row + 1);
            }
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
                false,
                false,
                &LayoutMode::BaseCalculation,
            ) {
                let child_box = self.layout_table.get(&child).unwrap();
                base_items.push(GridBaseItem {
                    node_idx: *child_idx,
                    base_width: child_box.rect.width,
                    target_width: child_box.rect.width,
                    base_height: child_box.rect.height,
                    target_height: child_box.rect.height,
                    column: current_column,
                    column_span,
                    row: current_row as i32,
                });
                current_column += column_span;
                column_count = column_count.max(current_column as usize);
            }
        }
        // Compute max sizes per column (used for auto calculation)
        let mut column_max_widths = vec![0; column_count];
        let mut column_max_heights = vec![0; row_count];
        for base_item in base_items.iter() {
            column_max_widths[base_item.column as usize] =
                column_max_widths[base_item.column as usize].max(base_item.base_width);
            column_max_heights[base_item.row as usize] =
                column_max_heights[base_item.row as usize].max(base_item.base_height);
        }
        // Deduct max sizes per {} from dynamic_{}_to_give as it will be used by auto calculation
        if let GridTemplateColumns::Values(ref template_columns) = grid_template_columns {
            for column in 0..column_count {
                if let Some(GridTemplateColumnsValue::Size(GridColumnSize::Auto)) =
                    template_columns.get(column)
                    && max_column_fractions > 0
                {
                    dynamic_width_to_give =
                        dynamic_width_to_give.saturating_sub(column_max_widths[column]);
                }
            }
        }
        if let GridTemplateColumns::Values(ref template_rows) = grid_template_rows {
            for row in 0..row_count {
                if let Some(GridTemplateColumnsValue::Size(GridColumnSize::Auto)) =
                    template_rows.get(row)
                    && max_row_fractions > 0
                {
                    dynamic_height_to_give =
                        dynamic_height_to_give.saturating_sub(column_max_heights[row]);
                }
            }
        }
        // Lay out base items and convert build real layout children
        for base_item in base_items.iter_mut() {
            let specified_column_size =
                if let GridTemplateColumns::Values(columns) = &grid_template_columns {
                    (base_item.column..base_item.column + base_item.column_span)
                        .map(|column| {
                            self.calculate_grid_item_size(
                                columns,
                                column as usize,
                                width_to_distribute,
                                dynamic_width_to_give,
                                max_column_fractions,
                                total_auto_columns,
                                &column_max_widths,
                            )
                        })
                        .sum()
                } else {
                    container_sizes.inner_width as i32
                };
            let specified_height = if let GridTemplateColumns::Values(rows) = &grid_template_rows {
                self.calculate_grid_item_size(
                    rows,
                    base_item.row as usize,
                    height_to_distribute,
                    dynamic_height_to_give,
                    max_row_fractions,
                    total_auto_rows,
                    &column_max_heights,
                )
            } else {
                base_item.base_height as i32
            };
            base_item.target_width = specified_column_size as u32;
            base_item.target_height = specified_height as u32;
        }
        let mut last_column = 0;
        for base_item in base_items {
            let wrap = base_item.column <= last_column;
            last_column = base_item.column;
            if wrap {
                content_position.x = original_content_position.x;
                content_position.y += max_child_height;
                max_child_height = 0;
            }
            let free_x = (base_item.target_width as i32 - base_item.base_width as i32).max(0);
            let free_y = (base_item.target_height as i32 - base_item.base_height as i32).max(0);
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
            let child_position = Position {
                x: content_position.x + offset_x,
                y: content_position.y + offset_y,
            };
            let child_style = self.node_styles.get(&base_item.node_idx).unwrap();
            let forced_width = match child_style.width {
                StyleSize::Auto if justify_items == StyleJustifyContent::Stretch => {
                    base_item.target_width
                }
                _ => base_item.base_width,
            };
            let forced_height = match (&grid_template_rows, &child_style.height) {
                (GridTemplateColumns::Values(_), StyleSize::Auto)
                    if align_items == StyleJustifyContent::Stretch =>
                {
                    Some(base_item.target_height)
                }
                (_, StyleSize::Auto) => None,
                _ => Some(base_item.base_height),
            };
            if let Some(child) = self.layout_node(
                base_item.node_idx,
                child_position,
                Size {
                    width: base_item.target_width,
                    height: base_item.target_height,
                },
                OptionalSize {
                    width: Some(forced_width),
                    height: forced_height,
                },
                containing_node_idx,
                child_allow_fill,
                save_as_final,
                mode,
            ) {
                content_position.x += base_item.target_width as i32;
                longest_row_width =
                    longest_row_width.max(content_position.x - original_content_position.x);
                max_child_height =
                    max_child_height.max(self.layout_table.get(&child).unwrap().rect.height as i32);
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
        if *mode != LayoutMode::BaseCalculation {
            for child_idx in free_children {
                self.queue_free_child_for_layout(containing_node_idx, child_idx, None);
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
        }
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
                self.nodes.get(node_idx).unwrap().get_parent()
            }
        };

        if matches!(
            style.position,
            StylePosition::Relative | StylePosition::Static | StylePosition::Sticky
        ) && let Some(containing_block_idx) = containing_block
        {
            let containing_block_sizes = self
                .resolved_content_sizes
                .get(&containing_block_idx)
                .cloned();

            let containing_block_width = containing_block_sizes
                .and_then(|v| v.width)
                .or((node_idx == self.dom_indexes.root_indice).then_some(self.window_size.width));
            let containing_block_height = containing_block_sizes
                .and_then(|v| v.height)
                .or((node_idx == self.dom_indexes.root_indice).then_some(self.window_size.height));

            (containing_block_height, containing_block_width)
        } else {
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
            self.get_paddings(node_idx, style, containing_node_idx);

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
            &SizeUnit::Px,
        )
        .and_then(|v| Some(v as u32)));
        let specified_height = forced_size.height.or(get_specified_size(
            font_size,
            &style.height,
            containing_block_height,
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .and_then(|v| Some(v as u32)));

        self.resolved_specified_heights
            .insert(node_idx, specified_height);
        self.resolved_specified_widths
            .insert(node_idx, specified_width);

        let container_sizes = self.get_container_sizes(
            node_idx,
            &forced_size,
            style,
            &available_size,
            containing_node_idx,
        );

        self.resolved_content_sizes.insert(
            node_idx,
            OptionalSize {
                width: Some(container_sizes.inner_width),
                height: if container_sizes.has_specified_height {
                    Some(container_sizes.inner_height)
                } else {
                    None
                },
            },
        );

        if *mode == LayoutMode::BaseCalculation
            && let (Some(height), Some(width)) = (specified_height, specified_width)
            && height > 0
            && width > 0
        {
            return Some((width, height, vec![], height));
        }

        let children_idxs: Vec<usize> = self
            .dom_indexes
            .children_index
            .get(&node_idx)
            .unwrap()
            .clone();

        let immediate_children: Vec<usize> = children_idxs
            .iter()
            .copied()
            .filter(|c| {
                let style = &self.node_styles.get(c);
                style.is_some_and(|style| !style.position.is_free())
            })
            .collect();
        let free_children: Vec<usize> = children_idxs
            .iter()
            .copied()
            .filter(|c| {
                let style = &self.node_styles.get(c);
                style.is_some_and(|style| style.position.is_free())
            })
            .collect();

        if style.position != StylePosition::Static {
            self.containing_nodes.insert(
                node_idx,
                ContainingNode {
                    node_idx,
                    cursor,
                    waiters: vec![],
                },
            );
            containing_node_idx = node_idx;
        }

        let mut max_child_width: u32 = 0;
        let mut max_child_height: u32 = 0;
        let mut row_height: u32 = 0;
        let mut child_width_buffer = 0;
        let mut line_has_content = false;

        let mut children_rows = MarginRows::new();

        // By default block elements fill their available width, but if it's a child of a flex, it only uses what it needs
        let shrink_to_content_width = matches!(
            &style.width,
            StyleSize::FitContent | StyleSize::MinContent | StyleSize::MaxContent
        );
        let wants_to_fill = style.display != StyleDisplay::InlineBlock
            && style.display != StyleDisplay::Inline
            && !shrink_to_content_width;

        // Inline-block doesn't fill the width, so instruct children to not do that either
        let child_allow_fill = match style.display {
            StyleDisplay::InlineBlock | StyleDisplay::Inline => false,
            _ => allow_fill,
        };

        for child_local_idx in 0..immediate_children.len() {
            let child_idx = immediate_children[child_local_idx];
            let prev_child_idx = child_local_idx
                .checked_sub(1)
                .map(|idx| immediate_children[idx]);
            let next_child_idx = immediate_children.get(child_local_idx + 1).copied();
            let child_style = self.node_styles.get(&child_idx).unwrap().clone();
            if child_style.display != StyleDisplay::None
                && matches!(
                    self.nodes.get(child_idx),
                    Some(Node::Element(element)) if element.tag == "br"
                )
            {
                content_position.x = original_cursor.x;
                content_position.y += row_height.max(font_size) as i32;
                child_width_buffer = 0;
                row_height = 0;
                line_has_content = false;
                max_child_height =
                    max_child_height.max((content_position.y - original_cursor.y).max(0) as u32);
                continue;
            }
            let (margin_left_size, margin_right_size, margin_top_size, margin_bottom_size) =
                self.get_margins(child_idx, &child_style, available_size);
            content_position.x += margin_left_size as i32;
            if let Some(child) = self.layout_node(
                child_idx,
                Position {
                    x: content_position.x,
                    y: content_position.y + margin_top_size as i32,
                },
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
                let child_width = child_box.rect.width;
                let child_height = child_box.rect.height;
                let prev_child_display: Option<StyleDisplay> =
                    prev_child_idx.map(|idx| self.node_styles.get(&idx).unwrap().display);
                let next_child_display: Option<StyleDisplay> =
                    next_child_idx.map(|idx| self.node_styles.get(&idx).unwrap().display);
                if child_style.display.is_inline()
                    && prev_child_display.is_none_or(|v| v.is_inline())
                    && next_child_display.is_none_or(|v| v.is_inline())
                {
                    let child_width_with_margin = child_width as i32 + margin_right_size;
                    if child_width_buffer > 0
                        && child_width_buffer + child_width_with_margin
                            > container_sizes.inner_width as i32
                    {
                        self.move_entire_box(
                            child,
                            original_cursor.x - content_position.x,
                            row_height as i32,
                        );
                        content_position.x = original_cursor.x + child_width_with_margin;
                        content_position.y += row_height as i32;
                        child_width_buffer = child_width_with_margin;
                        children_rows.new_row(child, 0);
                    } else {
                        content_position.x += child_width_with_margin;
                        child_width_buffer += child_width_with_margin;
                        if line_has_content {
                            children_rows.last_row(child, 0);
                        } else {
                            children_rows.new_row(child, 0);
                        }
                    }
                    line_has_content = true;
                    row_height = row_height.max(child_height);

                    if !child_style.position.is_free() {
                        max_child_width = max_child_width.max(child_width_buffer as u32);
                        max_child_height = max_child_height.max(row_height);
                    }
                } else {
                    // This is a wrap, so reset X
                    content_position.x = original_cursor.x;
                    content_position.y +=
                        margin_top_size as i32 + child_height as i32 + margin_bottom_size;
                    child_width_buffer = 0;
                    row_height = 0;
                    line_has_content = false;
                    children_rows.new_row(child, 0);

                    if !child_style.position.is_free() {
                        max_child_width = max_child_width.max(child_width);
                    }
                }
                children.push(child);
            }
        }

        let input_value = match &self.nodes.get(node_idx).unwrap() {
            Node::Element(element) => element.attributes.get_str("value"),
            Node::Text(_) | Node::Comment(_) => None,
        };
        if immediate_children.len() == 0
            && let Some(input_value) = input_value
            && input_value.len() > 0
        {
            let layout_box = self
                .create_input_text_box(
                    node_idx,
                    input_value.into_owned(),
                    &mut content_position,
                    font_size,
                    save_as_final,
                )
                .unwrap();
            max_child_width = self.layout_table.get(&layout_box).unwrap().rect.width;
            children.push(layout_box);
        }

        let content_height = ((content_position.y - original_cursor.y).max(0) as u32 + row_height)
            .max(max_child_height);
        let height = specified_height
            .unwrap_or_else(|| {
                if children.is_empty() && content_height == 0 {
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

        if *mode != LayoutMode::BaseCalculation {
            for child_idx in free_children {
                self.queue_free_child_for_layout(containing_node_idx, child_idx, None);
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
        }

        Some((width, height, children, content_height))
    }

    fn calculate_cross_offset(
        &self,
        node_idx: usize,
        used_cross: u32,
        parent_style: &Style,
        has_definite_height: bool,
        allow_fill: bool,
        container_sizes: &ContainerSizes,
    ) -> u32 {
        let Some(item_style) = self.node_styles.get(&node_idx) else {
            return 0;
        };
        let align = match item_style.align_self {
            StyleJustifyContent::Auto => parent_style.align_items,
            v => v,
        };
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
        let available_size = match parent_style.flex_direction {
            StyleFlexDirection::Row => Some(container_sizes.inner_width),
            StyleFlexDirection::Column if has_definite_height => Some(container_sizes.inner_height),
            StyleFlexDirection::Column => None,
        };
        let size = if item_style.flex_basis == StyleSize::Auto {
            match parent_style.flex_direction {
                StyleFlexDirection::Row => &item_style.width,
                StyleFlexDirection::Column => &item_style.height,
            }
        } else {
            &item_style.flex_basis
        };
        if *size == StyleSize::Auto {
            return None;
        }

        get_specified_size(
            font_size,
            size,
            available_size,
            None,
            &self.window_size,
            &SizeUnit::Px,
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
            self.get_paddings(node_idx, &style, containing_node_idx);

        let mut content_position = Position {
            x: cursor.x + padding_left_size as i32,
            y: cursor.y + padding_top_size as i32,
        };
        let original_content_cursor = content_position.clone();
        let mut base_items = Vec::new();
        let mut children = Vec::new();

        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();

        let container_sizes = self.get_container_sizes(
            node_idx,
            &forced_size,
            &style,
            &available_size,
            containing_node_idx,
        );
        let (containing_block_height, containing_block_width) =
            self.get_containing_block_size(containing_node_idx, node_idx, &style);

        let specified_height = forced_size.height.or(get_specified_size(
            font_size,
            &style.height,
            containing_block_height,
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .and_then(|v| Some(v as u32)));
        let specified_width = forced_size.width.or(get_specified_size(
            font_size,
            &style.width,
            containing_block_width,
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .and_then(|v| Some(v as u32)));
        let has_definite_height = forced_size.height.is_some() || specified_height.is_some();
        self.resolved_specified_heights
            .insert(node_idx, specified_height);
        self.resolved_specified_widths
            .insert(node_idx, specified_width);
        self.resolved_content_sizes.insert(
            node_idx,
            OptionalSize {
                width: Some(container_sizes.inner_width),
                height: if container_sizes.has_specified_height {
                    Some(container_sizes.inner_height)
                } else {
                    None
                },
            },
        );

        if *mode == LayoutMode::BaseCalculation {
            if let (Some(height), Some(width)) = (specified_height, specified_width) {
                return Some((width, height, vec![], height));
            }
        }

        if style.position != StylePosition::Static {
            self.containing_nodes.insert(
                node_idx,
                ContainingNode {
                    node_idx,
                    cursor,
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

        let mut immediate_children: Vec<&usize> = children_idxs
            .iter()
            .filter(|c| {
                let style = &self.node_styles.get(*c).unwrap();
                !style.position.is_free()
            })
            .collect();
        // Flex items are laid out by ascending `order`; equal values retain DOM order.
        immediate_children.sort_by_key(|child_idx| self.node_styles.get(*child_idx).unwrap().order);
        let free_children: Vec<&usize> = children_idxs
            .iter()
            .filter(|c| {
                let style = &self.node_styles.get(*c).unwrap();
                style.position.is_free()
            })
            .collect();

        let input_value = match &self.nodes.get(node_idx).unwrap() {
            Node::Element(element) => element.attributes.get_str("value"),
            Node::Text(_) | Node::Comment(_) => None,
        };
        if immediate_children.len() == 0
            && let Some(input_value) = input_value
            && input_value.len() > 0
        {
            if let Ok(layout_box_idx) = self.create_input_text_box(
                node_idx,
                input_value.into_owned(),
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
            let (margin_left, margin_right, margin_top, margin_bottom) = self.get_margins(
                *child_idx,
                &child_style,
                Size {
                    width: container_sizes.inner_width,
                    height: container_sizes.inner_height,
                },
            );
            let main_margin = match style.flex_direction {
                StyleFlexDirection::Row => margin_left + margin_right,
                StyleFlexDirection::Column => margin_top + margin_bottom,
            };
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
                    StyleFlexDirection::Row => child_box.rect.width,
                    StyleFlexDirection::Column => child_box.rect.height,
                };
                let cross_size = match style.flex_direction {
                    StyleFlexDirection::Row => child_box.rect.height,
                    StyleFlexDirection::Column => child_box.rect.width,
                };
                let max_width = get_specified_size(
                    font_size,
                    &child_style.max_width,
                    Some(container_sizes.inner_width),
                    None,
                    &self.window_size,
                    &SizeUnit::Px,
                )
                .unwrap_or(i32::MAX);
                let max_height = get_specified_size(
                    font_size,
                    &child_style.max_height,
                    Some(container_sizes.inner_height),
                    None,
                    &self.window_size,
                    &SizeUnit::Px,
                )
                .unwrap_or(i32::MAX);
                let max_size = match style.flex_direction {
                    StyleFlexDirection::Row => max_width,
                    StyleFlexDirection::Column => max_height,
                };
                let max_cross_size = match style.flex_direction {
                    StyleFlexDirection::Row => max_height,
                    StyleFlexDirection::Column => max_width,
                };
                let base_size = (size as f32).min(max_size as f32);
                base_items.push(FlexItem {
                    node_idx: *child_idx,
                    target_size: base_size,
                    base_size,
                    main_margin,
                    max_size: max_size as f32,
                    cross_size: (cross_size as f32).min(max_cross_size as f32),
                    max_cross_size: max_cross_size as f32,
                    shrink: child_style.flex_shrink,
                    grow: child_style.flex_grow,
                });
            }
        }

        // Flex free space is based on each item's outer size, including fixed main-axis margins.
        // Auto margins resolve to zero here and receive their share during final alignment.
        let total_outer_base: f32 = base_items
            .iter()
            .map(|item| item.base_size + item.main_margin as f32)
            .sum();
        let flex_available_size = match style.flex_direction {
            StyleFlexDirection::Row => container_sizes.inner_width,
            StyleFlexDirection::Column if has_definite_height => container_sizes.inner_height,
            StyleFlexDirection::Column => total_outer_base.max(0.).ceil() as u32,
        };
        let cross_available_size = match style.flex_direction {
            StyleFlexDirection::Column => container_sizes.inner_width,
            StyleFlexDirection::Row => container_sizes.inner_height,
        };
        let has_explicit_main_size = match style.flex_direction {
            StyleFlexDirection::Row => container_sizes.container_width_non_filling.is_some(),
            StyleFlexDirection::Column => container_sizes.container_height_non_filling.is_some(),
        };
        let fills_main_axis = match style.flex_direction {
            StyleFlexDirection::Row => allow_fill && style.display != StyleDisplay::InlineFlex,
            StyleFlexDirection::Column => {
                has_definite_height && style.display != StyleDisplay::InlineFlex
            }
        };
        let distributes_main_space = has_explicit_main_size || fills_main_axis;
        let overflow = total_outer_base - flex_available_size as f32;

        if overflow > 0. {
            let total_scaled: f32 = base_items
                .iter()
                .map(|i| i.base_size * i.shrink as f32)
                .sum();

            if total_scaled > 0. {
                for item in &mut base_items {
                    let scaled = item.base_size * item.shrink as f32;
                    let reduction = overflow * scaled / total_scaled;
                    item.target_size = (item.base_size - reduction).max(0.).min(item.max_size);
                }
            }
        } else if overflow < 0. && distributes_main_space {
            let left_to_grow: f32 = -overflow;
            let total_grow: u32 = base_items.iter().map(|i| i.grow).sum();
            if total_grow > 0 {
                for item in &mut base_items {
                    item.target_size = (item.base_size
                        + left_to_grow * (item.grow as f32 / total_grow as f32))
                        .min(item.max_size);
                }
            }
        }

        // Stretch children on cross-axis if appropiate
        let mut definite_cross_size = false;
        if style.align_items == StyleJustifyContent::Stretch && allow_fill {
            let row_cross_size = base_items
                .iter()
                .map(|item| item.cross_size)
                .fold(0., f32::max);
            for item in &mut base_items {
                let child_style: &Style = &self.node_styles.get(&item.node_idx).unwrap();
                let align = match child_style.align_self {
                    StyleJustifyContent::Auto => style.align_items,
                    v => v,
                };
                if align != StyleJustifyContent::Stretch {
                    continue;
                }
                match style.flex_direction {
                    StyleFlexDirection::Column => {
                        if child_style.width == StyleSize::Auto {
                            item.cross_size =
                                (cross_available_size as f32).min(item.max_cross_size);
                            definite_cross_size = true;
                        }
                    }
                    StyleFlexDirection::Row => {
                        if child_style.height == StyleSize::Auto {
                            let cross_size = if has_definite_height {
                                cross_available_size as f32
                            } else {
                                row_cross_size
                            };
                            item.cross_size = cross_size.min(item.max_cross_size);
                            definite_cross_size = true;
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
            &SizeUnit::Px,
        )
        .unwrap_or(0);
        let gap_total = authored_gap.saturating_mul(base_items.len().saturating_sub(1) as i32);

        let used_main: u32 = base_items
            .iter()
            .map(|item| (item.target_size + item.main_margin as f32).max(0.).round() as u32)
            .sum::<u32>()
            + gap_total as u32;
        let main_free_space = match style.flex_direction {
            StyleFlexDirection::Row if distributes_main_space => {
                container_sizes.inner_width.saturating_sub(used_main)
            }
            StyleFlexDirection::Row => 0,
            StyleFlexDirection::Column if distributes_main_space => {
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
                    let child_style = self.node_styles.get(&item.node_idx).unwrap().clone();
                    let (margin_left_size, margin_right_size, margin_top_size, margin_bottom_size) =
                        self.get_margins(item.node_idx, &child_style, available_size);
                    // Re-compute cursor for each child so that align-self works
                    content_position.y = original_content_cursor.y + margin_top_size;
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
                            height: definite_cross_size.then_some(item.cross_size as u32),
                            width: Some(item.target_size as u32),
                        },
                        containing_node_idx,
                        allow_fill,
                        save_as_final,
                        mode,
                    ) {
                        let child_box = self.layout_table.get(&child).unwrap();
                        // Adjust by cross offset after laying it out, as the final height may change from base due to different width
                        let outer_cross = child_box.rect.height
                            + margin_top_size.max(0) as u32
                            + margin_bottom_size.max(0) as u32;
                        let cross_offset = self.calculate_cross_offset(
                            item.node_idx,
                            outer_cross,
                            &style,
                            has_definite_height,
                            allow_fill,
                            &container_sizes,
                        );
                        if !child_style.position.is_free() {
                            content_position.x += child_box.rect.width as i32 + margin_right_size;
                            children_rows.last_row(child, 0);
                            // Don't add gap for last item
                            if !last {
                                content_position.x += main_gap as i32;
                            }
                            max_child_height = max_child_height.max(child_box.rect.height);
                        }
                        content_position.y += cross_offset as i32;
                        self.move_entire_box(child, 0, cross_offset as i32);
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
                    let child_style = self.node_styles.get(&item.node_idx).unwrap().clone();
                    let (margin_left_size, _, margin_top_size, margin_bottom_size) =
                        self.get_margins(item.node_idx, &child_style, available_size);
                    content_position.x = original_content_cursor.x + margin_left_size;
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
                            height: has_definite_height.then_some(item.target_size as u32),
                            width: definite_cross_size.then_some(item.cross_size as u32),
                        },
                        containing_node_idx,
                        allow_fill,
                        save_as_final,
                        mode,
                    ) {
                        let child_box = self.layout_table.get(&child).unwrap();
                        let outer_cross = child_box.rect.width
                            + margin_top_size.max(0) as u32
                            + margin_bottom_size.max(0) as u32;
                        let cross_offset = self.calculate_cross_offset(
                            item.node_idx,
                            outer_cross,
                            &style,
                            has_definite_height,
                            allow_fill,
                            &container_sizes,
                        );
                        if !child_style.position.is_free() {
                            max_affecting_child_width =
                                max_affecting_child_width.max(child_box.rect.width);
                            content_position.y += child_box.rect.height as i32 + margin_bottom_size;
                            // The flex cross-axis offset is already applied above.
                            children_rows.new_row(child, 0);
                            // Don't add gap for last item
                            if !last {
                                content_position.y += main_gap as i32;
                            }
                        }
                        content_position.x += cross_offset as i32;
                        self.move_entire_box(child, cross_offset as i32, 0);
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

        if *mode != LayoutMode::BaseCalculation {
            let static_position_available_height =
                height.saturating_sub((padding_top_size + padding_bottom_size).max(0) as u32);
            for child_idx in free_children {
                let static_position_offset = self
                    .containing_nodes
                    .get(&containing_node_idx)
                    .filter(|_| {
                        self.node_styles.get(child_idx).unwrap().position == StylePosition::Absolute
                    })
                    .map(|containing_node| {
                        let size_dependent_offset = match style.flex_direction {
                            StyleFlexDirection::Column => match style.justify_content {
                                StyleJustifyContent::Center => {
                                    Some(SizeDependentStaticOffset::CenterY(
                                        static_position_available_height,
                                    ))
                                }
                                StyleJustifyContent::FlexEnd => {
                                    Some(SizeDependentStaticOffset::EndY(
                                        static_position_available_height,
                                    ))
                                }
                                _ => None,
                            },
                            _ => None,
                        };
                        StaticPositionOffset {
                            offset: Position {
                                x: original_content_cursor.x - containing_node.cursor.x,
                                y: original_content_cursor.y - containing_node.cursor.y,
                            },
                            size_dependent_offset,
                        }
                    });
                self.queue_free_child_for_layout(
                    containing_node_idx,
                    *child_idx,
                    static_position_offset,
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
                if !style.visibility.is_visible() {
                    return false;
                }
                let layout_box = self
                    .layout_table
                    .get(&renderer_node.layout_box_idx)
                    .unwrap();
                let start_x =
                    (layout_box.rect.x + renderer_node.offset_x).max(renderer_node.clip.start_x);
                let start_y =
                    (layout_box.rect.y + renderer_node.offset_y).max(renderer_node.clip.start_y);
                let end_x =
                    (layout_box.rect.x + renderer_node.offset_x + layout_box.rect.width as i32)
                        .min(renderer_node.clip.end_x);
                let end_y =
                    (layout_box.rect.y + renderer_node.offset_y + layout_box.rect.height as i32)
                        .min(renderer_node.clip.end_y);

                position.x > start_x
                    && position.x < end_x
                    && position.y > start_y
                    && position.y < end_y
            });
        self.hovering = hovering.and_then(|v| Some(v.layout_box_idx));
    }

    fn paint_borders(
        &self,
        layout_box: &LayoutBox,
        buffer: &mut [u32],
        width: u32,
        height: u32,
        offset_x: i32,
        offset_y: i32,
        clip: PaintClip,
    ) {
        let container_start_x = layout_box.rect.x + offset_x;
        let container_start_y = layout_box.rect.y + offset_y;
        if let Some(border) = &layout_box.rect.border.left {
            draw_rect_filled_clipped(
                buffer,
                false,
                width,
                height,
                container_start_x,
                container_start_y,
                border.size,
                layout_box.rect.height,
                border.color,
                &BorderRadius::new_empty(),
                clip,
            );
        }
        if let Some(border) = &layout_box.rect.border.top {
            draw_rect_filled_clipped(
                buffer,
                false,
                width,
                height,
                container_start_x,
                container_start_y,
                layout_box.rect.width,
                border.size,
                border.color,
                &BorderRadius::new_empty(),
                clip,
            );
        }
        if let Some(border) = &layout_box.rect.border.right {
            draw_rect_filled_clipped(
                buffer,
                false,
                width,
                height,
                container_start_x + layout_box.rect.width as i32 - border.size as i32,
                container_start_y,
                border.size,
                layout_box.rect.height,
                border.color,
                &BorderRadius::new_empty(),
                clip,
            );
        }
        if let Some(border) = &layout_box.rect.border.bottom {
            draw_rect_filled_clipped(
                buffer,
                false,
                width,
                height,
                container_start_x,
                container_start_y + layout_box.rect.height as i32 - border.size as i32,
                layout_box.rect.width,
                border.size,
                border.color,
                &BorderRadius::new_empty(),
                clip,
            );
        }
    }

    fn apply_pixmap_on_buffer(
        &self,
        layout_box: &LayoutBox,
        buffer: &mut [u32],
        width: u32,
        height: u32,
        container_start_x: i32,
        container_start_y: i32,
        pixmap_buffer: &tiny_skia::Pixmap,
        opaque: bool,
        clip: PaintClip,
    ) {
        let pixels = pixmap_buffer.pixels();
        let pixmap_width = layout_box.rect.width.min(pixmap_buffer.width());
        let pixmap_height = layout_box.rect.height.min(pixmap_buffer.height());
        let pixmap_stride = pixmap_buffer.width();
        let Some(blit) = clipped_blit(
            width,
            height,
            pixmap_width,
            pixmap_height,
            container_start_x,
            container_start_y,
            clip,
        ) else {
            return;
        };

        for row in 0..blit.height {
            let src_start = ((blit.src_y + row) * pixmap_stride + blit.src_x) as usize;
            let src_row = &pixels[src_start..src_start + blit.width as usize];
            let dst_start = ((blit.dst_y + row) * width + blit.dst_x) as usize;
            let dst_row = &mut buffer[dst_start..dst_start + blit.width as usize];
            for pixel_x in 0..blit.width as usize {
                let pixel = src_row[pixel_x];
                if opaque {
                    dst_row[pixel_x] = ((pixel.red() as u32) << 16)
                        | ((pixel.green() as u32) << 8)
                        | (pixel.blue() as u32);
                } else {
                    dst_row[pixel_x] = self.blend_premul_over_rgb(dst_row[pixel_x], pixel);
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
        parent_offset_x: i32,
        parent_offset_y: i32,
        clip: PaintClip,
        rendered_nodes_ordered: &mut Vec<RenderedNode>,
        deferred_z_index: &mut Vec<DeferredPaint>,
        defer_positive_z_index: bool,
    ) {
        if clip.is_empty() {
            return;
        }

        let layout_box = self.layout_table.get(&layout_box_idx).unwrap();
        let style = self.node_styles.get(&layout_box.node_idx).cloned();
        let creates_stacking_context = style.as_ref().is_some_and(Self::creates_stacking_context);
        if defer_positive_z_index && layout_box.z_index > 0 && creates_stacking_context {
            deferred_z_index.push((layout_box_idx, parent_offset_x, parent_offset_y, clip));
            return;
        }
        let (transform_x, transform_y) = style
            .as_ref()
            .map(|style| self.resolve_transform_offset(style, layout_box))
            .unwrap_or((0, 0));
        let offset_x = parent_offset_x + transform_x;
        let offset_y = parent_offset_y + transform_y;
        let child_offset_y = offset_y
            + self
                .scroll_y
                .get(&self.layout_to_node_idx(&layout_box_idx))
                .copied()
                .unwrap_or(0);
        rendered_nodes_ordered.push(RenderedNode {
            layout_box_idx,
            offset_x,
            offset_y,
            clip,
        });
        if style.as_ref().is_some_and(|style| style.opacity == 0.0) {
            return;
        }
        let visible = style
            .as_ref()
            .is_none_or(|style| style.visibility == StyleVisibility::Visible);
        let container_start_x = layout_box.rect.x + offset_x;
        let container_start_y = layout_box.rect.y + offset_y;
        let container_end_y = container_start_y + layout_box.content_height as i32;
        // If outside viewport, don't render
        // This is a bit naive but should be okay for now
        if container_start_y > height as i32 || container_end_y < 0 {
            return;
        }
        if !visible {
            return;
        }
        let left_border_size = layout_box
            .rect
            .border
            .left
            .as_ref()
            .map_or(0, |border| border.size) as i32;
        let top_border_size = layout_box
            .rect
            .border
            .top
            .as_ref()
            .map_or(0, |border| border.size) as i32;
        let right_border_size = layout_box
            .rect
            .border
            .right
            .as_ref()
            .map_or(0, |border| border.size) as i32;
        let bottom_border_size = layout_box
            .rect
            .border
            .bottom
            .as_ref()
            .map_or(0, |border| border.size) as i32;
        match &layout_box.kind {
            LayoutKind::Element => {
                match &layout_box.rect.background {
                    StyleBackground::Hex(code) => {
                        draw_rect_filled_clipped(
                            buffer,
                            false,
                            width,
                            height,
                            container_start_x + left_border_size,
                            container_start_y + top_border_size,
                            (layout_box.rect.width as i32 - left_border_size - right_border_size)
                                .max(0) as u32,
                            (layout_box.rect.height as i32 - top_border_size - bottom_border_size)
                                .max(0) as u32,
                            code.clone(),
                            &layout_box.rect.border_radius,
                            clip,
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
                                container_start_x,
                                container_start_y,
                                pixmap,
                                false,
                                clip,
                            );
                        }
                    }
                    _ => {}
                };
                self.paint_borders(&layout_box, buffer, width, height, offset_x, offset_y, clip);
            }
            LayoutKind::Text(text) => {
                let bg_hex: Option<u32> = match layout_box.rect.background {
                    StyleBackground::Hex(code) => Some(code),
                    _ => None,
                };
                if let Some(bg) = bg_hex {
                    draw_rect_filled_clipped(
                        buffer,
                        false,
                        width,
                        height,
                        container_start_x,
                        container_start_y,
                        layout_box.rect.width,
                        layout_box.rect.height,
                        bg,
                        &layout_box.rect.border_radius,
                        clip,
                    );
                }
                self.apply_pixmap_on_buffer(
                    layout_box,
                    buffer,
                    width,
                    height,
                    container_start_x,
                    container_start_y,
                    text,
                    false,
                    clip,
                );
            }
            LayoutKind::PixMap((pixmap_buffer, opaque)) => {
                self.apply_pixmap_on_buffer(
                    layout_box,
                    buffer,
                    width,
                    height,
                    container_start_x,
                    container_start_y,
                    pixmap_buffer,
                    *opaque,
                    clip,
                );
            }
            LayoutKind::Canvas => {
                let pixmap = self
                    .canvas_buffers
                    .get_mut(&layout_box.node_idx)
                    .and_then(|canvas| {
                        canvas.update_if_needed();
                        let size = IntSize::from_wh(canvas.width, canvas.height)?;
                        tiny_skia::Pixmap::from_vec(
                            premul_rgba_buffer_to_bytes(&canvas.buffer),
                            size,
                        )
                    });
                if let Some(pixmap) = pixmap {
                    self.apply_pixmap_on_buffer(
                        layout_box,
                        buffer,
                        width,
                        height,
                        container_start_x,
                        container_start_y,
                        &pixmap,
                        false,
                        clip,
                    );
                }
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
                        container_start_x,
                        container_start_y,
                        clip,
                    );
                } else {
                    println!("Failed to find iframe frame");
                }
            }
        }

        let mut child_clip = clip;
        if let Some(style) = &style {
            if style.overflow_x.clips() {
                child_clip = child_clip.intersect_x(
                    container_start_x + left_border_size,
                    container_start_x
                        .saturating_add_unsigned(layout_box.rect.width)
                        .saturating_sub(right_border_size),
                );
            }
            if style.overflow_y.clips() {
                child_clip = child_clip.intersect_y(
                    container_start_y + top_border_size,
                    container_start_y
                        .saturating_add_unsigned(layout_box.rect.height)
                        .saturating_sub(bottom_border_size),
                );
            }
        }

        let mut local_deferred_z_index = vec![];
        let child_deferred_z_index = if creates_stacking_context {
            &mut local_deferred_z_index
        } else {
            deferred_z_index
        };
        for child in layout_box.children.clone() {
            self.paint_layout_box(
                child,
                buffer,
                width,
                height,
                offset_x,
                child_offset_y,
                child_clip,
                rendered_nodes_ordered,
                child_deferred_z_index,
                true,
            );
        }
        if creates_stacking_context {
            self.paint_deferred_z_index(
                &mut local_deferred_z_index,
                buffer,
                width,
                height,
                rendered_nodes_ordered,
            );
        }
    }

    fn creates_stacking_context(style: &Style) -> bool {
        matches!(style.position, StylePosition::Fixed | StylePosition::Sticky)
            || style.opacity < 1.0
            || style.transform != StyleTransform::None
            || (matches!(style.z_index, StyleZIndex::Number(_))
                && style.position != StylePosition::Static)
    }

    fn paint_deferred_z_index(
        &mut self,
        deferred_z_index: &mut Vec<DeferredPaint>,
        buffer: &mut [u32],
        width: u32,
        height: u32,
        rendered_nodes_ordered: &mut Vec<RenderedNode>,
    ) {
        deferred_z_index.sort_by(|(a, ..), (b, ..)| {
            let a_z = self.layout_table.get(a).unwrap().z_index;
            let b_z = self.layout_table.get(b).unwrap().z_index;
            a_z.cmp(&b_z)
        });
        let deferred_z_index_to_paint = std::mem::take(deferred_z_index);
        for (child, child_parent_offset_x, child_parent_offset_y, clip) in deferred_z_index_to_paint
        {
            self.paint_layout_box(
                child,
                buffer,
                width,
                height,
                child_parent_offset_x,
                child_parent_offset_y,
                clip,
                rendered_nodes_ordered,
                deferred_z_index,
                false,
            );
        }
    }

    fn walk_parent_tree(&self, buffer: &mut Vec<usize>, idx: usize) {
        buffer.push(idx);
        if let Some(node) = self.nodes.get(idx) {
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
        self.reserve_node_idxs(1);
    }

    fn reserve_node_idxs(&mut self, count: usize) -> usize {
        let first_idx = self.nodes.cursor + 1;
        if count == 0 {
            return first_idx;
        }

        self.nodes.cursor += count;
        self.nodes_idxs.extend(first_idx..=self.nodes.cursor);
        first_idx
    }

    pub fn insert_node_at_idx(&mut self, idx: usize, node: Node) {
        self.nodes.insert(idx, node);
    }

    pub fn push_node(&mut self, node: Node) {
        self.reserve_node_idx();
        self.insert_node_at_idx(self.nodes.cursor, node);
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
            if let Some(parent) = self.nodes.get(node_idx).unwrap().get_parent() {
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
        self.nodes.remove(node_idx);
        self.node_layout_mapping.remove(&node_idx);
        self.dom_indexes.children_index.remove(&node_idx);
    }

    fn remove_children(&mut self, parent_idx: usize) {
        let mut pending = self
            .dom_indexes
            .children_index
            .get(&parent_idx)
            .cloned()
            .unwrap_or_default();
        let mut removed = HashSet::with_capacity(pending.len());
        while let Some(node_idx) = pending.pop() {
            if !removed.insert(node_idx) {
                continue;
            }
            if let Some(children) = self.dom_indexes.children_index.get(&node_idx) {
                pending.extend(children);
            }
        }

        self.nodes_idxs.retain(|idx| !removed.contains(idx));
        for node_idx in removed {
            self.nodes.remove(node_idx);
            self.node_layout_mapping.remove(&node_idx);
            self.dom_indexes.children_index.remove(&node_idx);
        }
        self.dom_indexes.children_index.insert(parent_idx, vec![]);
    }

    pub fn detach_node(&mut self, node_idx: usize) {
        let Some(parent) = self.nodes.get(node_idx).and_then(|node| node.get_parent()) else {
            return;
        };

        if let Some(children) = self.dom_indexes.children_index.get_mut(&parent) {
            children.retain(|idx| *idx != node_idx);
        }

        if let Some(node) = self.nodes.get_mut(node_idx) {
            node.set_parent(None);
        }
        self.node_layout_mapping.remove(&node_idx);
    }

    pub fn recompute_dom_indexes(&mut self) {
        self.dom_indexes = get_dom_indexes(
            &self.nodes,
            &self.nodes_idxs,
            &mut self.css_parser.class_definitions,
        );
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
        let node_styles = std::mem::take(&mut self.node_styles);
        let resolved_font_sizes = std::mem::take(&mut self.resolved_font_sizes);
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
            &self.nodes_idxs,
            self.dom_indexes.root_indice,
            &self.window_size,
            &mut self.dom_indexes,
            &mut self.css_parse_cache,
            &mut self.flattened_css_cache,
            &hover_chain,
            &mut self.css_parser,
            node_styles,
            resolved_font_sizes,
        );
    }

    pub fn recompute_nodes(&mut self) {
        self.recompute_dom_indexes();
        self.recompute_styles();
    }

    fn queue_free_child_for_layout(
        &mut self,
        containing_node_idx: usize,
        child_idx: usize,
        static_position_offset: Option<StaticPositionOffset>,
    ) {
        let child_style = self.node_styles.get(&child_idx).unwrap();
        let containing_node_idx = if child_style.position == StylePosition::Fixed {
            self.dom_indexes.root_indice
        } else {
            containing_node_idx
        };

        let containing_node = self.containing_nodes.get_mut(&containing_node_idx).unwrap();

        containing_node.waiters.push(ResumableNode {
            node_idx: child_idx,
            static_position_offset,
        });
    }

    pub fn get_paddings(
        &self,
        node_idx: usize,
        style: &Style,
        containing_node_idx: usize,
    ) -> (i32, i32, i32, i32) {
        let (_, containing_block_width) =
            self.get_containing_block_size(containing_node_idx, node_idx, &style);
        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();
        let padding_left_size = get_specified_size(
            font_size,
            &style.padding_left,
            containing_block_width,
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .unwrap_or(0);
        let padding_right_size = get_specified_size(
            font_size,
            &style.padding_right,
            containing_block_width,
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .unwrap_or(0);
        let padding_top_size = get_specified_size(
            font_size,
            &style.padding_top,
            containing_block_width,
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .unwrap_or(0);
        let padding_bottom_size = get_specified_size(
            font_size,
            &style.padding_bottom,
            containing_block_width,
            None,
            &self.window_size,
            &SizeUnit::Px,
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
        containing_node_idx: usize,
    ) -> (i32, i32, i32, i32) {
        let (containing_block_height, containing_block_width) =
            self.get_containing_block_size(containing_node_idx, node_idx, &style);
        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();
        let left_size = if style.border_left.style == StyleBorderStyle::Solid {
            get_specified_size(
                font_size,
                &style.border_left.size,
                containing_block_width,
                None,
                &self.window_size,
                &SizeUnit::Px,
            )
            .unwrap_or(0)
        } else {
            0
        };
        let right_size = if style.border_right.style == StyleBorderStyle::Solid {
            get_specified_size(
                font_size,
                &style.border_right.size,
                containing_block_width,
                None,
                &self.window_size,
                &SizeUnit::Px,
            )
            .unwrap_or(0)
        } else {
            0
        };
        let top_size = if style.border_top.style == StyleBorderStyle::Solid {
            get_specified_size(
                font_size,
                &style.border_top.size,
                containing_block_height,
                None,
                &self.window_size,
                &SizeUnit::Px,
            )
            .unwrap_or(0)
        } else {
            0
        };
        let bottom_size = if style.border_bottom.style == StyleBorderStyle::Solid {
            get_specified_size(
                font_size,
                &style.border_bottom.size,
                containing_block_height,
                None,
                &self.window_size,
                &SizeUnit::Px,
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
            &SizeUnit::Px,
        )
        .unwrap_or(0);
        let margin_right_size = get_specified_size(
            font_size,
            &style.margin_right,
            Some(available_size.width),
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .unwrap_or(0);
        let margin_top_size = get_specified_size(
            font_size,
            &style.margin_top,
            Some(available_size.height),
            None,
            &self.window_size,
            &SizeUnit::Px,
        )
        .unwrap_or(0);
        let margin_bottom_size = get_specified_size(
            font_size,
            &style.margin_bottom,
            Some(available_size.height),
            None,
            &self.window_size,
            &SizeUnit::Px,
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
        let first_node_idx = self.reserve_node_idxs(parser.nodes.len());
        let mut idx_mapping = HashMap::new();
        for (node_internal_idx, _) in parser.nodes.iter().enumerate() {
            idx_mapping.insert(node_internal_idx, first_node_idx + node_internal_idx);
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
            self.event_loop_notify.notify_one();
        }
    }

    pub fn schedule_canvas_update(&mut self) {
        if !self.pending_canvas_update
            && let Some(proxy) = &self.event_loop_proxy
        {
            proxy.fire_user_event(UserEvent::CanvasUpdated).unwrap();
            self.pending_canvas_update = true;
            self.event_loop_notify.notify_one();
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

    pub fn upsert_script(&mut self, js: &Script) -> bool {
        if let ScriptContent::Link(link) = &js.content {
            if self.links.contains(&link) {
                // println!("Script has already been ran, ignoring: {}", link);
                false
            } else {
                self.links.push(link.to_string());
                true
            }
        } else if let Some(node_idx) = js.node_idx {
            if self.nodes.contains(&node_idx) {
                // println!("Script has already been ran, ignoring: {}", node_idx);
                false
            } else {
                self.nodes.push(node_idx);
                true
            }
        } else {
            true
        }
    }
}

struct Frame {
    url: String,
    renderer: Option<Rc<RefCell<Renderer>>>,
    window: Option<Arc<Window>>,
    js_runtime: Option<Rc<RefCell<JsRuntime>>>,
    tokio: Option<Rc<RefCell<tokio::runtime::Runtime>>>,
    html_parser: Option<HtmlParser>,
    font_handler: Rc<FontHandler>,
    layout_dirty: bool,
    layout_booted: bool,
    executed_scripts: Rc<RefCell<ExecutedScripts>>,
    network_fetch: Rc<RefCell<NetworkFetch>>,
    document_id: u64,
    dom_content_loaded_dispatched: bool,
    load_dispatched: bool,
    is_top: bool,
    hover_debugging: bool,
    render_size: PhysicalSize<u32>,
    loaded_nodes: Vec<usize>,
    last_hover_position: Option<Position>,
    animation_frame_requested: bool,
    last_animation_frame: Instant,
    blob_store: Arc<BlobStore>,
}

struct BootParams {
    nodes_idxs: Vec<usize>,
    nodes: NodesTable,
    dom_indexes: DomIndexes,
}

impl std::fmt::Debug for Frame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Frame")
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
            .field(
                "dom_content_loaded_dispatched",
                &self.dom_content_loaded_dispatched,
            )
            .field("hover_debugging", &self.hover_debugging)
            .finish()
    }
}

impl Frame {
    fn new(url: String, hover_debugging: bool, render_size: PhysicalSize<u32>) -> Self {
        install_default_crypto_provider();

        let font_handler = Rc::new(FontHandler::new().unwrap());

        Self {
            url,
            renderer: None,
            window: None,
            js_runtime: None,
            tokio: None,
            html_parser: None,
            font_handler,
            executed_scripts: Rc::new(RefCell::new(ExecutedScripts::new())),
            layout_dirty: true,
            layout_booted: false,
            network_fetch: Rc::new(RefCell::new(NetworkFetch::new())),
            document_id: 0,
            dom_content_loaded_dispatched: false,
            load_dispatched: false,
            is_top: true,
            hover_debugging,
            render_size,
            loaded_nodes: vec![],
            last_hover_position: None,
            animation_frame_requested: false,
            last_animation_frame: Instant::now(),
            blob_store: Arc::new(BlobStore::default()),
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

    async fn get_html_for_navigation(&self, request: FormNavigation) -> Result<(String, String)> {
        let url = request.url;
        if url.as_str() == "about:blank" {
            return Ok((
                r#"<html>
  <head></head>
  <body></body>
</html>"#
                    .to_string(),
                url.to_string(),
            ));
        }

        if request.method == FormMethod::Get
            && let Some(stripped) = url.as_str().strip_prefix("file://")
        {
            let contents = fs::read_to_string(stripped)?;
            Ok((contents, url.to_string()))
        } else {
            println!("Fetching HTML for {:?}", url);
            let client = &self.network_fetch.borrow_mut().client;
            let request = match request.method {
                FormMethod::Get => client.get(url),
                FormMethod::Post => client
                    .post(url)
                    .header("content-type", "application/x-www-form-urlencoded")
                    .body(request.body.unwrap_or_default()),
            };
            let resp = request.send().await?;
            let url = resp.url().to_string();
            let text = resp.text().await?;
            Ok((text, url))
        }
    }

    pub fn install_js_host(&mut self) {
        let broadcast_channel = InMemoryBroadcastChannel::default();
        let client = self.network_fetch.borrow().client.clone();
        self.js_runtime = Some(Rc::new(RefCell::new(deno_core::JsRuntime::new(
            deno_core::RuntimeOptions {
                module_loader: Some(Rc::new(HttpModuleLoader::new(client))),
                extensions: vec![
                    browser::init(),
                    deno_webidl::deno_webidl::init(),
                    deno_web::deno_web::init(Arc::clone(&self.blob_store), None, broadcast_channel),
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

    fn set_current_script(runtime: &mut JsRuntime, node_idx: Option<usize>) -> Result<()> {
        let code = match node_idx {
            Some(node_idx) => format!("__set_current_script_node_idx({node_idx})"),
            None => "__set_current_script_node_idx(null)".to_string(),
        };
        runtime.execute_script("set current script", code)?;
        Ok(())
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

    fn dispatch_dom_content_loaded_once(&mut self) -> Result<()> {
        if self.dom_content_loaded_dispatched {
            return Ok(());
        }

        self.dom_content_loaded_dispatched = true;
        self.execute_host_script(
            "DOMContentLoaded",
            r#"
                document.dispatchEvent(new Event("DOMContentLoaded", {
                    bubbles: true,
                    cancelable: false,
                }))
            "#
            .to_string(),
        )?;
        Ok(())
    }

    fn dispatch_load_once(&mut self) -> Result<()> {
        if self.load_dispatched {
            return Ok(());
        }

        self.load_dispatched = true;
        self.execute_host_script(
            "load",
            r#"
                window.dispatchEvent(new Event("load", {
                    bubbles: false,
                    cancelable: false,
                }))
            "#
            .to_string(),
        )?;
        Ok(())
    }

    fn reset_js_document_state(&mut self) -> Result<()> {
        self.execute_host_script(
            "document navigation reset",
            "globalThis.__clear_all_timers?.(); globalThis.__EVENT_LISTENERS = {}; globalThis.__clear_node_map?.(); history.state = null;".to_string(),
        )?;
        Ok(())
    }

    fn handle_frame_command(
        &mut self,
        cmd: FrameCommand,
        parent_proxy: &RendererProxy,
        size: &PhysicalSize<u32>,
        bitmap_for_thread: &Arc<Mutex<Vec<u32>>>,
    ) {
        match cmd {
            cmd @ (FrameCommand::Render
            | FrameCommand::UserEvent(UserEvent::DomUpdated)
            | FrameCommand::UserEvent(UserEvent::CanvasUpdated)
            | FrameCommand::UserEvent(UserEvent::ImagesPrefetched(_))) => {
                // A render may have already consumed the pending update before its queued event arrives.
                if matches!(&cmd, FrameCommand::UserEvent(UserEvent::DomUpdated))
                    && !self.renderer.as_ref().unwrap().borrow().pending_dom_update
                {
                    return;
                }
                let canvas_updated =
                    matches!(&cmd, FrameCommand::UserEvent(UserEvent::CanvasUpdated));
                if canvas_updated {
                    self.renderer
                        .as_ref()
                        .unwrap()
                        .borrow_mut()
                        .pending_canvas_update = false;
                }
                if let FrameCommand::UserEvent(UserEvent::ImagesPrefetched(urls)) = cmd
                    && let Some(renderer) = self.renderer.as_ref()
                {
                    renderer.borrow_mut().finish_image_prefetch(urls);
                }
                if self
                    .renderer
                    .as_ref()
                    .is_some_and(|renderer| renderer.borrow().pending_dom_update)
                {
                    self.process_dom_update();
                }

                let mut pixels = vec![0; (size.width * size.height) as usize];
                self.renderer.as_ref().unwrap().borrow_mut().render_into(
                    &mut pixels,
                    size.width,
                    size.height,
                    !canvas_updated,
                );

                *bitmap_for_thread.lock().unwrap() = pixels;

                let _ = parent_proxy.fire_user_event(UserEvent::FrameUpdated);
            }
            FrameCommand::UserEvent(UserEvent::Hover(position)) => {
                self.apply_hovering(&position);

                let mut pixels = vec![0; (size.width * size.height) as usize];
                self.renderer.as_ref().unwrap().borrow_mut().render_into(
                    &mut pixels,
                    size.width,
                    size.height,
                    true,
                );

                *bitmap_for_thread.lock().unwrap() = pixels;
                let _ = parent_proxy.fire_user_event(UserEvent::FrameUpdated);
            }
            FrameCommand::UserEvent(UserEvent::Click) => {
                if let Err(err) = self.on_click() {
                    eprintln!("Failed to handle iframe click: {err:?}");
                }

                if self
                    .renderer
                    .as_ref()
                    .is_some_and(|renderer| renderer.borrow().pending_dom_update)
                {
                    self.process_dom_update();
                }

                let mut pixels = vec![0; (size.width * size.height) as usize];
                self.renderer.as_ref().unwrap().borrow_mut().render_into(
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
            FrameCommand::UserEvent(UserEvent::ParentMessage(message)) => {
                let data = js_string_literal(&message);
                let code = format!(
                    r#"
                (() => {{
                    const event = new MessageEvent("message", {{ data: {} }})
                    window.dispatchEvent(event)
                }})()
                "#,
                    data
                );
                self.execute_host_script("parent message handler", code)
                    .unwrap();
            }
            FrameCommand::Dom(FrameDomCommand::QuerySelector {
                selector,
                required_parent,
                reply,
            }) => {
                let mut renderer = self.renderer.as_ref().unwrap().borrow_mut();
                let _ = reply.send(Ok(renderer.query_selector_node(selector, required_parent)));
            }
            FrameCommand::Dom(FrameDomCommand::QuerySelectorAll {
                selector,
                required_parent,
                reply,
            }) => {
                let mut renderer = self.renderer.as_ref().unwrap().borrow_mut();
                let _ = reply.send(Ok(
                    renderer.query_selector_all_nodes(selector, required_parent)
                ));
            }
            FrameCommand::Dom(FrameDomCommand::ReplaceInnerHtml {
                html,
                node_idx,
                reply,
            }) => {
                let mut renderer = self.renderer.as_ref().unwrap().borrow_mut();
                renderer.replace_inner_html(node_idx, html);
                let _ = reply.send(());
            }
            FrameCommand::Dom(FrameDomCommand::GetInnerHtml { node_idx, reply }) => {
                let renderer = self.renderer.as_ref().unwrap().borrow();
                let html = renderer.get_element_inner_html(node_idx);
                let _ = reply.send(html);
            }
            FrameCommand::Dom(FrameDomCommand::GetComputedStyle { node_idx, reply }) => {
                let renderer = self.renderer.as_ref().unwrap().borrow();
                let _ = reply.send(computed_style_properties(&renderer, node_idx));
            }
            FrameCommand::Dom(FrameDomCommand::CreateElement { tag, reply }) => {
                let mut renderer = self.renderer.as_ref().unwrap().borrow_mut();
                let idx = renderer.create_element(tag);
                let _ = reply.send(idx);
            }
            FrameCommand::Dom(FrameDomCommand::GetElementsByTagName {
                tag,
                reply,
                required_parent,
            }) => {
                let renderer = self.renderer.as_ref().unwrap().borrow_mut();
                let _ = reply.send(renderer.get_elements_by_tag_name(&tag, required_parent));
            }
            FrameCommand::Dom(FrameDomCommand::GetElementsByName {
                name,
                reply,
                required_parent,
            }) => {
                let renderer = self.renderer.as_ref().unwrap().borrow_mut();
                let _ = reply.send(renderer.get_elements_by_name(&name, required_parent));
            }
            FrameCommand::Dom(FrameDomCommand::GetElementsByClassName {
                class_names,
                reply,
                required_parent,
            }) => {
                let renderer = self.renderer.as_ref().unwrap().borrow_mut();
                let _ =
                    reply.send(renderer.get_elements_by_class_name(&class_names, required_parent));
            }
            FrameCommand::Dom(FrameDomCommand::UpdateElementAttributes {
                node_idx,
                attributes,
                reply,
            }) => {
                let mut renderer = self.renderer.as_ref().unwrap().borrow_mut();
                let _ = reply.send(renderer.update_element_attributes(node_idx, attributes));
            }
            FrameCommand::UserEvent(UserEvent::AnimationFrameRequested) => {
                self.animation_frame_requested = true;
            }
            _ => {}
        }
    }

    fn animation_frame_delay(&self) -> Option<Duration> {
        self.animation_frame_requested.then(|| {
            self.last_animation_frame
                .checked_add(ANIMATION_FRAME_INTERVAL)
                .unwrap()
                .saturating_duration_since(Instant::now())
        })
    }

    fn command_wait_timeout(&self, js_pending: bool) -> Option<Duration> {
        match (js_pending, self.animation_frame_delay()) {
            (true, Some(animation_delay)) => Some(Duration::from_millis(16).min(animation_delay)),
            (true, None) => Some(Duration::from_millis(16)),
            (false, Some(animation_delay)) => Some(animation_delay),
            (false, None) => None,
        }
    }

    fn run_animation_frame_if_due(&mut self) -> Result<bool> {
        if self
            .animation_frame_delay()
            .is_none_or(|delay| !delay.is_zero())
        {
            return Ok(false);
        }

        self.animation_frame_requested = false;
        self.last_animation_frame = Instant::now();
        self.execute_host_script(
            "requestAnimationFrame callbacks",
            "__run_animation_frame(performance.now())".to_string(),
        )?;
        Ok(true)
    }

    fn pump_js_event_loop_once(&mut self) -> Result<bool> {
        let event_loop_notify = self
            .renderer
            .as_ref()
            .unwrap()
            .borrow()
            .event_loop_notify
            .clone();
        let event_loop_wait = self
            .animation_frame_delay()
            .unwrap_or(Duration::from_millis(10))
            .min(Duration::from_millis(10));
        let mut runtime = self.js_runtime.as_mut().unwrap().borrow_mut();

        // The current-thread Tokio runtime only drives network/timer IO while block_on is active,
        // so keep this as a short cooperative slice rather than a pure Winit waker.
        self.tokio
            .as_ref()
            .unwrap()
            .clone()
            .borrow_mut()
            .block_on(async {
                tokio::select! {
                    result = runtime.run_event_loop(Default::default()) => match result {
                        Ok(()) => Ok(false),
                        Err(err) => {
                            eprintln!("Error occurred while pumping JS loop: {}", err);
                            Ok(true)
                        }
                    },
                    _ = event_loop_notify.notified() => Ok(true),
                    _ = tokio::time::sleep(event_loop_wait) => Ok(true),
                }
            })
    }

    async fn execute_js_script(&mut self, js: &Script) -> Result<()> {
        let document_id = self.document_id;
        let Some(mut runtime) = self.js_runtime.as_mut().and_then(|v| Some(v.borrow_mut())) else {
            return Ok(());
        };

        match &js.content {
            ScriptContent::Code(code) => {
                let code_context: String = code.chars().take(40).collect();
                Self::set_current_script(&mut runtime, js.node_idx)?;
                let result = runtime
                    .execute_script(format!("injected code ({})", code_context), code.clone());
                Self::set_current_script(&mut runtime, None)?;
                match result {
                    Ok(_) => Self::drain_microtasks(&mut runtime),
                    Err(err) => eprintln!("Failed to execute JS with error: {}", err),
                };
            }
            ScriptContent::Link(link) => {
                let Ok(base) = ReqwestUrl::parse(&self.url) else {
                    return Ok(());
                };
                let Ok(url) = resolve_url(&link, Some(&base)) else {
                    return Ok(());
                };
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
                        Self::set_current_script(&mut runtime, js.node_idx)?;
                        let result = runtime.execute_script(url.to_string(), code);
                        Self::set_current_script(&mut runtime, None)?;
                        match result {
                            Ok(_) => Self::drain_microtasks(&mut runtime),
                            Err(err) => {
                                eprintln!("Failed to execute JS at {} with error: {}", link, err)
                            }
                        };
                    }
                    ScriptType::Module => {
                        let module_id = if document_id == 0 {
                            runtime.load_side_es_module(&url).await
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
                                .append_pair("__frame_document", &document_id.to_string());
                            runtime
                                .load_side_es_module_from_code(&module_url, code)
                                .await
                        };
                        if let Ok(module_id) = module_id.inspect_err(|err| {
                            eprintln!("Failed to load JS module at {} with error: {}", url, err)
                        }) {
                            let result = runtime.mod_evaluate(module_id);
                            let _ = runtime
                                .with_event_loop_promise(result, Default::default())
                                .await
                                .inspect_err(|err| {
                                    eprintln!("Failed to execute JS at {} with error: {}", url, err)
                                });
                        }
                    }
                }
            }
        };

        // Run onload handlers
        if let Some(node_idx) = js.node_idx {
            let code = format!(
                "runEventListeners(`${{{}}}:load`, new Event('load'))",
                node_idx
            );
            runtime.execute_script("script onload", code.clone())?;
            Self::drain_microtasks(&mut runtime);
        }

        Ok(())
    }

    async fn execute_js(&mut self, scripts: Vec<Script>) -> Result<()> {
        for js in scripts {
            self.execute_js_script(&js).await?;
        }

        Ok(())
    }

    pub fn run_js(&mut self) -> Result<()> {
        let scripts: Vec<Script> = self
            .renderer
            .as_ref()
            .unwrap()
            .borrow_mut()
            .get_scripts()
            .into_iter()
            .filter(|js| self.executed_scripts.borrow_mut().upsert_script(js))
            .collect();

        if scripts.len() == 0 {
            return Ok(());
        }

        println!("Running {} JS scripts", scripts.len());

        self.tokio
            .as_ref()
            .unwrap()
            .clone()
            .borrow_mut()
            .block_on(self.execute_js(scripts))?;
        self.dispatch_dom_content_loaded_once()?;
        self.dispatch_load_once()?;

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
                .get_str("http-equiv")
                .is_some_and(|v| v.to_lowercase() == "refresh")
        {
            let Some(content) = element.attributes.get_str("content") else {
                return None;
            };
            let Some((delay, instructions)) = content.split_once(";") else {
                return None;
            };
            let Some(url) = instructions.strip_prefix("url=") else {
                return None;
            };
            let Ok(_delay) = delay.parse::<f64>() else {
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
        let url = resolve_url(&href, None)?;
        self.navigate_with_request(FormNavigation {
            url,
            method: FormMethod::Get,
            body: None,
        })
    }

    pub fn navigate_with_request(&mut self, request: FormNavigation) -> Result<()> {
        let (input, final_url) = self
            .tokio
            .as_ref()
            .unwrap()
            .borrow_mut()
            .block_on(self.get_html_for_navigation(request))?;
        println!("Changing url to {}", final_url);
        self.url = final_url;

        self.html_parser = Some(HtmlParser::new(input));
        self.html_parser.as_mut().unwrap().parse().expect(&format!(
            "Failed to parse. Context: {}",
            self.html_parser.as_mut().unwrap().get_context()
        ));

        if let Some(renderer) = &self.renderer {
            let nodes_table =
                NodesTable::new_from_nodes(self.html_parser.as_mut().unwrap().nodes.clone());
            let nodes_idxs = sorted_node_idxs(&nodes_table);
            renderer
                .borrow_mut()
                .replace_document(self.url.clone(), nodes_table, nodes_idxs);
            self.document_id += 1;
            *self.executed_scripts.borrow_mut() = ExecutedScripts::new();
            self.dom_content_loaded_dispatched = false;
            self.load_dispatched = false;
            self.loaded_nodes.clear();
            self.animation_frame_requested = false;
            self.last_animation_frame = Instant::now();
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
        proxy: RendererProxy,
    ) -> Result<()> {
        self.refresh_renderer(params.nodes, params.dom_indexes, params.nodes_idxs);

        self.renderer
            .as_mut()
            .unwrap()
            .borrow_mut()
            .event_loop_proxy = Some(proxy.clone());

        if let Some(js_runtime) = self.js_runtime.as_mut().and_then(|v| Some(v.borrow_mut())) {
            js_runtime.op_state().borrow_mut().put(JsHostState {
                renderer: self.renderer.as_mut().cloned().unwrap(),
                proxy: proxy,
                executed_scripts: self.executed_scripts.clone(),
                is_top: self.is_top,
            });
        }
        self.setup_js_dom()?;

        Ok(())
    }

    pub fn start_main_loop(&mut self, proxy: RendererProxy, rx: Receiver<FrameCommand>) {
        let mut js_pending = true;
        loop {
            let cmd = if let Some(timeout) = self.command_wait_timeout(js_pending) {
                match rx.recv_timeout(timeout) {
                    Ok(cmd) => Some(cmd),
                    Err(std::sync::mpsc::RecvTimeoutError::Timeout) => None,
                    Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => break,
                }
            } else {
                match rx.recv() {
                    Ok(cmd) => Some(cmd),
                    Err(_) => break,
                }
            };
            let had_command = cmd.is_some();
            if let Some(cmd) = cmd {
                self.handle_main_event(&proxy, cmd);

                while let Ok(cmd) = rx.try_recv() {
                    self.handle_main_event(&proxy, cmd);
                }
            }
            if had_command || js_pending {
                js_pending = self
                    .pump_js_event_loop_once()
                    .inspect_err(|err| eprintln!("Error occurred while pumping JS loop: {}", err))
                    .unwrap_or(false);
            }
            let _ = self.run_animation_frame_if_due().inspect_err(|err| {
                eprintln!("Error occurred while running animation frame: {}", err)
            });
        }
    }

    pub fn open(&mut self) -> Result<BootParams> {
        self.register_tokio_runtime()?;
        self.navigate(self.url.clone())?;
        self.install_js_host();
        let nodes_table =
            NodesTable::new_from_nodes(self.html_parser.as_mut().unwrap().nodes.clone());
        let nodes_idxs = sorted_node_idxs(&nodes_table);
        let dom_indexes = get_dom_indexes(&nodes_table, &nodes_idxs, &mut ClassIndexes::new());
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
            let clicked_iframe = {
                let renderer = self.renderer.as_ref().unwrap().borrow();
                renderer.nodes.get(hovering_node_idx).is_some_and(
                    |node| matches!(node, Node::Element(element) if element.tag == "iframe"),
                )
            };
            if clicked_iframe {
                if let Some(handle) = self
                    .renderer
                    .as_ref()
                    .unwrap()
                    .borrow()
                    .frames
                    .get(&hovering_node_idx)
                {
                    let _ = handle.tx.send(FrameCommand::UserEvent(UserEvent::Click));
                }
                return Ok(());
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
                            .get_str("type")
                            .is_none_or(|v| FOCUSABLE_INPUT_TYPES.contains(&v.as_ref()))
                });
                renderer.focusable = focusable;
            }

            let submittable_input = self.renderer.as_ref().unwrap().borrow().walk_node_upwards(
                hovering_node_idx,
                |node| {
                    let Node::Element(element) = node else {
                        return false;
                    };
                    is_submit_button(element)
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
                let parent_href = {
                    let renderer = self.renderer.as_ref().unwrap().borrow();
                    match renderer.nodes.get(parent) {
                        Some(Node::Element(element)) => {
                            element.attributes.get_str("href").map(|v| v.into_owned())
                        }
                        _ => None,
                    }
                };
                if let Some(href) = parent_href
                    && !default_prevented
                {
                    let current_url = url::Url::parse(&self.url)?;
                    let resolved_url = current_url.join(&href)?;
                    self.navigate(resolved_url.to_string()).unwrap();
                }
            }
        } else {
            let mut renderer = self.renderer.as_mut().unwrap().borrow_mut();
            renderer.focusable = None;
        }

        Ok(())
    }

    fn setup_js_dom(&mut self) -> Result<()> {
        let code = ScriptContent::Code(
            format!(
                r#"
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
        nodes_table: NodesTable,
        dom_indexes: DomIndexes,
        nodes_idxs: Vec<usize>,
    ) {
        self.renderer = Some(Rc::new(RefCell::new(Renderer::new(
            self.url.clone(),
            self.tokio.as_ref().unwrap().clone(),
            nodes_table,
            self.render_size,
            Rc::clone(&self.font_handler),
            Rc::clone(&self.network_fetch),
            dom_indexes,
            nodes_idxs,
            Arc::clone(&self.blob_store),
        ))));
    }

    fn tick_animations(&mut self) -> bool {
        let mut renderer = self.renderer.as_mut().unwrap().borrow_mut();
        renderer.tick_animations()
    }

    fn fire_load_phase(&mut self, phase: &LoadPhase, idxs: Option<&Vec<usize>>) {
        let nodes_idxs = {
            let renderer = self.renderer.as_ref().unwrap().borrow();
            let idxs_to_fire: Vec<&usize> = renderer
                .nodes_idxs
                .iter()
                .filter(|idx| {
                    idxs.is_none_or(|f| f.contains(idx))
                        && !self.loaded_nodes.contains(idx)
                        && renderer.element_has_loaded(**idx, phase)
                })
                .collect();

            for idx in idxs_to_fire.iter() {
                self.loaded_nodes.push(**idx);
            }

            idxs_to_fire
                .iter()
                .map(|idx| idx.to_string())
                .collect::<Vec<String>>()
                .join(",")
        };
        let load_code = format!(
            r#"
        (() => {{
            const idxs = [{}]
            for (let idx of idxs) {{
                runEventListeners(`${{idx}}:load`, new Event("load", {{
                    bubbles: false,
                    cancelable: false,
                }}))
            }}
        }})()
        "#,
            nodes_idxs
        );
        let _ = self
            .execute_host_script("load", load_code)
            .inspect_err(|err| eprintln!("Element load handler failed with err: {}", err));
    }

    fn refresh_hover_after_render(&mut self) {
        let Some(cursor) = self.last_hover_position else {
            return;
        };

        self.apply_hovering(&cursor);
    }

    fn refresh_intersections(&mut self) -> Result<()> {
        let (intersecting, not_intersecting) = {
            let mut renderer = self.renderer.as_mut().unwrap().borrow_mut();
            renderer.compute_intersections()
        };
        if !intersecting.is_empty() || !not_intersecting.is_empty() {
            let intersecting = deno_core::serde_json::to_string(&intersecting)?;
            let not_intersecting = deno_core::serde_json::to_string(&not_intersecting)?;
            self.execute_host_script(
                "IntersectionObserver callbacks",
                format!("__runIntersectionObservers({intersecting}, {not_intersecting})"),
            )?;
        }
        Ok(())
    }

    fn decode_detached_images(&mut self) {
        let mut renderer = self.renderer.as_mut().unwrap().borrow_mut();
        let mut detached_images = vec![];

        for (idx, node) in renderer.nodes.iter() {
            let Node::Element(element) = node else {
                continue;
            };
            if element.tag == "img" && node.get_parent().is_none() {
                detached_images.push(idx);
            }
        }

        for idx in detached_images {
            renderer.decode_and_rasterize_img(idx, &LayoutMode::Complete, None, None, None, None);
        }
    }

    fn update_newly_loaded_images(&mut self, prev_state: &HashSet<usize>) {
        let newly_loaded: Vec<(usize, u32, u32)> = {
            let renderer = self.renderer.as_ref().unwrap().borrow();
            renderer
                .images_nodes_loaded
                .iter()
                .filter(|(idx, _)| !prev_state.contains(idx))
                .map(|(&idx, &(height, width))| (idx, height, width))
                .collect()
        };

        if newly_loaded.is_empty() {
            return;
        }

        let images = newly_loaded
            .iter()
            .map(|(idx, height, width)| format!("[{idx}, {height}, {width}]"))
            .collect::<Vec<_>>()
            .join(",");

        self.execute_host_script(
            "update newly loaded images",
            format!(
                r#"
        for (const [idx, height, width] of [{}]) {{
            const node = __elementFromNodeIdx(idx)
            if (!node) continue

            node.naturalHeight = height
            node.naturalWidth = width
        }}
        "#,
                images
            ),
        )
        .unwrap();
    }

    fn render_loop(&mut self) -> Vec<u32> {
        let animation_redraw = self.tick_animations();
        let prev_loaded_images: HashSet<usize> = self
            .renderer
            .as_ref()
            .unwrap()
            .borrow()
            .images_nodes_loaded
            .keys()
            .copied()
            .collect();
        let first_boot = !self.layout_booted;
        if first_boot {
            let start = Instant::now();
            let js_result = self.run_js();
            println!(
                "Finished running JS code in {}ms: {:?}",
                Instant::now().duration_since(start).as_millis(),
                js_result
            );
            self.fire_load_phase(&LoadPhase::JsDone, None);
        }
        let mut buffer =
            vec![0; self.render_size.width as usize * self.render_size.height as usize];
        self.render(&mut buffer);
        self.refresh_hover_after_render();
        let _ = self.refresh_intersections();
        self.decode_detached_images();
        self.update_newly_loaded_images(&prev_loaded_images);

        // If there are animations, continue re-rendering until there aren't
        if animation_redraw && let Some(window) = &self.window {
            window.request_redraw();
        }

        buffer
    }

    fn render(&mut self, buffer: &mut Vec<u32>) -> bool {
        if self
            .renderer
            .as_ref()
            .is_some_and(|renderer| renderer.borrow().pending_dom_update)
        {
            self.process_dom_update();
        }

        let start = Instant::now();

        self.renderer.as_mut().unwrap().borrow_mut().render_into(
            buffer,
            self.render_size.width,
            self.render_size.height,
            self.layout_dirty,
        );
        self.layout_dirty = false;

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
        {
            let mut renderer = self.renderer.as_ref().unwrap().borrow_mut();
            renderer.pending_dom_update = false;
            renderer.hovering = None;
            renderer.clear_layout_state();
            renderer.recompute_nodes();
        }
        self.layout_dirty = true;
        let start = Instant::now();
        let js_result = self.run_js();
        println!(
            "Finished running JS code in {}ms: {:?}",
            Instant::now().duration_since(start).as_millis(),
            js_result
        );
        self.fire_load_phase(&LoadPhase::JsDone, None);

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
        self.last_hover_position = Some(*cursor);
        let (should_re_render, hovering, iframe_hover) = {
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
            let iframe_hover = new_value.and_then(|hovering_layout_idx| {
                let hovering_node_idx = renderer.layout_to_node_idx(&hovering_layout_idx);
                let iframe_node = renderer.nodes.get(hovering_node_idx).is_some_and(
                    |node| matches!(node, Node::Element(element) if element.tag == "iframe"),
                );
                if !iframe_node {
                    return None;
                }

                renderer
                    .rendered_nodes_ordered
                    .iter()
                    .find(|rendered_node| rendered_node.layout_box_idx == hovering_layout_idx)
                    .and_then(|rendered_node| {
                        renderer
                            .layout_table
                            .get(&hovering_layout_idx)
                            .map(|layout_box| {
                                (
                                    hovering_node_idx,
                                    Position {
                                        x: cursor.x - layout_box.rect.x - rendered_node.offset_x,
                                        y: cursor.y - layout_box.rect.y - rendered_node.offset_y,
                                    },
                                )
                            })
                    })
            });
            (
                new_value != old_value && one_has_hovering_impact,
                new_value,
                iframe_hover,
            )
        };
        if let Some((iframe_node_idx, local_position)) = iframe_hover {
            let frame_tx = {
                self.renderer
                    .as_ref()
                    .unwrap()
                    .borrow()
                    .frames
                    .get(&iframe_node_idx)
                    .map(|handle| handle.tx.clone())
            };
            if let Some(frame_tx) = frame_tx {
                let _ = frame_tx.send(FrameCommand::UserEvent(UserEvent::Hover(local_position)));
            }
        }
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
            if let Some(window) = self.window.as_mut() {
                window.request_redraw();
            }
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

    pub fn handle_main_event(&mut self, proxy: &RendererProxy, event: FrameCommand) {
        match event {
            FrameCommand::Render => {
                let buffer = self.render_loop();
                let _ = proxy.fire_tab_updated(buffer);
            }
            FrameCommand::Resized(new_size) => {
                self.render_size = new_size;
                self.layout_dirty = true;
                let buffer = self.render_loop();
                let _ = proxy.fire_tab_updated(buffer);
            }
            FrameCommand::UserEvent(
                event @ (UserEvent::FrameUpdated
                | UserEvent::CanvasUpdated
                | UserEvent::ImagesPrefetched(_)),
            ) => {
                match event {
                    UserEvent::CanvasUpdated => {
                        if let Some(renderer) = self.renderer.as_ref() {
                            renderer.borrow_mut().pending_canvas_update = false;
                        }
                    }
                    UserEvent::ImagesPrefetched(urls) => {
                        if let Some(renderer) = self.renderer.as_ref() {
                            renderer.borrow_mut().finish_image_prefetch(urls);
                        }
                        self.layout_dirty = true;
                    }
                    UserEvent::FrameUpdated => {}
                    _ => unreachable!(),
                }
                let buffer = self.render_loop();
                let _ = proxy.fire_tab_updated(buffer);
            }
            FrameCommand::UserEvent(UserEvent::FrameLoaded(node_idx)) => {
                self.fire_load_phase(&LoadPhase::IframeDone, Some(&vec![node_idx]));
            }
            FrameCommand::UserEvent(UserEvent::AnimationFrameRequested) => {
                self.animation_frame_requested = true;
            }
            FrameCommand::UserEvent(UserEvent::DomUpdated) => {
                // Ignore a queued notification when another render already processed its DOM changes.
                let pending_dom_update =
                    self.renderer.as_ref().unwrap().borrow().pending_dom_update;
                if pending_dom_update {
                    self.execute_dom_update();
                }
            }
            FrameCommand::UserEvent(UserEvent::ChildMessage(message)) => {
                let data = js_string_literal(&message);
                let code = format!(
                    r#"
                (() => {{
                    const event = new MessageEvent("message", {{ data: {} }})
                    window.dispatchEvent(event)
                }})()
                "#,
                    data
                );
                self.execute_host_script("child message handler", code)
                    .unwrap();
            }
            FrameCommand::UserEvent(UserEvent::Navigate((href, reload))) => {
                let navigation = match href {
                    UserNavigateUrl::Raw(raw) => {
                        let current_url = url::Url::parse(&self.url).unwrap();
                        FormNavigation {
                            url: current_url.join(&raw).unwrap(),
                            method: FormMethod::Get,
                            body: None,
                        }
                    }
                    UserNavigateUrl::Form(navigation) => navigation,
                };
                if reload {
                    if let Err(err) = self.navigate_with_request(navigation) {
                        eprintln!("Navigation failed: {err:?}");
                    } else {
                        let _ = proxy.fire_tab_url_updated(self.url.clone());
                    }
                } else {
                    self.url = navigation.url.to_string();
                    self.renderer.as_mut().unwrap().borrow_mut().url = self.url.clone();
                    self.setup_js_dom().unwrap();
                    let _ = proxy.fire_tab_url_updated(self.url.clone());
                }
            }
            FrameCommand::UserEvent(UserEvent::Hover(position)) => {
                self.apply_hovering(&position);
            }
            FrameCommand::UserEvent(UserEvent::Click) => {
                self.on_click().unwrap();
            }
            FrameCommand::UserEvent(UserEvent::Keyup(event)) => {
                self.handle_keyup(event);
            }
            FrameCommand::UserEvent(UserEvent::ScrollBy((_, y))) => {
                self.scroll_y_by(y);
            }
            FrameCommand::UserEvent(UserEvent::IntersectionTracked) => {
                let _ = self.refresh_intersections();
            }
            _ => {}
        };
    }

    pub fn scroll_y_by(&mut self, y: f32) {
        let scrollable_idx = {
            let mut renderer = self.renderer.as_mut().unwrap().borrow_mut();
            let Some((scrollable_idx, content_height, scrollport_height)) =
                renderer.get_scrollable_dimensions()
            else {
                return;
            };
            let max_scroll = (content_height as f32 - scrollport_height as f32).max(0.);
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
        let _ = self
            .execute_host_script("script onscroll", code)
            .inspect_err(|err| eprintln!("Script onscroll handler failed with err: {}", err));
        if let Some(window) = self.window.as_mut() {
            window.request_redraw();
        }
    }

    fn handle_keyup(&mut self, event: KeyEvent) {
        let focusable = self.renderer.as_ref().unwrap().borrow().focusable;
        if let Some(focusable) = focusable
            && let Some(input_text) = event.text
        {
            let new_text = {
                let mut renderer = self.renderer.as_ref().unwrap().borrow_mut();
                if let Some(Node::Element(element)) = renderer.nodes.get_mut(focusable) {
                    let entry = element
                        .attributes
                        .values
                        .entry("value".to_string())
                        .or_default();
                    *entry += input_text.as_str();
                    Some(entry.clone())
                } else {
                    None
                }
            };

            if new_text.is_some() {
                let input_data = js_string_literal(&input_text);
                let input_type =
                    js_string_literal(if input_text.contains('\n') || input_text.contains('\r') {
                        "insertLineBreak"
                    } else {
                        "insertText"
                    });
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
                    const event = new InputEvent("input", {{
                        bubbles: true,
                        cancelable: false,
                        data: {},
                        inputType: {},
                    }})
                    __elementFromNodeIdx({}).dispatchEvent(event)
                    return event.defaultPrevented
                }})()
                "#,
                        input_data, input_type, focusable
                    ),
                )
                .unwrap();
            }
        }
    }
}

fn profile_compute_node_styles(args: &[String]) -> Result<()> {
    let url = args
        .get(2)
        .map(String::as_str)
        .unwrap_or("https://slack.com/");
    let iterations = args
        .get(3)
        .map(|value| value.parse::<usize>())
        .transpose()
        .context("Expected iterations to be an integer")?
        .unwrap_or(50);

    let mut frame = Frame::new(
        url.to_string(),
        false,
        PhysicalSize {
            width: WINDOW_WIDTH,
            height: WINDOW_HEIGHT,
        },
    );
    let mut params = frame.open()?;
    let window_size = PhysicalSize::new(WINDOW_WIDTH, WINDOW_HEIGHT);
    let hovering_chain = vec![];
    let mut css_parse_cache = HashMap::new();
    let mut flattened_css_cache = None;
    let mut css_parser = CssParser::new();
    let mut compute = || {
        compute_node_styles(
            &frame.url,
            frame.tokio.as_ref().unwrap(),
            &frame.network_fetch,
            &params.nodes,
            &params.nodes_idxs,
            params.dom_indexes.root_indice,
            &window_size,
            &mut params.dom_indexes,
            &mut css_parse_cache,
            &mut flattened_css_cache,
            &hovering_chain,
            &mut css_parser,
            HashMap::new(),
            HashMap::new(),
        )
    };

    std::hint::black_box(compute());
    for _ in 0..iterations {
        std::hint::black_box(compute());
    }

    Ok(())
}

pub struct Browser {
    pub tabs: Vec<TabHandle>,
    window: Arc<Window>,
    event_loop_proxy: EventLoopProxy<UserEvent>,
    current_tab_idx: usize,
    fps_counter: Option<FpsCounter>,
}

pub struct TabHandle {
    tx: Sender<FrameCommand>,
    url: String,
}

enum BrowserAction {
    OpenTab(String),
    SelectTab(usize),
    Rerender,
    Navigate(String),
}

struct HeaderState {
    url: String,
    fps: Option<u32>,
}

struct FpsCounter {
    window_started: Instant,
    frames: u32,
    fps: u32,
}

impl FpsCounter {
    fn new() -> Self {
        Self {
            window_started: Instant::now(),
            frames: 0,
            fps: 0,
        }
    }

    fn record_present(&mut self) -> Option<u32> {
        self.frames += 1;
        let elapsed = self.window_started.elapsed();
        if elapsed < Duration::from_millis(500) {
            return None;
        }

        self.fps = (self.frames as f32 / elapsed.as_secs_f32()).round() as u32;
        self.frames = 0;
        self.window_started = Instant::now();
        Some(self.fps)
    }
}

impl Browser {
    pub fn current_tab(&self) -> &TabHandle {
        &self.tabs[self.current_tab_idx]
    }

    fn build_header(
        &self,
        builder: &mut UiBuilder,
        state: &Rc<RefCell<HeaderState>>,
        action_tx: Sender<BrowserAction>,
    ) -> Result<()> {
        builder.clean();

        builder.start_element();
        builder.width(WINDOW_WIDTH)?;
        builder.height(HEADER_HEIGHT)?;
        builder.bg(0x2e2e2eFF)?;

        builder.start_element();
        builder.width(WINDOW_WIDTH)?;
        builder.height(60)?;
        builder.padding(10)?;
        builder.hor()?;
        builder.gap(10)?;

        for (tab_idx, _) in self.tabs.iter().enumerate() {
            builder.start_element();
            builder.padding(10)?;
            builder.width(100)?;
            builder.height(40)?;
            builder.rounded(10)?;
            builder.bg(0x363636FF)?;
            builder.text(format!("Tab {}", tab_idx + 1))?;
            let tx = action_tx.clone();
            builder.on_click(move || {
                let _ = tx.send(BrowserAction::SelectTab(tab_idx));
            })?;
            builder.finish_element()?;
        }

        builder.start_element();
        builder.padding(10)?;
        builder.width(100)?;
        builder.height(40)?;
        builder.bg(0x363636FF)?;
        builder.rounded(10)?;
        builder.text("NEW".to_string())?;
        let tx = action_tx.clone();
        builder.on_click(move || {
            let _ = tx.send(BrowserAction::OpenTab("https://www.google.com".to_string()));
        })?;
        builder.finish_element()?;

        if self.fps_counter.is_some() {
            builder.start_element();
            builder.padding(10)?;
            builder.width(100)?;
            builder.height(40)?;
            builder.bg(0x363636FF)?;
            builder.text(match state.borrow().fps {
                Some(fps) => format!("{fps} FPS"),
                None => "-- FPS".to_string(),
            })?;
            builder.finish_element()?;
        }

        builder.finish_element()?;

        builder.start_element();
        builder.bg(0x363636FF)?;
        builder.padding(10)?;
        builder.width(WINDOW_WIDTH)?;
        builder.height(40)?;
        let enter_tx = action_tx.clone();
        let on_input_state = state.clone();
        builder.typeable(Typeable {
            text: state.borrow().url.clone(),
            color: 0xFF_FF_FF_FF,
            on_input: Some(Box::new(move |typeable: &Typeable| {
                on_input_state.borrow_mut().url = typeable.text.clone();
            })),
            on_enter: Some(Box::new(move |typeable: &Typeable| {
                let _ = enter_tx.send(BrowserAction::Navigate(typeable.text.clone()));
            })),
        })?;
        builder.finish_element()?;

        builder.finish_element()?;

        Ok(())
    }

    fn get_header_buffer(
        &self,
        url: &String,
        action_tx: Sender<BrowserAction>,
    ) -> Result<ui::UiRuntime<HeaderState>> {
        let state = HeaderState {
            url: url.clone(),
            fps: None,
        };
        let mut runtime =
            UiRuntime::new_empty(WINDOW_WIDTH, HEADER_HEIGHT, action_tx.clone(), state)?;
        self.build_header(&mut runtime.builder, &runtime.state, action_tx)?;
        runtime.rerender()?;
        Ok(runtime)
    }

    pub fn open_tab(
        &self,
        url: String,
        hover_debugging: bool,
        tab_idx: usize,
    ) -> Result<TabHandle> {
        let (tx, rx) = std::sync::mpsc::channel();
        let handle = TabHandle {
            tx: tx.clone(),
            url: url.clone(),
        };
        let proxy = self.event_loop_proxy.clone();
        let tab_window = Some(self.window.clone());
        std::thread::spawn(move || {
            let mut tab = Frame::new(
                url,
                hover_debugging,
                PhysicalSize {
                    width: WINDOW_WIDTH,
                    height: WINDOW_HEIGHT - HEADER_HEIGHT,
                },
            );
            tab.window = tab_window;
            match tab.open() {
                Ok(params) => {
                    let window_proxy = RendererProxy::WindowLoop { proxy, tab_idx };
                    let frame_proxy = RendererProxy::FrameLoop(tx);
                    tab.set_up_without_event_loop(params, frame_proxy).unwrap();
                    tab.start_main_loop(window_proxy, rx);
                }
                Err(err) => eprintln!("Failed to open frame due to {}", err),
            };
        });
        Ok(handle)
    }

    fn poll_header_events(
        &mut self,
        header: &mut UiRuntime<HeaderState>,
        window: &Arc<Window>,
        header_comms_rx: &Receiver<BrowserAction>,
        hover_debugging: bool,
    ) {
        while let Ok(action) = header_comms_rx.try_recv() {
            match action {
                BrowserAction::OpenTab(url) => {
                    match self.open_tab(url.clone(), hover_debugging, self.tabs.len()) {
                        Ok(handle) => {
                            self.tabs.push(handle);
                            self.current_tab_idx = self.tabs.len() - 1;
                            header.state.borrow_mut().url = self.current_tab().url.clone();
                            let comms_tx = header.builder.comms_tx.clone();
                            self.build_header(&mut header.builder, &header.state, comms_tx)
                                .unwrap();
                            match header.rerender() {
                                Ok(_) => {
                                    window.request_redraw();
                                }
                                Err(err) => {
                                    eprintln!("Failed to render header: {err:?}");
                                }
                            }
                        }
                        Err(err) => {
                            eprintln!("Failed to open tab: {err:?}")
                        }
                    }
                }
                BrowserAction::SelectTab(tab_idx) => {
                    self.current_tab_idx = tab_idx;
                    header.state.borrow_mut().url = self.current_tab().url.clone();
                    let comms_tx = header.builder.comms_tx.clone();
                    self.build_header(&mut header.builder, &header.state, comms_tx)
                        .unwrap();
                    match header.rerender() {
                        Ok(_) => {
                            window.request_redraw();
                        }
                        Err(err) => {
                            eprintln!("Failed to render header: {err:?}");
                        }
                    }
                }
                BrowserAction::Rerender => {
                    let comms_tx = header.builder.comms_tx.clone();
                    self.build_header(&mut header.builder, &header.state, comms_tx)
                        .unwrap();
                    match header.rerender() {
                        Ok(_) => {
                            window.request_redraw();
                        }
                        Err(err) => {
                            eprintln!("Failed to render header: {err:?}");
                        }
                    };
                }
                BrowserAction::Navigate(text) => {
                    let Ok(url) = ReqwestUrl::parse(&text) else {
                        return;
                    };
                    let url_text = url.to_string();
                    if let Some(tab) = self.tabs.get_mut(self.current_tab_idx) {
                        tab.url = url_text.clone();
                    }
                    header.state.borrow_mut().url = url_text;
                    let _ =
                        self.current_tab()
                            .tx
                            .send(FrameCommand::UserEvent(UserEvent::Navigate((
                                UserNavigateUrl::Form(FormNavigation {
                                    url,
                                    method: FormMethod::Get,
                                    body: None,
                                }),
                                true,
                            ))));
                }
            }
        }
    }

    pub fn open(url: String, hover_debugging: bool, show_fps_counter: bool) -> Result<()> {
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
        let mut size = window.inner_size();

        let ctx_window = window.clone();
        let ctx = SoftContext::new(ctx_window.display_handle().expect("Display handle"))
            .expect("Softbuffer context failed");
        let surf_window = window.clone();
        let mut surf = Surface::new(&ctx, surf_window.window_handle().expect("Window handle"))
            .expect("Softbuffer surface failed");

        let mut browser = Browser {
            tabs: vec![],
            current_tab_idx: 0,
            window: window.clone(),
            event_loop_proxy: event_loop.create_proxy(),
            fps_counter: show_fps_counter.then(FpsCounter::new),
        };
        let handle = browser.open_tab(url.clone(), hover_debugging, 0)?;
        browser.tabs.push(handle);

        let (browser_action_tx, browser_action_rx) = std::sync::mpsc::channel();
        let mut header = browser.get_header_buffer(&url, browser_action_tx.clone())?;

        event_loop
            .run(move |event, elwt| {
                match event {
                    Event::WindowEvent { event, .. } => match event {
                        WindowEvent::CloseRequested => elwt.exit(),
                        WindowEvent::Resized(new_size) => {
                            size = new_size;
                            let tab_size = PhysicalSize {
                                width: new_size.width,
                                height: new_size.height - HEADER_HEIGHT,
                            };
                            let _ = browser
                                .current_tab()
                                .tx
                                .send(FrameCommand::Resized(tab_size));
                        }
                        WindowEvent::ScaleFactorChanged { .. } => {
                            size = window.inner_size();
                        }
                        WindowEvent::RedrawRequested => {
                            let width = NonZeroU32::new(size.width.max(1)).expect("Non-zero width");
                            let height =
                                NonZeroU32::new(size.height.max(1)).expect("Non-zero height");
                            surf.resize(width, height).expect("Resize failed");
                            let _ = browser.current_tab().tx.send(FrameCommand::Render);
                        }
                        WindowEvent::CursorMoved {
                            device_id: _,
                            position,
                        } => {
                            header.apply_hovering(Position {
                                x: position.x as i32,
                                y: position.y as i32,
                            });
                            let tab_cursor = Position {
                                x: position.x as i32,
                                y: position.y as i32 - HEADER_HEIGHT as i32,
                            };
                            let _ = browser
                                .current_tab()
                                .tx
                                .send(FrameCommand::UserEvent(UserEvent::Hover(tab_cursor)));
                            browser.poll_header_events(
                                &mut header,
                                &window,
                                &browser_action_rx,
                                hover_debugging,
                            );
                        }
                        WindowEvent::MouseInput {
                            device_id: _,
                            state,
                            button,
                        } => match (button, state) {
                            (MouseButton::Left, ElementState::Released) => {
                                header.on_click();
                                let _ = browser
                                    .current_tab()
                                    .tx
                                    .send(FrameCommand::UserEvent(UserEvent::Click));
                                browser.poll_header_events(
                                    &mut header,
                                    &window,
                                    &browser_action_rx,
                                    hover_debugging,
                                );
                            }
                            _ => {}
                        },
                        WindowEvent::MouseWheel {
                            device_id: _,
                            delta,
                            phase: _,
                        } => {
                            match delta {
                                MouseScrollDelta::LineDelta(_, y) => {
                                    let _ = browser.current_tab().tx.send(FrameCommand::UserEvent(
                                        UserEvent::ScrollBy((0., y * 140.)),
                                    ));
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
                                let _ = browser
                                    .current_tab()
                                    .tx
                                    .send(FrameCommand::UserEvent(UserEvent::Keyup(event.clone())));
                                header.on_keyup(event);
                                browser.poll_header_events(
                                    &mut header,
                                    &window,
                                    &browser_action_rx,
                                    hover_debugging,
                                );
                            }
                        }
                        _ => {}
                    },
                    Event::UserEvent(UserEvent::TabUpdated {
                        tab_idx,
                        buffer: tab_buffer,
                    }) if tab_idx == browser.current_tab_idx => {
                        let mut buffer = surf.buffer_mut().expect("Failed to get back buffer");

                        // Apply data to buffer
                        let offset = (HEADER_HEIGHT * size.width) as usize;
                        buffer[offset..offset + tab_buffer.len()].copy_from_slice(&tab_buffer);

                        buffer[0..offset].copy_from_slice(&header.buffer);

                        buffer.present().expect("Failed to present");

                        if let Some(fps) = browser
                            .fps_counter
                            .as_mut()
                            .and_then(FpsCounter::record_present)
                        {
                            header.state.borrow_mut().fps = Some(fps);
                            let comms_tx = header.builder.comms_tx.clone();
                            browser
                                .build_header(&mut header.builder, &header.state, comms_tx)
                                .unwrap();
                            match header.rerender() {
                                Ok(_) => window.request_redraw(),
                                Err(err) => eprintln!("Failed to render header: {err:?}"),
                            }
                        }
                    }
                    Event::UserEvent(UserEvent::TabUpdated { .. }) => {}
                    Event::UserEvent(UserEvent::TabUrlUpdated { tab_idx, url }) => {
                        let is_current = tab_idx == browser.current_tab_idx;
                        if let Some(tab) = browser.tabs.get_mut(tab_idx) {
                            tab.url = url.clone();
                        }

                        if is_current {
                            header.state.borrow_mut().url = url;
                            let comms_tx = header.builder.comms_tx.clone();
                            browser
                                .build_header(&mut header.builder, &header.state, comms_tx)
                                .unwrap();
                            match header.rerender() {
                                Ok(_) => {
                                    window.request_redraw();
                                }
                                Err(err) => {
                                    eprintln!("Failed to render header: {err:?}");
                                }
                            }
                        }
                    }
                    _ => {}
                }
            })
            .context("Event loop failed")?;

        Ok(())
    }
}

fn main() -> Result<()> {
    let args = env::args().collect::<Vec<String>>();
    if args
        .get(1)
        .is_some_and(|arg| arg == "--profile-compute-node-styles")
    {
        return profile_compute_node_styles(&args);
    }

    let hover_debugging = args.iter().any(|arg| arg == "--hover-debugging");
    let show_fps_counter = args.iter().any(|arg| arg == "--fps-counter");
    Browser::open(
        "https://vite.dev/guide/features".to_string(),
        hover_debugging,
        show_fps_counter,
    )?;

    Ok(())
}

fn clear_buffer(buffer: &mut [u32], color: u32) {
    buffer.fill(color);
}

fn build_children_index(nodes: &NodesTable, node_idxs: &Vec<usize>) -> HashMap<usize, Vec<usize>> {
    let mut children_index = HashMap::new();

    for idx in node_idxs.iter() {
        if let Some(parent_idx) = nodes.get(*idx).unwrap().get_parent() {
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
    nodes: &NodesTable,
    layout_node_mapping: &HashMap<usize, usize>,
    layout_table: &HashMap<usize, LayoutBox>,
    node_styles: &HashMap<usize, Style>,
) -> String {
    let mut label = match &nodes.get(node_idx).unwrap() {
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

    let mut attributes = element.attributes.values.iter().collect::<Vec<_>>();
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

fn premul_rgba_buffer_to_bytes(buffer: &[u32]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(buffer.len() * 4);

    for pixel in buffer {
        let [r, g, b, a] = pixel.to_be_bytes();
        bytes.extend_from_slice(&[r, g, b, a]);
    }

    bytes
}

fn text_to_buffer(
    font_handler: &Rc<FontHandler>,
    color: u32,
    text: &String,
    font_px: u32,
    max_width: Option<u32>,
) -> Option<(Pixmap, u32, u32)> {
    text_to_buffer_with_line_height(font_handler, color, text, font_px, max_width, None)
}

fn text_to_buffer_with_line_height(
    font_handler: &Rc<FontHandler>,
    color: u32,
    text: &String,
    font_px: u32,
    max_width: Option<u32>,
    line_height_px: Option<u32>,
) -> Option<(Pixmap, u32, u32)> {
    let scaled_font = font_handler.font.as_scaled(font_px as f32);
    let mut width = 0f32;
    let x = 0;
    let y = 0;
    let mut pen_x: f32 = x as f32;
    let mut pen_y: f32 = y as f32;
    let mut previous = None;

    let mut glyph_positions = vec![];

    let default_line_height = scaled_font.height() + scaled_font.line_gap();
    let line_height = line_height_px
        .map(|line_height| line_height as f32)
        .unwrap_or(default_line_height);
    let leading = ((line_height - default_line_height) / 2.).max(0.);
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
            (glyph_pos.y + leading + scaled_font.ascent() + glyph_pos.glyph.px_bounds().min.y)
                as i32,
            &glyph_pos.glyph,
            color,
        );
    }
    let pixmap = Pixmap::from_vec(
        premul_rgba_buffer_to_bytes(&buffer),
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
            &BorderRadius::new_empty(),
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

pub fn draw_rect_filled(
    buffer: &mut [u32],
    buffer_rgba: bool,
    width: u32,
    height: u32,
    x: i32,
    y: i32,
    w: u32,
    h: u32,
    color: u32,
    border_radius: &BorderRadius,
) {
    draw_rect_filled_clipped(
        buffer,
        buffer_rgba,
        width,
        height,
        x,
        y,
        w,
        h,
        color,
        border_radius,
        PaintClip::viewport(width, height),
    );
}

fn draw_rect_filled_clipped(
    buffer: &mut [u32],
    buffer_rgba: bool,
    width: u32,
    height: u32,
    x: i32,
    y: i32,
    w: u32,
    h: u32,
    color: u32,
    border_radius: &BorderRadius,
    clip: PaintClip,
) {
    if clip.is_empty() {
        return;
    }

    let max_x = i32::try_from(width).unwrap_or(i32::MAX);
    let max_y = i32::try_from(height).unwrap_or(i32::MAX);
    let start_x = x.max(0).max(clip.start_x);
    let start_y = y.max(0).max(clip.start_y);
    let end_x = x.saturating_add_unsigned(w).min(max_x).min(clip.end_x);
    let end_y = y.saturating_add_unsigned(h).min(max_y).min(clip.end_y);
    if start_x >= end_x || start_y >= end_y {
        return;
    }
    let stride = width as usize;

    let has_border_radius = border_radius.top_left > 0
        || border_radius.top_right > 0
        || border_radius.bottom_right > 0
        || border_radius.bottom_left > 0;
    let color_tuple = rgba_to_premul_tuple(color);
    if !has_border_radius {
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
        return;
    }

    let mut mask = vec![true; (w * h) as usize];
    let radius = border_radius.top_left.min(w / 2).min(h / 2) as usize;
    for row in 0..radius {
        for col in 0..radius {
            let dx = radius as i32 - col as i32;
            let dy = radius as i32 - row as i32;

            if dx * dx + dy * dy > (radius * radius) as i32 {
                mask[row * w as usize + col] = false;
            }
        }
    }
    let radius = border_radius.top_right.min(w / 2).min(h / 2) as usize;
    for row in 0..radius {
        for col in 0..radius {
            let dx = col as i32;
            let dy = radius as i32 - row as i32;

            if dx * dx + dy * dy > (radius * radius) as i32 {
                mask[row * w as usize + col + w as usize - radius] = false;
            }
        }
    }
    let radius = border_radius.bottom_left.min(w / 2).min(h / 2) as usize;
    for row in 0..radius {
        for col in 0..radius {
            let dx = radius as i32 - col as i32;
            let dy = row as i32;

            if dx * dx + dy * dy > (radius * radius) as i32 {
                mask[(row + h as usize - radius) * w as usize + col] = false;
            }
        }
    }
    let radius = border_radius.bottom_right.min(w / 2).min(h / 2) as usize;
    for row in 0..radius {
        for col in 0..radius {
            let dx = col as i32;
            let dy = row as i32;

            if dx * dx + dy * dy > (radius * radius) as i32 {
                mask[(row + h as usize - radius) * w as usize + col + w as usize - radius] = false;
            }
        }
    }

    for py in start_y..end_y {
        let row = &mut buffer[py as usize * stride..(py as usize + 1) * stride];
        for px in start_x..end_x {
            let local_x = (px - x) as usize;
            let local_y = (py - y) as usize;
            if !mask[local_y * w as usize + local_x] {
                continue;
            }

            if buffer_rgba {
                row[px as usize] = blend_rgba_with_rgba(row[px as usize], color_tuple);
            } else {
                row[px as usize] = blend_rgb_with_rgba(row[px as usize], color_tuple);
            }
        }
    }
}

pub fn ensure_snapshot_matches(
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

#[cfg(test)]
mod tests {
    use anyhow::{Result, anyhow, bail};
    use std::{
        ops::Add,
        sync::mpsc::{Receiver, RecvTimeoutError},
        time::{Duration, Instant},
    };
    use winit::dpi::PhysicalSize;

    use crate::{
        Frame, FrameCommand, Position, RendererProxy, SizeUnit, UserEvent, ensure_snapshot_matches,
        style::{
            CalcExpression, StyleCalcOperator, StyleSize, parse_calc, split_ignoring_parentheses,
        },
    };

    impl Frame {
        fn wait_for_images_to_load(
            &mut self,
            frame_rx: &Receiver<FrameCommand>,
            timeout: Duration,
        ) -> Result<()> {
            let deadline = Instant::now().add(timeout);
            let mut ignored_events = 0;

            loop {
                let pending_images = self
                    .renderer
                    .as_ref()
                    .map(|renderer| renderer.borrow().pending_image_fetches.len())
                    .unwrap_or_default();
                if pending_images == 0 {
                    return Ok(());
                }

                let remaining = deadline.saturating_duration_since(Instant::now());
                if remaining.is_zero() {
                    bail!(
                        "Timed out waiting for {pending_images} image(s) to load after ignoring {ignored_events} already-applied frame event(s)"
                    );
                }

                match frame_rx.recv_timeout(remaining) {
                    Ok(FrameCommand::UserEvent(UserEvent::ImagesPrefetched(entries))) => {
                        self.renderer
                            .as_ref()
                            .unwrap()
                            .borrow_mut()
                            .finish_image_prefetch(entries);
                        self.layout_dirty = true;
                    }
                    // The headless tests drive JS and DOM updates directly, so their queued
                    // notifications have already been applied and must not be replayed here.
                    Ok(_) => ignored_events += 1,
                    Err(RecvTimeoutError::Timeout) => {
                        bail!(
                            "Timed out waiting for {pending_images} image(s) to load after ignoring {ignored_events} already-applied frame event(s)"
                        )
                    }
                    Err(RecvTimeoutError::Disconnected) => {
                        return Err(anyhow!(
                            "Frame event channel disconnected with {pending_images} image(s) pending"
                        ));
                    }
                }
            }
        }

        fn render_for_snapshot(
            &mut self,
            frame_rx: &Receiver<FrameCommand>,
            buffer: &mut [u32],
            width: u32,
            height: u32,
            timeout: Duration,
        ) -> Result<()> {
            // The initial layout discovers image URLs and starts their asynchronous fetches.
            self.render_into(buffer, width, height, true);
            self.wait_for_images_to_load(frame_rx, timeout)?;
            self.render_into(buffer, width, height, true);
            Ok(())
        }
    }

    #[test]
    fn renders_google() -> Result<()> {
        let (tx, rx) = std::sync::mpsc::channel();
        let mut frame = Frame::new(
            "https://www.google.com".to_string(),
            false,
            PhysicalSize::new(1920, 1080),
        );
        let params = frame.open()?;
        frame.set_up_without_event_loop(params, RendererProxy::FrameLoop(tx))?;
        frame.run_js()?;
        frame.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        let mut buffer = vec![0; 1920 * 1080];
        frame.render_for_snapshot(&rx, &mut buffer, 1920, 1080, Duration::from_secs(5))?;
        frame.apply_hovering(&Position { x: 864, y: 770 });
        frame.on_click()?;
        frame.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        frame.render_for_snapshot(&rx, &mut buffer, 1920, 1080, Duration::from_secs(5))?;
        ensure_snapshot_matches(&buffer, "googlecom", 1920, 1080)
    }

    #[test]
    fn renders_swapped_com() -> Result<()> {
        let (tx, rx) = std::sync::mpsc::channel();
        let mut frame = Frame::new(
            "https://widget.swapped.com/".to_string(),
            false,
            PhysicalSize::new(1920, 1080),
        );
        let params = frame.open()?;
        frame.set_up_without_event_loop(params, RendererProxy::FrameLoop(tx))?;
        frame.run_js()?;
        let pump_limit = Duration::from_secs(10);
        let pump_start = Instant::now();
        frame.pump_with_limit(Instant::now().add(pump_limit))?;
        println!(
            "renders_swapped_com pump={}ms limit={}ms",
            pump_start.elapsed().as_millis(),
            pump_limit.as_millis()
        );
        let mut buffer = vec![0; 1920 * 1080];
        let render_start = Instant::now();
        frame.render_into(&mut buffer, 1920, 1080, true);
        println!(
            "renders_swapped_com render_into_cold={}us",
            render_start.elapsed().as_micros()
        );
        frame.wait_for_images_to_load(&rx, Duration::from_secs(5))?;

        const HOT_RENDER_RUNS: usize = 100;
        let mut hot_render_times = Vec::with_capacity(HOT_RENDER_RUNS);
        for _ in 0..HOT_RENDER_RUNS {
            let render_start = Instant::now();
            frame.render_into(&mut buffer, 1920, 1080, true);
            let elapsed = render_start.elapsed().as_micros();
            hot_render_times.push(elapsed);
        }
        let hot_render_mean =
            hot_render_times.iter().sum::<u128>() / hot_render_times.len() as u128;
        let hot_render_min = hot_render_times.iter().min().copied().unwrap_or_default();
        let hot_render_max = hot_render_times.iter().max().copied().unwrap_or_default();
        println!(
            "renders_swapped_com render_into_hot_runs={} mean={}us min={}us max={}us",
            hot_render_times.len(),
            hot_render_mean,
            hot_render_min,
            hot_render_max
        );
        ensure_snapshot_matches(&buffer, "widgetswappedcom", 1920, 1080)
    }

    #[test]
    fn render_vite_dev() -> Result<()> {
        let (tx, rx) = std::sync::mpsc::channel();
        let mut frame = Frame::new(
            "https://vite.dev".to_string(),
            false,
            PhysicalSize::new(1920, 4320),
        );
        let params = frame.open()?;
        frame.set_up_without_event_loop(params, RendererProxy::FrameLoop(tx))?;
        frame.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        let mut buffer = vec![0; 1920 * 4320];
        frame.render_for_snapshot(&rx, &mut buffer, 1920, 4320, Duration::from_secs(5))?;
        ensure_snapshot_matches(&buffer, "vitedev", 1920, 4320)
    }

    #[test]
    fn render_vite_features() -> Result<()> {
        let (tx, rx) = std::sync::mpsc::channel();
        let mut frame = Frame::new(
            "https://vite.dev/guide/features".to_string(),
            false,
            PhysicalSize::new(1920, 1080),
        );
        let params = frame.open()?;
        frame.set_up_without_event_loop(params, RendererProxy::FrameLoop(tx))?;
        frame.run_js()?;
        frame.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        let mut buffer = vec![0; 1920 * 1080];
        frame.render_for_snapshot(&rx, &mut buffer, 1920, 1080, Duration::from_secs(5))?;
        ensure_snapshot_matches(&buffer, "vitefeatures", 1920, 1080)
    }

    #[test]
    fn render_marble_match() -> Result<()> {
        let (tx, rx) = std::sync::mpsc::channel();
        let mut frame = Frame::new(
            "https://marblematch.io".to_string(),
            false,
            PhysicalSize::new(1920, 1080),
        );
        let params = frame.open()?;
        frame.set_up_without_event_loop(params, RendererProxy::FrameLoop(tx))?;
        frame.run_js()?;
        frame.pump_with_limit(Instant::now().add(Duration::from_secs(2)))?;
        let mut buffer = vec![0; 1920 * 1080];
        frame.render_for_snapshot(&rx, &mut buffer, 1920, 1080, Duration::from_secs(5))?;
        ensure_snapshot_matches(&buffer, "marblematchio", 1920, 1080)
    }

    #[test]
    fn render_time_tracker() -> Result<()> {
        let (tx, rx) = std::sync::mpsc::channel();
        let mut frame = Frame::new(
            "https://pixel-time-tracker.pages.dev/".to_string(),
            false,
            PhysicalSize::new(1920, 1080),
        );
        let params = frame.open()?;
        frame.set_up_without_event_loop(params, RendererProxy::FrameLoop(tx))?;
        frame.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        let mut buffer = vec![0; 1920 * 1080];
        frame.render_for_snapshot(&rx, &mut buffer, 1920, 1080, Duration::from_secs(5))?;
        ensure_snapshot_matches(&buffer, "pixeltimetracker", 1920, 1080)
    }

    #[test]
    fn render_slack() -> Result<()> {
        let (tx, rx) = std::sync::mpsc::channel();
        let mut frame = Frame::new(
            "https://slack.com/".to_string(),
            false,
            PhysicalSize::new(1920, 8640),
        );
        let params = frame.open()?;
        frame.set_up_without_event_loop(params, RendererProxy::FrameLoop(tx))?;
        frame.run_js()?;
        frame.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        let mut buffer = vec![0; 1920 * 8640];
        frame.render_for_snapshot(&rx, &mut buffer, 1920, 8640, Duration::from_secs(5))?;
        ensure_snapshot_matches(&buffer, "slackcom", 1920, 8640)
    }

    #[test]
    fn render_nodejs() -> Result<()> {
        let (tx, rx) = std::sync::mpsc::channel();
        let mut frame = Frame::new(
            "https://nodejs.org/en".to_string(),
            false,
            PhysicalSize::new(1920, 2160),
        );
        let params = frame.open()?;
        frame.set_up_without_event_loop(params, RendererProxy::FrameLoop(tx))?;
        frame.run_js()?;
        frame.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        let mut buffer = vec![0; 1920 * 2160];
        frame.render_for_snapshot(&rx, &mut buffer, 1920, 2160, Duration::from_secs(5))?;
        ensure_snapshot_matches(&buffer, "nodejsorg", 1920, 2160)
    }

    #[test]
    fn render_mingolf() -> Result<()> {
        let (tx, rx) = std::sync::mpsc::channel();
        let mut frame = Frame::new(
            "https://mingolf.golf.se/".to_string(),
            false,
            PhysicalSize::new(1920, 2160),
        );
        let params = frame.open()?;
        frame.set_up_without_event_loop(params, RendererProxy::FrameLoop(tx))?;
        frame.run_js()?;
        frame.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        let mut buffer = vec![0; 1920 * 2160];
        frame.render_for_snapshot(&rx, &mut buffer, 1920, 2160, Duration::from_secs(5))?;
        frame.apply_hovering(&Position { x: 1140, y: 1850 });
        frame.on_click()?;
        frame.pump_with_limit(Instant::now().add(Duration::from_secs(5)))?;
        frame.render_for_snapshot(&rx, &mut buffer, 1920, 2160, Duration::from_secs(5))?;
        ensure_snapshot_matches(&buffer, "mingolfgolfse", 1920, 2160)
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
        assert_eq!(
            split_ignoring_parentheses("input:checked+label".into(), ' ', &['>', '~', '+']),
            vec!["input:checked", "+", "label"]
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

    #[test]
    fn solve_calc_single() -> Result<()> {
        let StyleSize::Calc(calc) = parse_calc("2px")? else {
            unreachable!();
        };

        assert_eq!(
            super::solve_calc(
                &calc,
                16,
                None,
                None,
                &PhysicalSize::new(100, 100),
                &SizeUnit::Px
            ),
            Some(2)
        );
        Ok(())
    }

    #[test]
    fn solve_calc_uses_order_of_operations() -> Result<()> {
        let StyleSize::Calc(calc) = parse_calc("2px + 3px * 4px")? else {
            unreachable!();
        };

        assert_eq!(
            super::solve_calc(
                &calc,
                16,
                None,
                None,
                &PhysicalSize::new(100, 100),
                &SizeUnit::Px
            ),
            Some(14)
        );
        Ok(())
    }
}
