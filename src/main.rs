mod css;
mod parser;
mod style;
mod loader;

use deno_web::{BlobStore, InMemoryBroadcastChannel};
use parser::{Element, HtmlParser, Node};
use style::{
    Style, StyleBackground, StyleDisplay, StyleFlexDirection, StyleJustifyContent, StylePosition,
    StyleSize, get_base_style, parse_style,
};

use std::cell::{RefCell};
use std::collections::HashMap;
use std::num::NonZeroU32;
use std::rc::Rc;
use std::sync::Arc;
use std::{env, fs, u32};

use anyhow::{Context, Result, anyhow};
use bytes::{Bytes};
use deno_core::{JsRuntime, OpState, extension, op2};
use deno_core::error::JsError;
use raw_window_handle::{HasDisplayHandle, HasWindowHandle};
use reqwest::{Url as ReqwestUrl};
use resvg::{tiny_skia, usvg};
use softbuffer::{Context as SoftContext, Surface};
use winit::dpi::PhysicalSize;
use winit::event::{ElementState, Event, MouseButton, WindowEvent};
use winit::event_loop::{EventLoopBuilder, EventLoopProxy};
use winit::window::{Window, WindowBuilder};

use crate::css::{ClassName, CssParser, Node as CssNode, selector_to_parts};
use crate::loader::HttpModuleLoader;
use crate::style::{CalcExpression, StyleAlign, StyleCalcOperator, class_matches_element};

const FONT_WIDTH: u32 = 5;
const FONT_HEIGHT: u32 = 7;
const WINDOW_WIDTH: u32 = 1920;
const WINDOW_HEIGHT: u32 = 1080;

#[derive(Debug, Clone)]
struct Rect {
    x: i32,
    y: i32,
    width: u32,
    height: u32,
    background: StyleBackground,
    color: StyleBackground,
    margin_bottom: i32,
    margin_right: i32,
    font_size: Option<u32>,
}

#[derive(Debug, Clone)]
enum LayoutKind {
    Element,
    PixMap(tiny_skia::Pixmap),
    Text(String),
}

#[derive(Debug, Clone)]
struct LayoutBox {
    rect: Rect,
    kind: LayoutKind,
    children: Vec<usize>,
    node_idx: usize,
}

#[derive(Debug, Clone)]
enum RequestCacheEntry {
    PngData(Bytes),
    SvgData(String),
    CssData(String),
    Unsupported,
}

#[derive(Debug)]
struct Renderer {
    node_idx_cursor: usize,
    pub nodes_idxs: Vec<usize>,
    pub nodes: HashMap<usize, parser::Node>,
    children_index: HashMap<usize, Vec<usize>>,
    root_indices: Vec<usize>,
    node_styles: HashMap<usize, Style>,
    layout_table: HashMap<usize, LayoutBox>,
    node_layout_mapping: HashMap<usize, usize>,
    containing_nodes: HashMap<usize, ContainingNode>,
    request_cache: HashMap<ReqwestUrl, RequestCacheEntry>,
    rendered_nodes_ordered: Vec<usize>,
    pub hovering: Option<usize>,
    tokio: Rc<RefCell<tokio::runtime::Runtime>>,
    resolved_font_sizes: HashMap<usize, u32>,
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
    min_height: Option<u32>,
    max_height: Option<u32>,
    min_width: Option<u32>,
    max_width: Option<u32>,
}

impl ContainerSizes {
    pub fn clamp_width(&self, value: u32) -> u32 {
        value
            .min(self.max_width.unwrap_or(u32::MAX))
            .max(self.min_width.unwrap_or(u32::MIN))
    }

    pub fn compute_actual_container_width(&self, used_width: u32) -> u32 {
        self.container_width_non_filling.unwrap_or(self.clamp_width(used_width))
    }
}

impl ContainingNode {
    pub fn layout_waiters(&mut self, renderer: &mut Renderer, height: u32, width: u32, children: &mut Vec<usize>) -> Result<()> {
        for waiter in &self.waiters {
            let style = renderer.node_styles.get(&waiter.node_idx).unwrap().clone();
            let mut forced_size = OptionalSize { height: None, width: None };
            let resolved_parent_font_size = renderer.get_parent_font_size(waiter.node_idx);
            let font_size = get_specified_size(resolved_parent_font_size, &style.font_size, resolved_parent_font_size, None).with_context(|| "Failed to get specific size")? as u32;
            renderer.resolved_font_sizes.insert(waiter.node_idx, font_size as u32);
            let top = get_specified_size(font_size, &style.top, waiter.available_size.height, None);
            let right = get_specified_size(font_size, &style.right, waiter.available_size.width, None);
            let bottom = get_specified_size(font_size, &style.bottom, waiter.available_size.height, None);
            let left = get_specified_size(font_size, &style.left, waiter.available_size.width, None);

            let margin_right = get_specified_size(font_size, &style.margin_right, waiter.available_size.width, None);
            let margin_left = get_specified_size(font_size, &style.margin_left, waiter.available_size.width, None);

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
    available_size: u32,
    auto_size: Option<i32>,
) -> Option<i32> {
    match value {
        StyleSize::Auto => auto_size,
        StyleSize::Percent(percentage) => {
            let computed = available_size as f32 * (*percentage as f32 / 100f32);
            Some(computed as i32)
        }
        StyleSize::Px(px) => Some(*px),
        // TODO: Make this handle order of operations
        StyleSize::Calc(calc) => {
            let mut value = match &calc[0] {
                CalcExpression::Size(size) => get_specified_size(font_size, &size, available_size, auto_size)?,
                _ => panic!("Expected first calc expression to be value"),
            };
            let mut exp_idx = 1;
            while exp_idx < calc.len() {
                let loop_operator = match &calc[exp_idx] {
                    CalcExpression::Operator(operator) => operator,
                    _ => panic!("Expected calc expression to be operator"),
                };
                let loop_value = match &calc[exp_idx + 1] {
                    CalcExpression::Size(size) => get_specified_size(font_size, &size, available_size, auto_size)?,
                    _ => panic!("Expected calc expression to be size"),
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
            Some(*em * font_size as i32)
        },
    }
}

fn rasterize_svg(svg_data: &[u8], target_w: u32, target_h: u32, style: &Style) -> Result<tiny_skia::Pixmap> {
    let mut opt = usvg::Options::default();
    let color_hex = match style.color {
        StyleBackground::Hex(hex) => hex,
        _ => 0x00_FF_FF_FF,
    };
    opt.style_sheet = Some(format!("svg {{ color: #{:06X}; fill: currentColor }}", color_hex).into());

    let tree = usvg::Tree::from_data(&svg_data, &opt)?;
    let svg_size = tree.size().to_int_size();

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

    Ok(pixmap)
}

fn rasterize_png(bytes: &[u8], target_w: u32, target_h: u32) -> Result<tiny_skia::Pixmap> {
    let src = tiny_skia::Pixmap::decode_png(bytes)?;
    if src.width() == target_w && src.height() == target_h {
        return Ok(src);
    }

    let mut dst = tiny_skia::Pixmap::new(target_w.max(1), target_h.max(1))
        .context("failed to allocate png pixmap")?;

    dst.as_mut().draw_pixmap(
        0,
        0,
        src.as_ref(),
        &tiny_skia::PixmapPaint::default(),
        tiny_skia::Transform::from_row(
            target_w as f32 / src.width() as f32,
            0.0,
            0.0,
            target_h as f32 / src.height() as f32,
            0.0,
            0.0,
        ),
        None,
    );

    Ok(dst)
}

fn resolve_url(href: &str, base_url: Option<&ReqwestUrl>) -> Result<ReqwestUrl> {
    if let Ok(url) = ReqwestUrl::parse(href) {
        return Ok(url);
    }

    let base_url = base_url.context(format!("relative URL without base: {href}"))?;
    Ok(base_url.join(href)?)
}

async fn fetch_link_strings(request_cache: &mut HashMap<ReqwestUrl, RequestCacheEntry>, links: &Vec<&String>, map_fn: impl Fn(String) -> RequestCacheEntry) -> Result<Vec<String>> {
    let mut results = vec![];
    for link in links.iter() {
        // TODO: Don't hardcode this
        let base = ReqwestUrl::parse("http://localhost:5173/")?;
        let url = resolve_url(link, Some(&base))?;

        if let Some(cache) = request_cache.get(&url) {
            results.push(cache.clone());
        } else {
            let resp = reqwest::get(url.clone()).await?.text().await?;
            let cache_entry = map_fn(resp);
            request_cache.insert(url, cache_entry.clone());

            results.push(cache_entry);
        }
    }
    let strings = results.iter().map(|r| match r {
        RequestCacheEntry::CssData(data) => Some(data.clone()),
        _ => None,
    }).flatten().collect::<Vec<String>>();

    Ok(strings)
}

fn combine_css_nodes(tokio: &Rc<RefCell<tokio::runtime::Runtime>>, request_cache: &mut HashMap<ReqwestUrl, RequestCacheEntry>, nodes: &HashMap<usize, Node>, node_idxs: &Vec<usize>, children_index: &HashMap<usize, Vec<usize>>) -> Result<Vec<String>> {
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
                        .is_some_and(|v| v == "stylesheet")
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
        tokio.borrow_mut().block_on(fetch_link_strings(request_cache, &stylesheet_links, |str| RequestCacheEntry::CssData(str)))?
    } else {
        vec![]
    };
    println!("Fetched {} CSS nodes", fetched_nodes.len());

    css_nodes.append(&mut fetched_nodes);

    Ok(css_nodes)
}

// TODO: Make the scale a float so that it can be more nuanced
fn text_scale_from_font_px(font_px: u32) -> u32 {
    (font_px / 6).max(1)
}

fn compute_node_style(
    node_styles: &mut HashMap<usize, Style>,
    nodes: &HashMap<usize, Node>,
    node_idx: usize,
    root_indices: &[usize],
    children_index: &HashMap<usize, Vec<usize>>,
    css_nodes: &Vec<CssNode>,
    parent_partial_matches: &HashMap<(usize, usize), usize>,
    parent_style: Option<Style>,
    parent_variables: &HashMap<String, String>,
) {
    let mut partial_matches = parent_partial_matches.clone();
    let mut variables = parent_variables.clone();
    let style = match &nodes.get(&node_idx).unwrap() {
        Node::Element(element) => parse_style(element, css_nodes, parent_style, &mut variables, &mut partial_matches).unwrap(),
        node => get_base_style(node, parent_style),
    };

    node_styles.insert(node_idx, style.clone());

    for child_idx in children_index.get(&node_idx).unwrap().iter() {
        compute_node_style(
            node_styles,
            nodes,
            *child_idx,
            root_indices,
            children_index,
            css_nodes,
            &partial_matches,
            Some(style.clone()),
            &variables,
        );
    }
}

fn parse_css_nodes(css_nodes: &Vec<String>) -> Result<Vec<CssNode>> {
    let joined = css_nodes.join("\n");
    let mut parser = CssParser::new(&joined.as_str());
    parser.parse()?;

    Ok(parser.nodes)
}

fn compute_node_styles(
    tokio: &Rc<RefCell<tokio::runtime::Runtime>>,
    request_cache: &mut HashMap<ReqwestUrl, RequestCacheEntry>,
    nodes: &HashMap<usize, Node>,
    node_idxs: &Vec<usize>,
    children_index: &HashMap<usize, Vec<usize>>,
    root_indices: &[usize],
) -> HashMap<usize, Style> {
    let css_nodes = combine_css_nodes(tokio, request_cache, nodes, node_idxs, &children_index).unwrap();
    let parsed_css_nodes = parse_css_nodes(&css_nodes).unwrap();
    let partial_matches: HashMap<(usize, usize), usize> = HashMap::new();

    let mut node_styles = HashMap::new();
    for node_idx in root_indices.iter() {
        compute_node_style(
            &mut node_styles,
            nodes,
            *node_idx,
            &root_indices,
            &children_index,
            &parsed_css_nodes,
            &partial_matches,
            None,
            &HashMap::new(),
        );
    }
    node_styles
}

#[derive(Debug, Clone)]
enum UserEvent {
    DomUpdated,
}

#[derive(Debug, Clone)]
struct JsHostState {
    renderer: Rc<RefCell<Renderer>>,
    proxy: EventLoopProxy<UserEvent>
}

#[op2]
#[serde]
fn op_append_child(state: &mut OpState, #[number] node_idx: usize, #[string] tag: String, #[serde] attrs: HashMap<String, String>, #[string] inner_html: Option<String>) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    host.renderer.borrow_mut().append_child(node_idx, tag, attrs, inner_html)?;
    host.proxy.send_event(UserEvent::DomUpdated).unwrap();
    Ok(())
}

#[op2]
fn op_get_element_by_id(state: &mut OpState, #[string] id: String) -> Result<Option<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let node_idx = renderer.nodes_idxs.iter().find(|idx| match renderer.nodes.get(*idx).unwrap() {
        Node::Element(element) => element.attributes.get("id").is_some_and(|v| *v == id),
        Node::Text(_) => false,
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
            Node::Text(_) => false,
        })
        .map(|idx| (*idx, renderer.nodes.get(idx).unwrap().clone()))
        .collect();
    Ok(nodes)
}

#[op2]
fn op_query_selector(state: &mut OpState, #[string] selector: String) -> Result<Option<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let nodes: Vec<(usize, &Node)> = query_selector_all(&renderer.nodes_idxs, &renderer.nodes, selector);
    let node = nodes.first();
    let owned = node.cloned().map(|(idx, node)| (idx, node.clone()));
    Ok(owned)
}

#[op2]
fn op_query_selector_all(state: &mut OpState, #[string] selector: String) -> Result<Vec<(usize, Node)>, JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let renderer = host.renderer.borrow();
    let nodes: Vec<(usize, &Node)> = query_selector_all(&renderer.nodes_idxs, &renderer.nodes, selector);
    let owned: Vec<(usize, Node)> = nodes.into_iter().map(|(idx, node)| (idx, node.clone())).collect();
    Ok(owned)
}

#[op2(fast)]
fn op_set_inner_html(state: &mut OpState, #[number] node_idx: usize, #[string] html: String) -> Result<(), JsError> {
    let host = state.borrow_mut::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let children = renderer.children_index.get(&node_idx).unwrap_or(&vec![]).clone();
    for child in children {
        renderer.remove_node(child, true);
    }
    renderer.create_children_from_html(node_idx, &html);
    host.proxy.send_event(UserEvent::DomUpdated).unwrap();
    Ok(())
}

// This should walk the tree to be fully correct I think
fn query_selector_all<'a>(node_idxs: &Vec<usize>, nodes_table: &'a HashMap<usize, Node>, selector: String) -> Vec<(usize, &'a Node)> {
    let class = ClassName {
        name: vec![selector.clone()],
        name_parts: vec![selector_to_parts(&selector)],
        parent: None,
    };
    let mut partial_matches = HashMap::new();
    let filtered: Vec<(usize, &Node)> = node_idxs
        .iter()
        .filter(|idx| match nodes_table.get(*idx).unwrap() {
            Node::Element(element) => {
                let result = class_matches_element(element, &class, 0, &mut partial_matches);
                result.target_matched
            },
            _ => false,
        })
        .map(|idx| (*idx, nodes_table.get(idx).unwrap()))
        .collect();
    filtered
}

extension!(
  browser,
  ops = [
    op_append_child,
    op_get_element_by_id,
    op_get_elements_by_tag_name,
    op_query_selector,
    op_query_selector_all,
    op_set_inner_html,
  ],
  esm_entry_point = "ext:browser/runtime.js",
  esm = [dir "src", "runtime.js"],
);

#[derive(Debug)]
pub enum ScriptType {
    Link(String),
    Code(String),
}

impl Renderer {
    fn new(tokio: Rc<RefCell<tokio::runtime::Runtime>>, nodes: Vec<Node>) -> Self {
        let root_indices: Vec<usize> = nodes
            .iter()
            .enumerate()
            .filter_map(|(idx, node)| node.get_parent().is_none().then_some(idx))
            .collect();

        let mut request_cache = HashMap::new();

        let layout_table = HashMap::new();
        let containing_nodes = HashMap::new();
        let node_layout_mapping = HashMap::new();

        let rendered_nodes_ordered = vec![];
        let hovering = None;

        let resolved_font_sizes = HashMap::new();

        let nodes_idxs: Vec<usize> = nodes.iter().enumerate().map(|(idx, _)| idx).collect();
        let nodes_table: HashMap<usize, Node> = nodes.into_iter().enumerate().collect();

        let children_index = build_children_index(&nodes_table, &nodes_idxs);
        let node_styles = compute_node_styles(&tokio, &mut request_cache, &nodes_table, &nodes_idxs, &children_index, &root_indices);

        let node_idx_cursor = nodes_idxs.len();

        Self {
            node_idx_cursor,
            nodes_idxs,
            nodes: nodes_table,
            children_index,
            root_indices,
            node_styles,
            layout_table,
            node_layout_mapping,
            containing_nodes,
            request_cache,
            rendered_nodes_ordered,
            hovering,
            tokio,
            resolved_font_sizes,
        }
    }

    pub fn get_scripts(&mut self) -> Vec<ScriptType> {
        let scripts: Vec<ScriptType> = self.nodes_idxs
            .iter()
            .filter(|node_idx| match self.nodes.get(*node_idx).unwrap() {
                Node::Element(element) => element.tag == "script",
                _ => false,
            })
            .map(|idx| -> Option<ScriptType> {
                let src = match self.nodes.get(idx).unwrap() {
                    Node::Element(element) => element.attributes.get("src"),
                    _ => None
                };
                if let Some(src) = src {
                    return Some(ScriptType::Link(src.to_string()));
                }

                let children = &self.children_index.get(idx).unwrap();
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
                    Node::Text(element) => Some(ScriptType::Code(element.text.clone())),
                };

                text
            })
            .flatten()
            .collect();

        scripts
    }


    fn render_into(&mut self, buffer: &mut [u32], width: u32, height: u32) {
        if width == 0 || height == 0 {
            return;
        }

        clear_buffer(buffer, 0xFF_FF_FF_FF);

        let layout_roots = self.build_layout(width, height);
        self.rendered_nodes_ordered.clear();
        for layout_box_idx in layout_roots {
            self.paint_layout_box(layout_box_idx, buffer, width, height);
        }
    }

    fn move_entire_box(&mut self, layout_box_idx: usize, x: i32, y: i32) {
        let layout_box = self.layout_table.get_mut(&layout_box_idx).unwrap();
        layout_box.rect.x += x;
        layout_box.rect.y += y;
        for child in layout_box.children.clone() {
            self.move_entire_box(child, x, y);
        }
    }

    fn build_layout(&mut self, width: u32, height: u32) -> Vec<usize> {
        let mut position = Position { x: 0, y: 0 };
        let mut layout_roots = Vec::new();

        self.node_layout_mapping.clear();

        for root_idx in self.root_indices.clone() {
            // Create initial containing node
            self.containing_nodes.insert(root_idx, ContainingNode {
                node_idx: root_idx,
                waiters: vec![],
            });
            let containing_node_idx = root_idx;

            if let Some(layout_box_idx) = self.layout_node(
                root_idx,
                position,
                Size { width, height },
                OptionalSize {
                    height: None,
                    width: None,
                },
                containing_node_idx,
                true,
            ) {
                let layout_box = self.layout_table.get(&layout_box_idx).unwrap();
                position.y += layout_box.rect.height as i32 + layout_box.rect.margin_bottom;
                layout_roots.push(layout_box_idx);
            }
        }

        layout_roots
    }

    fn inject_css_variables_into_str(&self, str: &mut String, variables: &HashMap<String, String>) {
        for (variable, value) in variables.iter() {
            *str = str.replace(&format!("var({})", variable), value);
        }
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
                for child_idx in self.children_index.get(&node_idx).unwrap() {
                    str += &self.get_element_html(*child_idx);
                }
                str += "</";
                str += &element.tag;
                str += ">";
            }
        }
        str
    }

    async fn get_img_src_data(&mut self, src: &str) -> Result<RequestCacheEntry> {
        let base = ReqwestUrl::parse("http://localhost:5173/")?;
        let url = resolve_url(src, Some(&base))?;
        let src_extension = if src.ends_with(".png") {
            Some("image/png")
        } else if src.ends_with(".svg") {
            Some("image/svg")
        } else {
            None
        };
        if let Some(cache) = self.request_cache.get(&url) {
            match cache {
                RequestCacheEntry::Unsupported => Err(anyhow!("Unsupported image")),
                v => Ok(v.clone())
            }
        } else {
            println!("Fetching img src: {}", url);
            let resp = reqwest::get(url.clone()).await?;
            let content_type = resp
                .headers()
                .get("content-type")
                .and_then(|v| v.to_str().ok())
                // TODO: Consider whether this is a sane production default
                .or(src_extension)
                .with_context(|| "Failed to get content-type for image")?;
            let cache_entry = match content_type {
                "image/png" => Ok(RequestCacheEntry::PngData(resp.bytes().await?)),
                "image/svg" => Ok(RequestCacheEntry::SvgData(resp.text().await?)),
                _ => Err(anyhow!("Failed to handle image content-type")),
            };
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
    ) -> usize {
        // This effectively acts as a vector right now
        let node_idx = layout_box.node_idx;
        let idx = self.layout_table.len() + 1;
        self.layout_table.insert(idx, layout_box);
        // Only store first team as that'll be the highest parent
        if !self.node_layout_mapping.contains_key(&node_idx) {
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
        mut cursor: Position,
        available_size: Size,
        forced_size: OptionalSize,
        containing_node_idx: usize,
        allow_fill: bool,
    ) -> Option<usize> {
        let style = self.node_styles.get(&node_idx).unwrap().clone();

        let resolved_parent_font_size = self.get_parent_font_size(node_idx);
        let resolved_font_size = get_specified_size(resolved_parent_font_size, &style.font_size, resolved_parent_font_size, None)?;
        self.resolved_font_sizes.insert(node_idx, resolved_font_size as u32);

        let (margin_left_size, margin_right_size, margin_top_size, margin_bottom_size) =
            self.get_margins(node_idx, &style, available_size);

        cursor.x += margin_left_size as i32;
        cursor.y += margin_top_size as i32;

        match self.nodes.get(&node_idx).unwrap().clone() {
            Node::Text(text) => {
                let text = collapse_whitespace(&text.text).unwrap();
                let (padding_left_size, padding_right_size, padding_top_size, padding_bottom_size) =
                    self.get_paddings(node_idx, &style, available_size);
                let font_scale = text_scale_from_font_px(resolved_font_size as u32);
                let width = forced_size.width.unwrap_or(
                    measure_text(&text, font_scale)
                        + padding_left_size as u32
                        + padding_right_size as u32,
                );
                let height = forced_size.height.unwrap_or(
                    FONT_HEIGHT * font_scale + padding_top_size as u32 + padding_bottom_size as u32,
                );

                Some(self.register_layout_box(LayoutBox {
                    rect: Rect {
                        x: cursor.x,
                        y: cursor.y,
                        width,
                        height,
                        background: StyleBackground::Transparent,
                        color: style.color,
                        margin_bottom: margin_bottom_size,
                        margin_right: margin_right_size,
                        font_size: Some(resolved_font_size as u32),
                    },
                    kind: LayoutKind::Text(text),
                    children: vec![],
                    node_idx,
                }))
            }
            Node::Element(element) => {
                if element.tag == "svg" || element.tag == "img" {
                    let style = self.node_styles.get(&node_idx).unwrap().clone();
                    let container_size = self.get_container_sizes(node_idx, &OptionalSize { height: None, width: None }, &style, &available_size);
                    let pixmap = match element.tag.as_str() {
                        "svg" => {
                            let mut svg_data = self.get_element_html(node_idx);
                            self.inject_css_variables_into_str(&mut svg_data, &style.variables);
                            let pixmap = rasterize_svg(svg_data.as_bytes(), container_size.container_width, container_size.container_height, &style)
                                .expect("Failed to rasterize SVG data");
                            pixmap
                        },
                        "img" => {
                            let src = element.attributes.get("src").unwrap();
                            if src.starts_with("data:") {
                                return None;
                            }
                            let img_data = self.tokio.clone().borrow_mut().block_on(self.get_img_src_data(src)).ok()?;
                            let pixmap = match img_data {
                                RequestCacheEntry::PngData(bytes) => {
                                    rasterize_png(&bytes, container_size.container_width, container_size.container_height).unwrap()
                                },
                                RequestCacheEntry::SvgData(svg_data) => {
                                    self.inject_css_variables_into_str(&mut svg_data.clone(), &style.variables);
                                    rasterize_svg(svg_data.as_bytes(), container_size.container_width, container_size.container_height, &style)
                                        .expect("Failed to rasterize SVG data")
                                },
                                _ => panic!(),
                            };
                            pixmap
                        },
                        _ => panic!(),
                    };

                    Some(self.register_layout_box(LayoutBox {
                        rect: Rect {
                            x: cursor.x,
                            y: cursor.y,
                            width: container_size.container_width,
                            height: container_size.container_height,
                            background: StyleBackground::Transparent,
                            color: StyleBackground::Transparent,
                            margin_bottom: margin_bottom_size,
                            margin_right: margin_right_size,
                            font_size: None,
                        },
                        kind: LayoutKind::PixMap(pixmap),
                        children: vec![],
                        node_idx,
                    }))
                } else {
                    let layout = match style.display {
                        StyleDisplay::Block | StyleDisplay::InlineBlock => self.layout_block(
                            node_idx,
                            cursor,
                            &style,
                            available_size,
                            forced_size,
                            containing_node_idx,
                            allow_fill,
                        ),
                        StyleDisplay::Flex => self.layout_flex(
                            node_idx,
                            cursor,
                            &style,
                            available_size,
                            forced_size,
                            containing_node_idx,
                            allow_fill,
                        ),
                        StyleDisplay::None => None,
                    };

                    if let Some((width, height, children)) = layout {
                        Some(self.register_layout_box(LayoutBox {
                            rect: Rect {
                                x: cursor.x,
                                y: cursor.y,
                                width,
                                height,
                                background: style.background,
                                color: style.color,
                                margin_bottom: margin_bottom_size,
                                margin_right: margin_right_size,
                                font_size: None,
                            },
                            kind: LayoutKind::Element,
                            children,
                            node_idx,
                        }))
                    } else {
                        None
                    }
                }
            }
        }
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

    fn divide_free_space_for_margin(&mut self, children: &Vec<usize>, container_width: i32, free_space_y: u32) {
        let mut rows: Vec<Vec<&usize>> = vec![];
        for child in children {
            let child_style = &self.node_styles.get(&self.layout_to_node_idx(child)).unwrap();
            if child_style.display == StyleDisplay::InlineBlock && rows.len() > 0 {
                let last_row = rows.last_mut().unwrap();
                last_row.push(child);
                continue;
            }
            rows.push(vec![child]);
        }
        let mut free_space_to_give_y = 0;
        if let (Some(first_child), Some(last_child)) = (children.first(), children.last()) {
            let first_child_style = &self.node_styles.get(&self.layout_to_node_idx(first_child)).unwrap();
            let last_child_style = &self.node_styles.get(&self.layout_to_node_idx(last_child)).unwrap();
            free_space_to_give_y = self.get_margin_free_space_to_give(free_space_y, &first_child_style.margin_top, &last_child_style.margin_bottom);
        }
        for row in rows {
            let first_child = row.first().unwrap();
            let last_child = row.last().unwrap();

            let first_child_style = &self.node_styles.get(&self.layout_to_node_idx(*first_child)).unwrap();
            let last_child_style = &self.node_styles.get(&self.layout_to_node_idx(*last_child)).unwrap();

            let mut used_space = 0i32;
            for child in row.iter() {
                let child_box = &self.layout_table.get(child).unwrap();
                used_space += child_box.rect.width as i32;
            }
            let free_space_x = (container_width - used_space).max(0) as u32;

            let mut first_margin = first_child_style.margin_left.clone();
            let mut last_margin = last_child_style.margin_right.clone();
            // If the text-align isn't left, and all children in this row are the same, use that instead of the margin
            if first_child_style.text_align != StyleAlign::Left && row.iter().all(|c| self.node_styles.get(&self.layout_to_node_idx(*c)).unwrap().text_align == first_child_style.text_align) {
                (first_margin, last_margin) = match first_child_style.text_align {
                    StyleAlign::Left => panic!(),
                    StyleAlign::Center => (StyleSize::Auto, StyleSize::Auto),
                    StyleAlign::Right => (StyleSize::Auto, StyleSize::Px(0)),
                };
            }

            let free_space_to_give_x = self.get_margin_free_space_to_give(free_space_x, &first_margin, &last_margin);
            for child in row {
                self.move_entire_box(*child, free_space_to_give_x as i32, free_space_to_give_y as i32);
            }
        }
    }

    fn get_container_sizes(&self, node_idx: usize, forced_size: &OptionalSize, style: &Style, available_size: &Size) -> ContainerSizes {
        let (padding_left_size, padding_right_size, padding_top_size, padding_bottom_size) =
            self.get_paddings(node_idx, style, *available_size);

        let resolved_font_size = self.resolved_font_sizes.get(&node_idx).unwrap();

        let min_height = get_specified_size(*resolved_font_size, &style.min_height, available_size.height, None)
            .and_then(|v| Some(v as u32));
        let max_height = get_specified_size(*resolved_font_size, &style.max_height, available_size.height, None)
            .and_then(|v| Some(v as u32));
        let min_width = get_specified_size(*resolved_font_size, &style.min_width, available_size.width, None)
            .and_then(|v| Some(v as u32));
        let max_width = get_specified_size(*resolved_font_size, &style.max_width, available_size.width, None)
            .and_then(|v| Some(v as u32));

        let specified_width = forced_size.width.or(get_specified_size(
            *resolved_font_size,
            &style.width,
            available_size.width,
            None,
        )
        .and_then(|v| Some(v as u32)));
        let specified_height = forced_size.height.or(get_specified_size(
            *resolved_font_size,
            &style.height,
            available_size.height,
            None,
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
        let inner_width = container_width.saturating_sub((padding_left_size + padding_right_size) as u32);
        let container_height = specified_height
            .unwrap_or(available_size.height);
        let inner_height = container_height
            .saturating_sub((padding_top_size + padding_bottom_size) as u32);

        ContainerSizes {
            inner_height,
            inner_width,
            container_width,
            container_width_non_filling,
            container_height,
            min_height,
            max_height,
            min_width,
            max_width,
        }
    }

    fn create_input_text_box(&mut self, node_idx: usize, input_value: String, cursor: &mut Position, font_size: u32) -> Result<usize> {
        let style = &self.node_styles.get(&node_idx).unwrap();
        let text = collapse_whitespace(&input_value).unwrap();
        let font_scale = text_scale_from_font_px(font_size as u32);
        let width = measure_text(&text, font_scale);
        let height = FONT_HEIGHT * font_scale;

        let layout_box = self.register_layout_box(LayoutBox {
            rect: Rect {
                x: cursor.x,
                y: cursor.y,
                width,
                height,
                background: StyleBackground::Transparent,
                color: style.color,
                margin_bottom: 0,
                margin_right: 0,
                font_size: Some(font_size as u32),
            },
            kind: LayoutKind::Text(text),
            children: vec![],
            node_idx,
        });
        Ok(layout_box)
    }

    fn layout_block(
        &mut self,
        node_idx: usize,
        mut cursor: Position,
        style: &Style,
        available_size: Size,
        forced_size: OptionalSize,
        mut containing_node_idx: usize,
        allow_fill: bool,
    ) -> Option<(u32, u32, Vec<usize>)> {
        let (padding_left_size, _, padding_top_size, padding_bottom_size) =
            self.get_paddings(node_idx, style, available_size);

        let original_cursor = cursor.clone();
        let content_position = Position {
            x: cursor.x + padding_left_size as i32,
            y: cursor.y + padding_top_size as i32,
        };
        let mut children = Vec::new();

        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();

        let specified_height = forced_size.height.or(get_specified_size(
            font_size,
            &style.height,
            available_size.height,
            None,
        )
        .and_then(|v| Some(v as u32)));

        let container_sizes = self.get_container_sizes(node_idx, &forced_size, style, &available_size);

        let children_idxs: Vec<usize> = self.children_index.get(&node_idx).unwrap().clone();

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
                .push(ResumableNode { parent_idx: node_idx, node_idx: *child_idx, available_size, cursor });
        }

        let mut max_child_width: u32 = 0;
        let mut max_child_height: u32 = 0;
        let mut child_width_buffer = 0;

        for child_local_idx in 0..immediate_children.len() {
            let child_idx = immediate_children[child_local_idx];
            let next_child_idx = if child_local_idx + 1 < immediate_children.len() {
                Some(immediate_children[child_local_idx + 1])
            } else {
                None
            };
            if let Some(child) = self.layout_node(
                *child_idx,
                cursor,
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
                    StyleDisplay::InlineBlock => false,
                    _ => allow_fill,
                },
            ) {
                let child_box = self.layout_table.get(&child).unwrap();
                let child_style = &self.node_styles.get(child_idx).unwrap();
                let next_child_display: Option<StyleDisplay> = next_child_idx.and_then(|idx| Some(self.node_styles.get(idx).unwrap().display));
                if child_style.display == StyleDisplay::InlineBlock && next_child_display.is_none_or(|v| v == StyleDisplay::InlineBlock) {
                    // TODO: This will need to support overflows
                    cursor.x += child_box.rect.width as i32 + child_box.rect.margin_right as i32;
                    child_width_buffer += child_box.rect.width as i32 + child_box.rect.margin_right as i32;

                    if !child_style.position.is_free() {
                        max_child_width = max_child_width.max(child_width_buffer as u32);
                        max_child_height = max_child_height.max(child_box.rect.height);
                    }
                } else {
                    // This is a wrap, so reset X
                    cursor.x = original_cursor.x;
                    cursor.y += child_box.rect.height as i32 + child_box.rect.margin_bottom as i32;
                    child_width_buffer = 0;

                    if !child_style.position.is_free() {
                        max_child_width = max_child_width.max(child_box.rect.width);
                    }
                }
                children.push(child);
            }
        }

        let input_value = match &self.nodes.get(&node_idx).unwrap() {
            Node::Element(element) => element.attributes.get("value"),
            Node::Text(_) => None,
        };
        if immediate_children.len() == 0 && input_value.is_some_and(|v| v.len() > 0) {
            let layout_box = self.create_input_text_box(node_idx, input_value.unwrap().clone(), &mut cursor, font_size).unwrap();
            max_child_width = self.layout_table.get(&layout_box).unwrap().rect.width;
            children.push(layout_box);
        }

        let content_height = (cursor.y - content_position.y).max(max_child_height as i32).max(0) as u32;
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
        let wants_to_fill = style.display != StyleDisplay::InlineBlock;
        let width = if allow_fill && wants_to_fill { container_sizes.container_width } else { container_sizes.compute_actual_container_width(max_child_width) };

        // Margin: auto
        let free_space_y = (container_sizes.inner_height as i32 - content_height as i32).max(0) as u32;
        self.divide_free_space_for_margin(&children, width as i32, free_space_y);

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
        };
        cross_offset
    }

    fn layout_flex(
        &mut self,
        node_idx: usize,
        mut cursor: Position,
        style: &Style,
        available_size: Size,
        forced_size: OptionalSize,
        mut containing_node_idx: usize,
        allow_fill: bool,
    ) -> Option<(u32, u32, Vec<usize>)> {
        let (padding_left_size, _, padding_top_size, padding_bottom_size) =
            self.get_paddings(node_idx, style, available_size);

        let original_cursor = cursor.clone();
        let content_position = Position {
            x: cursor.x + padding_left_size as i32,
            y: cursor.y + padding_top_size as i32,
        };
        let mut base_items = Vec::new();
        let mut children = Vec::new();

        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();

        let container_sizes = self.get_container_sizes(node_idx, &forced_size, style, &available_size);

        let specified_height = get_specified_size(
            font_size,
            &style.height,
            available_size.height,
            None,
        )
        .and_then(|v| Some(v as u32));
        let has_definite_height = forced_size.height.is_some() || specified_height.is_some();

        if style.position == StylePosition::Relative {
            self.containing_nodes.insert(node_idx, ContainingNode {
                node_idx,
                waiters: vec![],
            });
            containing_node_idx = node_idx;
        }

        for child_idx in self.children_index.get(&node_idx).unwrap().clone() {
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

        // Justify-content
        let authored_gap = get_specified_size(font_size, &style.gap, flex_available_size, None).unwrap_or(0);
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
            StyleJustifyContent::Auto | StyleJustifyContent::FlexStart => (0, 0),
            StyleJustifyContent::FlexEnd => (main_free_space, 0),
            StyleJustifyContent::Center => (main_free_space / 2, 0),
            StyleJustifyContent::SpaceBetween if base_items.len() > 1 => {
                (0, main_free_space / (base_items.len() as u32 - 1))
            }
            StyleJustifyContent::SpaceBetween => (0, 0),
        };

        let main_gap = main_distributed_gap + authored_gap as u32;

        let (width, mut height) = match style.flex_direction {
            StyleFlexDirection::Row => {
                let mut max_child_height = 0u32;
                cursor.x = content_position.x + main_start_offset as i32;

                for (item_idx, item) in base_items.iter().enumerate() {
                    let cross_offset = self.calculate_cross_offset(&item, &style, has_definite_height, allow_fill, &container_sizes);
                    // Re-compute cursor for each child so that align-self works
                    cursor.y = original_cursor.y + cross_offset as i32;

                    let last = item_idx == base_items.len() - 1;
                    if let Some(child) = self.layout_node(
                        item.node_idx,
                        cursor,
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
                    ) {
                        let child_box = self.layout_table.get(&child).unwrap();
                        let child_style = &self.node_styles.get(&item.node_idx).unwrap();
                        if !child_style.position.is_free() {
                            cursor.x += child_box.rect.width as i32 + child_box.rect.margin_right;
                            // Don't add gap for last item
                            if !last {
                                cursor.x += main_gap as i32;
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
                let width = if allow_fill { container_sizes.container_width } else { container_sizes.compute_actual_container_width((cursor.x - content_position.x) as u32) };

                // Margin: auto
                let free_space_y = (container_sizes.inner_height as i32 - max_child_height as i32).max(0) as u32;
                self.divide_free_space_for_margin(&children, width as i32, free_space_y);

                (width, height)
            }
            StyleFlexDirection::Column => {
                cursor.y = content_position.y + main_start_offset as i32;

                let mut max_affecting_child_width = 0;

                for (item_idx, item) in base_items.iter().enumerate() {
                    let cross_offset = self.calculate_cross_offset(&item, &style, has_definite_height, allow_fill, &container_sizes);
                    cursor.x = original_cursor.x + cross_offset as i32;

                    let last = item_idx == base_items.len() - 1;
                    if let Some(child) = self.layout_node(
                        item.node_idx,
                        cursor,
                        Size {
                            width: container_sizes.inner_width,
                            height: item.target_size as u32,
                        },
                        OptionalSize {
                            height: Some(item.target_size as u32),
                            width: None,
                        },
                        containing_node_idx,
                        allow_fill,
                    ) {
                        let child_box = self.layout_table.get(&child).unwrap();
                        let child_style = &self.node_styles.get(&item.node_idx).unwrap();
                        if !child_style.position.is_free() {
                            max_affecting_child_width = max_affecting_child_width.max(child_box.rect.width);
                            cursor.y += child_box.rect.height as i32 + child_box.rect.margin_bottom;
                            // Don't add gap for last item
                            if !last {
                                cursor.y += main_gap as i32;
                            }
                        }
                        children.push(child);
                    }
                }

                let content_height = (cursor.y - content_position.y).max(0);
                let height = specified_height.unwrap_or_else(|| {
                    if children.is_empty() {
                        (padding_top_size + padding_bottom_size) as u32
                    } else {
                        (content_height + padding_top_size + padding_bottom_size) as u32
                    }
                });

                // By default block elements fill their available width, but if it's a child of a flex, it only uses what it needs
                let width = if allow_fill { container_sizes.container_width } else { container_sizes.compute_actual_container_width(max_affecting_child_width) };

                // Margin: auto
                let free_space_y = (container_sizes.inner_height as i32 - content_height as i32).max(0) as u32;
                self.divide_free_space_for_margin(&children, width as i32, free_space_y);

                (width, height)
            }
        };

        height = height.min(container_sizes.max_height.unwrap_or(u32::MAX)).max(container_sizes.min_height.unwrap_or(u32::MIN));

        Some((width, height, children))
    }

    fn blend_premul_over_rgb(&self, dst: u32, src: tiny_skia::PremultipliedColorU8) -> u32 {
        let a = src.alpha() as u32;
        if a == 0 {
            return dst;
        }
        if a == 255 {
            return ((src.red() as u32) << 16) | ((src.green() as u32) << 8) | (src.blue() as u32);
        }

        let inv_a = 255 - a;

        let dr = (dst >> 16) & 0xFF;
        let dg = (dst >> 8) & 0xFF;
        let db = dst & 0xFF;

        let r = src.red() as u32 + (dr * inv_a + 127) / 255;
        let g = src.green() as u32 + (dg * inv_a + 127) / 255;
        let b = src.blue() as u32 + (db * inv_a + 127) / 255;

        (r << 16) | (g << 8) | b
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
                    position.y > layout_box.rect.y &&
                    position.y < end_y
            });
        self.hovering = hovering.copied();
    }

    fn paint_layout_box(
        &mut self,
        layout_box_idx: usize,
        buffer: &mut [u32],
        width: u32,
        height: u32,
    ) {
        self.rendered_nodes_ordered.push(layout_box_idx);
        let layout_box = self.layout_table.get(&layout_box_idx).unwrap();
        match &layout_box.kind {
            LayoutKind::Element => {
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
                        layout_box.rect.y,
                        layout_box.rect.width,
                        layout_box.rect.height,
                        bg,
                    );
                }
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
                        layout_box.rect.y,
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
                        buffer,
                        width,
                        height,
                        layout_box.rect.x as i32,
                        layout_box.rect.y as i32,
                        text,
                        color,
                        text_scale_from_font_px(layout_box.rect.font_size.unwrap()),
                    );
                }
            }
            LayoutKind::PixMap(pixmap_buffer) => {
                let pixels = pixmap_buffer.pixels();
                let pixmap_width = pixmap_buffer.width();
                let pixmap_height = pixmap_buffer.height();
                let end_x = pixmap_width.min((width as i32 - layout_box.rect.x).max(0) as u32);
                let end_y = pixmap_height.min((height as i32 - layout_box.rect.y).max(0) as u32);
                for pixel_x in 0..end_x {
                    for pixel_y in 0..end_y {
                        let pixel = pixels[(pixel_x + pixel_y * pixmap_width) as usize];
                        let dist = (layout_box.rect.y as u32 * width
                            + layout_box.rect.x as u32
                            + (pixel_x + pixel_y * width))
                            as usize;
                        buffer[dist] = self.blend_premul_over_rgb(buffer[dist], pixel);
                    }
                }
            }
        }

        for child in layout_box.children.clone() {
            self.paint_layout_box(child, buffer, width, height);
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
            Node::Text(_) => false,
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

    pub fn append_child(&mut self, node_idx: usize, tag: String, attributes: HashMap<String, String>, inner_html: Option<String>) -> Result<(), JsError> {
        self.push_node(Node::Element(Element { tag, attributes, parent: Some(node_idx) }));
        if let Some(html) = inner_html {
            self.create_children_from_html(self.node_idx_cursor, &html);
        }
        Ok(())
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
        for child in self.children_index.get(&node_idx).unwrap().clone() {
            self.remove_node(child, false);
        }

        // Remove from parent
        if remove_from_parent {
            if let Some(parent) = self.nodes.get(&node_idx).unwrap().get_parent() {
                let children = self.children_index.get(&parent).unwrap();
                let filtered: Vec<usize> = children.into_iter().filter(|idx| **idx != node_idx).cloned().collect();
                self.children_index.insert(parent, filtered);
            }
        }

        // Remove node itself
        self.nodes_idxs = self.nodes_idxs.iter().filter(|idx| **idx != node_idx).cloned().collect();
        self.nodes.remove(&node_idx);
        self.children_index.remove(&node_idx);
    }

    pub fn recompute_nodes(&mut self) {
        self.children_index = build_children_index(&self.nodes, &self.nodes_idxs);
        self.node_styles = compute_node_styles(&self.tokio, &mut self.request_cache, &self.nodes, &self.nodes_idxs, &self.children_index, &self.root_indices);
    }

    pub fn get_paddings(&self, node_idx: usize, style: &Style, available_size: Size) -> (i32, i32, i32, i32) {
        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();
        let padding_left_size =
            get_specified_size(font_size, &style.padding_left, available_size.width, None).unwrap_or(0);
        let padding_right_size =
            get_specified_size(font_size, &style.padding_right, available_size.width, None).unwrap_or(0);
        let padding_top_size =
            get_specified_size(font_size, &style.padding_top, available_size.height, None).unwrap_or(0);
        let padding_bottom_size =
            get_specified_size(font_size, &style.padding_bottom, available_size.height, None).unwrap_or(0);

        (
            padding_left_size,
            padding_right_size,
            padding_top_size,
            padding_bottom_size,
        )
    }

    pub fn get_margins(&self, node_idx: usize, style: &Style, available_size: Size) -> (i32, i32, i32, i32) {
        let font_size = self.resolved_font_sizes.get(&node_idx).cloned().unwrap();
        let margin_left_size =
            get_specified_size(font_size, &style.margin_left, available_size.width, None).unwrap_or(0);
        let margin_right_size =
            get_specified_size(font_size, &style.margin_right, available_size.width, None).unwrap_or(0);
        let margin_top_size =
            get_specified_size(font_size, &style.margin_top, available_size.height, None).unwrap_or(0);
        let margin_bottom_size =
            get_specified_size(font_size, &style.margin_bottom, available_size.height, None).unwrap_or(0);

        (
            margin_left_size,
            margin_right_size,
            margin_top_size,
            margin_bottom_size,
        )
    }

    pub fn create_children_from_html(&mut self, parent_idx: usize, html: &String) {
        let mut parser = HtmlParser::new(html);
        parser.parse().expect("Failed to parse inner html");
        let mut idx_mapping = HashMap::new();
        for (node_internal_idx, _) in parser.nodes.iter().enumerate() {
            self.reserve_node_idx();
            idx_mapping.insert(node_internal_idx, self.node_idx_cursor);
        }
        for (node_internal_idx, node) in parser.nodes.iter_mut().enumerate() {
            match node {
                Node::Element(element) => {
                    // Set root elements parent to us
                    if element.parent.is_none() {
                        element.parent = Some(parent_idx);
                    } else {
                        let _ = element.parent.insert(*idx_mapping.get(&element.parent.unwrap()).unwrap());
                    }
                },
                Node::Text(element) => {
                    // Set root elements parent to us
                    if element.parent.is_none() {
                        element.parent = Some(parent_idx);
                    } else {
                        let _ = element.parent.insert(*idx_mapping.get(&element.parent.unwrap()).unwrap());
                    }
                },
            };
            self.insert_node_at_idx(*idx_mapping.get(&node_internal_idx).unwrap(), node.clone());
        }
    }
}

struct Browser {
    url: String,
    renderer: Option<Rc<RefCell<Renderer>>>,
    window: Option<Window>,
    js_runtime: Option<Rc<RefCell<JsRuntime>>>,
    tokio: Option<Rc<RefCell<tokio::runtime::Runtime>>>,
}

impl Browser {
    fn new(url: String) -> Self {
        Self {
            url,
            renderer: None,
            window: None,
            js_runtime: None,
            tokio: None,
        }
    }

    async fn get_html(&self, url: String) -> Result<String> {
        if let Some(stripped) = url.strip_prefix("file://") {
            let contents = fs::read_to_string(stripped)?;
            Ok(contents)
        } else {
            let url = resolve_url(&url, None)?;
            println!("Fetching HTML for {:?}", url);
            let resp = reqwest::get(url).await?.text().await?;
            Ok(resp)
        }
    }

    pub fn dump_tree(&mut self) -> Result<()> {
        self.register_tokio_runtime()?;
        self.navigate(self.url.clone())?;
        let event_loop = EventLoopBuilder::with_user_event().build().expect("Failed to create event loop");
        self.js_runtime.as_mut().unwrap().borrow_mut().op_state().borrow_mut().put(JsHostState {
            renderer: self.renderer.as_mut().cloned().unwrap(),
            proxy: event_loop.create_proxy(),
        });
        self.setup_js_dom()?;

        let js_result = self.run_js();
        println!("Finished running JS code: {:?}", js_result);

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
                ],
                ..Default::default()
            })))
        );
    }

    async fn execute_js(&mut self, scripts: Vec<ScriptType>) -> Result<()> {
        let mut runtime = self.js_runtime.as_mut().unwrap().borrow_mut();
        for (idx, js) in scripts.iter().enumerate() {
            match js {
                ScriptType::Code(code) => {
                    runtime.execute_script(format!("injected code {}", idx), code.clone())?;
                }
                ScriptType::Link(link) => {
                    let base = ReqwestUrl::parse("http://localhost:5173/")?;
                    let url = resolve_url(link, Some(&base))?;
                    let module_id = runtime.load_side_es_module(&url).await?;
                    runtime.mod_evaluate(module_id).await?;
                }
            };
        }
        runtime.run_event_loop(Default::default()).await?;

        Ok(())
    }

    pub fn run_js(&mut self) -> Result<()> {
        let scripts = self.renderer.as_ref().unwrap().borrow_mut().get_scripts();

        println!("Running {} JS scripts", scripts.len());

        self.tokio.as_ref().unwrap().clone().borrow_mut().block_on(self.execute_js(scripts))?;

        Ok(())
    }

    pub fn navigate(&mut self, href: String) -> Result<()> {
        self.url = href.clone();
        println!("Changing url to {}", self.url);

        let input = self.tokio.as_ref().unwrap().borrow_mut().block_on(self.get_html(self.url.clone()))?;

        let mut parser: HtmlParser = HtmlParser::new(&input);
        parser.parse().expect(&format!(
            "Failed to parse. Context: {}",
            parser.get_context()
        ));

        self.renderer = Some(Rc::new(RefCell::new(Renderer::new(self.tokio.as_ref().unwrap().clone(), parser.nodes))));
        if let Some(window) = self.window.as_mut() {
            window.request_redraw();
        }
        self.install_js_host();
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
        self.start_event_loop()
    }

    fn on_click(&mut self) -> Result<()> {
        let (href, code): (Option<String>, Option<String>) = {
            let renderer_ref = self.renderer.as_ref().unwrap().clone();
            let renderer = renderer_ref.borrow();
            let hovering = renderer.hovering;
            if let Some(hovering) = hovering {
                // Run event listeners
                let hovering_node_idx = renderer.layout_to_node_idx(&hovering);
                let parents: Vec<String> = renderer.get_parents(hovering_node_idx).into_iter().map(|idx| idx.to_string()).collect();
                let code = format!(r#"
                    [{}].forEach(idx => {{
                        if (__EVENT_LISTENERS[`${{idx}}:click`]) {{
                            __EVENT_LISTENERS[`${{idx}}:click`]?.forEach(cb => {{
                                cb()
                            }})
                        }}
                    }})
                "#, parents.join(", "));

                let parent_link = renderer.get_parent_link(hovering_node_idx);
                if let Some(parent) = parent_link {
                    match &renderer.nodes.get(&parent).unwrap() {
                        Node::Element(element) => (element.attributes.get("href").cloned(), Some(code)),
                        _ => (None, Some(code)),
                    }
                } else {
                    (None, Some(code))
                }
            } else {
                (None, None)
            }
        };

        if let Some(href) = href {
            self.navigate(href.clone()).unwrap();
        } else if let Some(code) = code {
            self.tokio.as_ref().unwrap().clone().borrow_mut().block_on(self.execute_js(vec![ScriptType::Code(code.to_string())]))?;
        }

        Ok(())
    }

    fn setup_js_dom(&mut self) -> Result<()> {
        let code = ScriptType::Code(r#"
            document.documentElement = document.querySelector("html");
            document.body = document.querySelector("body");
            document.head = document.querySelector("head");
        "#.to_string());
        self.tokio.as_ref().unwrap().clone().borrow_mut().block_on(self.execute_js(vec![code]))?;
        Ok(())
    }

    fn start_event_loop(&mut self) -> Result<()> {
        let event_loop = EventLoopBuilder::with_user_event().build().expect("Failed to create event loop");
        self.window = Some(WindowBuilder::new()
            .with_title("XML demo")
            .with_inner_size(PhysicalSize::new(WINDOW_WIDTH, WINDOW_HEIGHT))
            .build(&event_loop)
            .expect("Failed to create window"));
        let mut size = self.window.as_ref().unwrap().inner_size();

        self.js_runtime.as_mut().unwrap().borrow_mut().op_state().borrow_mut().put(JsHostState {
            renderer: self.renderer.as_mut().cloned().unwrap(),
            proxy: event_loop.create_proxy(),
        });

        self.setup_js_dom()?;

        let js_result = self.run_js();
        println!("Finished running JS code: {:?}", js_result);

        event_loop
            .run(move |event, elwt| {
                let window = self.window.as_ref().unwrap();
                match event {
                    Event::UserEvent(UserEvent::DomUpdated) => {
                        self.renderer.as_ref().unwrap().borrow_mut().recompute_nodes();
                        window.request_redraw();
                    }
                    Event::WindowEvent { event, .. } => match event {
                        WindowEvent::CloseRequested => elwt.exit(),
                        WindowEvent::Resized(new_size) => {
                            size = new_size;
                        }
                        WindowEvent::ScaleFactorChanged { .. } => {
                            size = window.inner_size();
                        }
                        WindowEvent::RedrawRequested => {
                            let ctx =
                                SoftContext::new(window.display_handle().expect("Display handle"))
                                    .expect("Softbuffer context failed");
                            let mut surf =
                                Surface::new(&ctx, window.window_handle().expect("Window handle"))
                                    .expect("Softbuffer surface failed");
                            let width = NonZeroU32::new(size.width.max(1)).expect("Non-zero width");
                            let height = NonZeroU32::new(size.height.max(1)).expect("Non-zero height");
                            surf.resize(width, height).expect("Resize failed");

                            let mut buffer = surf.buffer_mut().expect("Failed to get back buffer");
                            self.renderer.as_mut().unwrap().borrow_mut().render_into(&mut buffer, size.width, size.height);
                            buffer.present().expect("Failed to present");
                        }
                        WindowEvent::CursorMoved { device_id: _, position } => {
                            self.renderer.as_mut().unwrap().borrow_mut().compute_hovering(Position {
                                x: position.x as i32,
                                y: position.y as i32,
                            });
                        }
                        WindowEvent::MouseInput { device_id: _, state, button } => {
                            match (button, state) {
                                (MouseButton::Left, ElementState::Released) => self.on_click().unwrap(),
                                _ => {},
                            }
                        }
                        _ => {}
                    }
                    _ => {}
                }
            })
            .context("Event loop failed")?;

        Ok(())
    }
}

fn main() -> Result<()> {
    let dump_tree = env::args().any(|arg| arg == "--dump-tree");
    let mut browser = Browser::new("http://localhost:5173".to_string());
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
    let mut layout_info = vec![None; renderer.nodes.len()];
    collect_layout_info(&layout_roots, &mut layout_info, &renderer.layout_table);
    let mut out = String::new();

    for &idx in &renderer.root_indices {
        write_tree(
            &renderer.nodes,
            &renderer.children_index,
            &renderer.node_styles,
            &renderer.node_layout_mapping,
            &layout_info,
            idx,
            0,
            &mut out,
        );
    }

    out
}

fn collect_layout_info(layout_boxes: &[usize], layout_info: &mut [Option<LayoutDumpInfo>], layout_table: &HashMap<usize, LayoutBox>) {
    for layout_box_idx in layout_boxes {
        let layout_box = layout_table.get(&layout_box_idx).unwrap();
        layout_info[*layout_box_idx] = Some(LayoutDumpInfo {
            kind: layout_kind_label(&layout_box.kind),
            rect: layout_box.rect.clone(),
        });
        collect_layout_info(&layout_box.children, layout_info, layout_table);
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
    layout_info: &[Option<LayoutDumpInfo>],
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
    };
    label.push_str(&format!(" [idx={}]", node_idx));
    match layout_node_mapping.get(&node_idx).and_then(|idx| layout_info[*idx].clone()) {
        Some(info) => {
            label.push_str(&format!(
                " [layout={} x={} y={} width={} height={}]",
                info.kind, info.rect.x, info.rect.y, info.rect.width, info.rect.height
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

fn measure_text(text: &str, scale: u32) -> u32 {
    let glyphs = text.chars().count() as u32;
    if glyphs == 0 {
        return 0;
    }

    let advance = FONT_WIDTH * scale + scale;
    glyphs * advance - scale
}

fn draw_text(
    buffer: &mut [u32],
    width: u32,
    height: u32,
    x: i32,
    y: i32,
    text: &str,
    color: u32,
    scale: u32,
) {
    let advance = (FONT_WIDTH * scale + scale) as i32;
    let mut pen_x = x;

    for ch in text.chars() {
        draw_glyph(buffer, width, height, pen_x, y, glyph_for(ch), color, scale);
        pen_x += advance;
    }
}

fn draw_glyph(
    buffer: &mut [u32],
    width: u32,
    height: u32,
    x: i32,
    y: i32,
    glyph: [u8; FONT_HEIGHT as usize],
    color: u32,
    scale: u32,
) {
    for (row, bits) in glyph.iter().enumerate() {
        for col in 0..FONT_WIDTH {
            let mask = 1 << (FONT_WIDTH - 1 - col);
            if bits & mask as u8 == 0 {
                continue;
            }

            draw_rect_filled(
                buffer,
                width,
                height,
                x + (col * scale) as i32,
                y + (row as u32 * scale) as i32,
                scale,
                scale,
                color,
            );
        }
    }
}

fn glyph_for(ch: char) -> [u8; FONT_HEIGHT as usize] {
    match ch {
        ' ' => [0, 0, 0, 0, 0, 0, 0],
        '!' => [0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0, 0b00100],
        '"' => [0b01010, 0b01010, 0b00100, 0, 0, 0, 0],
        '\'' => [0b00100, 0b00100, 0, 0, 0, 0, 0],
        ',' => [0, 0, 0, 0, 0b01100, 0b00100, 0b01000],
        '-' => [0, 0, 0, 0b11111, 0, 0, 0],
        '.' => [0, 0, 0, 0, 0, 0b01100, 0b01100],
        '/' => [0b00001, 0b00010, 0b00100, 0b01000, 0b10000, 0, 0],
        '0' => [
            0b01110, 0b10001, 0b10011, 0b10101, 0b11001, 0b10001, 0b01110,
        ],
        '1' => [
            0b00100, 0b01100, 0b00100, 0b00100, 0b00100, 0b00100, 0b01110,
        ],
        '2' => [
            0b01110, 0b10001, 0b00001, 0b00010, 0b00100, 0b01000, 0b11111,
        ],
        '3' => [
            0b11110, 0b00001, 0b00001, 0b01110, 0b00001, 0b00001, 0b11110,
        ],
        '4' => [
            0b00010, 0b00110, 0b01010, 0b10010, 0b11111, 0b00010, 0b00010,
        ],
        '5' => [
            0b11111, 0b10000, 0b10000, 0b11110, 0b00001, 0b00001, 0b11110,
        ],
        '6' => [
            0b01110, 0b10000, 0b10000, 0b11110, 0b10001, 0b10001, 0b01110,
        ],
        '7' => [
            0b11111, 0b00001, 0b00010, 0b00100, 0b01000, 0b01000, 0b01000,
        ],
        '8' => [
            0b01110, 0b10001, 0b10001, 0b01110, 0b10001, 0b10001, 0b01110,
        ],
        '9' => [
            0b01110, 0b10001, 0b10001, 0b01111, 0b00001, 0b00001, 0b01110,
        ],
        ':' => [0, 0b01100, 0b01100, 0, 0b01100, 0b01100, 0],
        ';' => [0, 0b01100, 0b01100, 0, 0b01100, 0b00100, 0b01000],
        '<' => [
            0b00010, 0b00100, 0b01000, 0b10000, 0b01000, 0b00100, 0b00010,
        ],
        '>' => [
            0b01000, 0b00100, 0b00010, 0b00001, 0b00010, 0b00100, 0b01000,
        ],
        '?' => [0b01110, 0b10001, 0b00001, 0b00010, 0b00100, 0, 0b00100],
        'A' => [
            0b01110, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001,
        ],
        'B' => [
            0b11110, 0b10001, 0b10001, 0b11110, 0b10001, 0b10001, 0b11110,
        ],
        'C' => [
            0b01111, 0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b01111,
        ],
        'D' => [
            0b11110, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11110,
        ],
        'E' => [
            0b11111, 0b10000, 0b10000, 0b11110, 0b10000, 0b10000, 0b11111,
        ],
        'F' => [
            0b11111, 0b10000, 0b10000, 0b11110, 0b10000, 0b10000, 0b10000,
        ],
        'G' => [
            0b01111, 0b10000, 0b10000, 0b10111, 0b10001, 0b10001, 0b01110,
        ],
        'H' => [
            0b10001, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001,
        ],
        'I' => [
            0b11111, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b11111,
        ],
        'J' => [
            0b00001, 0b00001, 0b00001, 0b00001, 0b00001, 0b10001, 0b01110,
        ],
        'K' => [
            0b10001, 0b10010, 0b10100, 0b11000, 0b10100, 0b10010, 0b10001,
        ],
        'L' => [
            0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b11111,
        ],
        'M' => [
            0b10001, 0b11011, 0b10101, 0b10101, 0b10001, 0b10001, 0b10001,
        ],
        'N' => [
            0b10001, 0b10001, 0b11001, 0b10101, 0b10011, 0b10001, 0b10001,
        ],
        'O' => [
            0b01110, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01110,
        ],
        'P' => [
            0b11110, 0b10001, 0b10001, 0b11110, 0b10000, 0b10000, 0b10000,
        ],
        'Q' => [
            0b01110, 0b10001, 0b10001, 0b10001, 0b10101, 0b10010, 0b01101,
        ],
        'R' => [
            0b11110, 0b10001, 0b10001, 0b11110, 0b10100, 0b10010, 0b10001,
        ],
        'S' => [
            0b01111, 0b10000, 0b10000, 0b01110, 0b00001, 0b00001, 0b11110,
        ],
        'T' => [
            0b11111, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100,
        ],
        'U' => [
            0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01110,
        ],
        'V' => [
            0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01010, 0b00100,
        ],
        'W' => [
            0b10001, 0b10001, 0b10001, 0b10101, 0b10101, 0b10101, 0b01010,
        ],
        'X' => [
            0b10001, 0b10001, 0b01010, 0b00100, 0b01010, 0b10001, 0b10001,
        ],
        'Y' => [
            0b10001, 0b10001, 0b01010, 0b00100, 0b00100, 0b00100, 0b00100,
        ],
        'Z' => [
            0b11111, 0b00001, 0b00010, 0b00100, 0b01000, 0b10000, 0b11111,
        ],
        'a' => [0, 0, 0b01110, 0b00001, 0b01111, 0b10001, 0b01111],
        'b' => [
            0b10000, 0b10000, 0b10110, 0b11001, 0b10001, 0b10001, 0b11110,
        ],
        'c' => [0, 0, 0b01110, 0b10000, 0b10000, 0b10001, 0b01110],
        'd' => [
            0b00001, 0b00001, 0b01101, 0b10011, 0b10001, 0b10001, 0b01111,
        ],
        'e' => [0, 0, 0b01110, 0b10001, 0b11111, 0b10000, 0b01110],
        'f' => [
            0b00110, 0b01001, 0b01000, 0b11100, 0b01000, 0b01000, 0b01000,
        ],
        'g' => [0, 0b01111, 0b10001, 0b10001, 0b01111, 0b00001, 0b01110],
        'h' => [
            0b10000, 0b10000, 0b10110, 0b11001, 0b10001, 0b10001, 0b10001,
        ],
        'i' => [0b00100, 0, 0b01100, 0b00100, 0b00100, 0b00100, 0b01110],
        'j' => [0b00010, 0, 0b00110, 0b00010, 0b00010, 0b10010, 0b01100],
        'k' => [
            0b10000, 0b10000, 0b10010, 0b10100, 0b11000, 0b10100, 0b10010,
        ],
        'l' => [
            0b01100, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b01110,
        ],
        'm' => [0, 0, 0b11010, 0b10101, 0b10101, 0b10101, 0b10101],
        'n' => [0, 0, 0b10110, 0b11001, 0b10001, 0b10001, 0b10001],
        'o' => [0, 0, 0b01110, 0b10001, 0b10001, 0b10001, 0b01110],
        'p' => [0, 0b11110, 0b10001, 0b10001, 0b11110, 0b10000, 0b10000],
        'q' => [0, 0b01101, 0b10011, 0b10001, 0b01111, 0b00001, 0b00001],
        'r' => [0, 0, 0b10110, 0b11001, 0b10000, 0b10000, 0b10000],
        's' => [0, 0, 0b01111, 0b10000, 0b01110, 0b00001, 0b11110],
        't' => [
            0b01000, 0b01000, 0b11100, 0b01000, 0b01000, 0b01001, 0b00110,
        ],
        'u' => [0, 0, 0b10001, 0b10001, 0b10001, 0b10011, 0b01101],
        'v' => [0, 0, 0b10001, 0b10001, 0b10001, 0b01010, 0b00100],
        'w' => [0, 0, 0b10001, 0b10001, 0b10101, 0b10101, 0b01010],
        'x' => [0, 0, 0b10001, 0b01010, 0b00100, 0b01010, 0b10001],
        'y' => [0, 0b10001, 0b10001, 0b10001, 0b01111, 0b00001, 0b01110],
        'z' => [0, 0, 0b11111, 0b00010, 0b00100, 0b01000, 0b11111],
        _ => glyph_for('?'),
    }
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

    for py in start_y..end_y {
        let row = &mut buffer[py as usize * stride..(py as usize + 1) * stride];
        for px in start_x..end_x {
            row[px as usize] = color;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::css::{CssParser, Node as CssNode};
    use crate::parser::Element;
    use crate::style::{
        Style, StyleAlign, StyleBackground, StyleDisplay, StyleFlexDirection, StyleJustifyContent, StylePosition, StyleSize, parse_style
    };
    use crate::{HtmlParser, Renderer};
    use anyhow::{Context, Result};
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::fs;
    use std::rc::Rc;

    const SAMPLE_PAGE_PATH: &str = "pages/google_real.html";

    #[test]
    fn test_parse_svg() -> Result<()> {
        let svg_input = r#"<svg class="lnXdpd" aria-label="Google" height="92" role="img" viewBox="0 0 272 92" width="272" xmlns="http://www.w3.org/2000/svg"><path d="M115.75 47.18c0 12.77-9.99 22.18-22.25 22.18s-22.25-9.41-22.25-22.18C71.25 34.32 81.24 25 93.5 25s22.25 9.32 22.25 22.18zm-9.74 0c0-7.98-5.79-13.44-12.51-13.44S80.99 39.2 80.99 47.18c0 7.9 5.79 13.44 12.51 13.44s12.51-5.55 12.51-13.44zm57.74 0c0 12.77-9.99 22.18-22.25 22.18s-22.25-9.41-22.25-22.18c0-12.85 9.99-22.18 22.25-22.18s22.25 9.32 22.25 22.18zm-9.74 0c0-7.98-5.79-13.44-12.51-13.44s-12.51 5.46-12.51 13.44c0 7.9 5.79 13.44 12.51 13.44s12.51-5.55 12.51-13.44zm55.74-20.84v39.82c0 16.38-9.66 23.07-21.08 23.07-10.75 0-17.22-7.19-19.66-13.07l8.48-3.53c1.51 3.61 5.21 7.87 11.17 7.87 7.31 0 11.84-4.51 11.84-13v-3.19h-.34c-2.18 2.69-6.38 5.04-11.68 5.04-11.09 0-21.25-9.66-21.25-22.09 0-12.52 10.16-22.26 21.25-22.26 5.29 0 9.49 2.35 11.68 4.96h.34v-3.61h9.25zm-8.56 20.92c0-7.81-5.21-13.52-11.84-13.52-6.72 0-12.35 5.71-12.35 13.52 0 7.73 5.63 13.36 12.35 13.36 6.63 0 11.84-5.63 11.84-13.36zM225 3v65h-9.5V3h9.5zm37.02 51.48l7.56 5.04c-2.44 3.61-8.32 9.83-18.48 9.83-12.6 0-22.01-9.74-22.01-22.18 0-13.19 9.49-22.18 20.92-22.18 11.51 0 17.14 9.16 18.98 14.11l1.01 2.52-29.65 12.28c2.27 4.45 5.8 6.72 10.75 6.72 4.96 0 8.4-2.44 10.92-6.14zm-23.27-7.98l19.82-8.23c-1.09-2.77-4.37-4.7-8.23-4.7-4.95 0-11.84 4.37-11.59 12.93zM35.29 41.41V32H67c.31 1.64.47 3.58.47 5.68 0 7.06-1.93 15.79-8.15 22.01-6.05 6.3-13.78 9.66-24.02 9.66C16.32 69.35.36 53.89.36 34.91.36 15.93 16.32.47 35.3.47c10.5 0 17.98 4.12 23.6 9.49l-6.64 6.64c-4.03-3.78-9.49-6.72-16.97-6.72-13.86 0-24.7 11.17-24.7 25.03 0 13.86 10.84 25.03 24.7 25.03 8.99 0 14.11-3.61 17.39-6.89 2.66-2.66 4.41-6.46 5.1-11.65l-22.49.01z" fill="\#FFF"></path></svg>"#;
        let input = format!(
            r#"<html style="width:100%;height:100%;background-color:#FFFFFF;">{}</html>"#,
            svg_input
        );
        let mut parser: HtmlParser = HtmlParser::new(&input);
        parser.parse().expect("Failed to parse");

        let tokio = Rc::new(RefCell::new(tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .ok()
            .with_context(|| "Failed to construct tokio")?));

        let renderer = Renderer::new(tokio, parser.nodes);
        assert_eq!(renderer.get_element_html(1), svg_input);

        Ok(())
    }

    #[test]
    fn test_self_closing() {
        let input = r#"<html><img src="test.png"><p>Haha</p></html>"#;
        let mut parser: HtmlParser = HtmlParser::new(&input);
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
            &Element {
                tag: "div".to_string(),
                attributes,
                parent: None,
            },
            &vec![],
            None,
            &mut HashMap::new(),
            &mut HashMap::new(),
        )?;

        assert_eq!(
            Style {
                width: StyleSize::Percent(100),
                height: StyleSize::Percent(100),
                background: StyleBackground::Hex(0x00_FF_FF_FF),
                display: StyleDisplay::Block,
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
                color: StyleBackground::Transparent,
                min_height: StyleSize::Auto,
                max_height: StyleSize::Auto,
                min_width: StyleSize::Auto,
                max_width: StyleSize::Auto,
                position: StylePosition::Static,
                text_align: StyleAlign::Left,
                variables: HashMap::new(),
                font_size: StyleSize::Px(16),
                align_self: StyleJustifyContent::Auto,
            },
            parsed
        );

        Ok(())
    }

    #[test]
    fn test_parse_google() -> Result<()> {
        let input = fs::read_to_string(SAMPLE_PAGE_PATH)
            .with_context(|| format!("Failed to read sample page at {SAMPLE_PAGE_PATH}"))?;

        let mut parser: HtmlParser = HtmlParser::new(&input);
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
        let mut parser: HtmlParser = HtmlParser::new(&input);
        parser.parse().expect("Failed to parse");

        let tokio = Rc::new(RefCell::new(tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .ok()
            .with_context(|| "Failed to construct tokio")?));

        let mut renderer = Renderer::new(tokio, parser.nodes);
        let width = 1280;
        let height = 720;
        let mut buffer = vec![0; width * height];
        renderer.render_into(&mut buffer, width as u32, height as u32);

        // Ensure all white, meaning nothing was painted
        assert!(buffer.iter().all(|p| *p == 0xFF_FF_FF_FF));

        Ok(())
    }

    #[test]
    fn test_parse_complex_css_selelctor() -> Result<()> {
        let input = r#"<html><style>.test input[type="submit"] { background-color: #ff0000; width: 100%; height: 100%; }</style><input class="test" type="submit"></html>"#;
        let mut parser: HtmlParser = HtmlParser::new(&input);
        parser.parse().expect("Failed to parse");

        let tokio = Rc::new(RefCell::new(tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .ok()
            .with_context(|| "Failed to construct tokio")?));

        let mut renderer = Renderer::new(tokio, parser.nodes);
        let width = 1280;
        let height = 720;
        let mut buffer = vec![0; width * height];
        renderer.render_into(&mut buffer, width as u32, height as u32);

        // Ensure all red, meaning nothing was painted
        assert!(buffer.iter().all(|p| *p == 0xFF_00_00));

        Ok(())
    }

    #[test]
    fn test_parse_css_links() -> Result<()> {
        let input = r#"<html><head><link rel="stylesheet" href="https://pastebin.com/raw/rTDWxgsa"></head><input class="test" type="submit"></html>"#;
        let mut parser: HtmlParser = HtmlParser::new(&input);
        parser.parse().expect("Failed to parse");

        let tokio = Rc::new(RefCell::new(tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .ok()
            .with_context(|| "Failed to construct tokio")?));

        let mut renderer = Renderer::new(tokio, parser.nodes);
        let width = 1280;
        let height = 720;
        let mut buffer = vec![0; width * height];
        renderer.render_into(&mut buffer, width as u32, height as u32);

        // Ensure all red, meaning nothing was painted
        assert!(buffer.iter().all(|p| *p == 0xFF_00_00));

        Ok(())
    }
}
