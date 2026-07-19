#![allow(dead_code, unused_imports)]

use std::{cell::RefCell, collections::HashMap, rc::Rc, sync::mpsc::Sender};

use anyhow::{Context, Result, anyhow};
use render::{BorderRadius, FontHandler, blend_rgb_with_rgba, draw_rect_filled, text_to_buffer};
use resvg::tiny_skia::Pixmap;
use winit::{
    event::KeyEvent,
    keyboard::{KeyCode, PhysicalKey},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UiEvent {
    Rerender,
}

pub struct UiBuilder {
    curr: Option<usize>,
    pub nodes: Vec<Node>,
    width: u32,
    height: u32,
    font_handler: Rc<FontHandler>,
    pub comms_tx: Sender<UiEvent>,
}

pub struct Typeable {
    pub text: String,
    pub color: u32,
    pub on_input: Option<Box<dyn Fn(&Typeable)>>,
    pub on_enter: Option<Box<dyn Fn(&Typeable)>>,
}

pub struct Element {
    pub bg_color: u32,
    pub height: u32,
    pub width: u32,
    pub padding: u32,
    pub parent: Option<usize>,
    pub on_click: Option<Box<dyn Fn()>>,
    pub hor: Option<Hor>,
    pub typeable: Option<Typeable>,
    pub gap: u32,
    pub border_radius: u32,
}

impl Element {
    pub fn new() -> Self {
        Self {
            bg_color: 0x00_00_00_00,
            padding: 0,
            width: 0,
            height: 0,
            parent: None,
            on_click: None,
            hor: None,
            typeable: None,
            gap: 0,
            border_radius: 0,
        }
    }
}

pub struct TextElement {
    text: String,
    color: u32,
    font_px: u32,
    parent: Option<usize>,
}

pub enum Node {
    Element(Element),
    Text(TextElement),
}

impl Node {
    pub fn get_parent(&self) -> Option<usize> {
        match self {
            Node::Element(element) => element.parent,
            Node::Text(element) => element.parent,
        }
    }
}

pub struct UiRuntime<T> {
    pub builder: UiBuilder,
    pub buffer: Vec<u32>,
    pub layout: Vec<LayoutBox>,
    pub hovering: Option<usize>,
    pub focused: Option<usize>,
    pub state: Rc<RefCell<T>>,
}

impl<T> UiRuntime<T> {
    pub fn new_empty(width: u32, height: u32, comms_tx: Sender<UiEvent>, state: T) -> Result<Self> {
        Ok(Self {
            builder: UiBuilder {
                curr: None,
                nodes: vec![],
                width,
                height,
                font_handler: Rc::new(FontHandler::new()?),
                comms_tx,
            },
            buffer: vec![],
            layout: vec![],
            hovering: None,
            focused: None,
            state: Rc::new(RefCell::new(state)),
        })
    }

    pub fn apply_hovering(&mut self, x: i32, y: i32) {
        for layout_box in self.layout.iter().rev() {
            let start_x = layout_box.x;
            let start_y = layout_box.y;
            let end_x = start_x + layout_box.width as i32;
            let end_y = start_y + layout_box.height as i32;

            if matches!(&&self.builder.nodes[layout_box.node_idx], Node::Element(_))
                && x >= start_x
                && x < end_x
                && y >= start_y
                && y < end_y
            {
                self.hovering = Some(layout_box.node_idx);
                return;
            }
        }
        self.hovering = None;
    }

    pub fn on_click(&mut self) {
        let Some(hovering) = self.hovering else {
            self.focused = None;
            return;
        };
        let mut outer_node = Some((hovering, &self.builder.nodes[hovering]));
        let mut typeable_found = false;
        while let Some((node_idx, node)) = outer_node {
            if let Node::Element(element) = node {
                if let Some(cb) = &element.on_click {
                    cb();
                }
                if element.typeable.is_some() && !typeable_found {
                    typeable_found = true;
                    self.focused = Some(node_idx);
                }
            };
            outer_node = node
                .get_parent()
                .map(|parent| (parent, &self.builder.nodes[parent]));
        }
        if !typeable_found {
            self.focused = None;
        }
    }

    pub fn on_keyup(&mut self, event: KeyEvent) {
        let Some(focused) = self.focused else {
            return;
        };
        let Node::Element(element) = &mut self.builder.nodes[focused] else {
            return;
        };
        let Some(typeable) = &mut element.typeable else {
            return;
        };
        if let Some(text) = event.text {
            if typeable.text.len() > 0
                && matches!(event.physical_key, PhysicalKey::Code(KeyCode::Backspace))
            {
                typeable.text.pop();
            } else if matches!(event.physical_key, PhysicalKey::Code(KeyCode::Enter))
                && let Some(on_enter) = &typeable.on_enter
            {
                on_enter(&*typeable);
            } else {
                typeable.text += &text;
            }
            if let Some(on_input) = &typeable.on_input {
                on_input(&*typeable);
            }
            let _ = self.builder.comms_tx.send(UiEvent::Rerender);
        }
    }

    pub fn rerender(&mut self) -> Result<()> {
        let (layout, buffer) = self.builder.layout_pair()?;
        self.layout = layout;
        self.buffer = buffer;
        Ok(())
    }
}

pub enum JustifyContent {
    Start,
    Center,
    End,
}

pub struct Hor {
    justify_content: JustifyContent,
    align_items: JustifyContent,
}

impl Hor {
    pub fn new() -> Self {
        Self {
            justify_content: JustifyContent::Start,
            align_items: JustifyContent::Start,
        }
    }
}

impl UiBuilder {
    pub fn new(width: u32, height: u32, comms_tx: Sender<UiEvent>) -> Result<Self> {
        Ok(Self {
            curr: None,
            nodes: vec![],
            width,
            height,
            font_handler: Rc::new(FontHandler::new()?),
            comms_tx,
        })
    }

    pub fn start_element(&mut self) {
        let mut el = Element::new();
        el.parent = self.curr;
        self.nodes.push(Node::Element(el));
        self.curr = Some(self.nodes.len() - 1);
    }

    pub fn finish_element(&mut self) -> Result<()> {
        if self.curr.is_none() {
            return Err(anyhow!("finish_element called with no element in progress"));
        }
        self.curr = self.curr.and_then(|n| self.nodes[n].get_parent());
        Ok(())
    }

    fn curr_element_mut(&mut self) -> Result<&mut Element> {
        match self.curr.map(|idx| &mut self.nodes[idx]) {
            Some(Node::Element(element)) => Ok(element),
            _ => Err(anyhow!("called without element in progress")),
        }
    }

    pub fn bg(&mut self, rgba: u32) -> Result<()> {
        self.curr_element_mut()?.bg_color = rgba;
        Ok(())
    }

    pub fn padding(&mut self, padding: u32) -> Result<()> {
        self.curr_element_mut()?.padding = padding;
        Ok(())
    }

    pub fn height(&mut self, height: u32) -> Result<()> {
        self.curr_element_mut()?.height = height;
        Ok(())
    }

    pub fn width(&mut self, width: u32) -> Result<()> {
        self.curr_element_mut()?.width = width;
        Ok(())
    }

    pub fn hor(&mut self) -> Result<()> {
        self.curr_element_mut()?.hor = Some(Hor::new());
        Ok(())
    }

    pub fn gap(&mut self, gap: u32) -> Result<()> {
        self.curr_element_mut()?.gap = gap;
        Ok(())
    }

    pub fn justify(&mut self, value: JustifyContent) -> Result<()> {
        self.curr_element_mut()?
            .hor
            .as_mut()
            .with_context(|| "Hor must be set for justify to work")?
            .justify_content = value;
        Ok(())
    }

    pub fn align(&mut self, value: JustifyContent) -> Result<()> {
        self.curr_element_mut()?
            .hor
            .as_mut()
            .with_context(|| "Hor must be set for justify to work")?
            .align_items = value;
        Ok(())
    }

    pub fn rounded(&mut self, border_radius: u32) -> Result<()> {
        self.curr_element_mut()?.border_radius = border_radius;
        Ok(())
    }

    pub fn typeable(&mut self, typeable: Typeable) -> Result<()> {
        self.curr_element_mut()?.typeable = Some(typeable);
        Ok(())
    }

    pub fn text(&mut self, text: String) -> Result<()> {
        let node = Node::Text(TextElement {
            text,
            color: 0xFF_FF_FF_FF,
            font_px: 16,
            parent: self.curr,
        });
        self.nodes.push(node);
        Ok(())
    }

    pub fn on_click<F>(&mut self, cb: F) -> Result<()>
    where
        F: Fn() + 'static,
    {
        self.curr_element_mut()?.on_click = Some(Box::new(cb));
        Ok(())
    }

    pub fn clean(&mut self) {
        self.nodes.clear();
        self.curr = None;
    }

    fn render_node(
        &self,
        layouts: &mut Vec<LayoutBox>,
        mut cursor: (i32, i32),
        node_idx: usize,
        children_index: &HashMap<usize, Vec<usize>>,
    ) -> Result<usize> {
        let idx = layouts.len();
        match &self.nodes[node_idx] {
            Node::Element(el) => {
                layouts.push(LayoutBox {
                    x: cursor.0,
                    y: cursor.1,
                    height: el.height,
                    width: el.width,
                    kind: LayoutKind::Element,
                    bg_color: el.bg_color,
                    node_idx,
                    border_radius: el.border_radius,
                });

                cursor.0 += el.padding as i32;
                cursor.1 += el.padding as i32;

                if let Some(children) = children_index.get(&node_idx) {
                    let (shift_x, shift_y) = if let Some(hor) = &el.hor {
                        let mut base_items = vec![];
                        let mut layout_buffer = vec![];
                        for child in children.iter() {
                            let idx = self.render_node(
                                &mut layout_buffer,
                                cursor,
                                *child,
                                children_index,
                            )?;
                            base_items.push(idx);
                        }
                        let shift_x = match hor.justify_content {
                            JustifyContent::Start => 0,
                            JustifyContent::Center => {
                                let free = el.width as i32
                                    - el.padding as i32 * 2
                                    - base_items
                                        .iter()
                                        .map(|l| layout_buffer[*l].width as i32)
                                        .sum::<i32>();
                                free / 2
                            }
                            JustifyContent::End => {
                                el.width as i32
                                    - el.padding as i32 * 2
                                    - base_items
                                        .iter()
                                        .map(|l| layout_buffer[*l].width as i32)
                                        .sum::<i32>()
                            }
                        };
                        let shift_y = match hor.align_items {
                            JustifyContent::Start => 0,
                            JustifyContent::Center => {
                                let free = el.height as i32
                                    - el.padding as i32 * 2
                                    - base_items
                                        .iter()
                                        .map(|l| layout_buffer[*l].height as i32)
                                        .sum::<i32>();
                                free / 2
                            }
                            JustifyContent::End => {
                                el.height as i32
                                    - el.padding as i32 * 2
                                    - base_items
                                        .iter()
                                        .map(|l| layout_buffer[*l].height as i32)
                                        .sum::<i32>()
                            }
                        };
                        (shift_x, shift_y)
                    } else {
                        (0, 0)
                    };

                    cursor.0 += shift_x;
                    cursor.1 += shift_y;

                    for child in children {
                        self.render_node(layouts, cursor, *child, children_index)?;

                        let child_node = &self.nodes[*child];
                        if let Node::Element(child_el) = child_node {
                            if el.hor.is_some() {
                                cursor.0 += child_el.width as i32 + el.gap as i32;
                            } else {
                                cursor.1 += child_el.height as i32 + el.gap as i32;
                            }
                        }
                    }
                }

                if let Some(typeable) = &el.typeable
                    && typeable.text.len() > 0
                {
                    let (pixmap, width, height) = text_to_buffer(
                        &self.font_handler,
                        typeable.color,
                        &typeable.text,
                        14,
                        None,
                    )
                    .with_context(|| "Failed to convert text to buffer")?;

                    layouts.push(LayoutBox {
                        x: cursor.0,
                        y: cursor.1,
                        kind: LayoutKind::Text(pixmap),
                        width,
                        height,
                        bg_color: 0x00_00_00_00,
                        node_idx,
                        border_radius: 0,
                    });
                }
            }
            Node::Text(el) => {
                let (pixmap, width, height) =
                    text_to_buffer(&self.font_handler, el.color, &el.text, el.font_px, None)
                        .with_context(|| "Failed to convert text to buffer")?;

                layouts.push(LayoutBox {
                    x: cursor.0,
                    y: cursor.1,
                    kind: LayoutKind::Text(pixmap),
                    width,
                    height,
                    bg_color: 0x00_00_00_00,
                    node_idx,
                    border_radius: 0,
                });
            }
        };
        Ok(idx)
    }

    fn layout_to_buffer(&self, layouts: &Vec<LayoutBox>) -> Vec<u32> {
        let mut buffer = vec![0; (self.width * self.height) as usize];
        for layout in layouts.iter() {
            match &layout.kind {
                LayoutKind::Element => {
                    draw_rect_filled(
                        &mut buffer,
                        false,
                        self.width,
                        self.height,
                        layout.x as i32,
                        layout.y as i32,
                        layout.width,
                        layout.height,
                        layout.bg_color,
                        &BorderRadius {
                            top_left: layout.border_radius,
                            top_right: layout.border_radius,
                            bottom_right: layout.border_radius,
                            bottom_left: layout.border_radius,
                        },
                    );
                }
                LayoutKind::Text(pixmap) => {
                    for y in 0..layout.height {
                        let dst_y = layout.y + y as i32;
                        if dst_y < 0 || dst_y >= self.height as i32 {
                            continue;
                        }
                        for x in 0..layout.width {
                            let dst_x = layout.x + x as i32;
                            if dst_x < 0 || dst_x >= self.width as i32 {
                                continue;
                            }
                            let pixel = pixmap.pixels()[(y * pixmap.width() + x) as usize];
                            let dst =
                                &mut buffer[(dst_y as u32 * self.width + dst_x as u32) as usize];
                            *dst = blend_rgb_with_rgba(
                                *dst,
                                (pixel.red(), pixel.green(), pixel.blue(), pixel.alpha()),
                            );
                        }
                    }
                }
            }
        }
        buffer
    }

    fn compute_children_index(&self) -> HashMap<usize, Vec<usize>> {
        let mut children_index: HashMap<usize, Vec<usize>> = HashMap::new();
        for (idx, node) in self.nodes.iter().enumerate() {
            if let Some(parent) = node.get_parent() {
                children_index.entry(parent).or_default().push(idx);
            }
        }
        children_index
    }

    pub fn layout_pair(&self) -> Result<(Vec<LayoutBox>, Vec<u32>)> {
        let cursor = (0, 0);
        let children_index = self.compute_children_index();
        let mut layouts = vec![];
        self.render_node(&mut layouts, cursor, 0, &children_index)?;
        let buffer = self.layout_to_buffer(&layouts);
        Ok((layouts, buffer))
    }
}

pub enum LayoutKind {
    Element,
    Text(Pixmap),
}

pub struct LayoutBox {
    pub x: i32,
    pub y: i32,
    pub kind: LayoutKind,
    pub width: u32,
    pub height: u32,
    pub bg_color: u32,
    pub node_idx: usize,
    pub border_radius: u32,
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use anyhow::Result;
    use render::ensure_snapshot_matches;

    use crate::UiRuntime;

    fn snapshot_dir() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join("snapshots")
    }

    #[test]
    fn renders() -> Result<()> {
        let (tx, _) = std::sync::mpsc::channel();
        let state = false;
        let mut runtime = UiRuntime::new_empty(1920, 1080, tx, state)?;
        let builder = &mut runtime.builder;
        builder.start_element();
        builder.bg(0x00_FF_00_FF)?;
        builder.width(1920)?;
        builder.height(1080)?;

        builder.start_element();
        builder.bg(0xFF_00_00_FF)?;
        builder.padding(50)?;
        builder.height(200)?;
        builder.width(200)?;
        builder.text("Hi there".to_string())?;
        builder.finish_element()?;

        builder.finish_element()?;

        runtime.rerender()?;

        ensure_snapshot_matches(&runtime.buffer, snapshot_dir(), "UiBuilder", 1920, 1080)?;

        Ok(())
    }
}
