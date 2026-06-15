#![allow(dead_code, unused_imports)]

use std::{collections::HashMap, rc::Rc};

use anyhow::{Context, Result, anyhow};
use resvg::tiny_skia::Pixmap;

use crate::{FontHandler, Position, blend_rgba_with_rgba, draw_rect_filled, text_to_buffer};

pub struct UiBuilder {
    curr: Option<usize>,
    pub nodes: Vec<Node>,
    width: u32,
    height: u32,
    font_handler: Rc<FontHandler>,
}

pub struct Element {
    pub bg_color: u32,
    pub height: u32,
    pub width: u32,
    pub padding: u32,
    pub parent: Option<usize>,
    pub on_click: Option<Box<dyn Fn()>>,
    pub hor: bool,
    pub gap: u32,
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
            hor: false,
            gap: 0,
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

pub struct UiRuntime {
    pub nodes: Vec<Node>,
    pub buffer: Vec<u32>,
    pub layout: Vec<LayoutBox>,
    pub hovering: Option<usize>,
}

impl UiRuntime {
    pub fn apply_hovering(&mut self, position: Position) {
        for layout_box in self.layout.iter().rev() {
            let start_x = layout_box.x;
            let start_y = layout_box.y;
            let end_x = start_x + layout_box.width as i32;
            let end_y = start_y + layout_box.height as i32;

            if matches!(&self.nodes[layout_box.node_idx], Node::Element(_))
                && position.x >= start_x
                && position.x < end_x
                && position.y >= start_y
                && position.y < end_y
            {
                self.hovering = Some(layout_box.node_idx);
                return;
            }
        }
        self.hovering = None;
    }

    pub fn on_click(&mut self) {
        let Some(hovering) = self.hovering else {
            return;
        };
        let mut outer_node = Some(&self.nodes[hovering]);
        while let Some(node) = outer_node {
            if let Node::Element(element) = node {
                if let Some(cb) = &element.on_click {
                    cb();
                }
            };
            outer_node = node.get_parent().map(|parent| &self.nodes[parent]);
        }
    }
}

impl UiBuilder {
    pub fn new(width: u32, height: u32) -> Result<Self> {
        Ok(Self {
            curr: None,
            nodes: vec![],
            width,
            height,
            font_handler: Rc::new(FontHandler::new()?),
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
        self.curr_element_mut()?.hor = true;
        Ok(())
    }

    pub fn gap(&mut self, gap: u32) -> Result<()> {
        self.curr_element_mut()?.gap = gap;
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

    fn render_node(
        &self,
        layouts: &mut Vec<LayoutBox>,
        mut cursor: (i32, i32),
        node_idx: usize,
        children_index: &HashMap<usize, Vec<usize>>,
        horizontal: bool,
    ) -> Result<()> {
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
                });

                cursor.0 += el.padding as i32;
                cursor.1 += el.padding as i32;

                if let Some(children) = children_index.get(&node_idx) {
                    for child in children {
                        self.render_node(layouts, cursor, *child, children_index, el.hor)?;

                        let child_node = &self.nodes[*child];
                        if let Node::Element(child_el) = child_node {
                            if horizontal {
                                cursor.0 += child_el.width as i32 + el.gap as i32;
                            } else {
                                cursor.1 += child_el.height as i32 + el.gap as i32;
                            }
                        }
                    }
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
                });
            }
        };
        Ok(())
    }

    pub fn render(&mut self) -> Result<UiRuntime> {
        let mut buffer = vec![0; (self.width * self.height) as usize];
        let cursor = (0, 0);
        let mut children_index: HashMap<usize, Vec<usize>> = HashMap::new();
        for (idx, node) in self.nodes.iter().enumerate() {
            if let Some(parent) = node.get_parent() {
                children_index.entry(parent).or_default().push(idx);
            }
        }
        // Start on root node
        let mut layouts = vec![];
        let hor = if let Node::Element(el) = &self.nodes[0] {
            el.hor
        } else {
            false
        };
        self.render_node(&mut layouts, cursor, 0, &children_index, hor)?;
        for layout in layouts.iter() {
            match &layout.kind {
                LayoutKind::Element => {
                    draw_rect_filled(
                        &mut buffer,
                        true,
                        self.width,
                        self.height,
                        layout.x as i32,
                        layout.y as i32,
                        layout.width,
                        layout.height,
                        layout.bg_color,
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
                            *dst = blend_rgba_with_rgba(
                                *dst,
                                (pixel.red(), pixel.green(), pixel.blue(), pixel.alpha()),
                            );
                        }
                    }
                }
            }
        }
        Ok(UiRuntime {
            layout: layouts,
            buffer,
            nodes: self.nodes.drain(..).collect(),
            hovering: None,
        })
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
}

mod tests {
    use std::{cell::Cell, num::NonZero, rc::Rc, sync::Arc};

    use anyhow::{Context, Result, anyhow};
    use raw_window_handle::{HasDisplayHandle, HasWindowHandle};
    use softbuffer::{Context as SoftContext, Surface};
    use winit::{dpi::PhysicalSize, event_loop::EventLoopBuilder, window::WindowBuilder};

    use crate::{Position, ensure_snapshot_matches, ui::UiBuilder};

    #[test]
    fn renders() -> Result<()> {
        let mut builder = UiBuilder::new(1920, 1080)?;
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

        let runtime = builder.render()?;

        ensure_snapshot_matches(&runtime.buffer, "UiBuilder", 1920, 1080)?;

        Ok(())
    }
}
