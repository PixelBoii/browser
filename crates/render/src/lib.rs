use std::{path::Path, rc::Rc};

use ab_glyph::{Font, FontRef, Glyph, OutlinedGlyph, ScaleFont};
use anyhow::Result;
use resvg::tiny_skia::{IntSize, Pixmap};

#[derive(Debug, Clone)]
pub struct BorderRadius {
    pub top_left: u32,
    pub top_right: u32,
    pub bottom_right: u32,
    pub bottom_left: u32,
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

#[derive(Debug, Clone, Copy)]
pub struct PaintClip {
    pub start_x: i32,
    pub start_y: i32,
    pub end_x: i32,
    pub end_y: i32,
}

impl PaintClip {
    pub fn viewport(width: u32, height: u32) -> Self {
        Self {
            start_x: 0,
            start_y: 0,
            end_x: i32::try_from(width).unwrap_or(i32::MAX),
            end_y: i32::try_from(height).unwrap_or(i32::MAX),
        }
    }

    pub fn intersect_x(mut self, start_x: i32, end_x: i32) -> Self {
        self.start_x = self.start_x.max(start_x);
        self.end_x = self.end_x.min(end_x);
        self
    }

    pub fn intersect_y(mut self, start_y: i32, end_y: i32) -> Self {
        self.start_y = self.start_y.max(start_y);
        self.end_y = self.end_y.min(end_y);
        self
    }

    pub fn is_empty(self) -> bool {
        self.start_x >= self.end_x || self.start_y >= self.end_y
    }
}

#[derive(Debug)]
pub struct FontHandler {
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

pub fn blend_rgba_with_rgba(dst: u32, src: (u8, u8, u8, u8)) -> u32 {
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

pub fn blend_rgb_with_rgba(dst: u32, src: (u8, u8, u8, u8)) -> u32 {
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

pub fn text_to_buffer(
    font_handler: &Rc<FontHandler>,
    color: u32,
    text: &String,
    font_px: u32,
    max_width: Option<u32>,
) -> Option<(Pixmap, u32, u32)> {
    text_to_buffer_with_line_height(font_handler, color, text, font_px, max_width, None)
}

pub fn text_to_buffer_with_line_height(
    font_handler: &Rc<FontHandler>,
    color: u32,
    text: &String,
    font_px: u32,
    max_width: Option<u32>,
    line_height_px: Option<u32>,
) -> Option<(Pixmap, u32, u32)> {
    let scaled_font = font_handler.font.as_scaled(font_px as f32);
    let mut width = 0f32;
    let mut pen_x = 0f32;
    let mut pen_y = 0f32;
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
        if max_width.is_some_and(|max_width| pen_x + advance >= max_width as f32) && ch == ' ' {
            pen_x = 0.;
            pen_y += line_height;
        } else {
            pen_x += advance;
            width = width.max(pen_x);
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

struct GlyphPosition {
    x: f32,
    y: f32,
    glyph: OutlinedGlyph,
}

fn with_coverage(color: u32, coverage: f32) -> u32 {
    let alpha = color & 0xFF;
    let covered_alpha = ((alpha as f32) * coverage.clamp(0.0, 1.0)).round() as u32;
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
    glyph.draw(|glyph_x, glyph_y, coverage| {
        draw_rect_filled(
            buffer,
            true,
            width,
            height,
            x + glyph_x as i32,
            y + glyph_y as i32,
            1,
            1,
            with_coverage(color, coverage),
            &BorderRadius::new_empty(),
        );
    });
}

pub fn premul_rgba_buffer_to_bytes(buffer: &[u32]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(buffer.len() * 4);
    for pixel in buffer {
        let [r, g, b, a] = pixel.to_be_bytes();
        bytes.extend_from_slice(&[r, g, b, a]);
    }
    bytes
}

pub fn rgba_to_premul_tuple(src: u32) -> (u8, u8, u8, u8) {
    let [r, g, b, a] = src.to_be_bytes();
    let r = (r as u32 * a as u32 / 255) as u8;
    let g = (g as u32 * a as u32 / 255) as u8;
    let b = (b as u32 * a as u32 / 255) as u8;
    (r, g, b, a)
}

pub fn rgba_buffer_to_premul_bytes(buffer: &[u32]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(buffer.len() * 4);
    for pixel in buffer {
        let (r, g, b, a) = rgba_to_premul_tuple(*pixel);
        bytes.extend_from_slice(&[r, g, b, a]);
    }
    bytes
}

pub fn rgb_to_premul_tuple(src: u32) -> (u8, u8, u8, u8) {
    let [_, r, g, b] = src.to_be_bytes();
    (r, g, b, 255)
}

pub fn rgb_buffer_to_premul_bytes(buffer: &[u32]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(buffer.len() * 4);
    for pixel in buffer {
        let (r, g, b, a) = rgb_to_premul_tuple(*pixel);
        bytes.extend_from_slice(&[r, g, b, a]);
    }
    bytes
}

pub fn ensure_snapshot_matches(
    buffer: &[u32],
    snapshot_dir: impl AsRef<Path>,
    name: &str,
    width: u32,
    height: u32,
) -> Result<()> {
    let snapshot_path = snapshot_dir.as_ref().join(format!("{name}.png"));
    let pixmap = Pixmap::from_vec(
        rgb_buffer_to_premul_bytes(buffer),
        IntSize::from_wh(width, height)
            .ok_or_else(|| anyhow::anyhow!("Failed to create IntSize"))?,
    )
    .ok_or_else(|| anyhow::anyhow!("Failed to create pixmap"))?;

    if snapshot_path.exists() {
        let snapshot = Pixmap::load_png(&snapshot_path)?;
        if pixmap.width() == snapshot.width()
            && pixmap.height() == snapshot.height()
            && pixmap.data() == snapshot.data()
        {
            return Ok(());
        }

        let invalid_path = snapshot_dir.as_ref().join(format!("{name}.invalid.png"));
        pixmap.save_png(&invalid_path)?;
        return Err(anyhow::anyhow!(
            "Pixmap did not match saved snapshot. Saved invalid file in {invalid_path:?}"
        ));
    }

    pixmap.save_png(&snapshot_path)?;
    Err(anyhow::anyhow!("No snapshot existed. Created one now."))
}

#[allow(clippy::too_many_arguments)]
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

#[allow(clippy::too_many_arguments)]
pub fn draw_rect_filled_clipped(
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
                row[px as usize] = if buffer_rgba {
                    blend_rgba_with_rgba(row[px as usize], color_tuple)
                } else {
                    blend_rgb_with_rgba(row[px as usize], color_tuple)
                };
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
