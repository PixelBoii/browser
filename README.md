# [WIP] Browser written in Rust
- Handwritten HTML and CSS engine
- Deno as JS runtime
- resvg for SVG rendering
- ab_glyph for font rendering (Only Inter supported for now)

The `browser` crate also exposes individual headless frames for embedding:

```rust
let frame = browser::Frame::open_headless("about:blank".into())?;
// The frame runs on its own Rust thread while this handle is alive.
drop(frame); // Requests shutdown without blocking.
```

Headless startup reuses the frame setup used by the rendering tests and creates
no Winit event loop or window. `cargo run` continues to launch the desktop browser.
