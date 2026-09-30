// Isolated example; not yet used by iframe creation.
#![allow(dead_code)]

use std::sync::Mutex;
use std::time::Instant;
use std::{cell::RefCell, sync::Arc};
use std::rc::Rc;

use anyhow::Result;
use deno_core::{JsRuntime, v8};
use deno_error::JsErrorBox;

use crate::window_messaging::ParentWindow;
use crate::{Frame, FrameCommand, FrameHandle, FrameSurface, JsHostState, PreparedFrame, RendererProxy, UserEvent, collect_frame_commands, custom_elements, mutation_observer};

// Deno uses slots 1 and 2 for its context state and module map.
const FRAME_STATE_SLOT_INDEX: i32 = 3;

struct FrameState {
    host: JsHostState,
    custom_elements: custom_elements::Registry,
    mutation_observers: mutation_observer::Callbacks,
}

#[derive(Default)]
struct FrameStates(Vec<Rc<RefCell<FrameState>>>);

/// Creates a same-origin child context of the supplied parent window.
///
/// V8 supplies the child's built-ins, including Promise and native eval.
/// `initialize` runs inside the child and must install its browser globals and
/// bind DOM operations to its FrameState. The existing runtime.js bootstrap and
/// DOM operations are not yet adapted to do that.
pub(crate) fn create_frame_context(
    scope: &mut v8::PinScope,
    parent_context: &v8::Global<v8::Context>,
    host: JsHostState,
    initialize: impl FnOnce(&mut v8::PinScope) -> Result<(), JsErrorBox>,
) -> Result<v8::Global<v8::Context>, JsErrorBox> {
    let frame = Rc::new(RefCell::new(FrameState {
        host,
        custom_elements: custom_elements::Registry::default(),
        mutation_observers: mutation_observer::Callbacks::default(),
    }));

    // A retained JS function can outlive its iframe, so keep the host state
    // until the runtime is dropped, including if initialization fails.
    let op_state = JsRuntime::op_state_from(scope);
    {
        let mut state = op_state.borrow_mut();
        if !state.has::<FrameStates>() {
            state.put(FrameStates::default());
        }
        state.borrow_mut::<FrameStates>().0.push(frame.clone());
    }

    let parent = v8::Local::new(scope, parent_context);
    let context = v8::Context::new(scope, Default::default());
    context.set_security_token(parent.get_security_token(scope));
    context.set_microtask_queue(parent.get_microtask_queue());

    // SAFETY: Deno owns the shared pointers for this runtime's lifetime.
    // FrameStates retains the aligned frame allocation for that same lifetime.
    // These slots borrow the pointers; they never take ownership of them.
    unsafe {
        for slot in [
            deno_core::CONTEXT_STATE_SLOT_INDEX,
            deno_core::MODULE_MAP_SLOT_INDEX,
        ] {
            context.set_aligned_pointer_in_embedder_data(
                slot,
                parent.get_aligned_pointer_from_embedder_data(slot),
            );
        }
        context.set_aligned_pointer_in_embedder_data(
            FRAME_STATE_SLOT_INDEX,
            Rc::as_ptr(&frame).cast_mut().cast(),
        );
    }
    // Raw slot setters also allocate an unused Rust slot table with a GC
    // finalizer. Remove that table; the raw pointers above remain installed.
    context.clear_all_slots();

    let scope = &mut v8::ContextScope::new(scope, context);
    let window = context.global(scope);
    for (name, value) in [
        ("window", window),
        ("self", window),
        ("parent", parent.global(scope)),
    ] {
        let key = v8::String::new(scope, name).unwrap();
        window.set(scope, key.into(), value.into());
    }
    initialize(scope)?;

    Ok(v8::Global::new(scope, context))
}

pub fn spawn_frame(
    scope: &mut v8::PinScope,
    parent_context: &v8::Global<v8::Context>,
    init: PreparedFrame,
) -> Result<FrameHandle> {
    let (tx, rx) = std::sync::mpsc::channel();
    let latest_bitmap = Arc::new(Mutex::new(FrameSurface {
        size: init.size,
        pixels: vec![0; (init.size.width * init.size.height) as usize],
    }));
    let bitmap_for_thread = Arc::clone(&latest_bitmap);
    tx.send(FrameCommand::Render).unwrap();
    let tx_proxy = RendererProxy::FrameLoop(tx.clone());
    let parent_window = ParentWindow {
        proxy: init.parent_proxy.clone(),
        node_idx: init.node_idx,
        origin: init.origin,
    };
    if init.url.as_str() == "about:blank" {
        let mut frame = Frame::new(init.url.to_string(), false, init.size);
        frame.parent_window = Some(parent_window);
        frame.window_name = init.window_name;

        let frame_result = frame.open_as_context(scope, parent_context, tx_proxy);
        match frame_result {
            Ok(()) => {}
            Err(err) => {
                eprintln!("Failed to boot iframe frame: {:?}", err);
            }
        };

        Ok(FrameHandle {
            surface: latest_bitmap,
            requested_size: init.size,
            tx,
            frame: Some(Rc::new(RefCell::new(frame))),
            rx: Some(rx),
        })
    } else {
        std::thread::spawn(move || {
            let mut frame = Frame::new(init.url.to_string(), false, init.size);
            frame.parent_window = Some(parent_window);
            frame.window_name = init.window_name;

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
            let _ = init.parent_proxy.fire_user_event(UserEvent::FrameLoaded(init.node_idx));

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
                for cmd in collect_frame_commands(cmd, &rx) {
                    if matches!(cmd, FrameCommand::Close) {
                        return;
                    }
                    frame.handle_frame_command(cmd, &init.parent_proxy, &bitmap_for_thread);
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
                js_pending |= frame.poll_shared_frames();
            }
        });

        Ok(FrameHandle {
            surface: latest_bitmap,
            requested_size: init.size,
            tx,
            frame: None,
            rx: None,
        })
    }
}
