use std::cell::{Cell, RefCell};
use std::rc::Rc;

use anyhow::Result;
use deno_core::{JsRuntime, v8};

use crate::window_messaging::ParentWindow;
use crate::{
    Frame, FrameCommand, FrameHandle, FrameSurface, JsHostState, PreparedFrame, RendererProxy,
    custom_elements, mutation_observer,
};

// Deno resources remain in the runtime's OpState. DOM bindings and their V8
// handles belong to the document context and live until that context is destroyed.
pub(crate) struct FrameState {
    pub host: Rc<JsHostState>,
    pub custom_elements: custom_elements::Registry,
    pub mutation_observers: mutation_observer::Callbacks,
    window_id: usize,
    cross_origin_window: v8::Global<v8::Value>,
    active: bool,
    connected: Rc<Cell<bool>>,
    parent: Option<Rc<RefCell<FrameState>>>,
}

#[derive(Default)]
pub(crate) struct WindowSources(pub Vec<v8::Global<v8::Context>>);

pub(crate) fn window_id(context: v8::Local<v8::Context>) -> usize {
    context
        .get_slot::<RefCell<FrameState>>()
        .unwrap()
        .borrow()
        .window_id
}

pub(crate) fn is_active(scope: &mut v8::PinScope) -> bool {
    // Workers have no document state and remain active until their runtime closes.
    let mut state = scope
        .get_current_context()
        .get_slot::<RefCell<FrameState>>();
    while let Some(frame) = state {
        let frame = frame.borrow();
        if !frame.active || !frame.connected.get() {
            return false;
        }
        state = frame.parent.clone();
    }
    true
}

#[deno_core::op2(fast)]
pub(crate) fn op_realm_is_active(scope: &mut v8::PinScope) -> bool {
    is_active(scope)
}

pub(crate) fn deactivate_realm(scope: &mut v8::PinScope) {
    // The fork retains realms until runtime drop. Stop browser callbacks here;
    // queued Promise jobs and pending Deno ops are not cancelled.
    {
        let frame = frame_state(scope);
        let mut frame = frame.borrow_mut();
        if !frame.active {
            return;
        }
        frame.active = false;
        let mut renderer = frame.host.renderer.borrow_mut();
        renderer.frames.clear();
        renderer.workers.clear();
    }
    if let Err(err) = crate::run_v8_source(scope, "close frame realm", "__clear_all_timers()") {
        eprintln!("Failed to close iframe realm: {err}");
    }
}

pub(crate) fn frame_state(scope: &mut v8::PinScope) -> Rc<RefCell<FrameState>> {
    scope
        .get_current_context()
        .get_slot::<RefCell<FrameState>>()
        .unwrap()
}

pub(crate) fn frame_host(scope: &mut v8::PinScope) -> Rc<JsHostState> {
    frame_state(scope).borrow().host.clone()
}

pub(crate) fn context_origin(context: v8::Local<v8::Context>) -> url::Origin {
    context
        .get_slot::<RefCell<FrameState>>()
        .unwrap()
        .borrow()
        .host
        .renderer
        .borrow()
        .origin
        .clone()
}

pub(crate) fn caller_origin(scope: &mut v8::PinScope) -> url::Origin {
    context_origin(scope.get_entered_or_microtask_context())
}

pub(crate) fn window_for_origin<'s>(
    scope: &mut v8::PinScope<'s, '_>,
    context: v8::Local<'s, v8::Context>,
    origin: &url::Origin,
) -> v8::Local<'s, v8::Value> {
    if context_origin(context) == *origin {
        context.global(scope).into()
    } else {
        let frame = context.get_slot::<RefCell<FrameState>>().unwrap();
        v8::Local::new(scope, &frame.borrow().cross_origin_window)
    }
}

pub(crate) fn bind_frame_state(
    scope: &mut v8::PinScope,
    host: JsHostState,
    connected: Rc<Cell<bool>>,
    parent_context: Option<&v8::Global<v8::Context>>,
) {
    let parent = parent_context.map(|context| {
        v8::Local::new(scope, context)
            .get_slot::<RefCell<FrameState>>()
            .unwrap()
    });
    let context = scope.get_current_context();
    let window = context.global(scope);
    let key = v8::String::new(scope, "__crossOriginWindow").unwrap();
    let cross_origin_window = window.get(scope, key.into()).unwrap();
    let cross_origin_window = v8::Global::new(scope, cross_origin_window);
    let shared = JsRuntime::op_state_from(scope);
    let mut shared = shared.borrow_mut();
    let sources = shared.borrow_mut::<WindowSources>();
    let window_id = sources.0.len();
    sources.0.push(v8::Global::new(scope, context));
    context.set_slot(Rc::new(RefCell::new(FrameState {
        host: Rc::new(host),
        custom_elements: custom_elements::Registry::default(),
        mutation_observers: mutation_observer::Callbacks::default(),
        window_id,
        cross_origin_window,
        active: true,
        connected,
        parent,
    })));
}

pub fn spawn_frame(
    scope: &mut v8::PinScope,
    parent_context: &v8::Global<v8::Context>,
    init: PreparedFrame,
) -> Result<FrameHandle> {
    let (tx, rx) = std::sync::mpsc::channel();
    let surface = Rc::new(RefCell::new(FrameSurface {
        size: init.size,
        pixels: vec![0; (init.size.width * init.size.height) as usize],
    }));
    tx.send(FrameCommand::Render).unwrap();
    let tx_proxy = RendererProxy::FrameLoop(tx.clone());
    let parent_window = ParentWindow {
        proxy: init.parent_proxy.clone(),
        node_idx: init.node_idx,
    };
    let mut frame = Frame::new("about:blank".to_string(), false, init.size);
    frame.parent_window = Some(parent_window);
    frame.window_name = init.window_name;

    frame.open_as_context(scope, parent_context, tx_proxy)?;
    let command = if init.url.as_str() == "about:blank" {
        FrameCommand::Initialize
    } else {
        FrameCommand::UserEvent(crate::UserEvent::Navigate((
            crate::UserNavigateUrl::Raw(init.url.to_string()),
            true,
        )))
    };
    tx.send(command).unwrap();

    let Some(crate::FrameJs::Shared(shared)) = &frame.js_runtime else {
        unreachable!()
    };
    Ok(FrameHandle {
        surface,
        requested_size: init.size,
        requested_url: init.url,
        tx,
        js: shared.clone(),
        frame: Rc::new(RefCell::new(frame)),
        rx,
    })
}
