use deno_core::{OpState, op2};
use deno_error::JsErrorBox;
use url::Origin;

use crate::{
    Frame, FrameCommand, JsHostState, RendererProxy, ReqwestUrl, UserEvent, WorkerMessage,
    js_string_literal,
};

#[derive(Debug, Clone)]
pub(crate) struct ParentWindow {
    pub proxy: RendererProxy,
    pub node_idx: usize,
    pub origin: Origin,
}

#[derive(Debug)]
enum MessageSource {
    Window,
    Parent,
    Frame(usize),
}

#[derive(Debug)]
pub struct WindowMessage {
    data: WorkerMessage,
    origin: String,
    target_origin: Option<Origin>,
    source: MessageSource,
}

impl WindowMessage {
    fn take(
        state: &mut OpState,
        data: deno_web::JsMessageData,
        target_origin: &str,
        source: MessageSource,
    ) -> Result<Self, JsErrorBox> {
        let origin = state
            .borrow::<JsHostState>()
            .renderer
            .borrow()
            .origin
            .clone();
        let target_origin = match target_origin {
            "*" => None,
            "/" => Some(origin.clone()),
            value => Some(
                ReqwestUrl::parse(value)
                    .map_err(|_| {
                        JsErrorBox::new(
                            "DOMExceptionSyntaxError",
                            "Invalid postMessage target origin",
                        )
                    })?
                    .origin(),
            ),
        };
        Ok(Self {
            data: WorkerMessage::take(state, data)?,
            origin: origin.ascii_serialization(),
            target_origin,
            source,
        })
    }
}

#[op2(fast)]
pub(crate) fn op_is_top(state: &mut OpState) -> bool {
    state.borrow::<JsHostState>().parent_window.is_none()
}

#[op2]
pub(crate) fn op_post_message_to_parent(
    state: &mut OpState,
    #[serde] data: deno_web::JsMessageData,
    #[string] target_origin: &str,
) -> Result<(), JsErrorBox> {
    let host = state.borrow::<JsHostState>();
    let (proxy, source) = match &host.parent_window {
        Some(parent) => (parent.proxy.clone(), MessageSource::Frame(parent.node_idx)),
        None => (host.proxy.clone(), MessageSource::Window),
    };
    let message = WindowMessage::take(state, data, target_origin, source)?;
    let _ = proxy.fire_user_event(UserEvent::WindowMessage(message));
    Ok(())
}

#[op2]
pub(crate) fn op_post_message_to_frame(
    state: &mut OpState,
    #[serde] data: deno_web::JsMessageData,
    #[number] frame_id: Option<usize>,
    #[string] target_origin: &str,
) -> Result<(), JsErrorBox> {
    let source = if frame_id.is_some() {
        MessageSource::Parent
    } else {
        MessageSource::Window
    };
    let message = WindowMessage::take(state, data, target_origin, source)?;
    let host = state.borrow::<JsHostState>();
    if let Some(frame_id) = frame_id {
        if let Some(frame) = host.renderer.borrow().frames.get(&frame_id) {
            let _ = frame
                .tx
                .send(FrameCommand::UserEvent(UserEvent::WindowMessage(message)));
        }
    } else {
        let _ = host
            .proxy
            .fire_user_event(UserEvent::WindowMessage(message));
    }
    Ok(())
}

impl Frame {
    pub(crate) fn dispatch_window_message(&mut self, message: WindowMessage) {
        // Check the receiver at delivery time: it may have navigated since the send.
        if message
            .target_origin
            .as_ref()
            .is_some_and(|origin| *origin != self.renderer.as_ref().unwrap().borrow().origin)
        {
            return;
        }
        let source = match message.source {
            MessageSource::Window => "\"window\"".to_owned(),
            MessageSource::Parent => "\"parent\"".to_owned(),
            MessageSource::Frame(idx) => idx.to_string(),
        };
        let origin = js_string_literal(&message.origin);
        let state = self.js_runtime.as_ref().unwrap().borrow().op_state();
        state.borrow_mut().put(message.data);
        let code = format!("__dispatchWindowMessage({source}, {origin})");
        if let Err(err) = self.execute_host_script("window message handler", code) {
            eprintln!("Failed to dispatch window message: {err}");
        }
        state.borrow_mut().try_take::<WorkerMessage>();
    }
}
