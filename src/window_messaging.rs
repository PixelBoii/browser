use deno_core::{OpState, op2, v8};
use deno_error::JsErrorBox;
use url::Origin;

use crate::frame_context::{
    WindowSources, context_origin, frame_host, window_for_origin, window_id,
};
use crate::{Frame, RendererProxy, ReqwestUrl, UserEvent, WorkerMessage, js_string_literal};

#[derive(Debug, Clone)]
pub(crate) struct ParentWindow {
    pub proxy: RendererProxy,
    pub node_idx: usize,
}

#[derive(Debug)]
pub struct WindowMessage {
    data: WorkerMessage,
    origin: String,
    target_origin: Option<Origin>,
    source: usize,
}

impl WindowMessage {
    fn take(
        state: &mut OpState,
        origin: &Origin,
        data: deno_web::JsMessageData,
        target_origin: &str,
        source: usize,
    ) -> Result<Self, JsErrorBox> {
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

#[op2]
pub(crate) fn op_window_post_message(
    scope: &mut v8::PinScope,
    state: &mut OpState,
    #[serde] data: deno_web::JsMessageData,
    #[string] target_origin: &str,
) -> Result<(), JsErrorBox> {
    let caller = scope.get_entered_or_microtask_context();
    let origin = context_origin(caller);
    let source = window_id(caller);
    let host = frame_host(scope);
    let message = WindowMessage::take(state, &origin, data, target_origin, source)?;
    let _ = host
        .proxy
        .fire_user_event(UserEvent::WindowMessage(message));
    Ok(())
}

#[op2]
pub(crate) fn op_window_message_source<'s>(
    scope: &mut v8::PinScope<'s, '_>,
    state: &mut OpState,
    #[number] id: usize,
) -> Option<v8::Local<'s, v8::Value>> {
    let context = v8::Local::new(scope, state.borrow::<WindowSources>().0.get(id)?);
    let origin = context_origin(scope.get_current_context());
    Some(window_for_origin(scope, context, &origin))
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
        let origin = js_string_literal(&message.origin);
        let state = self.js_runtime.as_ref().unwrap().op_state();
        state.borrow_mut().put(message.data);
        let code = format!("__dispatchWindowMessage({}, {origin})", message.source);
        if let Err(err) = self.execute_host_script("window message handler", code) {
            eprintln!("Failed to dispatch window message: {err}");
        }
        state.borrow_mut().try_take::<WorkerMessage>();
    }
}
