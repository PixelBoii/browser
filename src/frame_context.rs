// Isolated example; not yet used by iframe creation.
#![allow(dead_code)]

use std::cell::RefCell;
use std::rc::Rc;

use deno_core::{JsRuntime, v8};
use deno_error::JsErrorBox;

use crate::{JsHostState, custom_elements, mutation_observer};

// Deno uses slots 1 and 2 for its context state and module map.
const FRAME_STATE_SLOT_INDEX: i32 = 3;

struct FrameState {
    host: JsHostState,
    custom_elements: custom_elements::Registry,
    mutation_observers: mutation_observer::Callbacks,
}

#[derive(Default)]
struct FrameStates(Vec<Rc<RefCell<FrameState>>>);

/// Creates a same-origin child context of the runtime's main window.
///
/// V8 supplies the child's built-ins, including Promise and native eval.
/// `initialize` runs inside the child and must install its browser globals and
/// bind DOM operations to its FrameState. The existing runtime.js bootstrap and
/// DOM operations are not yet adapted to do that.
pub(crate) fn create_frame_context(
    runtime: &mut JsRuntime,
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
    let op_state = runtime.op_state();
    {
        let mut state = op_state.borrow_mut();
        if !state.has::<FrameStates>() {
            state.put(FrameStates::default());
        }
        state.borrow_mut::<FrameStates>().0.push(frame.clone());
    }

    deno_core::scope!(scope, runtime);
    let parent = scope.get_current_context();
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
