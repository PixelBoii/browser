# Running same-origin frames on one event loop

A same-origin iframe needs its own document and JavaScript globals. It can run on the same thread, V8 isolate, and event loop as its parent. The next step is to give a child frame a context and make the existing runtime owner drive its work.

Today, `Renderer::spawn_frame` starts a thread. That thread creates a `Frame`, calls `open()` to create its Tokio and Deno runtimes, and runs a command loop. Each iframe independently pumps JavaScript, delivers animation callbacks, and paints a bitmap for its parent.

The unused constructor in `src/frame_context.rs` supplies the context creation mechanism. This article describes the integration still needed. The Rust examples are design sketches; proposed helpers and variants are not implemented APIs.

Consider this page code:

```js
const iframe = document.createElement("iframe");
document.body.appendChild(iframe);
const child = iframe.contentWindow;

child.eval(`
    const message = document.createElement("p");
    document.body.appendChild(message);

    requestAnimationFrame(() => {
        setTimeout(() => {
            message.textContent = "The child timer ran";
            Promise.resolve().then(() => {
                message.style.color = "green";
            });
        }, 20);
    });
`);
```

The parent has finished its script. The child still needs an animation callback, a timer callback, a Promise microtask, and a repaint. All of that must progress while the parent document is idle.

A frame can keep its existing renderer, viewport, script tracking, and animation state. Its JavaScript execution mode needs one distinction:

```rust
enum FrameJs {
    Owned(Rc<RefCell<JsRuntime>>),
    Shared(v8::Global<v8::Context>),
}
```

The `Owned` frame drives Deno and Tokio. A `Shared` frame uses its context whenever browser code enters JavaScript for that document. Its renderer can receive the owner's existing Tokio handle, but child setup must skip runtime creation and child code must not start another `block_on` or event-loop pump.

The owner retains the local child `Frame` objects. A registry exposes their context and `FrameState` handles to native ops, so an op does not need to borrow the currently executing `Frame`. Registry borrows must end before calling JavaScript. Renderers keep the handles and surfaces needed to find or draw children; existing threaded children can keep their channel handles.

Nested shared frames use the same owner. If A owns the runtime, B is A's child, and C is B's child, A drives all three contexts. C's `parent` is still B's window. A cross-origin frame running on its own thread can become the owner for its own same-origin children.

The main window also needs a `FrameState`. Otherwise, every DOM operation needs separate rules for the main document and its children. Each state's `JsHostState`, custom-element registry, and observer callbacks belong to its document. Deno resources and internal event-loop bookkeeping stay shared.

Creating the child must work during a JavaScript call. Our `contentWindow` getter currently calls `op_spawn_frame`. A page can immediately call `.eval()` on the returned window, so preparing that window cannot wait for a later scheduler tick.

The example constructor currently accepts `&mut JsRuntime` and selects its main context. Integration needs an internal constructor accepting the active V8 scope and the actual parent context. The runtime is already executing the native op; borrowing it again through `Rc<RefCell<JsRuntime>>` would conflict with the existing borrow.

The creation path would look like this:

```rust
// Inside a reentrant DOM op, with renderer borrows released.
let parent = context_for_frame(scope, parent_id)?;
let host = prepare_blank_frame(parent_id, iframe_node_idx)?;
let child = create_frame_context_in_scope(scope, parent, host)?;
let window = child.open(scope).global(scope);
register_child(parent_id, iframe_node_idx, child);
// Return `window` directly to JavaScript.
```

`prepare_blank_frame` builds the empty document, renderer, host state, and event destination. The context constructor attaches that state, shares the owner's Deno bookkeeping and microtask queue, installs the window globals, and runs the browser initializer. Registration associates the iframe element with the child so repeated accesses return the same global. Load events can be queued for later delivery.

There is a second creation path to handle: layout currently calls `Renderer::spawn_frame` when it discovers an iframe. Bootstrapping a context there would run JavaScript while the renderer is mutably borrowed. Frame preparation should move to the owning browser layer, after parsing or DOM updates and before painting. The `contentWindow` path can ensure creation synchronously when requested. Both paths must reuse the same child entry.

The initializer is a real prerequisite. `runtime.js` currently combines shared Deno setup with per-window state. DOM constructors, wrapper caches, timer bookkeeping, and window event handlers must be initialized separately for each child. Internal Deno event-loop hooks remain registered once.

The per-window bootstrap must be compiled in the child context. Calling a function created in the parent with the child as `this` does not change that function's lexical globals. Reimporting the same module from a shared module map also does not produce a fresh window environment. Shared services can be passed into code compiled in the child; modules that save a global window reference need attention during that split.

Native operations need an explicit target frame. The existing operations read a single `JsHostState` from `OpState`. V8's current context alone is insufficient when a shared native function was created in the main context.

For example, the child bootstrap can capture a frame identifier in its private bindings:

```js
const ops = {
    createElement: tag => native.createElement(frameId, tag),
    requestAnimationFrame: () => native.requestAnimationFrame(frameId),
};
```

The native side resolves `frameId` to the retained `FrameState`. Window operations use that window's identifier; node operations use the owning document of the receiver. This distinction matters when a parent calls a method on a child document. Node indices alone are insufficient because both documents can contain node 12.

A shared child's DOM operations execute directly on the owning thread. They cannot use the existing `js_send_onetime_to_frame` request/reply path: waiting for a reply from the same thread would stall until the timeout. Native code must also release renderer and state borrows before invoking custom-element constructors or other JavaScript callbacks, which can reenter the DOM.

Queued browser events still need a destination. The owner can allocate a `FrameId` for each local frame and route child events through its existing command queue:

```rust
owner_tx.send(FrameCommand::ForFrame {
    frame_id,
    event: UserEvent::AnimationFrameRequested,
})?;
owner_notify.notify_one();
```

That identifier is unique within the runtime's frame registry. The iframe's node index remains local to its parent's document. Commands carry identifiers and event data; the V8 handles remain on the owning thread.

The channel wakes an owner waiting for commands. A shared `Notify` also interrupts the owner's bounded Tokio/Deno pump. Each child renderer must use that notification source instead of keeping a private notification that nobody awaits. DOM updates, canvas updates, animation requests, and resource completions can then wake the same driver while retaining their target frame.

Deno is pumped once for the whole group. Child timers registered through the shared Deno timer service are handled by that pump. V8 functions retain their creation context, so a timer callback created by `child.eval` executes with the child's globals even though the owner drove the event loop.

Browser-triggered work needs an explicit context entry. `JsRuntime::execute_script` uses its main realm. Calls from `execute_host_script`, `set_current_script`, and classic-script execution must go through a helper that selects the target context and compiles there. For example, the owner would invoke a child's animation callbacks like this:

```rust
deno_core::scope!(scope, runtime);
let context = v8::Local::new(scope, &child_context);
let scope = &mut v8::ContextScope::new(scope, context);
run_v8_source(
    scope,
    "child animation callbacks",
    "__run_animation_frame(performance.now())",
)?;
```

This happens from the outer browser driver, where borrowing the runtime is valid. It is different from creating a child inside an already executing native op, where the active scope must be reused.

The existing command loop can remain the driver. Its work becomes group-wide:

```rust
let mut js_pending = true;
loop {
    let commands = receive_commands(wait_timeout(
        js_pending,
        earliest_animation_deadline(),
    ));
    for command in commands {
        dispatch_to_target_frame(command)?;
    }

    js_pending = pump_shared_runtime_once()?;

    for frame_id in due_animation_frames() {
        run_animation_callbacks(frame_id)?;
        js_pending = true;
    }
    js_pending |= update_documents_and_paint()?;
}
```

This is a scheduling sketch, not a complete implementation of HTML task ordering. `earliest_animation_deadline` covers all attached local frames. In this sketch, `update_documents_and_paint` reports whether it entered JavaScript, such as executing a newly inserted script or delivering a load event. Work after the Deno pump must request another pump if it could have started asynchronous work.

That last rule is essential for the opening example. Deno can report idle before the child's animation callback runs. The animation callback then creates a timer. If the owner trusts the earlier idle result, it may wait indefinitely for another browser command while the timer has no opportunity to run. The current main-frame loop already sets `js_pending = true` after animation callbacks; the shared loop must apply that rule to every frame.

Keep the existing bounded Tokio pumping approach initially. A current-thread Tokio runtime drives I/O while `block_on` is active; merely entering it does not advance timers or sockets. `pump_js_event_loop_once` already allows a short slice, capped at 10 ms, and can return early on a notification. Its deadline should account for the earliest animation request across the group. When document loading is added, the pump must also drive browser-owned loader futures and remain active while they are pending, even when Deno itself reports idle.

The microtask queue is shared. Browser tasks must schedule observer delivery for the affected frame states, then perform checkpoints at the appropriate task boundaries. A nested synchronous `child.eval()` call should return to its parent script without introducing an extra checkpoint midway through that script. Deno already performs checkpoints while driving its own callbacks. Rust-backed observer delivery callbacks should carry their target frame identity too, so delivery retrieves the correct callback registry and document.

Rendering remains per document. A child mutation marks its renderer dirty and requests an owner update. During that update, parent layout determines iframe viewport sizes, dirty descendants lay out and paint into their surfaces, and the parent composites those surfaces. Descendants must be painted before their pixels are consumed; layout may first need to propagate a new viewport size down the tree.

The existing `FrameSurface` can remain. Its locking is unnecessary for local children, but changing that is optional cleanup. The necessary change is orchestration: the owner visits dirty children even when its own document has no mutations. Painting should run after releasing JavaScript execution borrows, and JavaScript callbacks should run after releasing mutable renderer borrows.

For the first implementation, I would enable this for same-origin `about:blank` children and keep the existing threaded path for other documents. A blank child can inherit its parent's origin and be initialized synchronously. The shared path must exclude sandboxed frames with an opaque origin. Supporting fetched same-origin documents adds asynchronous document loading and a decision based on the final origin after redirects.

A retained child function can outlive removal of its iframe. Keep its context-associated host state until runtime teardown, as the constructor already proposes. Detaching the frame should stop its timers and animation requests and remove it from painting; retaining its state is a separate lifetime decision. Navigation needs a design for replacing documents and preserving window identity. Sharing the module map also leaves per-document page-module isolation unresolved.

A useful first slice would connect blank-frame creation, the per-window bootstrap and DOM bindings, targeted events, and the shared scheduler. The opening example would then exercise the intended behavior: immediate access to a child window, an animation callback that starts a timer, a child Promise callback, and a visible DOM update while the parent is idle. Cross-document node adoption and general navigation can remain separate changes.
