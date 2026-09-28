# Making iframe eval work with a shared JavaScript runtime

Our browser gives each iframe a thread and a Deno runtime. Each runtime has a separate V8 heap. That becomes a problem when a page calls `iframe.contentWindow.eval()` and expects a JavaScript object or function back.

The proposed design puts same-origin `about:blank` frames in separate V8 contexts within one runtime. Each frame keeps its own globals and document. Objects and functions can pass directly between them.

For a same-origin iframe, this should work:

```js
const iframe = document.createElement("iframe");
document.body.appendChild(iframe);
const child = iframe.contentWindow;

const readDocument = child.eval("() => document");
readDocument() === child.document; // true
child.Object !== Object;          // true
```

The returned function keeps using the child's globals when the parent calls it. A channel can carry source code and serialized results, but a live function also captures its execution environment. Supporting that across runtimes would require remote function calls and a way to preserve object identity.

V8 provides another option. An **isolate** owns a JavaScript heap and garbage collector. A **context** provides a global object and built-ins such as `Object`, `Promise`, and `eval`. Multiple contexts can share an isolate. Objects referenced across those contexts retain their identity and prototypes.

An eval result is already in the shared heap, so returning it requires no serialization. `child.eval(...)` is an indirect eval: it uses the global environment belonging to that eval function. Exposing the child's native eval gives us that behavior. Returning the parent's eval would use the parent's globals.

| Resource | Owner in the proposed design |
| --- | --- |
| V8 heap and Deno event loop | Shared runtime |
| Global object, JavaScript built-ins, native eval | Each frame's V8 context |
| Document, DOM nodes, DOM callback registries | Each frame's Rust host state |
| Viewport, layout, painted bitmap | Each frame's renderer |

V8 supplies the JavaScript built-ins. We must install `window`, `document`, DOM constructors, timers, and browser APIs in each context. The bootstrap therefore needs two parts: initialize shared runtime dependencies once, then initialize each frame's browser environment. Runtime-wide hooks must only be registered once.

Creating a context does not create a new Deno `OpState`, the Rust state associated with the runtime. Deno resources remain shared. Each frame needs its own host state containing its document's renderer and callback registries.

Today, a native DOM operation reads one `JsHostState` from the runtime. With several documents, it must select the state belonging to the document being modified. Node indices are local to each document; node 12 in the parent and node 12 in the child can be different elements.

Bind each frame's DOM operations to its window or host-state identifier during initialization. That association survives nested callbacks and calls from another frame. Shared native Deno functions originate in the main context, so their own creation context cannot identify the target document.

`deno_core` 0.404 exposes V8 access without a public helper for creating another initialized Deno realm. A context adapter must create and enter V8 contexts, attach the required Deno bookkeeping, and retain the associated Rust state. DOM operations should only need to retrieve their frame's state.

These frames execute JavaScript on one owning thread. The parent drives the shared Deno event loop, while each frame tracks its browser callbacks. Network requests can still progress asynchronously. Promise callbacks use the shared microtask queue and run at checkpoints after script execution.

The parent also visits child frames to deliver queued events and animation callbacks, entering the target context when evaluating code there. Child work must wake the parent even when the parent document is idle. If a child animation callback starts a timer, the shared event loop must continue running so that timer can fire. Merely visiting children during painting would leave asynchronous work stuck when nothing needs repainting.

Rendering can keep its existing structure. Each child lays out its document and paints a bitmap; the parent composites that bitmap into the iframe's rectangle. A child DOM mutation marks its renderer dirty and wakes the parent. During a rendering update, dirty children must be painted before the parent consumes their pixels.

Lifetime needs an explicit policy. The parent can retain a function from a removed iframe, so its context and Rust state must remain valid while still referenced. Keeping child host states until the owning runtime is destroyed is a simple first policy, with a memory cost. Cancelling detached-frame work is a separate responsibility.

For a same-origin blank frame that cannot navigate, `contentWindow` can expose the child global directly. General iframe support needs a stable `WindowProxy` that survives navigation and enforces origin checks while its underlying global changes.

The prototype confirmed native eval, separate globals, live function results, child callbacks, and rendering. HLTV's challenge advanced past the missing-eval failure, then encountered DOM adoption: Cloudflare inserted a `div` from its challenge document into a blank iframe. The JavaScript reference could cross contexts; the native node still belonged to another document's storage. Verification did not complete.

A smaller implementation can land in three steps: introduce contexts and native eval, bind DOM operations to their frame, then connect child scheduling and painting. Navigation, module loading, DOM adoption, and complete window-message metadata can follow separately.
