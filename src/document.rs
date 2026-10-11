use std::cell::RefCell;
use std::rc::Rc;

use deno_core::{GarbageCollected, op2, v8};
use deno_error::JsErrorBox;

use crate::frame_context::frame_host;
use crate::{
    BLANK_DOCUMENT, ExecutedScripts, JsHostState, Node, NodesTable, Renderer, custom_elements,
    get_dom_indexes, mutation_observer, parser::HtmlParser, sorted_node_idxs,
};

#[derive(Clone)]
pub(crate) struct DocumentState {
    pub renderer: Rc<RefCell<Renderer>>,
    pub executed_scripts: Rc<RefCell<ExecutedScripts>>,
    pub detached: bool,
}

// The wrapper cache stays on the JS Document. Existing frame-owned JS handles
// remain managed by FrameState and the renderer; there are no cppgc members to trace.
unsafe impl GarbageCollected for DocumentState {
    fn trace(&self, _: &mut v8::cppgc::Visitor) {}

    fn get_name(&self) -> &'static std::ffi::CStr {
        c"DocumentState"
    }
}

fn state_key<'s>(scope: &mut v8::PinScope<'s, '_>) -> v8::Local<'s, v8::Private> {
    let name = v8::String::new(scope, "browser::Document::state").unwrap();
    v8::Private::for_api(scope, Some(name))
}

fn bind_document(scope: &mut v8::PinScope, document: v8::Local<v8::Object>, state: DocumentState) {
    let key = state_key(scope);
    let state = deno_core::cppgc::make_cppgc_object(scope, state);
    assert_eq!(document.set_private(scope, key, state.into()), Some(true));
}

pub(crate) fn bind_frame_document(scope: &mut v8::PinScope, host: &JsHostState) {
    let global = scope.get_current_context().global(scope);
    let key = v8::String::new(scope, "document").unwrap();
    let document = global.get(scope, key.into()).unwrap();
    let document = v8::Local::<v8::Object>::try_from(document).unwrap();
    bind_document(
        scope,
        document,
        DocumentState {
            renderer: host.renderer.clone(),
            executed_scripts: host.executed_scripts.clone(),
            detached: false,
        },
    );
}

pub(crate) fn document_state(
    scope: &mut v8::PinScope,
    document: v8::Local<v8::Object>,
) -> DocumentState {
    let key = state_key(scope);
    let state = document.get_private(scope, key).unwrap();
    let state = deno_core::cppgc::try_unwrap_cppgc_object::<DocumentState>(scope, state).unwrap();
    (*state).clone()
}

// Detached document custom-element upgrades and mutation observers are not implemented.
pub(crate) fn deliver_reactions(scope: &mut v8::PinScope, document: v8::Local<v8::Object>) {
    if !document_state(scope, document).detached {
        custom_elements::deliver_reactions(scope);
    }
}

pub(crate) fn schedule_mutations(scope: &mut v8::PinScope, document: v8::Local<v8::Object>) {
    if !document_state(scope, document).detached {
        mutation_observer::schedule(scope);
    }
}

#[op2(fast)]
pub(crate) fn op_parse_html_document(
    scope: &mut v8::PinScope,
    document: v8::Local<v8::Object>,
    #[string] html: String,
    #[string] url: String,
) -> Result<(), JsErrorBox> {
    let host = frame_host(scope);
    let source = host.renderer.borrow();
    let mut parser = HtmlParser::new(None);
    parser
        .parse(html)
        .map_err(|err| JsErrorBox::generic(err.to_string()))?;
    // Indexes need an element or text root. Keep parsed comments and supply the
    // existing blank document when there is no root to index.
    if !parser
        .nodes
        .iter()
        .any(|node| node.get_parent().is_none() && matches!(node, Node::Element(_) | Node::Text(_)))
    {
        parser
            .parse(BLANK_DOCUMENT.to_string())
            .map_err(|err| JsErrorBox::generic(err.to_string()))?;
    }
    // Implied html/head/body elements remain a limitation of the shared parser.
    let nodes = NodesTable::new_from_nodes(parser.nodes);
    let nodes_idxs = sorted_node_idxs(&nodes);
    let mut classes = crate::ClassIndexes::new();
    let indexes = get_dom_indexes(&nodes, &nodes_idxs, &mut classes);
    let mut scripts = ExecutedScripts::new();
    scripts.nodes = nodes
        .iter()
        .filter_map(|(idx, node)| {
            matches!(node, Node::Element(element) if element.tag == "script").then_some(idx)
        })
        .collect();
    let mut renderer = Renderer::new(
        url,
        source.tokio.clone(),
        nodes,
        parser.template_contents,
        source.window_size,
        source.font_handler.clone(),
        source.network_fetch.clone(),
        indexes,
        nodes_idxs,
        source.blob_store.clone(),
        true,
    );
    renderer.origin = source.origin.clone();
    renderer.css_parser.class_definitions = classes;
    drop(source);
    bind_document(
        scope,
        document,
        DocumentState {
            renderer: Rc::new(RefCell::new(renderer)),
            executed_scripts: Rc::new(RefCell::new(scripts)),
            detached: true,
        },
    );
    Ok(())
}
