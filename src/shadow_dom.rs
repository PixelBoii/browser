use deno_core::{OpState, op2};
use deno_error::JsErrorBox;

use crate::{JsHostState, Node, Renderer, custom_elements, parser::ShadowRootMode};

#[op2(fast)]
#[number]
pub fn op_attach_shadow(
    state: &mut OpState,
    #[number] host_idx: usize,
    #[string] mode: &str,
) -> Result<usize, JsErrorBox> {
    let mode = match mode {
        "open" => ShadowRootMode::Open,
        "closed" => ShadowRootMode::Closed,
        _ => {
            return Err(JsErrorBox::type_error(
                "Shadow root mode must be open or closed",
            ));
        }
    };
    let host = state.borrow::<JsHostState>();
    let mut renderer = host.renderer.borrow_mut();
    let Some(Node::Element(element)) = renderer.nodes.get(host_idx) else {
        return Err(JsErrorBox::type_error("Expected a shadow host element"));
    };
    let valid_host = custom_elements::valid_name(&element.tag)
        || matches!(
            element.tag.as_str(),
            "article"
                | "aside"
                | "blockquote"
                | "body"
                | "div"
                | "footer"
                | "h1"
                | "h2"
                | "h3"
                | "h4"
                | "h5"
                | "h6"
                | "header"
                | "main"
                | "nav"
                | "p"
                | "section"
                | "span"
        );
    if !valid_host || renderer.shadow_roots.contains_key(&host_idx) {
        return Err(JsErrorBox::new(
            "DOMExceptionNotSupportedError",
            "This element cannot attach a shadow root",
        ));
    }
    renderer.push_node(Node::ShadowRoot {
        host: host_idx,
        mode,
    });
    let root = renderer.nodes.cursor;
    renderer.dom_indexes.children_index.insert(root, vec![]);
    renderer.shadow_roots.insert(host_idx, root);
    renderer.selector_changes.child_list_changed(host_idx);
    renderer.schedule_dom_update();
    Ok(root)
}

#[op2]
pub fn op_get_shadow_root(state: &mut OpState, #[number] host_idx: usize) -> Option<u32> {
    let host = state.borrow::<JsHostState>();
    let renderer = host.renderer.borrow();
    let root = *renderer.shadow_roots.get(&host_idx)?;
    matches!(
        renderer.nodes.get(root),
        Some(Node::ShadowRoot {
            mode: ShadowRootMode::Open,
            ..
        })
    )
    .then_some(root as u32)
}

impl Renderer {
    // A shadow root has no DOM parent or layout box. Its children use the host's box.
    pub fn layout_parent(&self, node_idx: usize) -> Option<usize> {
        let parent = self.nodes.get(node_idx)?.get_parent()?;
        match self.nodes.get(parent)? {
            Node::ShadowRoot { host, .. } => Some(*host),
            _ => Some(parent),
        }
    }
}
