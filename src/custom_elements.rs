use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use deno_core::{JsRuntime, OpState, op2, v8};
use deno_error::JsErrorBox;

use crate::{JsHostState, Node, native_node_index};

struct Definition {
    constructor: v8::Global<v8::Function>,
    // Existing wrappers awaiting super(); None means super() already consumed the wrapper.
    upgrade_stack: RefCell<Vec<Option<v8::Global<v8::Object>>>>,
}

impl Definition {
    fn upgrade<'s>(
        &self,
        scope: &mut v8::PinScope<'s, '_>,
        element: v8::Local<'s, v8::Object>,
    ) -> Option<v8::Local<'s, v8::Object>> {
        self.upgrade_stack
            .borrow_mut()
            .push(Some(v8::Global::new(scope, element)));
        let constructor = v8::Local::new(scope, &self.constructor);
        let result = constructor.new_instance(scope, &[]);
        self.upgrade_stack.borrow_mut().pop();
        result
    }

    fn element_for_construction<'s>(
        &self,
        scope: &mut v8::PinScope<'s, '_>,
        name: String,
    ) -> Result<Option<v8::Local<'s, v8::Object>>, JsErrorBox> {
        if let Some(entry) = self.upgrade_stack.borrow_mut().last_mut() {
            let existing = entry.take().ok_or_else(|| {
                JsErrorBox::new(
                    "DOMExceptionInvalidStateError",
                    "Custom element is already constructed",
                )
            })?;
            return Ok(Some(v8::Local::new(scope, existing)));
        }

        Ok(create_element(scope, name))
    }
}

#[derive(Default)]
pub struct Registry {
    definitions: HashMap<String, Rc<Definition>>,
    // A failed upgrade must not be attempted again either.
    attempted: HashSet<usize>,
}

fn valid_name(name: &str) -> bool {
    name.starts_with(|c: char| c.is_ascii_lowercase())
        && name.contains('-')
        && name.chars().all(|c| {
            matches!(c,
            '-' | '.' | '0'..='9' | '_' | 'a'..='z' | '\u{b7}' |
            '\u{c0}'..='\u{d6}' | '\u{d8}'..='\u{f6}' | '\u{f8}'..='\u{37d}' |
            '\u{37f}'..='\u{1fff}' | '\u{200c}'..='\u{200d}' | '\u{203f}'..='\u{2040}' |
            '\u{2070}'..='\u{218f}' | '\u{2c00}'..='\u{2fef}' | '\u{3001}'..='\u{d7ff}' |
            '\u{f900}'..='\u{fdcf}' | '\u{fdf0}'..='\u{fffd}' | '\u{10000}'..='\u{effff}')
        })
        && !matches!(
            name,
            "annotation-xml"
                | "color-profile"
                | "font-face"
                | "font-face-src"
                | "font-face-uri"
                | "font-face-format"
                | "font-face-name"
                | "missing-glyph"
        )
}

fn node_wrapper<'s>(
    scope: &mut v8::PinScope<'s, '_>,
    idx: usize,
) -> Option<v8::Local<'s, v8::Object>> {
    let global = scope.get_current_context().global(scope);
    let key = v8::String::new(scope, "__elementFromNodeIdx").unwrap();
    let function = global.get(scope, key.into())?;
    let function = v8::Local::<v8::Function>::try_from(function).ok()?;
    let idx = v8::Number::new(scope, idx as f64);
    let value = function.call(scope, global.into(), &[idx.into()])?;
    v8::Local::<v8::Object>::try_from(value).ok()
}

// Used by super() for direct construction, and for a failed factory result.
fn create_element<'s>(
    scope: &mut v8::PinScope<'s, '_>,
    name: String,
) -> Option<v8::Local<'s, v8::Object>> {
    let state = JsRuntime::op_state_from(scope);
    let renderer = state.borrow().borrow::<JsHostState>().renderer.clone();
    let idx = renderer.borrow_mut().create_element(name);
    state
        .borrow_mut()
        .borrow_mut::<Registry>()
        .attempted
        .insert(idx);
    node_wrapper(scope, idx)
}

#[op2(reentrant)]
pub fn op_custom_element_create<'s>(
    scope: &mut v8::PinScope<'s, '_>,
    #[string] name: String,
) -> Option<v8::Local<'s, v8::Object>> {
    let state = JsRuntime::op_state_from(scope);
    let definition = state
        .borrow()
        .borrow::<Registry>()
        .definitions
        .get(&name)
        .cloned()?;
    let result = {
        v8::tc_scope!(let scope, scope);
        let constructor = v8::Local::new(scope, &definition.constructor);
        let result = constructor.new_instance(scope, &[]).and_then(|element| {
            let idx = native_node_index(scope, element)?;
            let state = state.borrow();
            let renderer = state.borrow::<JsHostState>().renderer.borrow();
            let valid = matches!(renderer.nodes.get(idx), Some(Node::Element(node))
                if node.tag == name && node.parent.is_none() && node.attributes.values.is_empty())
                && renderer
                    .dom_indexes
                    .children_index
                    .get(&idx)
                    .is_none_or(Vec::is_empty);
            valid.then_some(element)
        });
        if result.is_none() {
            if let Some(exception) = scope.exception() {
                eprintln!(
                    "Custom element {name} construction failed: {}",
                    exception.to_rust_string_lossy(scope)
                );
            } else {
                eprintln!(
                    "Custom element {name} constructor must return an empty, detached element of the requested type"
                );
            }
        }
        result
    };
    // Leave the catch scope before creating a fallback, so no exception is pending.
    result.or_else(|| create_element(scope, name))
}

fn upgrade_element(scope: &mut v8::PinScope, idx: usize) {
    let state = JsRuntime::op_state_from(scope);
    let definition = {
        let state = state.borrow();
        let registry = state.borrow::<Registry>();
        if registry.attempted.contains(&idx) {
            return;
        }
        let renderer = state.borrow::<JsHostState>().renderer.borrow();
        let Some(Node::Element(element)) = renderer.nodes.get(idx) else {
            return;
        };
        let Some(definition) = registry.definitions.get(&element.tag) else {
            return;
        };
        (element.tag.clone(), definition.clone())
    };
    let (name, definition) = definition;
    state
        .borrow_mut()
        .borrow_mut::<Registry>()
        .attempted
        .insert(idx);
    v8::tc_scope!(let scope, scope);
    let result = (|| {
        let element = node_wrapper(scope, idx)?;
        let key = v8::String::new(scope, "namespaceURI").unwrap();
        let namespace = element.get(scope, key.into())?;
        let html_namespace = v8::String::new(scope, "http://www.w3.org/1999/xhtml").unwrap();
        if !namespace.strict_equals(html_namespace.into()) {
            return Some(());
        }
        let result = definition.upgrade(scope, element)?;
        if result != element {
            let message = v8::String::new(
                scope,
                "Custom element constructor returned a different object",
            )
            .unwrap();
            let error = v8::Exception::type_error(scope, message);
            scope.throw_exception(error);
            return None;
        }
        Some(())
    })();
    if result.is_none() {
        if let Some(exception) = scope.exception() {
            eprintln!(
                "Custom element {name} upgrade failed: {}",
                exception.to_rust_string_lossy(scope)
            );
        } else {
            eprintln!("Custom element {name} upgrade failed");
        }
    }
}

pub fn upgrade_subtree(scope: &mut v8::PinScope, root: Option<usize>, name: Option<&str>) {
    let state = JsRuntime::op_state_from(scope);
    let candidates = {
        let state = state.borrow();
        let renderer = state.borrow::<JsHostState>().renderer.borrow();
        let mut pending = vec![root.unwrap_or(renderer.dom_indexes.root_indice)];
        let mut candidates = Vec::new();
        while let Some(idx) = pending.pop() {
            if let Some(Node::Element(element)) = renderer.nodes.get(idx)
                && name.is_none_or(|name| element.tag == name)
            {
                candidates.push(idx);
            }
            // Template contents live in a separate fragment and stay inert.
            if let Some(children) = renderer.dom_indexes.children_index.get(&idx) {
                pending.extend(children.iter().rev().copied());
            }
        }
        candidates
    };
    for idx in candidates {
        upgrade_element(scope, idx);
    }
}

#[op2(nofast, reentrant)]
pub fn op_custom_element_define(
    scope: &mut v8::PinScope,
    #[string] name: String,
    constructor: v8::Local<v8::Function>,
) -> Result<(), JsErrorBox> {
    if !valid_name(&name) {
        return Err(JsErrorBox::new(
            "DOMExceptionSyntaxError",
            "Invalid custom element name",
        ));
    }
    let state = JsRuntime::op_state_from(scope);
    let key = v8::String::new(scope, "prototype").unwrap();
    let Some(prototype) = constructor.get(scope, key.into()) else {
        // Preserve a JavaScript exception thrown by a prototype getter.
        return Ok(());
    };
    if !prototype.is_object() {
        return Err(JsErrorBox::type_error(
            "Custom element prototype must be an object",
        ));
    }
    {
        let mut state = state.borrow_mut();
        let registry = state.borrow_mut::<Registry>();
        if registry.definitions.contains_key(&name)
            || registry
                .definitions
                .values()
                .any(|definition| v8::Local::new(scope, &definition.constructor) == constructor)
        {
            return Err(JsErrorBox::new(
                "DOMExceptionNotSupportedError",
                "Custom element name or constructor is already registered",
            ));
        }
        registry.definitions.insert(
            name.clone(),
            Rc::new(Definition {
                constructor: v8::Global::new(scope, constructor),
                upgrade_stack: RefCell::default(),
            }),
        );
    }
    upgrade_subtree(scope, None, Some(&name));
    Ok(())
}

#[op2]
pub fn op_custom_element_get<'s>(
    scope: &mut v8::PinScope<'s, '_>,
    state: &mut OpState,
    #[string] name: String,
) -> Option<v8::Local<'s, v8::Function>> {
    state
        .borrow::<Registry>()
        .definitions
        .get(&name)
        .map(|definition| v8::Local::new(scope, &definition.constructor))
}

#[op2(reentrant)]
pub fn op_custom_element_upgrade(scope: &mut v8::PinScope, #[number] root: Option<usize>) {
    upgrade_subtree(scope, root, None);
}

#[op2(reentrant)]
pub fn op_custom_element_construct<'s>(
    scope: &mut v8::PinScope<'s, '_>,
    constructor: v8::Local<v8::Function>,
) -> Result<Option<v8::Local<'s, v8::Object>>, JsErrorBox> {
    let state = JsRuntime::op_state_from(scope);
    let definition = state
        .borrow()
        .borrow::<Registry>()
        .definitions
        .iter()
        .find(|(_, definition)| v8::Local::new(scope, &definition.constructor) == constructor)
        .map(|(name, definition)| (name.clone(), definition.clone()));
    let Some((name, definition)) = definition else {
        return Ok(None);
    };
    let key = v8::String::new(scope, "prototype").unwrap();
    let Some(prototype) = constructor.get(scope, key.into()) else {
        return Ok(None);
    };
    if !prototype.is_object() {
        return Err(JsErrorBox::type_error(
            "Custom element prototype must be an object",
        ));
    }
    let Some(element) = definition.element_for_construction(scope, name)? else {
        return Ok(None);
    };
    if element.set_prototype(scope, prototype) != Some(true) {
        return Ok(None);
    }
    Ok(Some(element))
}
