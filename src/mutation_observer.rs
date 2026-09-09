use std::collections::HashMap;

use deno_core::{JsRuntime, OpState, op2, serde_v8, v8};
use deno_error::JsErrorBox;
use serde::{Deserialize, Serialize};

use crate::{JsHostState, Node, Renderer};

#[derive(Clone, Debug, Default, Deserialize)]
#[serde(default, rename_all = "camelCase")]
pub struct Options {
    child_list: bool,
    attributes: Option<bool>,
    character_data: Option<bool>,
    subtree: bool,
    attribute_old_value: Option<bool>,
    character_data_old_value: Option<bool>,
    attribute_filter: Option<Vec<String>>,
}

impl Options {
    fn validate(&mut self) -> Result<(), JsErrorBox> {
        let attributes = *self
            .attributes
            .get_or_insert(self.attribute_old_value.is_some() || self.attribute_filter.is_some());
        let character_data = *self
            .character_data
            .get_or_insert(self.character_data_old_value.is_some());
        if !self.child_list && !attributes && !character_data {
            return Err(JsErrorBox::type_error("No mutations selected"));
        }
        if !attributes
            && (self.attribute_old_value == Some(true) || self.attribute_filter.is_some())
        {
            return Err(JsErrorBox::type_error(
                "Attribute options require attributes",
            ));
        }
        if !character_data && self.character_data_old_value == Some(true) {
            return Err(JsErrorBox::type_error("Old text requires characterData"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Record {
    #[serde(rename = "type")]
    kind: &'static str,
    target: usize,
    attribute_name: Option<String>,
    old_value: Option<String>,
}

#[derive(Debug, Default)]
pub struct Observers {
    next_id: usize,
    // None is the Document; element and character-data targets use their node index.
    registrations: HashMap<Option<usize>, Vec<(usize, Options)>>,
    records: HashMap<usize, Vec<Record>>,
    pending: Vec<usize>,
}

impl Observers {
    pub fn is_empty(&self) -> bool {
        self.registrations.is_empty()
    }

    fn create(&mut self) -> usize {
        let id = self.next_id;
        self.next_id += 1;
        self.records.insert(id, Vec::new());
        id
    }

    fn observe(
        &mut self,
        id: usize,
        target: Option<usize>,
        mut options: Options,
    ) -> Result<(), JsErrorBox> {
        if !self.records.contains_key(&id) {
            return Err(JsErrorBox::type_error("Unknown mutation observer"));
        }
        options.validate()?;
        let registrations = self.registrations.entry(target).or_default();
        if let Some((_, previous)) = registrations
            .iter_mut()
            .find(|(registered, _)| *registered == id)
        {
            *previous = options;
        } else {
            registrations.push((id, options));
        }
        Ok(())
    }

    fn disconnect(&mut self, id: usize) {
        self.registrations.retain(|_, registrations| {
            registrations.retain(|(registered, _)| *registered != id);
            !registrations.is_empty()
        });
        self.take_records(id);
    }

    fn take_records(&mut self, id: usize) -> Vec<Record> {
        self.records
            .get_mut(&id)
            .map(std::mem::take)
            .unwrap_or_default()
    }

    fn queue(&mut self, ancestors: &[Option<usize>], record: Record) {
        let mut interested: Vec<(usize, bool)> = Vec::new();
        for (depth, node) in ancestors.iter().enumerate() {
            for (id, options) in self.registrations.get(node).into_iter().flatten() {
                if depth != 0 && !options.subtree {
                    continue;
                }
                let old_value = if record.kind == "attributes" {
                    if options.attributes != Some(true)
                        || options.attribute_filter.as_ref().is_some_and(|filter| {
                            record
                                .attribute_name
                                .as_ref()
                                .is_none_or(|name| !filter.contains(name))
                        })
                    {
                        continue;
                    }
                    options.attribute_old_value == Some(true)
                } else {
                    if options.character_data != Some(true) {
                        continue;
                    }
                    options.character_data_old_value == Some(true)
                };
                if let Some((_, include_old)) = interested
                    .iter_mut()
                    .find(|(registered, _)| registered == id)
                {
                    *include_old |= old_value;
                } else {
                    interested.push((*id, old_value));
                }
            }
        }
        for (id, include_old) in interested {
            let mut record = record.clone();
            if !include_old {
                record.old_value = None;
            }
            self.records.get_mut(&id).unwrap().push(record);
            if !self.pending.contains(&id) {
                self.pending.push(id);
            }
        }
    }
}

impl Renderer {
    pub fn record_mutation(
        &mut self,
        target: usize,
        attribute_name: Option<String>,
        old_value: Option<String>,
    ) {
        if self.mutation_observers.registrations.is_empty() {
            return;
        }
        let mut ancestors = vec![Some(target)];
        let mut current = target;
        while let Some(parent) = self.nodes.get(current).and_then(Node::get_parent) {
            ancestors.push(Some(parent));
            current = parent;
        }
        if current == self.dom_indexes.root_indice {
            ancestors.push(None);
        }
        self.mutation_observers.queue(
            &ancestors,
            Record {
                kind: if attribute_name.is_some() {
                    "attributes"
                } else {
                    "characterData"
                },
                target,
                attribute_name,
                old_value,
            },
        );
    }
}

// V8 handles belong to the realm's OpState, not the renderer's DOM state.
#[derive(Default)]
pub struct Callbacks {
    functions: HashMap<usize, v8::Global<v8::Function>>,
    queued: bool,
}

pub fn schedule(scope: &mut v8::PinScope) {
    let state = JsRuntime::op_state_from(scope);
    let mut state = state.borrow_mut();
    let Some(host) = state.try_borrow::<JsHostState>() else {
        return;
    };
    if host.renderer.borrow().mutation_observers.pending.is_empty() {
        return;
    }
    let callbacks = state.borrow_mut::<Callbacks>();
    if callbacks.queued {
        return;
    }
    callbacks.queued = true;
    let callback = v8::Function::new(scope, deliver).unwrap();
    scope.enqueue_microtask(callback);
}

fn deliver(scope: &mut v8::PinScope, _: v8::FunctionCallbackArguments, _: v8::ReturnValue) {
    let state = JsRuntime::op_state_from(scope);
    let renderer = state.borrow().borrow::<JsHostState>().renderer.clone();
    state.borrow_mut().borrow_mut::<Callbacks>().queued = false;
    let pending = std::mem::take(&mut renderer.borrow_mut().mutation_observers.pending);
    for id in pending {
        let records = renderer.borrow_mut().mutation_observers.take_records(id);
        if records.is_empty() {
            continue;
        }
        let callback = state.borrow().borrow::<Callbacks>().functions[&id].clone();
        v8::tc_scope!(let scope, scope);
        let callback = v8::Local::new(scope, callback);
        let records = serde_v8::to_v8(scope, records).unwrap();
        let receiver = v8::undefined(scope).into();
        if callback.call(scope, receiver, &[records]).is_none()
            && let Some(exception) = scope.exception()
        {
            eprintln!(
                "MutationObserver callback failed: {}",
                exception.to_rust_string_lossy(scope)
            );
        }
    }
}

#[op2(fast)]
#[number]
pub fn op_mutation_observer_create(state: &mut OpState) -> usize {
    state
        .borrow::<JsHostState>()
        .renderer
        .borrow_mut()
        .mutation_observers
        .create()
}

#[op2]
pub fn op_mutation_observer_observe(
    scope: &mut v8::PinScope,
    #[number] id: usize,
    #[number] target: Option<usize>,
    #[serde] options: Options,
    callback: v8::Local<v8::Function>,
) -> Result<(), JsErrorBox> {
    let state = JsRuntime::op_state_from(scope);
    let mut state = state.borrow_mut();
    state
        .borrow::<JsHostState>()
        .renderer
        .borrow_mut()
        .mutation_observers
        .observe(id, target, options)?;
    let callback = v8::Global::new(scope, callback);
    state
        .borrow_mut::<Callbacks>()
        .functions
        .insert(id, callback);
    Ok(())
}

#[op2(fast)]
pub fn op_mutation_observer_disconnect(state: &mut OpState, #[number] id: usize) {
    state
        .borrow::<JsHostState>()
        .renderer
        .borrow_mut()
        .mutation_observers
        .disconnect(id);
    state.borrow_mut::<Callbacks>().functions.remove(&id);
}

#[op2]
#[serde]
pub fn op_mutation_observer_take_records(state: &mut OpState, #[number] id: usize) -> Vec<Record> {
    state
        .borrow::<JsHostState>()
        .renderer
        .borrow_mut()
        .mutation_observers
        .take_records(id)
}
