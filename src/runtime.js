import { serializeWorkerMessage, deserializeWorkerMessage } from "./worker_messaging.js";
import * as webidl from "ext:deno_webidl/00_webidl.js";
import * as url from "ext:deno_web/00_url.js";
import * as urlPattern from "ext:deno_web/01_urlpattern.js";
import * as infra from "ext:deno_web/00_infra.js";
import * as DOMException from "ext:deno_web/01_dom_exception.js";
import * as broadcastChannel from "ext:deno_web/01_broadcast_channel.js";
import * as mimesniff from "ext:deno_web/01_mimesniff.js";
import * as denoEvent from "ext:deno_web/02_event.js";
import * as structuredClone from "ext:deno_web/02_structured_clone.js";
import * as abortSignal from "ext:deno_web/03_abort_signal.js";
import * as globalInterfaces from "ext:deno_web/04_global_interfaces.js";
import * as base64 from "ext:deno_web/05_base64.js";
import * as streams from "ext:deno_web/06_streams.js";
import * as encoding from "ext:deno_web/08_text_encoding.js";
import * as file from "ext:deno_web/09_file.js";
import * as fileReader from "ext:deno_web/10_filereader.js";
// import * as location from "ext:deno_web/12_location.js";
import * as messagePort from "ext:deno_web/13_message_port.js";
import * as compression from "ext:deno_web/14_compression.js";
import * as performance from "ext:deno_web/15_performance.js";
import * as imageData from "ext:deno_web/16_image_data.js";
import * as net from "ext:deno_net/01_net.js";
import * as tls from "ext:deno_net/02_tls.js";
import * as headers from "ext:deno_fetch/20_headers.js";
import * as formData from "ext:deno_fetch/21_formdata.js";
import * as request from "ext:deno_fetch/23_request.js";
import * as response from "ext:deno_fetch/23_response.js";
import * as fetch from "ext:browser/runtime_fetch.js";
import * as crypto from "ext:deno_crypto/00_crypto.js";
import { EventTarget } from "./event_target.js";
import { XMLHttpRequest } from "ext:browser/xml_http_request.js";

denoEvent.saveGlobalThisReference(globalThis)

const { core } = Deno
let nextTimerId = 1
const activeTimers = new Map()
let nextAnimationFrameId = 1
let animationFrameRequested = false
const animationFrameCallbacks = new Map()

function createTimer(callback, delay, args, repeat) {
    if (typeof callback !== "function") {
        throw new TypeError("Timer callback must be a function")
    }

    const timerId = nextTimerId++
    const timer = core.createTimer(() => {
        if (!repeat) {
            activeTimers.delete(timerId)
        }

        callback(...args)
    }, delay, undefined, repeat, true, false)

    activeTimers.set(timerId, timer)
    return timerId
}

function setTimeoutImpl(callback, delay = 0, ...args) {
    return createTimer(callback, delay, args, false)
}

function clearTimeoutImpl(timerId) {
    const timer = activeTimers.get(timerId)
    if (!timer) {
        return
    }

    activeTimers.delete(timerId)
    core.cancelTimer(timer)
}

function setIntervalImpl(callback, delay = 0, ...args) {
    return createTimer(callback, delay, args, true)
}

function clearAllTimers() {
    for (const timer of activeTimers.values()) {
        core.cancelTimer(timer)
    }
    activeTimers.clear()
    animationFrameCallbacks.clear()
    animationFrameRequested = false
}

function requestAnimationFrameImpl(callback) {
    if (typeof callback !== "function") {
        throw new TypeError("requestAnimationFrame callback must be a function")
    }

    const callbackId = nextAnimationFrameId++
    animationFrameCallbacks.set(callbackId, callback)
    if (!animationFrameRequested) {
        animationFrameRequested = true
        core.ops.op_request_animation_frame()
    }
    return callbackId
}

function cancelAnimationFrameImpl(callbackId) {
    animationFrameCallbacks.delete(callbackId)
}

function runAnimationFrame(timestamp) {
    animationFrameRequested = false
    const callbacks = Array.from(animationFrameCallbacks.values())
    animationFrameCallbacks.clear()
    for (const callback of callbacks) {
        try {
            callback(timestamp)
        } catch (err) {
            console.error("requestAnimationFrame callback failed", err?.stack ?? err?.message ?? String(err))
        }
    }
}

Object.defineProperty(globalThis, "__run_animation_frame", {
    value: runAnimationFrame,
    configurable: true,
})

function scrollToImpl(x = 0, y = 0) {
    //
}

class SVGAnimatedString {
    //
}

Object.defineProperty(globalThis, "SVGAnimatedString", {
    value: SVGAnimatedString,
    configurable: true,
    writable: true,
    enumerable: true
})

Object.defineProperty(globalThis, "EventTarget", {
    value: EventTarget,
    enumerable: true,
    configurable: true,
    writable: true,
})

class BaseNode extends EventTarget {
    constructor() {
        super()
        this.__node_idx = null
        this.ownerDocument = currentDocument
    }

    getParent() {
        return this.parentNode ?? (this === this.ownerDocument.documentElement ? this.ownerDocument : null)
    }

    get isConnected() {
        return this.__node_idx != null && this.getRootNode() === this.ownerDocument
    }

    get parentNode() {
        const parent = core.ops.op_get_parent_node(this.__node_idx)
        return parent ? nodeToElement(parent) : null
    }

    get parentElement() {
        const parent = this.parentNode
        return parent?.nodeType === Node.ELEMENT_NODE ? parent : null
    }

    get nextSibling() {
        const sibling = core.ops.op_get_next_sibling(this.__node_idx)
        return sibling ? nodeToElement(sibling) : null
    }

    get firstChild() {
        const child = core.ops.op_get_edge_child(this.__node_idx, false)
        return child ? nodeToElement(child) : null
    }

    getRootNode() {
        let node = this
        while (node.parentNode) {
            node = node.parentNode
        }
        return node === this.ownerDocument.documentElement ? this.ownerDocument : node
    }

    cloneNode(deep = false) {
        let newNodeIdx = core.ops.op_clone_node(this.__node_idx, deep)
        return withDocument(this.ownerDocument, () => elementFromNodeIdx(newNodeIdx))
    }

    registerInBackend() {
        throw new Error("registerInBackend is not implemented for this node", this)
    }

    contains(other) {
        if (!other) {
            return false
        }

        let current = other
        while (current) {
            if (current.__node_idx != null && current.__node_idx === this.__node_idx) {
                return true
            }
            current = current.parentNode
        }
        return false
    }

    compareDocumentPosition(other) {
        if (other && other.__node_idx === this.__node_idx) {
            return 0
        }
        return Node.DOCUMENT_POSITION_FOLLOWING
    }

    isEqualNode(other) {
        return nodesAreEqual(this, other)
    }

    prepend(...elements) {
        const firstChild = this.firstChild
        for (const element of elements) {
            this.insertBefore(element, firstChild)
        }
    }

    appendChild(element) {
        return this.insertBefore(element, null)
    }

    get childNodes() {
        return withDocument(this.ownerDocument, () => core.ops.op_get_child_nodes(this.__node_idx).map(nodeToElement))
    }

    get children() {
        return this.childNodes.filter(node => node.nodeType === Node.ELEMENT_NODE)
    }

    get lastChild() {
        const child = core.ops.op_get_edge_child(this.__node_idx, true)
        return child ? nodeToElement(child) : null
    }

    hasChildNodes() {
        return this.childNodes.length > 0
    }

    removeChild(element) {
        if (!element) {
            throw new TypeError("Element is not an object")
        }

        if (element.__node_idx != null) {
            core.ops.op_remove_child(element.__node_idx)
        }
        return element
    }

    replaceChild(newChild, oldChild) {
        this.insertBefore(newChild, oldChild)
        this.removeChild(oldChild)
        return oldChild
    }

    insertBefore(newNode, referenceNode) {
        if (!newNode) {
            throw new TypeError("insertBefore called without newNode")
        }
        if (referenceNode && newNode.__node_idx === referenceNode.__node_idx) {
            return newNode
        }
        if (core.ops.op_would_create_cycle(this.__node_idx, newNode.__node_idx)) {
            throw new Error("Cannot insert a node into itself or its descendants")
        }
        if (newNode.nodeType === Node.DOCUMENT_FRAGMENT_NODE) {
            for (const child of newNode.childNodes) {
                this.insertBefore(child, referenceNode)
            }
            return newNode
        }
        core.ops.op_append_child(this.__node_idx, newNode.__node_idx, referenceNode?.__node_idx)
        return newNode
    }

    querySelector(selector) {
        const node = core.ops.op_query_selector(selector, this.__node_idx)
        return withDocument(this.ownerDocument, () => node ? nodeToElement(node) : null)
    }

    querySelectorAll(selector) {
        const nodes = core.ops.op_query_selector_all(selector, this.__node_idx)
        return withDocument(this.ownerDocument, () => nodes.map(nodeToElement))
    }

    get textContent() {
        return core.ops.op_get_text_content(this.__node_idx)
    }

    set textContent(value) {
        core.ops.op_set_text_content(this.__node_idx, value);
    }

    getElementsByTagName(tag) {
        const nodes = core.ops.op_get_elements_by_tag_name(tag, this.__node_idx, this.ownerDocument.__frameId)
        return withDocument(this.ownerDocument, () => nodes.map(nodeToElement))
    }
}

function nodeNameForEquality(node) {
    if (node.nodeName != null) {
        return node.nodeName
    }

    switch (node.nodeType) {
        case Node.TEXT_NODE:
            return "#text"
        case Node.COMMENT_NODE:
            return "#comment"
        case Node.DOCUMENT_NODE:
            return "#document"
        case Node.DOCUMENT_FRAGMENT_NODE:
            return "#document-fragment"
        default:
            return null
    }
}

function nodeValueForEquality(node) {
    if (node.nodeType === Node.TEXT_NODE || node.nodeType === Node.COMMENT_NODE) {
        return node.nodeValue ?? node.textContent ?? ""
    }
    return node.nodeValue ?? null
}

function nodeLocalNameForEquality(node) {
    if (node.nodeType !== Node.ELEMENT_NODE) {
        return node.localName ?? null
    }

    return node.localName ?? node.tag ?? node.tagName?.toLowerCase() ?? null
}

function nodeChildrenForEquality(node) {
    if (node.nodeType === Node.TEXT_NODE || node.nodeType === Node.COMMENT_NODE) {
        return []
    }
    if (node.nodeType === Node.DOCUMENT_NODE) {
        const root = node.documentElement
        return root ? [root] : []
    }
    return Array.from(node.childNodes ?? [])
}

function nodeAttributesForEquality(node) {
    if (node.nodeType !== Node.ELEMENT_NODE) {
        return []
    }
    return Array.from(node.attributes ?? [])
}

function nodesHaveEqualAttributes(left, right) {
    const leftAttributes = nodeAttributesForEquality(left)
    const rightAttributes = nodeAttributesForEquality(right)
    if (leftAttributes.length !== rightAttributes.length) {
        return false
    }

    for (const attribute of leftAttributes) {
        const rightAttribute = rightAttributes.find(candidate => candidate.name === attribute.name)
        if (!rightAttribute || rightAttribute.value !== attribute.value) {
            return false
        }
    }

    return true
}

function nodesAreEqual(left, right) {
    if (left === right) {
        return true
    }
    if (!right || right.nodeType == null || left.nodeType !== right.nodeType) {
        return false
    }

    if (nodeNameForEquality(left) !== nodeNameForEquality(right)) {
        return false
    }
    if (nodeLocalNameForEquality(left) !== nodeLocalNameForEquality(right)) {
        return false
    }
    if ((left.namespaceURI ?? null) !== (right.namespaceURI ?? null)) {
        return false
    }
    if ((left.prefix ?? null) !== (right.prefix ?? null)) {
        return false
    }
    if (nodeValueForEquality(left) !== nodeValueForEquality(right)) {
        return false
    }
    if (!nodesHaveEqualAttributes(left, right)) {
        return false
    }

    const leftChildren = nodeChildrenForEquality(left)
    const rightChildren = nodeChildrenForEquality(right)
    if (leftChildren.length !== rightChildren.length) {
        return false
    }

    return leftChildren.every((child, index) => nodesAreEqual(child, rightChildren[index]))
}

BaseNode.ELEMENT_NODE = 1
BaseNode.TEXT_NODE = 3
BaseNode.COMMENT_NODE = 8
BaseNode.DOCUMENT_NODE = 9
BaseNode.DOCUMENT_FRAGMENT_NODE = 11
BaseNode.DOCUMENT_POSITION_PRECEDING = 2
BaseNode.DOCUMENT_POSITION_FOLLOWING = 4

Object.defineProperty(globalThis, "Node", {
    value: BaseNode,
    enumerable: true,
    configurable: true,
    writable: true,
})

const NodeFilter = {
    FILTER_ACCEPT: 1,
    FILTER_REJECT: 2,
    FILTER_SKIP: 3,
    SHOW_ALL: 0xFFFFFFFF,
    SHOW_ELEMENT: 0x1,
    SHOW_ATTRIBUTE: 0x2,
    SHOW_TEXT: 0x4,
    SHOW_CDATA_SECTION: 0x8,
    SHOW_ENTITY_REFERENCE: 0x10,
    SHOW_ENTITY: 0x20,
    SHOW_PROCESSING_INSTRUCTION: 0x40,
    SHOW_COMMENT: 0x80,
    SHOW_DOCUMENT: 0x100,
    SHOW_DOCUMENT_TYPE: 0x200,
    SHOW_DOCUMENT_FRAGMENT: 0x400,
    SHOW_NOTATION: 0x800,
}

Object.defineProperty(globalThis, "NodeFilter", {
    value: NodeFilter,
    enumerable: true,
    configurable: true,
    writable: true,
})

class CustomElementRegistry {
    constructor() {
        this.definitions = new Map()
    }

    // TODO: Definition validation, element upgrades, lifecycle callbacks, and whenDefined().
    define(name, constructor) {
        this.definitions.set(name, constructor)
    }

    get(name) {
        return this.definitions.get(name)
    }
}

Object.defineProperty(globalThis, "CustomElementRegistry", {
    value: CustomElementRegistry,
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperty(globalThis, "customElements", {
    value: new CustomElementRegistry(),
    enumerable: true,
    configurable: true,
    writable: true,
})

class DocumentFragment extends BaseNode {
    constructor() {
        super()
        if (autoRegisterNode) {
            this.registerInBackend()
        }
    }

    registerInBackend() {
        this.__node_idx = core.ops.op_create_document_fragment()
        cacheNodeElement(this.__node_idx, this)
    }

    get nodeType() { return Node.DOCUMENT_FRAGMENT_NODE }
    get nodeName() { return "#document-fragment" }
    get nodeValue() { return null }
}

Object.defineProperty(globalThis, "DocumentFragment", {
    value: DocumentFragment,
    enumerable: true,
    configurable: true,
    writable: true,
})

class TreeWalker {
    constructor(root) {
        this.root = root
        this.currentNode = root
        // TODO: Filtering, live DOM changes, and repositioning currentNode.
        this.nodes = core.ops.op_get_descendant_nodes(root.__node_idx ?? null).map(nodeToElement)
        this.index = 0
    }

    nextNode() {
        if (this.index === this.nodes.length) return null
        this.currentNode = this.nodes[this.index++]
        return this.currentNode
    }
}

Object.defineProperty(globalThis, "TreeWalker", {
    value: TreeWalker,
    enumerable: true,
    configurable: true,
    writable: true,
})

class TextNode extends BaseNode {
    constructor(text) {
        super()
        this.text = text
        if (autoRegisterNode) {
            this.registerInBackend()
        }
    }

    registerInBackend() {
        this.__node_idx = core.ops.op_create_text_element(this.text)
        cacheNodeElement(this.__node_idx, this)
    }

    get data() { return this.text }
    set data(value) {
        this.text = String(value)
        if (this.__node_idx != null) {
            core.ops.op_set_text_content(this.__node_idx, this.text)
        }
    }

    get nodeValue() { return this.text }
    set nodeValue(value) { this.data = value }

    get textContent() { return this.text }
    set textContent(value) { this.data = value }

    get nodeType() {
        return 3
    }
}

Object.defineProperty(globalThis, "Text", {
    value: TextNode,
    enumerable: true,
    configurable: true,
    writable: true,
})

class CDATASection extends TextNode {
    constructor() {
        throw new TypeError("CDATASection construction is not implemented")
    }

    get nodeType() { return 4 }
}

Object.defineProperty(globalThis, "CDATASection", {
    value: CDATASection,
    enumerable: true,
    configurable: true,
    writable: true,
})

// TODO: CharacterData inheritance once that interface is implemented.
class ProcessingInstruction extends BaseNode {
    constructor() {
        throw new TypeError("ProcessingInstruction construction is not implemented")
    }

    get nodeType() { return 7 }
}

Object.defineProperty(globalThis, "ProcessingInstruction", {
    value: ProcessingInstruction,
    enumerable: true,
    configurable: true,
    writable: true,
})

const { Event } = denoEvent

Object.defineProperty(globalThis, "Event", {
    value: Event,
    enumerable: true,
    configurable: true,
    writable: true,
});

class MouseEvent extends Event {
    constructor(type, options = {}) {
        super(type, options)
        this.detail = options.detail ?? 0
        this.clientX = options.clientX ?? 0
        this.clientY = options.clientY ?? 0
        this.screenX = options.screenX ?? this.clientX
        this.screenY = options.screenY ?? this.clientY
        this.button = options.button ?? 0
        this.buttons = options.buttons ?? 0
        this.ctrlKey = options.ctrlKey ?? false
        this.shiftKey = options.shiftKey ?? false
        this.altKey = options.altKey ?? false
        this.metaKey = options.metaKey ?? false
    }
}

Object.defineProperty(globalThis, "MouseEvent", {
    value: MouseEvent,
    enumerable: true,
    configurable: true,
    writable: true,
});

class KeyboardEvent extends Event {
    constructor(type, options = {}) {
        super(type, options)
        this.key = options.key ?? ""
        this.code = options.code ?? ""
        this.location = options.location ?? 0
        this.ctrlKey = options.ctrlKey ?? false
        this.shiftKey = options.shiftKey ?? false
        this.altKey = options.altKey ?? false
        this.metaKey = options.metaKey ?? false
        this.repeat = options.repeat ?? false
        this.isComposing = options.isComposing ?? false
        this.keyCode = options.keyCode ?? 0
        this.charCode = options.charCode ?? 0
        this.which = options.which ?? 0
    }
}

Object.defineProperty(globalThis, "KeyboardEvent", {
    value: KeyboardEvent,
    enumerable: true,
    configurable: true,
    writable: true,
})

class PointerEvent extends MouseEvent {
    constructor(type, options = {}) {
        super(type, options)
        this.pointerId = options.pointerId ?? 1
        this.width = options.width ?? 1
        this.height = options.height ?? 1
        this.pressure = options.pressure ?? 0
        this.tangentialPressure = options.tangentialPressure ?? 0
        this.tiltX = options.tiltX ?? 0
        this.tiltY = options.tiltY ?? 0
        this.twist = options.twist ?? 0
        this.pointerType = options.pointerType ?? "mouse"
        this.isPrimary = options.isPrimary ?? true
    }
}

Object.defineProperty(globalThis, "PointerEvent", {
    value: PointerEvent,
    enumerable: true,
    configurable: true,
    writable: true,
});

class InputEvent extends Event {
    constructor(type, options = {}) {
        super(type, options)
        this.data = options.data ?? null
        this.inputType = options.inputType ?? ""
        this.isComposing = options.isComposing ?? false
    }
}

Object.defineProperty(globalThis, "InputEvent", {
    value: InputEvent,
    enumerable: true,
    configurable: true,
    writable: true,
});

let autoRegisterNode = true

function withoutAutoRegisterNode(cb) {
    let prev = autoRegisterNode
    autoRegisterNode = false
    let res = null
    try {
        res = cb()
    } finally {
        autoRegisterNode = prev
    }
    return res
}

// TODO: Live attribute access and writing dataset values back to the element.
class DOMStringMap {}

Object.defineProperty(globalThis, "DOMStringMap", {
    value: DOMStringMap,
    enumerable: true,
    configurable: true,
    writable: true,
})

class HtmlElement extends BaseNode {
    constructor(tag) {
        super()
        this.tag = tag
        this.namespaceURI = "http://www.w3.org/1999/xhtml"
        if (autoRegisterNode) {
            this.registerInBackend()
        }
    }

    registerInBackend() {
        this.__node_idx = core.ops.op_create_element(this.tag, this.ownerDocument.__frameId)
        cacheNodeElement(this.__node_idx, this)
    }

    click() {
        return this.dispatchEvent(new MouseEvent("click", {
            bubbles: true,
            cancelable: true,
            composed: true,
            detail: 1,
        }))
    }

    get attributes() {
        const attributeEntries = Object.entries(core.ops.op_get_attributes(this.__node_idx))
        const attributes = attributeEntries.map(([name, value]) => ({
            name,
            value,
            nodeName: name,
            nodeValue: value,
            textContent: value,
            specified: true,
        }))

        attributes.item = index => attributes[index] ?? null
        attributes.getNamedItem = name => attributes.find(attribute => attribute.name === name) ?? null
        for (const attribute of attributes) {
            attributes[attribute.name] = attribute
        }

        return attributes
    }

    getAttributeNames() {
        return Object.keys(core.ops.op_get_attributes(this.__node_idx))
    }

    getElementsByClassName(classNames) {
        const nodes = core.ops.op_get_elements_by_class_name(
            String(classNames),
            this.__node_idx,
            this.ownerDocument.__frameId,
        )
        return withDocument(this.ownerDocument, () => nodes.map(nodeToElement))
    }

    getAttribute(attr) {
        return core.ops.op_get_attribute(this.__node_idx, String(attr))
    }

    setAttribute(attr, value) {
        core.ops.op_update_attributes(this.__node_idx, { [String(attr)]: String(value) }, this.ownerDocument.__frameId)
    }

    removeAttribute(attr) {
        core.ops.op_remove_attribute(this.__node_idx, String(attr))
    }

    hasAttribute(attr) {
        return this.getAttribute(attr) != null
    }

    toggleAttribute(attr, force = undefined) {
        if (arguments.length === 0) {
            throw new TypeError("toggleAttribute requires an attribute name")
        }

        const name = String(attr)
        const present = this.hasAttribute(name)
        const shouldBePresent = force === undefined ? !present : Boolean(force)

        if (shouldBePresent && !present) {
            this.setAttribute(name, "")
        } else if (!shouldBePresent && present) {
            this.removeAttribute(name)
        }

        return shouldBePresent
    }

    remove() {
        this.parentNode?.removeChild(this)
    }

    getComputedStyle() {
        return getComputedStyle(this)
    }

    closest(selector) {
        const node = core.ops.op_get_closest(selector, this.__node_idx)
        return withDocument(this.ownerDocument, () => node ? nodeToElement(node) : null)
    }

    matches(selector) {
        const node = core.ops.op_get_closest(selector, this.__node_idx)
        return node ? node[0] === this.__node_idx : false
    }

    focus() {
        document.activeElement = this
        this.dispatchEvent(new Event("focus", { bubbles: false, cancelable: false }))
    }

    blur() {
        if (document.activeElement?.__node_idx === this.__node_idx) {
            document.activeElement = document.body
        }
        this.dispatchEvent(new Event("blur", { bubbles: false, cancelable: false }))
    }

    get tagName() {
        return this.tag.toUpperCase()
    }

    get nodeName() {
        return this.tagName
    }

    get innerHTML() {
        return core.ops.op_get_inner_html(this.__node_idx, this.ownerDocument.__frameId)
    }

    get outerHTML() {
        const attributes = this.attributes
            .map(attribute => ` ${attribute.name}="${attribute.value}"`)
            .join("")
        return `<${this.tag}${attributes}>${this.innerHTML}</${this.tag}>`
    }

    get nodeType() {
        return 1
    }

    set innerHTML(value) {
        core.ops.op_set_inner_html(this.__node_idx, value, this.ownerDocument.__frameId);
    }

    get classList() {
        return new ClassList(this.getAttribute('class'), this)
    }

    get sheet() {
        if ((this.tag !== "style" && this.tag !== "link") || !this.isConnected) {
            return null
        }
        const data = core.ops.op_get_stylesheet(this.__node_idx, false)
        if (!data) return null
        let sheet = styleSheets.get(this)
        if (!sheet || sheet.href !== data.href) {
            sheet = new CSSStyleSheet(this, data.href)
            styleSheets.set(this, sheet)
        }
        return sheet
    }

    get style() {
        return new CSSStyleDeclaration(this.getAttribute('style'), this)
    }

    set style(value) {
        if (!(value instanceof CSSStyleDeclaration)) {
            throw new TypeError("Unsupported style value (for now)")
        }
        this.setAttribute('style', value)
    }

    get href() {
        const value = this.getAttribute("href")
        return value == null ? "" : new URL(value, globalThis.location.href).href
    }

    set href(value) {
        this.setAttribute('href', value)
    }

    get hash() {
        return this.href ? new URL(this.href).hash : ""
    }

    get host() {
        return this.href ? new URL(this.href).host : ""
    }

    get pathname() {
        return this.href ? new URL(this.href).pathname : ""
    }

    get rel() {
        return this.getAttribute('rel') ?? ''
    }

    set rel(value) {
        this.setAttribute('rel', value)
    }

    get relList() {
        return {
            supports(feature) {
                return feature === 'modulepreload'
            }
        }
    }

    get src() {
        return this.getAttribute('src') ?? ""
    }

    set src(value) {
        this.setAttribute('src', value)
    }

    get srcset() {
        return this.getAttribute('srcset') ?? ""
    }

    set srcset(value) {
        this.setAttribute('srcset', value)
    }

    get loading() {
        return this.getAttribute('loading') ?? ""
    }

    set loading(value) {
        this.setAttribute('loading', value)
    }

    get id() {
        return this.getAttribute('id')
    }

    set id(value) {
        this.setAttribute('id', value)
    }

    get className() {
        return this.getAttribute('class') ?? ''
    }

    set className(value) {
        this.setAttribute('class', value)
    }

    get value() {
        return this.getAttribute('value') ?? ''
    }

    set value(value) {
        this.setAttribute('value', value)
    }

    get selected() {
        return this.hasAttribute('selected')
    }

    set selected(value) {
        if (value) {
            this.setAttribute('selected', '')
        } else {
            this.removeAttribute('selected')
        }
    }

    get checked() {
        return this.hasAttribute('checked')
    }

    set checked(value) {
        if (value) {
            this.setAttribute('checked', '')
        } else {
            this.removeAttribute('checked')
        }
    }

    get height() {
        return Number.parseFloat(this.getAttribute('height')) || 0
    }

    set height(value) {
        this.setAttribute('height', value)
    }

    get width() {
        return Number.parseFloat(this.getAttribute('width')) || 0
    }

    set width(value) {
        this.setAttribute('width', value)
    }

    get clientWidth() {
        return Number.parseFloat(this.getAttribute("width")) || globalThis.innerWidth || 0
    }

    get clientHeight() {
        return Number.parseFloat(this.getAttribute("height")) || globalThis.innerHeight || 0
    }

    get offsetWidth() {
        return this.clientWidth
    }

    get offsetHeight() {
        return this.clientHeight
    }

    get scrollWidth() {
        return this.clientWidth
    }

    get scrollHeight() {
        return this.clientHeight
    }

    getClientRects() {
        return [this.getBoundingClientRect()]
    }

    getBoundingClientRect() {
        const width = this.clientWidth
        const height = this.clientHeight
        return {
            x: 0,
            y: 0,
            left: 0,
            top: 0,
            width,
            height,
            right: width,
            bottom: height,
        }
    }

    scrollIntoView() {}

    select() {}

    get dataset() {
        const attributes = core.ops.op_get_attributes(this.__node_idx)
        let data = Object.entries(attributes)
            .filter(([key, value]) => key.startsWith('data-'))
            .map(([key, value]) => [camelize(key.replace('data-', '')).replaceAll('-', ''), value])
        return Object.setPrototypeOf(Object.fromEntries(data), DOMStringMap.prototype)
    }
}

function camelize(str) {
    return str.replace(/(?:^\w|[A-Z]|\b\w|\s+)/g, function(match, index) {
        if (+match === 0) return "";
        return index === 0 ? match.toLowerCase() : match.toUpperCase();
    });
}

const CANVAS_COMMAND_POINT = "point"
const CANVAS_COMMAND_MOVE_TO = "moveTo"
const CANVAS_COMMAND_CLOSE = "close"
const CANVAS_COMMAND_BEZIER_CURVE = "bezierCurve"
const CANVAS_COMMAND_FILL_RECT = "fillRect"
const CANVAS_COMMAND_STROKE_RECT = "strokeRect"
const CANVAS_COMMAND_TRANSFORM = "transform"
const CANVAS_COMMAND_RESET_TRANSFORM = "resetTransform"
const CANVAS_COMMAND_SAVE = "save"
const CANVAS_COMMAND_RESTORE = "restore"
const CANVAS_COMMAND_CLEAR_RECT = "clearRect"
const CANVAS_COMMAND_BEGIN_PATH = "beginPath"

class CanvasGradient {
    constructor() {
        this.colorStops = []
    }

    addColorStop(offset, color) {
        this.colorStops.push([offset, color])
    }
}

class CanvasRenderingContext2D {
    constructor(canvas) {
        this.canvas = canvas
        this.lineWidth = 1
        this.fillStyle = "#000000"
        this.strokeStyle = "#000000"
    }

    fillRect(x, y, width, height) {
        core.ops.op_canvas_record_command(this.canvas.__node_idx, {
            type: CANVAS_COMMAND_FILL_RECT,
            x,
            y,
            width,
            height
        })
        core.ops.op_canvas_paint(this.canvas.__node_idx)
    }

    strokeRect(x, y, width, height) {
        core.ops.op_canvas_record_command(this.canvas.__node_idx, {
            type: CANVAS_COMMAND_STROKE_RECT,
            x,
            y,
            width,
            height,
            line_width: lineWidth
        })
        core.ops.op_canvas_paint(this.canvas.__node_idx)
    }

    clearRect(x, y, width, height) {
        core.ops.op_canvas_record_command(this.canvas.__node_idx, {
            type: CANVAS_COMMAND_CLEAR_RECT,
            x,
            y,
            width,
            height
        })
        core.ops.op_canvas_paint(this.canvas.__node_idx)
    }

    save() {
        core.ops.op_canvas_record_command(this.canvas.__node_idx, {
            type: CANVAS_COMMAND_SAVE
        })
    }

    restore() {
        core.ops.op_canvas_record_command(this.canvas.__node_idx, {
            type: CANVAS_COMMAND_RESTORE
        })
    }

    clip(firstArg = null, secondArg = null) {
        let path = null
        let fillRule = "nonzero"
        if (firstArg instanceof Path2D) {
            path = firstArg.path
            if (typeof secondArg === "string") {
                fillRule = secondArg
            }
        } else if (typeof firstArg === "string") {
            fillRule = firstArg
        }

        core.ops.op_canvas_path_clip(this.canvas.__node_idx, path, fillRule)
    }

    // TODO: Rasterize gradients instead of falling back to the existing solid canvas color.
    createLinearGradient() {
        return new CanvasGradient()
    }

    // TODO: Rasterize gradients instead of falling back to the existing solid canvas color.
    createRadialGradient() {
        return new CanvasGradient()
    }

    drawImage(image, ...args) {
        if (!(image instanceof HTMLImageElement) || image.__node_idx == null) {
            return
        }

        let x
        let y
        let width = null
        let height = null
        if (args.length === 2) {
            [x, y] = args
        } else if (args.length === 4) {
            [x, y, width, height] = args
        } else {
            // TODO: Support the source-cropping drawImage overload.
            return
        }

        const queued = core.ops.op_canvas_draw_image(
            this.canvas.__node_idx,
            image.__node_idx,
            { x, y, width, height },
        )
        if (queued) {
            core.ops.op_canvas_paint(this.canvas.__node_idx)
        }
    }

    beginPath() {
        core.ops.op_canvas_record_command(this.canvas.__node_idx, {
            type: CANVAS_COMMAND_BEGIN_PATH
        })
    }

    moveTo(x, y) {
        core.ops.op_canvas_record_command(this.canvas.__node_idx, {
            type: CANVAS_COMMAND_MOVE_TO,
            point: [x, y]
        })
    }

    lineTo(x, y) {
        core.ops.op_canvas_record_command(this.canvas.__node_idx, {
            type: CANVAS_COMMAND_POINT,
            point: [x, y]
        })
    }

    arc() {
        // TODO: Implement this
    }

    closePath() {
        core.ops.op_canvas_record_command(this.canvas.__node_idx, {
            type: CANVAS_COMMAND_CLOSE
        })
    }

    bezierCurveTo(cp1x, cp1y, cp2x, cp2y, x, y) {
        core.ops.op_canvas_record_command(this.canvas.__node_idx, {
            type: CANVAS_COMMAND_BEZIER_CURVE,
            cp1: [cp1x, cp1y],
            cp2: [cp2x, cp2y],
            endpoint: [x, y]
        })
    }

    stroke(suppliedPath = null) {
        const path = suppliedPath && suppliedPath instanceof Path2D ? suppliedPath.path : null
        const lineWidth = suppliedPath && suppliedPath instanceof Path2D ? suppliedPath.lineWidth : this.lineWidth
        const strokeStyle = typeof this.strokeStyle === "string" ? this.strokeStyle : "#000000"

        core.ops.op_canvas_path_stroke(this.canvas.__node_idx, path, lineWidth, strokeStyle)
        core.ops.op_canvas_paint(this.canvas.__node_idx)
    }

    fill(firstArg = null, secondArg = null) {
        let suppliedPath = null;
        let fillRule = "nonzero";
        if (firstArg && secondArg) {
            suppliedPath = firstArg
            fillRule = secondArg
        } else if (firstArg && firstArg instanceof Path2D) {
            suppliedPath = firstArg
        } else if (firstArg && typeof firstArg === "string") {
            fillRule = firstArg
        }

        const path = suppliedPath && suppliedPath instanceof Path2D ? suppliedPath.path : null
        const fillStyle = typeof this.fillStyle === "string" ? this.fillStyle : "#000000"

        core.ops.op_canvas_path_fill(this.canvas.__node_idx, path, fillStyle, fillRule)
        core.ops.op_canvas_paint(this.canvas.__node_idx)
    }

    transform(a, b, c, d, e, f) {
        core.ops.op_canvas_record_command(this.canvas.__node_idx, {
            type: CANVAS_COMMAND_TRANSFORM,
            matrix: {
                data: [
                    a, c, e,
                    b, d, f,
                    0, 0, 1,
                ],
                rows: 3,
                columns: 3,
            },
        })
    }

    resetTransform() {
        core.ops.op_canvas_record_command(this.canvas.__node_idx, {
            type: CANVAS_COMMAND_RESET_TRANSFORM,
        })
    }
}

class Path2D {
    constructor() {
        this.path = []
        this.lineWidth = 1
    }

    moveTo(x, y) {
        this.path.push({
            type: CANVAS_COMMAND_MOVE_TO,
            point: [x, y]
        })
    }

    lineTo(x, y) {
        this.path.push({
            type: CANVAS_COMMAND_POINT,
            point: [x, y]
        })
    }

    closePath() {
        this.path.push({ type: CANVAS_COMMAND_CLOSE })
    }

    bezierCurveTo(cp1x, cp1y, cp2x, cp2y, x, y) {
        this.path.push({
            type: CANVAS_COMMAND_BEZIER_CURVE,
            cp1: [cp1x, cp1y],
            cp2: [cp2x, cp2y],
            endpoint: [x, y]
        })
    }
}

class HtmlCanvasElement extends HtmlElement {
    constructor(tag) {
        super(tag)

        this.__contexts = {}
    }

    getContext(type) {
        if (type === "2d") {
            if (!this.__contexts["2d"]) {
                this.__contexts["2d"] = new CanvasRenderingContext2D(this)
            }
            return this.__contexts["2d"]
        } else {
            return null
        }
    }
}

class HTMLIFrameElement extends HtmlElement {
    constructor() {
        super("iframe")
    }

    spawnFrame() {
        core.ops.op_spawn_frame(this.__node_idx, this.getAttribute("src"))
    }

    get src() {
        return this.getAttribute("src")
    }

    set src(src) {
        this.setAttribute("src", src)
        if (src) {
            this.spawnFrame()
        }
    }

    get contentDocument() {
        // Frame idx is the node idx
        this.spawnFrame()
        return new Document(this.__node_idx)
    }

    get contentWindow() {
        // Frame idx is the node idx
        this.spawnFrame()
        return new WindowProxy(this.__node_idx)
    }
}

class WindowProxy {
    constructor(frameId) {
        this.__frame_id = frameId
    }

    postMessage(message) {
        core.ops.op_post_message_to_frame(message, this.__frame_id)
    }

    get document() {
        return new Document(this.__frame_id)
    }
}

class HTMLScriptElement extends HtmlElement {
    constructor() {
        super("script")
    }

    get type() { return this.getAttribute("type") ?? "" }
    set type(value) { this.setAttribute("type", String(value)) }

    get src() { return this.getAttribute("src") ?? "" }
    set src(value) { this.setAttribute("src", String(value)) }

    get nonce() { return this.getAttribute("nonce") ?? "" }
    set nonce(value) { this.setAttribute("nonce", String(value)) }

    get async() { return this.hasAttribute("async") }
    set async(value) {
        if (value) {
            this.setAttribute("async", "")
        } else {
            this.removeAttribute("async")
        }
    }

    get defer() { return this.hasAttribute("defer") }
    set defer(value) {
        if (value) {
            this.setAttribute("defer", "")
        } else {
            this.removeAttribute("defer")
        }
    }

    get noModule() { return this.hasAttribute("nomodule") }
    set noModule(value) {
        if (value) {
            this.setAttribute("nomodule", "")
        } else {
            this.removeAttribute("nomodule")
        }
    }
}

class HTMLFormControlElement extends HtmlElement {
    constructor(tag) {
        super(tag)
        this.__customValidityMessage = ""
    }

    setCustomValidity(message) {
        this.__customValidityMessage = String(message)
    }

    checkValidity() {
        return this.__customValidityMessage === ""
    }

    reportValidity() {
        return this.checkValidity()
    }

    get validationMessage() {
        return this.__customValidityMessage
    }

    get validity() {
        const customError = this.__customValidityMessage !== ""
        return {
            badInput: false,
            customError,
            patternMismatch: false,
            rangeOverflow: false,
            rangeUnderflow: false,
            stepMismatch: false,
            tooLong: false,
            tooShort: false,
            typeMismatch: false,
            valid: !customError,
            valueMissing: false,
        }
    }

    get willValidate() {
        return !this.hasAttribute("disabled")
    }
}

class HTMLInputElement extends HTMLFormControlElement {
    constructor() {
        super("input")
    }
}

class HTMLTextAreaElement extends HTMLFormControlElement {
    constructor() {
        super("textarea")
    }
}

class HTMLSelectElement extends HTMLFormControlElement {
    constructor() {
        super("select")
    }

    get options() {
        return this.getElementsByTagName("option")
    }
}

class HTMLButtonElement extends HTMLFormControlElement {
    constructor() {
        super("button")
    }
}

class HTMLFormElement extends HtmlElement {
    constructor() {
        super("form")
    }
}

class HTMLMediaElement extends HtmlElement {
    constructor(tag) {
        super(tag)
        this.paused = true
        this.__currentTime = 0
    }

    pause() {
        this.paused = true
    }

    play() {
        this.paused = false
        return Promise.resolve()
    }

    get currentTime() {
        return this.__currentTime
    }

    set currentTime(value) {
        const number = Number(value)
        this.__currentTime = Number.isFinite(number) ? number : 0
    }
}

class HTMLDivElement extends HtmlElement {
    constructor() {
        super("div")
    }
}

Object.defineProperty(globalThis, "HTMLDivElement", {
    value: HTMLDivElement,
    enumerable: true,
    configurable: true,
    writable: true,
})

class HTMLVideoElement extends HTMLMediaElement {
    constructor() {
        super("video")
    }
}

class HTMLAudioElement extends HTMLMediaElement {
    constructor() {
        super("audio")
    }
}

Object.defineProperty(globalThis, "Path2D", {
    value: Path2D,
    enumerable: true,
    configurable: true,
    writable: true,
});

Object.defineProperty(globalThis, "HTMLElement", {
    value: HtmlElement,
    enumerable: true,
    configurable: true,
    writable: true,
});
Object.defineProperty(globalThis, "Element", {
    value: HtmlElement,
    enumerable: true,
    configurable: true,
    writable: true,
});
Object.defineProperty(globalThis, "HTMLCanvasElement", {
    value: HtmlCanvasElement,
    enumerable: true,
    configurable: true,
    writable: true,
});
Object.defineProperty(globalThis, "HTMLIFrameElement", {
    value: HTMLIFrameElement,
    enumerable: true,
    configurable: true,
    writable: true,
});
Object.defineProperty(globalThis, "HTMLScriptElement", {
    value: HTMLScriptElement,
    enumerable: true,
    configurable: true,
    writable: true,
});
Object.defineProperty(globalThis, "HTMLInputElement", {
    value: HTMLInputElement,
    enumerable: true,
    configurable: true,
    writable: true,
});
Object.defineProperty(globalThis, "HTMLTextAreaElement", {
    value: HTMLTextAreaElement,
    enumerable: true,
    configurable: true,
    writable: true,
});
Object.defineProperty(globalThis, "HTMLSelectElement", {
    value: HTMLSelectElement,
    enumerable: true,
    configurable: true,
    writable: true,
});
Object.defineProperty(globalThis, "HTMLButtonElement", {
    value: HTMLButtonElement,
    enumerable: true,
    configurable: true,
    writable: true,
});
Object.defineProperty(globalThis, "HTMLFormElement", {
    value: HTMLFormElement,
    enumerable: true,
    configurable: true,
    writable: true,
});
Object.defineProperty(globalThis, "HTMLMediaElement", {
    value: HTMLMediaElement,
    enumerable: true,
    configurable: true,
    writable: true,
});
Object.defineProperty(globalThis, "HTMLVideoElement", {
    value: HTMLVideoElement,
    enumerable: true,
    configurable: true,
    writable: true,
});
Object.defineProperty(globalThis, "HTMLAudioElement", {
    value: HTMLAudioElement,
    enumerable: true,
    configurable: true,
    writable: true,
});

const intersectionObserverMapping = {}

class IntersectionObserver {
    constructor(callback) {
        if (typeof callback !== "function") {
            throw new TypeError("IntersectionObserver callback must be a function")
        }

        this.callback = callback
        this.targets = new Set()
    }

    observe(target) {
        if (!(target instanceof HTMLElement)) {
            throw new Error("Target must be an element")
        }
        if (this.targets.has(target)) {
            return
        }
        this.targets.add(target)
        intersectionObserverMapping[target.__node_idx] = this
        core.ops.op_track_intersection(target.__node_idx)
    }

    unobserve(target) {
        if (!this.targets.delete(target)) {
            return
        }
        intersectionObserverMapping[target.__node_idx] = undefined
        core.ops.op_untrack_intersection(target.__node_idx)
    }

    disconnect() {
        for (const target of this.targets) {
            intersectionObserverMapping[target.__node_idx] = undefined
            core.ops.op_untrack_intersection(target.__node_idx)
        }
        this.targets.clear()
    }

    takeRecords() {
        return []
    }
}

function runIntersectionObservers(intersectingNodeIdxs, notIntersectingNodeIdxs) {
    const entriesByObserver = new Map()

    for (const [nodeIdxs, isIntersecting] of [
        [intersectingNodeIdxs, true],
        [notIntersectingNodeIdxs, false],
    ]) {
        for (const idx of nodeIdxs) {
            const observer = intersectionObserverMapping[idx]
            if (!observer) {
                continue
            }

            const entries = entriesByObserver.get(observer) ?? []
            entries.push({
                target: __elementFromNodeIdx(idx),
                isIntersecting,
            })
            entriesByObserver.set(observer, entries)
        }
    }

    for (const [observer, entries] of entriesByObserver) {
        observer.callback(entries, observer)
    }
}

Object.defineProperty(globalThis, "__runIntersectionObservers", {
    value: runIntersectionObservers,
    enumerable: true,
    configurable: true,
    writable: true,
});

Object.defineProperty(globalThis, "IntersectionObserver", {
    value: IntersectionObserver,
    enumerable: true,
    configurable: true,
    writable: true,
});

class ResizeObserver {
    constructor(callback) {
        if (typeof callback !== "function") {
            throw new TypeError("ResizeObserver callback must be a function")
        }
        this.callback = callback
        this.targets = new Set()
    }

    observe(target) {
        this.targets.add(target)
    }

    unobserve(target) {
        this.targets.delete(target)
    }

    disconnect() {
        this.targets.clear()
    }
}

Object.defineProperty(globalThis, "ResizeObserver", {
    value: ResizeObserver,
    enumerable: true,
    configurable: true,
    writable: true,
});

const styleSheets = new WeakMap()

// Read-only CSSOM subset. Rule declarations, nested rules and stylesheet editing
// are not exposed yet; selectors come from the same parser used for rendering.
class CSSRule {
    constructor(parentStyleSheet) {
        this.parentStyleSheet = parentStyleSheet
        this.parentRule = null
    }
}

CSSRule.STYLE_RULE = 1
CSSRule.prototype.STYLE_RULE = 1

class CSSStyleRule extends CSSRule {
    constructor(parentStyleSheet, selectorText) {
        super(parentStyleSheet)
        this.__selectorText = selectorText
    }

    get type() { return CSSRule.STYLE_RULE }
    get selectorText() { return this.__selectorText }
}

class CSSStyleSheet {
    constructor(ownerNode, href = null) {
        if (!ownerNode) throw new TypeError("Constructed stylesheets are not implemented")
        this.ownerNode = ownerNode
        this.href = href
        this.type = "text/css"
    }

    get cssRules() {
        const data = core.ops.op_get_stylesheet(this.ownerNode.__node_idx, true)
        if (data?.href && new URL(data.href).origin !== new URL(this.ownerNode.ownerDocument.location.href).origin) {
            throw new DOMException.DOMException("Cannot read a cross-origin stylesheet", "SecurityError")
        }
        const rules = (data?.selectors ?? []).map(selector => selector === null
            ? new CSSRule(this)
            : new CSSStyleRule(this, selector))
        rules.item = index => rules[index] ?? null
        return rules
    }

    get rules() { return this.cssRules }
}

for (const type of [CSSRule, CSSStyleRule, CSSStyleSheet]) {
    Object.defineProperty(globalThis, type.name, {
        value: type,
        configurable: true,
        writable: true,
    })
}

class CSSStyleDeclaration {
    constructor(style, element) {
        this.__element = element
        this.cssText = style

        return new Proxy(this, {
            get(target, key, receiver) {
                if (typeof key === "string" && !(key in target)) {
                    return target.getPropertyValue(key)
                }

                return Reflect.get(target, key, receiver)
            },
            set(target, key, value) {
                if (typeof key === "symbol" || String(key).startsWith("__")) {
                    return Reflect.set(target, key, value)
                }

                target.setProperty(key, value)
                return true
            }
        })
    }

    get cssText() {
        let out = ""
        for (const [key, value] of Object.entries(this.__properties)) {
            out += `${key}:${value};`
        }
        return out
    }

    set cssText(style) {
        this.__properties = {}
        let pairs = style ? style.split(";") : []
        for (const pair of pairs) {
            const separator = pair.indexOf(":")
            if (separator === -1) continue

            let key = pair.slice(0, separator)
            let value = pair.slice(separator + 1)
            key = key?.trim()
            value = value?.trim()
            if (!key || !value) continue
            this.__properties[cssPropertyName(key)] = value
        }
    }

    getProperty(key) {
        return this.__properties[cssPropertyName(key)]
    }

    getPropertyValue(key) {
        return this.__properties[cssPropertyName(key)] ?? ""
    }

    setProperty(key, value) {
        if (key === "cssText") {
            this.cssText = value
            this.sync()
            return
        }
        key = cssPropertyName(key)
        if (this.__properties[key] === value) {
            return
        }
        this.__properties[key] = value
        this.sync()
    }

    sync() {
        const out = this.cssText
        this.__element.__style = out
        core.ops.op_update_attributes(this.__element.__node_idx, { style: out }, this.__element.ownerDocument.__frameId)
    }
}

Object.defineProperty(globalThis, "CSSStyleDeclaration", {
    value: CSSStyleDeclaration,
    enumerable: true,
    configurable: true,
    writable: true,
})

function cssPropertyName(key) {
    const keyString = String(key)
    if (keyString.startsWith("--")) {
        return keyString
    }

    return keyString.replace(/[A-Z]/g, letter => `-${letter.toLowerCase()}`)
}

class SVGElement extends HtmlElement {
    constructor(tag) {
        super(tag)

        this.namespaceURI = "http://www.w3.org/2000/svg"
    }
}

class Image extends HTMLElement {
    constructor() {
        super("img")
    }

    get width() {
        return super.width || this.naturalWidth || 0
    }

    set width(value) {
        super.width = value
    }

    get height() {
        return super.height || this.naturalHeight || 0
    }

    set height(value) {
        super.height = value
    }
}

Object.defineProperty(globalThis, "Image", {
    value: Image,
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperty(globalThis, "HTMLImageElement", {
    value: Image,
    enumerable: true,
    configurable: true,
    writable: true,
})

class HTMLTemplateElement extends HtmlElement {
    get content() {
        return withDocument(this.ownerDocument, () => elementFromNodeIdx(core.ops.op_get_template_content(this.__node_idx)))
    }
}

Object.defineProperty(globalThis, "HTMLTemplateElement", {
    value: HTMLTemplateElement,
    enumerable: true,
    configurable: true,
    writable: true,
})

class CommentNode extends BaseNode {
    constructor(data) {
        super()
        this.data = data
        if (autoRegisterNode) {
            this.registerInBackend()
        }
    }

    registerInBackend() {
        this.__node_idx = core.ops.op_create_comment_element(this.data)
        cacheNodeElement(this.__node_idx, this)
    }

    get nodeValue() { return this.data }
    set nodeValue(value) { this.textContent = value }

    get textContent() { return this.data }
    set textContent(value) {
        this.data = String(value)
        if (this.__node_idx != null) {
            core.ops.op_set_text_content(this.__node_idx, this.data)
        }
    }

    get nodeType() {
        return 8
    }
}

Object.defineProperty(globalThis, "Comment", {
    value: CommentNode,
    enumerable: true,
    configurable: true,
    writable: true,
})

class ClassList {
    constructor(str, element) {
        this.list = new Set((str || "").split(" "))
        this.element = element
    }

    sync() {
        this.element.class = Array.from(this.list).join(" ")
        core.ops.op_update_attributes(this.element.__node_idx, { class: this.element.class }, this.element.ownerDocument.__frameId)
    }

    add(...tokens) {
        let changed = false
        for (const token of tokens) {
            if (this.list.has(token)) {
                continue
            }
            this.list.add(token)
            changed = true
        }
        if (changed) {
            this.sync()
        }
    }

    contains(str) {
        return this.list.has(str)
    }

    toggle(str, force) {
        const shouldAdd = force === undefined ? !this.list.has(str) : !!force
        if (shouldAdd) {
            if (!this.list.has(str)) {
                this.list.add(str)
                this.sync()
            }
            return true
        }
        if (this.list.has(str)) {
            this.list.delete(str)
            this.sync()
        }
        return false
    }

    remove(...tokens) {
        let changed = false
        for (const token of tokens) {
            if (!this.list.has(token)) {
                continue
            }
            this.list.delete(token)
            changed = true
        }
        if (changed) {
            this.sync()
        }
    }

    get length() {
        return this.list.size
    }

    [Symbol.iterator]() {
        return this.list[Symbol.iterator]();
    }
}

const nodeMap = new Map()

function nodeMapKey(nodeIdx) {
    return `${currentDocument?.__frameId ?? "main"}:${nodeIdx}`
}

function clearNodeMap() {
    nodeMap.clear()
}

function cacheNodeElement(nodeIdx, element) {
    if (nodeIdx != null) {
        nodeMap.set(nodeMapKey(nodeIdx), element)
    }
}

Object.defineProperty(globalThis, "__clear_node_map", {
    value: clearNodeMap,
    enumerable: false,
    configurable: true,
    writable: true,
})

function nodeToElement(pair) {
    const node_idx = pair[0]
    const node = pair[1]
    const key = nodeMapKey(node_idx)
    const existing = nodeMap.get(key)
    if (existing) {
        return existing
    }
    let element;
    if (node.kind === "element") {
        const elementClass = tagToElement(node.tag)
        element = withoutAutoRegisterNode(() => new elementClass(node.tag))
    } else if (node.kind === "fragment") {
        element = withoutAutoRegisterNode(() => new DocumentFragment())
    } else if (node.kind === "comment") {
        element = withoutAutoRegisterNode(() => new CommentNode(node.comment))
    } else if (node.kind === "text") {
        element = withoutAutoRegisterNode(() => new TextNode(node.text))
    }
    element.__node_idx = node_idx
    nodeMap.set(key, element)
    return element
}

function elementFromNodeIdx(idx) {
    const element = core.ops.op_get_node(idx)
    return element ? nodeToElement(element) : null
}

Object.defineProperty(globalThis, "__elementFromNodeIdx", {
    value: elementFromNodeIdx,
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperty(globalThis, "SVGElement", {
    value: SVGElement,
    enumerable: true,
    configurable: true,
    writable: true,
})

function tagToElement(tag) {
    return tag === "svg" ?
        SVGElement :
        tag === "template" ?
            HTMLTemplateElement :
        tag === "canvas" ?
            HtmlCanvasElement :
            tag === "iframe" ?
                HTMLIFrameElement :
                tag === "script" ?
                    HTMLScriptElement :
                    tag === "input" ?
                        HTMLInputElement :
                    tag === "textarea" ?
                        HTMLTextAreaElement :
                    tag === "select" ?
                        HTMLSelectElement :
                    tag === "button" ?
                        HTMLButtonElement :
                    tag === "form" ?
                        HTMLFormElement :
                    tag === "video" ?
                        HTMLVideoElement :
                        tag === "audio" ?
                            HTMLAudioElement :
                            tag === "div" ?
                                HTMLDivElement :
                                HtmlElement
}

class Document extends EventTarget {
    constructor(frameId = null) {
        super()
        this.__frameId = frameId
        this.__activeElement = null
        this.__currentScript = null
    }
    get nodeType() {
        return Node.DOCUMENT_NODE
    }
    get hidden() {
        return false
    }
    get visibilityState() {
        return "visible"
    }
    get readyState() {
        return "complete"
    }
    get activeElement() {
        return this.__activeElement ?? this.body
    }
    set activeElement(element) {
        this.__activeElement = element
    }
    get defaultView() {
        return globalThis
    }
    get location() {
        return globalThis.location
    }
    set location(value) {
        globalThis.location.href = value
    }
    get cookie() {
        return core.ops.op_get_cookie(globalThis.location.href)
    }
    set cookie(newValue) {
        core.ops.op_set_cookie(globalThis.location.href, String(newValue))
    }
    get styleSheets() {
        const root = this.documentElement
        const sheets = root ? withDocument(this, () => core.ops.op_get_stylesheet_nodes(root.__node_idx)
            .map(idx => elementFromNodeIdx(idx).sheet).filter(Boolean)) : []
        sheets.item = index => sheets[index] ?? null
        return sheets
    }
    get scripts() {
        return this.querySelectorAll('script')
    }
    get links() {
        return this.querySelectorAll("a[href], area[href]")
    }
    get currentScript() {
        return this.__currentScript
    }
    get referrer() {
        return ""
    }
    createEvent(interfaceName) {
        if (String(interfaceName) === "CustomEvent") {
            return new CustomEvent("")
        }
        if (!["Event", "Events", "HTMLEvents"].includes(String(interfaceName))) {
            throw new DOMException.DOMException(
                `Unsupported event interface: ${interfaceName}`,
                "NotSupportedError",
            )
        }
        return new Event("")
    }
    write() {
        // TODO: Implement parser insertion for document.write.
    }
    hasStorageAccess() {
        return Promise.resolve(true)
    }
    requestStorageAccess() {
        return Promise.resolve()
    }
    get fonts() {
        return {
            status: "loaded",
            ready: Promise.resolve([]),
            load() {
                return Promise.resolve([])
            },
            check() {
                return true
            },
            addEventListener() {},
            removeEventListener() {},
            dispatchEvent() {
                return true
            },
        }
    }
    get documentElement() {
        return this.querySelector("html")
    }
    get head() {
        return this.querySelector("head")
    }
    get body() {
        return this.querySelector("body")
    }
    createElementNS(ns, tag) {
        tag = String(tag)
        const elementClass = tagToElement(tag)
        const element = withDocument(this, () => new elementClass(tag))
        element.namespaceURI = ns
        return element
    }
    createElement(tag, ...args) {
        tag = String(tag).replace(/[A-Z]/g, char => char.toLowerCase())
        const elementClass = tagToElement(tag)
        const element = withDocument(this, () => new elementClass(tag, ...args))
        return element
    }
    createComment(data) {
        const element = withDocument(this, () => new CommentNode(data))
        return element
    }
    getElementById(id) {
        const node = core.ops.op_get_element_by_id(id)
        return withDocument(this, () => node ? nodeToElement(node) : null)
    }
    getElementsByName(name) {
        const nodes = core.ops.op_get_elements_by_name(String(name), null, this.__frameId)
        return withDocument(this, () => nodes.map(nodeToElement))
    }
    getElementsByTagName(tag) {
        const nodes = core.ops.op_get_elements_by_tag_name(tag, null, this.__frameId)
        return withDocument(this, () => nodes.map(nodeToElement))
    }
    getElementsByClassName(classNames) {
        const nodes = core.ops.op_get_elements_by_class_name(String(classNames), null, this.__frameId)
        return withDocument(this, () => nodes.map(nodeToElement))
    }
    querySelector(selector) {
        const node = core.ops.op_query_selector(selector, null, this.__frameId)
        return withDocument(this, () => node ? nodeToElement(node) : null)
    }
    querySelectorAll(selector) {
        const nodes = core.ops.op_query_selector_all(selector, null, this.__frameId)
        return withDocument(this, () => nodes.map(nodeToElement))
    }
    getParent(event) {
        return event?.type === "load" ? null : this.defaultView
    }
    getRootNode() {
        return this
    }
    isEqualNode(other) {
        return nodesAreEqual(this, other)
    }
    createTextNode(text) {
        const element = new TextNode(text)
        return element
    }
    importNode(node, deep = false) {
        // TODO: Copy nodes between document backends.
        if (node.ownerDocument !== this) {
            throw new Error("Cross-document importNode is not implemented")
        }
        return node.cloneNode(deep)
    }
    createDocumentFragment() {
        return withDocument(this, () => new DocumentFragment())
    }
    createTreeWalker(root) {
        return new TreeWalker(root)
    }
    hasFocus() {
        return true
    }
    get implementation() {
        return {
            createHTMLDocument() {
                const element = new HTMLIFrameElement()
                element.setAttribute('src', 'about:blank')
                element.spawnFrame()
                return element.contentDocument
            },
            hasFeature() {
                return false
            }
        }
    }
}

const document = new Document()

Object.defineProperty(globalThis, "document", {
  value: document,
  enumerable: true,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "Document", {
  value: Document,
  enumerable: true,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "__set_current_script_node_idx", {
    value(nodeIdx) {
        document.__currentScript = nodeIdx == null ? null : elementFromNodeIdx(nodeIdx)
    },
    enumerable: false,
    configurable: true,
    writable: true,
})

let currentDocument = globalThis.document

function withDocument(documentToUse, cb) {
    let prev = currentDocument
    currentDocument = documentToUse
    let res = null
    try {
        res = cb()
    } finally {
        currentDocument = prev
    }
    return res
}

Object.defineProperty(globalThis, "setTimeout", {
  value: setTimeoutImpl,
  enumerable: true,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "clearTimeout", {
  value: clearTimeoutImpl,
  enumerable: true,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "requestAnimationFrame", {
  value: requestAnimationFrameImpl,
  enumerable: true,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "cancelAnimationFrame", {
  value: cancelAnimationFrameImpl,
  enumerable: true,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "setInterval", {
  value: setIntervalImpl,
  enumerable: true,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "clearInterval", {
  value: clearTimeoutImpl,
  enumerable: true,
  configurable: true,
  writable: true,
});

Object.defineProperties(globalThis, {
  innerWidth: { value: 1024, enumerable: true, configurable: true, writable: true },
  innerHeight: { value: 768, enumerable: true, configurable: true, writable: true },
  outerWidth: { value: 1024, enumerable: true, configurable: true, writable: true },
  outerHeight: { value: 768, enumerable: true, configurable: true, writable: true },
  devicePixelRatio: { value: 1, enumerable: true, configurable: true, writable: true },
  pageXOffset: { value: 0, enumerable: true, configurable: true, writable: true },
  pageYOffset: { value: 0, enumerable: true, configurable: true, writable: true },
  scrollTo: {
    value: scrollToImpl,
    enumerable: true,
    configurable: true,
    writable: true,
  },
});

Object.defineProperty(globalThis, "scrollX", {
    get() {
        return 0
    },
    enumerable: true,
    configurable: true,
})

Object.defineProperty(globalThis, "scrollY", {
    get() {
        let nodeIdx = document.body.__node_idx
        if (nodeIdx == null) {
            return 0
        } else {
            return -core.ops.op_get_offset_y(nodeIdx)
        }
    },
    enumerable: true,
    configurable: true,
})

Object.defineProperty(globalThis, "__clear_all_timers", {
  value: clearAllTimers,
  enumerable: false,
  configurable: true,
  writable: true,
});

function resolveBrowserUrl(value) {
    return new URL(value, globalThis.location?.href ?? "about:blank").href
}

function initLocation(href) {
    Object.defineProperty(globalThis, "location", {
        value: new Location(href),
        enumerable: true,
        configurable: true,
        writable: true,
    })
}

class Location {
    constructor(href) {
        this.__url = new URL(href);
    }

    reload() {
        core.ops.op_set_location_href(this.href, true)
    }

    replace(value) {
        core.ops.op_set_location_href(value, true)
    }

    assign(value) {
        core.ops.op_set_location_href(value, true)
    }

    get href() {
        return this.__url.href
    }

    toString() {
        return this.href
    }

    set href(value) {
        core.ops.op_set_location_href(value, true)
    }

    get host() {
        return this.__url.host
    }

    get hostname() {
        return this.__url.hostname
    }

    get port() {
        return this.__url.port
    }

    get origin() {
        return this.__url.origin
    }

    get pathname() {
        return this.__url.pathname
    }

    get search() {
        return this.__url.search
    }

    get hash() {
        return this.__url.hash
    }

    get protocol() {
        return this.__url.protocol
    }

    get ancestorOrigins() {
        // TODO: Replace with a `DOMStringList` instance.
        return {
            length: 0,
            item: () => null,
            contains: () => false,
        };
    }
}

Object.defineProperty(globalThis, "__init_location", {
    value: initLocation,
    enumerable: true,
    configurable: true,
    writable: true
})

Object.defineProperty(globalThis, "isSecureContext", {
    get() {
        return globalThis.location?.protocol === "https:" || globalThis.location?.hostname === "localhost"
    },
    enumerable: true,
    configurable: true,
})

Object.defineProperty(globalThis, "screen", {
    value: {
        width: 1024,
        height: 768,
        availWidth: 1024,
        availHeight: 768,
        colorDepth: 24,
        pixelDepth: 24,
    },
    enumerable: true,
    configurable: true,
    writable: true,
})

function getComputedStyle(element) {
    if (element?.__node_idx == null) {
        throw new TypeError("getComputedStyle requires an Element")
    }

    const properties = {
        "font-size": "16px",
        ...core.ops.op_get_computed_style(element.__node_idx, element.ownerDocument?.__frameId),
        "transition-duration": "0s",
        "transition-delay": "0s",
        "scroll-behavior": "auto",
    }

    for (const [property, value] of Object.entries(properties)) {
        const camelCaseProperty = property.replace(/-([a-z])/g, (_, letter) => letter.toUpperCase())
        properties[camelCaseProperty] = value
    }

    Object.defineProperty(properties, "getPropertyValue", {
        value(property) {
            const propertyName = String(property).trim()
            const normalizedProperty = propertyName.startsWith("--") ? propertyName : propertyName.toLowerCase()
            const camelCaseProperty = normalizedProperty.replace(/-([a-z])/g, (_, letter) => letter.toUpperCase())
            return properties[normalizedProperty] ?? properties[camelCaseProperty] ?? ""
        },
    })

    return properties
}

Object.defineProperty(globalThis, "getComputedStyle", {
    value: getComputedStyle,
    enumerable: true,
    configurable: true,
    writable: true,
})

const CSS = {
    supports(propertyOrCondition, value) {
        const unsupportedPrefix = /-(webkit|moz|ms)-/i
        return !unsupportedPrefix.test(String(propertyOrCondition))
    },
    escape(value) {
        return String(value).replace(/[^a-zA-Z0-9_\-]/g, char => `\\${char}`)
    },
}

Object.defineProperty(globalThis, "CSS", {
    value: CSS,
    enumerable: true,
    configurable: true,
    writable: true,
})

const browserPerformance = performance.performance
browserPerformance.timing = {
    navigationStart: Date.now(),
}

Object.defineProperties(globalThis, {
    URL: { value: url.URL, configurable: true, writable: true },
    URLSearchParams: { value: url.URLSearchParams, configurable: true, writable: true },
    URLPattern: { value: urlPattern.URLPattern, configurable: true, writable: true },
    performance: { value: browserPerformance, configurable: true, writable: true },
    Performance: { value: performance.Performance, configurable: true, writable: true },
    PerformanceObserver: { value: performance.PerformanceObserver, configurable: true, writable: true },
    DOMException: { value: DOMException.DOMException, configurable: true, writable: true },
});

// Poor mans storage
// TODO: Sync this with file storage somewhere
class Storage {
    __STORE = {}

    getItem(key) {
        return this.__STORE[key] ?? null
    }

    setItem(key, value) {
        this.__STORE[key] = value
    }

    removeItem(key) {
        this.__STORE[key] = null
    }
}

Object.defineProperty(globalThis, "Storage", {
    value: Storage,
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperty(globalThis, "localStorage", {
    value: new Storage(),
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperty(globalThis, "sessionStorage", {
    value: new Storage(),
    enumerable: true,
    configurable: true,
    writable: true,
})

class MediaQueryListEvent extends Event {
    constructor(type, options = {}) {
        super(type, options)
        this.matches = options.matches ?? false
        this.media = options.media ?? ""
    }
}

Object.defineProperty(globalThis, "MediaQueryListEvent", {
    value: MediaQueryListEvent,
    enumerable: true,
    configurable: true,
    writable: true,
})

class CustomEvent extends Event {
    constructor(type, options = {}) {
        super(type, options)
        this.__detail = options.detail ?? null
    }

    get detail() {
        return this.__detail
    }

    initCustomEvent(type, bubbles = false, cancelable = false, detail = null) {
        this.initEvent(type, bubbles, cancelable)
        this.__detail = detail
    }
}

Object.defineProperty(globalThis, "CustomEvent", {
    value: CustomEvent,
    enumerable: true,
    configurable: true,
    writable: true,
})

class MediaQueryList extends EventTarget {
    constructor(media) {
        super()
        this.media = String(media)
        this.__onchange = null
    }

    get matches() {
        return core.ops.op_media_query_matches(this.media)
    }

    get onchange() {
        return this.__onchange
    }

    set onchange(callback) {
        if (this.__onchange !== null) {
            this.removeEventListener("change", this.__onchange)
        }

        this.__onchange = typeof callback === "function" ? callback : null

        if (this.__onchange !== null) {
            this.addEventListener("change", this.__onchange)
        }
    }

    addListener(callback) {
        this.addEventListener("change", callback)
    }

    removeListener(callback) {
        this.removeEventListener("change", callback)
    }
}

Object.defineProperty(globalThis, "MediaQueryList", {
    value: MediaQueryList,
    enumerable: true,
    configurable: true,
    writable: true,
})

function matchMedia(selector) {
    return new MediaQueryList(selector)
}

Object.defineProperty(globalThis, "matchMedia", {
    value: matchMedia,
    enumerable: true,
    configurable: true,
    writable: true
})

const navigator = {
    // This is set by setup_js_dom in rust
    userAgent: null,
    platform: "Linux x86_64",
    language: "en-US",
    languages: ["en-US", "en"],
    cookieEnabled: true,
    onLine: true,
    maxTouchPoints: 0,
    mediaDevices: {
        enumerateDevices() {
            return Promise.resolve([])
        },
    },
    userAgentData: {
        brands: [
            { brand: "Chromium", version: "124" },
            { brand: "Not-A.Brand", version: "99" },
        ],
        mobile: false,
        platform: "Linux",
        getHighEntropyValues(hints) {
            const values = {
                architecture: "x86",
                bitness: "64",
                brands: this.brands,
                fullVersionList: this.brands,
                mobile: this.mobile,
                model: "",
                platform: this.platform,
                platformVersion: "",
                uaFullVersion: "124.0.0.0",
            }

            return Promise.resolve(Object.fromEntries(String(hints ?? "").split(",").filter(Boolean).map(hint => [hint, values[hint]])))
        },
    },
}

Object.defineProperty(globalThis, "navigator", {
    value: navigator,
    enumerable: true,
    configurable: true,
    writable: true,
})

function dispatchClickFromNodeIdx(targetNodeIdx, pathNodeIdxs) {
    const path = pathNodeIdxs
        .map(idx => __elementFromNodeIdx(idx))
        .filter(Boolean)

    const target = path.find(node => node?.nodeType === Node.ELEMENT_NODE) ?? __elementFromNodeIdx(targetNodeIdx)
    let clickEvent = null
    for (const eventType of ["pointerdown", "mousedown", "pointerup", "mouseup", "click"]) {
        const eventOptions = {
            bubbles: true,
            cancelable: true,
            composed: true,
            detail: eventType === "click" ? 1 : 0,
            button: 0,
            buttons: eventType === "pointerdown" || eventType === "mousedown" ? 1 : 0,
        }
        const event = eventType.startsWith("pointer")
            ? new PointerEvent(eventType, eventOptions)
            : new MouseEvent(eventType, eventOptions)
        denoEvent.setIsTrusted(event, true)
        denoEvent.dispatch(target, event)
        if (eventType === "click") {
            clickEvent = event
        }
    }
    return clickEvent?.defaultPrevented ?? false
}

class Window extends EventTarget {}

// The existing global object becomes the Window instance.
globalThis[webidl.brand] = webidl.brand
denoEvent.setEventTargetData(globalThis)

for (const prototype of [HtmlElement.prototype, Document.prototype, Window.prototype]) {
    for (const type of ["click", "load", "error", "input", "change", "keydown", "keyup", "focus", "blur", "scroll", "message"]) {
        denoEvent.defineEventHandler(prototype, type)
    }
}

Object.setPrototypeOf(globalThis, Window.prototype)

Object.defineProperty(globalThis, "Window", {
    value: Window,
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperty(globalThis, "__dispatchClickFromNodeIdx", {
    value: dispatchClickFromNodeIdx,
    enumerable: true,
    configurable: true,
    writable: true,
})

class History {
    constructor() {
        this.state = null
    }

    pushState(state, unused, url) {
        this.state = state

        if (url) {
            globalThis.location.__url = new URL(url, globalThis.location.__url)
            core.ops.op_set_location_href(url, false)
        }
    }

    replaceState(state, unused, url) {
        this.state = state

        if (url) {
            globalThis.location.__url = new URL(url, globalThis.location.__url)
            core.ops.op_set_location_href(url, false)
        }
    }
}

Object.defineProperty(globalThis, "history", {
    value: new History(),
    enumerable: true,
    configurable: true,
    writable: true,
})

// Set up the callback for Wasm streaming ops
Deno.core.setWasmStreamingCallback(fetch.handleWasmStreaming);

function resolveFetchInput(input) {
    if (typeof input === "string") {
        return resolveBrowserUrl(input)
    }
    if (input instanceof URL) {
        return input.href
    }
    return input
}

class BrowserRequest extends request.Request {
    constructor(input, init) {
        super(resolveFetchInput(input), init)
    }
}

function fetchLogUrl(input) {
    if (typeof input === "string") {
        return input
    }
    if (input instanceof URL) {
        return input.href
    }
    if (typeof input?.url === "string") {
        return input.url
    }
    return String(input)
}

function fetchLogMethod(input, init) {
    return String(init?.method ?? input?.method ?? "GET").toUpperCase()
}

const FETCH_LOG_BODY_LIMIT = 20000

function fetchLogBodyPreview(text) {
    text = String(text)
    if (text.length <= FETCH_LOG_BODY_LIMIT) {
        return text
    }
    return `${text.slice(0, FETCH_LOG_BODY_LIMIT)}...[truncated ${text.length - FETCH_LOG_BODY_LIMIT} chars]`
}

function fetchLogContentTypeIsText(contentType) {
    return contentType.startsWith("text/") || contentType.startsWith("application/json")
}

function fetchLogBodyText(body) {
    if (body == null) {
        return null
    }
    if (typeof body === "string") {
        return body
    }
    if (body instanceof URLSearchParams) {
        return body.toString()
    }
    if (body instanceof ArrayBuffer) {
        return `[${body.byteLength} bytes omitted]`
    }
    if (ArrayBuffer.isView(body)) {
        return `[${body.byteLength} bytes omitted]`
    }
    if (body instanceof Blob) {
        return `[${body.size} bytes omitted]`
    }
    const contentType = body?.headers?.get?.("content-type") ?? ""
    if (contentType && !fetchLogContentTypeIsText(contentType)) {
        return "[bytes omitted]"
    }
    if (typeof body.entries === "function") {
        return JSON.stringify(Array.from(body.entries()).map(([key, value]) => {
            return [key, typeof value === "string" ? value : `[${value?.constructor?.name ?? "object"}]`]
        }))
    }
    if (typeof body.text === "function") {
        return body.text()
    }
    return `[${body?.constructor?.name ?? typeof body}]`
}

function fetchLogBody(label, body) {
    try {
        const text = fetchLogBodyText(body)
        if (text == null) {
            return
        }
        if (typeof text?.then === "function") {
            text.then(value => {
                console.log(`${label}\n${fetchLogBodyPreview(value)}`)
            }, err => {
                console.error(`${label} <failed to read>`, err)
            })
        } else {
            console.log(`${label}\n${fetchLogBodyPreview(text)}`)
        }
    } catch (err) {
        console.error(`${label} <failed to read>`, err)
    }
}

function browserFetch(input, init) {
    const resolvedInput = resolveFetchInput(input)
    const method = fetchLogMethod(resolvedInput, init)
    const url = fetchLogUrl(resolvedInput)

    console.log(`[fetch] -> ${method} ${url}`)
    if (init?.body != null) {
        fetchLogBody(`[fetch] request body ${method} ${url}`, init.body)
    } else if (typeof resolvedInput?.clone === "function" && !resolvedInput.bodyUsed && method !== "GET" && method !== "HEAD") {
        fetchLogBody(`[fetch] request body ${method} ${url}`, resolvedInput.clone())
    }

    return fetch.fetch(resolvedInput, init).then(response => {
        const contentType = response.headers.get("content-type") ?? ""
        console.log(`[fetch] <- ${response.status} ${response.statusText} ${method} ${response.url || url} content-type=${contentType}`)
        try {
            fetchLogBody(`[fetch] response body ${response.status} ${method} ${response.url || url}`, response.clone())
        } catch (err) {
            console.error(`[fetch] response body ${method} ${response.url || url} <failed to clone>`, err)
        }
        return response
    }, err => {
        console.error(`[fetch] !! ${method} ${url}`, err)
        throw err
    })
}

Object.defineProperty(globalThis, "fetch", {
  value: browserFetch,
  enumerable: true,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "AbortController", {
  value: abortSignal.AbortController,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "AbortSignal", {
  value: abortSignal.AbortSignal,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "Request", {
  value: BrowserRequest,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "Response", {
  value: response.Response,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "Headers", {
  value: headers.Headers,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "FormData", {
  value: formData.FormData,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperties(globalThis, {
  Blob: {
    value: file.Blob,
    enumerable: true,
    configurable: true,
    writable: true,
  },
  atob: {
    value: base64.atob,
    enumerable: true,
    configurable: true,
    writable: true,
  },
  btoa: {
    value: base64.btoa,
    enumerable: true,
    configurable: true,
    writable: true,
  },
});

Object.defineProperty(globalThis, "CryptoKey", {
  value: crypto.CryptoKey,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "crypto", {
  value: crypto.crypto,
  enumerable: false,
  configurable: true,
  writable: false,
});

Object.defineProperty(globalThis, "Crypto", {
  value: crypto.Crypto,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "SubtleCrypto", {
  value: crypto.SubtleCrypto,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "TextDecoder", {
  value: encoding.TextDecoder,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "TextEncoder", {
  value: encoding.TextEncoder,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "TextDecoderStream", {
  value: encoding.TextDecoderStream,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "TextEncoderStream", {
  value: encoding.TextEncoderStream,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "MessageChannel", {
  value: messagePort.MessageChannel,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "MessagePort", {
  value: messagePort.MessagePort,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "File", {
  value: file.File,
  enumerable: false,
  configurable: true,
  writable: true,
});

// TODO: Fill this out
const frames = {}

Object.defineProperty(globalThis, "frames", {
  value: frames,
  enumerable: false,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "XMLHttpRequest", {
    value: XMLHttpRequest,
    enumerable: true,
    configurable: true,
    writable: true,
})

class MutationObserver {
    constructor(cb) {
        //
    }

    observe(node, config) {
        //
    }

    disconnect() {
        //
    }
}

Object.defineProperty(globalThis, "MutationObserver", {
    value: MutationObserver,
    enumerable: true,
    configurable: true,
    writable: true,
})

// Ideally this would be of the same structure as document, but that's a much larger change that will happen later on
const parentStub = {
    postMessage(message) {
        core.ops.op_post_message_to_parent(message)
    }
}

Object.defineProperty(globalThis, "parent", {
    get() {
        return core.ops.op_is_top() ? globalThis : parentStub
    },
    enumerable: true,
    configurable: true,
})

Object.defineProperty(globalThis, "top", {
    get() {
        return core.ops.op_is_top() ? globalThis : parentStub
    },
    enumerable: true,
    configurable: true,
})

function postMessage(message) {
    globalThis.dispatchEvent(new denoEvent.MessageEvent("message", { data: message }))
}

Object.defineProperty(globalThis, "postMessage", {
    value: postMessage,
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperty(globalThis, "MessageEvent", {
    value: denoEvent.MessageEvent,
    enumerable: true,
    configurable: true,
    writable: true,
})

class FormData {
    constructor(formElement = null) {
        if (formElement instanceof Node) {
            this.data = core.ops.op_collect_data_for_form(formElement.__node_idx)
        } else {
            this.data = {}
        }
    }

    [Symbol.iterator]() {
        return Object.entries(this.data)[Symbol.iterator]()
    }
}

Object.defineProperty(globalThis, "FormData", {
    value: FormData,
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperty(globalThis, "structuredClone", {
    value: structuredClone.structuredClone,
    enumerable: true,
    configurable: true,
    writable: true,
})

const __workers = new Map()

class Worker extends denoEvent.EventTarget {
    constructor(scriptURL) {
        super()
        this.scriptURL = String(scriptURL)
        this.__worker_id = core.ops.op_spawn_worker(this.scriptURL)
        __workers.set(this.__worker_id, this)
    }

    postMessage(message, transferOrOptions) {
        core.ops.op_post_message_to_worker(this.__worker_id, serializeWorkerMessage(message, transferOrOptions))
    }
}

denoEvent.defineEventHandler(Worker.prototype, "message")

// Called from Rust when a worker posts a message back to this document.
function __dispatchWorkerMessage(workerId) {
    const worker = __workers.get(workerId)
    if (!worker) {
        return
    }
    const event = deserializeWorkerMessage(core.ops.op_take_worker_message())
    worker.dispatchEvent(event)
}

Object.defineProperty(globalThis, "__dispatchWorkerMessage", {
    value: __dispatchWorkerMessage,
    enumerable: false,
    configurable: true,
    writable: true,
})

Object.defineProperty(globalThis, "Worker", {
    value: Worker,
    enumerable: true,
    configurable: true,
    writable: true,
})

globalThis.window = globalThis
globalThis.self = globalThis
