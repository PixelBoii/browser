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

globalThis.__EVENT_LISTENERS = {}

const DOCUMENT_EVENT_TARGET = "document"
const WINDOW_EVENT_TARGET = "window"

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

    addEventListener(event, cb) {
        if (cb == null) {
            return
        }
        registerEventListener(`${this.__node_idx}:${event}`, cb)
    }

    removeEventListener(event, cb) {
        removeEventListenerByKey(`${this.__node_idx}:${event}`, cb)
    }

    dispatchEvent(event) {
        return dispatchEventToTarget(this, event)
    }

    get isConnected() {
        return this.__node_idx != null && core.ops.op_get_node(this.__node_idx) != null
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
        // TODO: Probably want to port this to rust later
        const parent = this.parentNode
        const siblings = parent.childNodes
        const me = siblings.findIndex(node => node.__node_idx == this.__node_idx)
        if (me === -1) {
            throw new Error("nextSibling: Failed to locate self")
        }
        return siblings.length - 1 >= me + 1 ? siblings[me + 1] : null
    }

    get firstChild() {
        return this.childNodes.length > 0 ? this.childNodes[0] : null
    }

    getRootNode() {
        return globalThis.document
    }

    cloneNode(deep = false) {
        let newNodeIdx = core.ops.op_clone_node(this.__node_idx, deep)
        return elementFromNodeIdx(newNodeIdx)
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

const __trustedEvents = new WeakSet()

class Event {
    constructor(type, options = {}) {
        this.type = String(type)
        this.name = this.type
        this.bubbles = options.bubbles ?? false
        this.cancelable = options.cancelable ?? true
        this.composed = options.composed ?? false
        this.target = null
        this.currentTarget = null
        this.defaultPrevented = false
        this.eventPhase = 0
        this.timeStamp = Date.now()
        this.__stopped = false
        this.__immediateStopped = false
        this.__path = []
    }

    get isTrusted() {
        return __trustedEvents.has(this)
    }

    preventDefault() {
        if (this.cancelable) {
            this.defaultPrevented = true
        }
    }

    stopPropagation() {
        this.__stopped = true
    }

    stopImmediatePropagation() {
        this.__stopped = true
        this.__immediateStopped = true
    }

    composedPath() {
        return this.__path.slice()
    }
}

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

    addEventListener(event, cb) {
        const key = `${this.__node_idx}:${event}`
        registerEventListener(key, cb)
    }

    removeEventListener(event, cb) {
        removeEventListenerByKey(`${this.__node_idx}:${event}`, cb)
    }

    dispatchEvent(event) {
        return dispatchEventToTarget(this, event)
    }

    click() {
        return dispatchEventToTarget(this, new MouseEvent("click", {
            bubbles: true,
            cancelable: true,
            composed: true,
            detail: 1,
        }))
    }

    set onload(cb) {
        this.addEventListener('load', cb)
    }

    set onclick(cb) {
        this.addEventListener('click', cb)
    }

    prepend(...elements) {
        if (this.__node_idx == null) {
            throw new Error("Item has not been registered on rust backend yet")
        }

        for (const element of elements) {
            if (!element) {
                throw new TypeError("Element is not an object")
            }

            // TODO: Optimize this
            let childNodes = this.childNodes
            core.ops.op_append_child(this.__node_idx, element.__node_idx, childNodes.length ? childNodes[0].__node_idx : null)
            return element
        }
    }

    appendChild(element) {
        if (!element) {
            throw new TypeError("Element is not an object")
        }

        if (this.__node_idx == null) {
            throw new Error("Item has not been registered on rust backend yet")
        }

        core.ops.op_append_child(this.__node_idx, element.__node_idx)
        return element
    }

    get childNodes() {
        return core.ops.op_get_child_nodes(this.__node_idx).map(nodeToElement)
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

    get children() {
        return this.childNodes.filter(node => node.nodeType === Node.ELEMENT_NODE)
    }

    getElementsByClassName(classNames) {
        const nodes = core.ops.op_get_elements_by_class_name(
            String(classNames),
            this.__node_idx,
            this.ownerDocument.__frameId,
        )
        return withDocument(this.ownerDocument, () => nodes.map(nodeToElement))
    }

    get firstChild() {
        return this.childNodes.at(0)
    }

    get lastChild() {
        return this.childNodes.at(-1)
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
        core.ops.op_append_child(this.__node_idx, newNode.__node_idx, referenceNode?.__node_idx)
        return newNode
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

    remove() {
        this.parentNode?.removeChild(this)
    }

    // TODO: Implement this
    getComputedStyle() {
        return {}
    }

    querySelector(selector) {
        const node = core.ops.op_query_selector(selector, this.__node_idx)
        return withDocument(this.ownerDocument, () => node ? nodeToElement(node) : null)
    }

    querySelectorAll(selector) {
        const nodes = core.ops.op_query_selector_all(selector, this.__node_idx)
        return withDocument(this.ownerDocument, () => nodes.map(nodeToElement))
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
        dispatchEventToTarget(this, new Event("focus", { bubbles: false, cancelable: false }))
    }

    blur() {
        if (document.activeElement?.__node_idx === this.__node_idx) {
            document.activeElement = document.body
        }
        dispatchEventToTarget(this, new Event("blur", { bubbles: false, cancelable: false }))
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

    get nodeType() {
        return 1
    }

    set innerHTML(value) {
        core.ops.op_set_inner_html(this.__node_idx, value, this.ownerDocument.__frameId);
    }

    get textContent() {
        return core.ops.op_get_text_content(this.__node_idx)
    }

    set textContent(value) {
        core.ops.op_set_text_content(this.__node_idx, value);
    }

    get classList() {
        return new ClassList(this.getAttribute('class'), this)
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
        return Object.fromEntries(data)
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

    // TODO: Track a clipping region in canvas state and apply it to subsequent drawing operations.
    clip() {}

    // TODO: Rasterize gradients instead of falling back to the existing solid canvas color.
    createLinearGradient() {
        return new CanvasGradient()
    }

    // TODO: Rasterize gradients instead of falling back to the existing solid canvas color.
    createRadialGradient() {
        return new CanvasGradient()
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

        core.ops.op_canvas_path_stroke(this.canvas.__node_idx, path, lineWidth)
        core.ops.op_canvas_paint(this.canvas.__node_idx)
    }

    fill(suppliedPath = null) {
        const path = suppliedPath && suppliedPath instanceof Path2D ? suppliedPath.path : null
        const fillStyle = typeof this.fillStyle === "string" ? this.fillStyle : "#000000"

        core.ops.op_canvas_path_fill(this.canvas.__node_idx, path, fillStyle)
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

class TemplateElement extends HtmlElement {
    // TODO: Actually return a fragment of children here
    get content() {
        return this
    }
}

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
            TemplateElement :
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
    get scripts() {
        return this.querySelectorAll('script')
    }
    get currentScript() {
        return this.__currentScript
    }
    get referrer() {
        return ""
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
        const element = this.createElement(tag)
        element.namespaceURI = ns
        return element
    }
    createElement(tag, ...args) {
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
    addEventListener(event, cb) {
        registerEventListener(`${DOCUMENT_EVENT_TARGET}:${event}`, cb)
    }
    removeEventListener(event, cb) {
        removeEventListenerByKey(`${DOCUMENT_EVENT_TARGET}:${event}`, cb)
    }
    dispatchEvent(event) {
        return dispatchEventToTarget(this, event)
    }
    set onclick(cb) {
        this.addEventListener('click', cb)
    }
    isEqualNode(other) {
        return nodesAreEqual(this, other)
    }
    createTextNode(text) {
        const element = new TextNode(text)
        return element
    }
    createDocumentFragment() {
        return this.createElement("fragment")
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

// TODO: Fill this out from the resolved style table.
function getComputedStyle() {
    return {
        transitionDuration: "0s",
        transitionDelay: "0s",
        scrollBehavior: "auto",
        getPropertyValue() {
            return ""
        },
    }
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
    constructor(type, options) {
        super(type)
        this.__detail = options.detail
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
        this.__listeners = []
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

    addEventListener(type, callback) {
        if (type !== "change" || callback == null || this.__listeners.includes(callback)) {
            return
        }
        this.__listeners.push(callback)
    }

    removeEventListener(type, callback) {
        if (type !== "change") {
            return
        }
        const idx = this.__listeners.indexOf(callback)
        if (idx !== -1) {
            this.__listeners.splice(idx, 1)
        }
    }

    dispatchEvent(event) {
        if (!(event instanceof Event)) {
            throw new TypeError("dispatchEvent expects an Event")
        }

        event.target = event.target ?? this
        event.currentTarget = this

        for (const listener of this.__listeners.slice()) {
            if (typeof listener === "function") {
                listener.call(this, event)
            } else if (typeof listener?.handleEvent === "function") {
                listener.handleEvent(event)
            }

            if (event.__immediateStopped) {
                break
            }
        }

        event.currentTarget = null
        return !event.defaultPrevented
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

function registerEventListener(key, cb) {
    if (cb == null) {
        return
    }
    if (!(key in globalThis.__EVENT_LISTENERS)) {
        globalThis.__EVENT_LISTENERS[key] = []
    }
    if (globalThis.__EVENT_LISTENERS[key].includes(cb)) {
        return
    }
    globalThis.__EVENT_LISTENERS[key].push(cb)
}

function removeEventListenerByKey(key, cb) {
    const listeners = globalThis.__EVENT_LISTENERS[key]
    if (!listeners) {
        return
    }

    const idx = listeners.indexOf(cb)
    if (idx !== -1) {
        listeners.splice(idx, 1)
    }
}

function hasEventListeners(event_key) {
    return !!globalThis.__EVENT_LISTENERS[event_key]
}

function runEventListeners(event_key, event) {
    const listeners = globalThis.__EVENT_LISTENERS[event_key]
    if (!listeners) {
        return event?.defaultPrevented ?? false
    }

    for (const cb of listeners.slice()) {
        try {
            const target = event.currentTarget ?? event.target ?? globalThis
            if (typeof cb === "function") {
                cb.call(target, event)
            } else if (typeof cb?.handleEvent === "function") {
                cb.handleEvent(event)
            }
        } catch (err) {
            console.error(err)
        }
        if (event.__immediateStopped) {
            break
        }
    }
    return event?.defaultPrevented ?? false
}

function eventKeyForTarget(target, type) {
    if (target === globalThis || target === globalThis.window) {
        return `${WINDOW_EVENT_TARGET}:${type}`
    }
    if (target === globalThis.document) {
        return `${DOCUMENT_EVENT_TARGET}:${type}`
    }
    return `${target.__node_idx}:${type}`
}

function eventPathForTarget(target) {
    if (target === globalThis) {
        return [globalThis]
    }
    if (target === globalThis.document) {
        return [globalThis.document, globalThis]
    }

    const path = []
    let current = target
    while (current) {
        path.push(current)
        current = current.parentNode
    }
    path.push(globalThis.document, globalThis)
    return path
}

function dispatchEventToPath(path, event, target = null) {
    if (!(event instanceof Event)) {
        throw new TypeError("dispatchEvent expects an Event")
    }

    const eventTarget = target ?? path.find(node => node?.nodeType === Node.ELEMENT_NODE) ?? path[0] ?? null
    event.target = event.target ?? eventTarget
    event.__path = path.slice()

    for (const currentTarget of path) {
        event.currentTarget = currentTarget
        runEventListeners(eventKeyForTarget(currentTarget, event.type), event)
        if (event.__stopped) {
            break
        }
    }

    event.currentTarget = null
    return !event.defaultPrevented
}

function dispatchEventToTarget(target, event) {
    return dispatchEventToPath(eventPathForTarget(target), event, target)
}

function dispatchClickFromNodeIdx(targetNodeIdx, pathNodeIdxs) {
    const path = pathNodeIdxs
        .map(idx => __elementFromNodeIdx(idx))
        .filter(Boolean)
    path.push(globalThis.document, globalThis)

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
        __trustedEvents.add(event)
        dispatchEventToPath(path, event, target)
        if (eventType === "click") {
            clickEvent = event
        }
    }
    return clickEvent?.defaultPrevented ?? false
}

Object.defineProperty(globalThis, "hasEventListeners", {
    value: hasEventListeners,
    enumerable: true,
    configurable: true,
    writable: true
})

Object.defineProperty(globalThis, "runEventListeners", {
    value: runEventListeners,
    enumerable: true,
    configurable: true,
    writable: true
})

function addEventListener(event, cb) {
    registerEventListener(`${WINDOW_EVENT_TARGET}:${event}`, cb)
}

function removeEventListener(event, cb) {
    removeEventListenerByKey(`${WINDOW_EVENT_TARGET}:${event}`, cb)
}

function dispatchDenoEventToWindow(event) {
    denoEvent.setTarget(event, globalThis)
    runEventListeners(`${WINDOW_EVENT_TARGET}:${event.type}`, event)
    return !event.defaultPrevented
}

function dispatchEvent(event) {
    if (event instanceof denoEvent.Event) {
        return dispatchDenoEventToWindow(event)
    }
    return dispatchEventToTarget(globalThis, event)
}

// TODO: Build window first, then map to globalThis
function Window() {}

Window.prototype.addEventListener = addEventListener
Window.prototype.removeEventListener = removeEventListener
Window.prototype.dispatchEvent = dispatchEvent

Object.defineProperty(Window, Symbol.hasInstance, {
    value(instance) {
        return instance === globalThis
    },
    configurable: true,
})

Object.defineProperty(globalThis, "Window", {
    value: Window,
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperty(globalThis, "addEventListener", {
    value: addEventListener,
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperty(globalThis, "removeEventListener", {
    value: removeEventListener,
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperty(globalThis, "dispatchEvent", {
    value: dispatchEvent,
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
    dispatchDenoEventToWindow(new denoEvent.MessageEvent("message", { data: message }))
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

class Worker {
    constructor(scriptURL) {
        this.scriptURL = scriptURL
        core.ops.op_spawn_worker(scriptURL)
    }
}

Object.defineProperty(globalThis, "Worker", {
    value: Worker,
    enumerable: true,
    configurable: true,
    writable: true,
})

globalThis.window = globalThis
globalThis.self = globalThis
