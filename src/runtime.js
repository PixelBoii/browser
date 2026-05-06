import * as webidl from "ext:deno_webidl/00_webidl.js";
import * as url from "ext:deno_web/00_url.js";
import * as urlPattern from "ext:deno_web/01_urlpattern.js";
import * as infra from "ext:deno_web/00_infra.js";
import * as DOMException from "ext:deno_web/01_dom_exception.js";
import * as broadcastChannel from "ext:deno_web/01_broadcast_channel.js";
import * as mimesniff from "ext:deno_web/01_mimesniff.js";
import * as event from "ext:deno_web/02_event.js";
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

const { core } = Deno
let nextTimerId = 1
const activeTimers = new Map()

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

const ELEMENT_ATTRIBUTES = ['src', 'style', 'id', 'class', 'height', 'width']

globalThis.__EVENT_LISTENERS = {}

class BaseNode {
    constructor() {
        this.__node_idx = null
    }

    get parentNode() {
        const parent = core.ops.op_get_parent_node(this.__node_idx)
        return nodeToElement(parent)
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
}

BaseNode.ELEMENT_NODE = 1
BaseNode.TEXT_NODE = 3
BaseNode.COMMENT_NODE = 8
BaseNode.DOCUMENT_NODE = 9
BaseNode.DOCUMENT_FRAGMENT_NODE = 11

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
        this.registerInBackend()
    }

    registerInBackend() {
        this.__node_idx = core.ops.op_create_text_element(this.text)
    }

    // TODO: Should probably sync these with the backend
    get data() { return this.text }
    set data(value) { this.text = value; }

    get nodeValue() { return this.text }
    set nodeValue(value) { this.data = value }

    get textContent() { return this.text }
    set textContent(value) { this.data = value }

    get nodeType() {
        return 3
    }
}

class Event {
    constructor(name) {
        this.name = name
        this.target = null
        this.defaultPrevented = false
    }

    preventDefault() {
        this.defaultPrevented = true
    }
}

class MouseEvent extends Event {}

Object.defineProperty(globalThis, "MouseEvent", {
    value: MouseEvent,
    enumerable: true,
    configurable: true,
    writable: true,
});

class HtmlElement extends BaseNode {
    constructor(tag) {
        super()
        this.tag = tag
        this.namespaceURI = "http://www.w3.org/1999/xhtml"
        this.registerInBackend()

        return new Proxy(this, {
            set(target, key, value) {
                if (String(key).startsWith("__")) {
                    return Reflect.set(target, key, value)
                }

                target.setAttribute(key, value)
                return true
            }
        })
    }

    registerInBackend() {
        this.__node_idx = core.ops.op_create_element(this.tag)
    }

    addEventListener(event, cb) {
        const key = `${this.__node_idx}:${event}`
        if (!(key in globalThis.__EVENT_LISTENERS)) {
            globalThis.__EVENT_LISTENERS[key] = []
        }
        globalThis.__EVENT_LISTENERS[key].push(cb)
    }

    set onload(cb) {
        this.addEventListener('load', cb)
    }

    appendChild(element) {
        if (!element) {
            throw new TypeError("Element is not an object")
        }

        if (!this.__node_idx) {
            throw new Error("Item has not been registered on rust backend yet")
        }

        core.ops.op_append_child(this.__node_idx, element.__node_idx)
    }

    getPassableAttributes() {
        let attributes = {}

        for (const attr in ELEMENT_ATTRIBUTES) {
            if (this[attr] !== null && this[attr] !== undefined) {
                attributes[attr] = this[attr]
            }
        }
        attributes = Object.fromEntries(Object.entries(attributes).filter(([k, v]) => v))

        return attributes
    }

    get childNodes() {
        return core.ops.op_get_child_nodes(this.__node_idx).map(nodeToElement)
    }

    hasChildNodes() {
        return this.childNodes.length > 0
    }

    removeChild(element) {
        if (!element) {
            throw new TypeError("Element is not an object")
        }

        if (element.__node_idx) {
            core.ops.op_remove_child(element.__node_idx)
        }
    }

    insertBefore(newNode, referenceNode) {
        if (!newNode) {
            throw new TypeError("insertBefore called without newNode")
        }
        if (referenceNode) {
            console.log('referenceNode!', referenceNode)
        }
        core.ops.op_append_child(this.__node_idx, newNode.__node_idx, referenceNode?.__node_idx)
    }

    getAttribute(attr) {
        return this[attr]
    }

    setAttribute(attr, value) {
        this[attr] = value
        if (this.__node_idx) {
            // TODO: This should probably not stringify all values
            core.ops.op_update_attributes(this.__node_idx, { [attr]: String(value) })
        }
    }

    removeAttribute(attr) {
        this[attr] = undefined
    }

    hasAttribute(attr) {
        return !!this[attr]
    }

    // TODO: Implement this
    getComputedStyle() {
        return {}
    }

    querySelector(selector) {
        const node = core.ops.op_query_selector(selector, this.__node_idx)
        return node ? nodeToElement(node) : null
    }

    querySelectorAll(selector) {
        const nodes = core.ops.op_query_selector_all(selector, this.__node_idx)
        return nodes.map(nodeToElement)
    }

    get tagName() {
        return this.tag.toUpperCase()
    }

    get innerHTML() {
        return core.ops.op_get_inner_html(this.__node_idx)
    }

    get nodeType() {
        return 1
    }

    set innerHTML(value) {
        core.ops.op_set_inner_html(this.__node_idx, value);
    }

    get textContent() {
        return core.ops.op_get_text_content(this.__node_idx)
    }

    set textContent(value) {
        core.ops.op_set_text_content(this.__node_idx, value);
    }

    get classList() {
        return new ClassList(this.class, this)
    }

    get style() {
        return new CSSStyleDeclaration(this.__style, this)
    }

    set style(value) {
        if (!value instanceof CSSStyleDeclaration) {
            throw new TypeError("Unsupported style value (for now)")
        }
        this.__style = value
    }
}

class CanvasRenderingContext2D {
    constructor(canvas) {
        this.canvas = canvas
        this.lineWidth = 1
        this.path = null
        this.cursor = null
    }

    fillRect(x, y, width, height) {
        core.ops.op_fill_canvas_rect(this.canvas.__node_idx, x, y, width, height)
    }

    strokeRect(x, y, width, height) {
        core.ops.op_stroke_canvas_rect(this.canvas.__node_idx, x, y, width, height, this.lineWidth)
    }

    beginPath() {
        this.path = []
    }

    moveTo(x, y) {
        this.cursor = [x, y]
    }

    lineTo(x, y) {
        if (this.path.length === 0) {
            this.path.push(this.cursor)
        }
        this.path.push([x, y])
        this.cursor = [x, y]
    }

    closePath() {
        this.path.push(this.path[0])
    }

    stroke() {
        if (!this.path) {
            return
        }

        core.ops.op_canvas_path_stroke(this.canvas.__node_idx, this.path, this.lineWidth)
    }
}

class HtmlCanvasElement extends HtmlElement {
    constructor(tag) {
        super(tag)
    }

    getContext(type) {
        if (type === "2d") {
            return new CanvasRenderingContext2D(this)
        } else {
            return null
        }
    }
}

Object.defineProperty(globalThis, "HTMLElement", {
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

class CSSStyleDeclaration {
    constructor(style, element) {
        let pairs = style ? style.split(";") : []
        for (const pair of pairs) {
            const [key, value] = pair.split(":")
            this[key] = value
        }
        this.__element = element

        return new Proxy(this, {
            set(target, key, value) {
                if (String(key).startsWith("__")) {
                    return Reflect.set(target, key, value)
                }

                target.setProperty(key, value)
                return true
            }
        })
    }

    getProperty(key) {
        return this[key]
    }

    setProperty(key, value) {
        this[key] = value
        this.sync()
    }

    sync() {
        const keys = Object.keys(this)
        let out = ""
        for (const key of keys) {
            if (key.startsWith("__")) continue
            const value = this[key]
            if (typeof value !== "boolean" || typeof value !== "number" || typeof value !== "string") {
                out += `${key}:${value};`
            }
        }

        this.__element.__style = out
        core.ops.op_update_attributes(this.__element.__node_idx, { style: out })
    }
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
}

Object.defineProperty(globalThis, "Image", {
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
        this.registerInBackend()
    }

    registerInBackend() {
        this.__node_idx = core.ops.op_create_comment_element(this.data)
    }

    get nodeType() {
        return 8
    }
}

class ClassList {
    constructor(str, element) {
        this.list = new Set((str || "").split(" "))
        this.element = element
    }

    sync() {
        this.element.class = Array.from(this.list).join(" ")
        core.ops.op_update_attributes(this.element.__node_idx, { class: this.element.class })
    }

    add(str) {
        this.list.add(str)
        this.sync()
    }

    contains(str) {
        return this.list.has(str)
    }

    toggle(str) {
        if (this.list.has(str)) {
            this.list.delete(str)
        } else {
            this.list.add(str)
        }
        this.sync()
    }

    remove(str) {
        this.list.delete(str)
        this.sync()
    }

    get length() {
        return this.list.length
    }

    [Symbol.iterator]() {
        return this.list[Symbol.iterator]();
    }
}

function nodeToElement(pair) {
    const node_idx = pair[0]
    const node = pair[1]
    let element;
    if (node.kind === "element") {
        const elementClass = tagToElement(node.tag)
        element = new elementClass(node.tag)
        for (const [key, value] of Object.entries(node.attributes)) {
            if (ELEMENT_ATTRIBUTES.includes(key)) {
                element.setAttribute(key, value)
            }
        }
    } else if (node.kind === "comment") {
        element = new CommentNode(node.comment)
    } else if (node.kind === "text") {
        element = new TextNode(node.text)
    }
    element.__node_idx = node_idx
    return element
}

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
                HtmlElement
}

const documentFonts = {
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

globalThis.document = {
    get cookie() {
        return core.ops.op_get_cookie(globalThis.location.href)
    },
    set cookie(newValue) {
        core.ops.op_set_cookie(globalThis.location.href, String(newValue))
    },
    referrer: "",
    fonts: documentFonts,
    createElementNS(ns, tag) {
        const element = this.createElement(tag)
        element.namespaceURI = ns
        return element
    },
    createElement(tag, ...args) {
        const elementClass = tagToElement(tag)
        const element = new elementClass(tag, ...args)
        return element
    },
    createComment(data) {
        const element = new CommentNode(data)
        return element
    },
    getElementById(id) {
        const node = core.ops.op_get_element_by_id(id)
        return node ? nodeToElement(node) : null
    },
    getElementsByTagName(tag) {
        const nodes = core.ops.op_get_elements_by_tag_name(tag)
        return nodes.map(nodeToElement)
    },
    querySelector(selector) {
        const node = core.ops.op_query_selector(selector)
        return node ? nodeToElement(node) : null
    },
    querySelectorAll(selector) {
        const nodes = core.ops.op_query_selector_all(selector)
        return nodes.map(nodeToElement)
    },
    addEventListener(event, cb) {
        // TODO: Implement this
    },
    removeEventListener(event, cb) {
        // TODO: Implement this
    },
    createTextNode(text) {
        const element = new TextNode(text)
        return element
    }
};

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
        console.log('reload!')
    }

    replace() {
        console.log('replace!')
    }

    assign() {
        console.log('assign!')
    }

    get href() {
        return this.__url.href
    }

    set href(value) {
        core.ops.op_set_location_href(value, true)
    }

    get host() {
        return this.__url.host
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

// TODO: Implement this
function getComputedStyle() {
    return {}
}

Object.defineProperty(globalThis, "getComputedStyle", {
    value: getComputedStyle,
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperties(globalThis, {
    URL: { value: url.URL, configurable: true, writable: true },
    URLSearchParams: { value: url.URLSearchParams, configurable: true, writable: true },
    URLPattern: { value: urlPattern.URLPattern, configurable: true, writable: true },
    performance: { value: performance.performance, configurable: true, writable: true },
    Performance: { value: performance.Performance, configurable: true, writable: true },
    PerformanceObserver: { value: performance.PerformanceObserver, configurable: true, writable: true },
    DOMException: { value: DOMException.DOMException, configurable: true, writable: true },
});

// Poor mans storage
// TODO: Sync this with file storage somewhere
class Storage {
    __STORE = {}

    getItem(key) {
        return this.__STORE[key]
    }

    setItem(key, value) {
        this.__STORE[key] = value
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

function matchMedia(selector) {
    const matches = core.ops.op_media_query_matches(selector)
    return {
        media: selector,
        matches,
        onchange: null,
    }
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
    platform: "Linux x86_64"
}

Object.defineProperty(globalThis, "navigator", {
    value: navigator,
    enumerable: true,
    configurable: true,
    writable: true,
})

// TODO: Implement this
function addEventListener(event, cb) {

}

Object.defineProperty(globalThis, "addEventListener", {
    value: addEventListener,
    enumerable: true,
    configurable: true,
    writable: true,
})

class History {
    constructor() {
        this.state = null
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

Object.defineProperty(globalThis, "fetch", {
  value: fetch.fetch,
  enumerable: true,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "Request", {
  value: request.Request,
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

class XMLHttpRequest {
    constructor() {
        //
    }

    addEventListener(event, cb) {
        //
    }

    send() {
        //
    }
}

Object.defineProperty(globalThis, "XMLHttpRequest", {
    value: XMLHttpRequest,
    enumerable: true,
    configurable: true,
    writable: true,
})

globalThis.window = globalThis
globalThis.self = globalThis
