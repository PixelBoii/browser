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
import * as location from "ext:deno_web/12_location.js";
import * as messagePort from "ext:deno_web/13_message_port.js";
import * as compression from "ext:deno_web/14_compression.js";
import * as performance from "ext:deno_web/15_performance.js";
import * as imageData from "ext:deno_web/16_image_data.js";

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

const ELEMENT_ATTRIBUTES = ['src', 'style', 'id', 'class']

globalThis.__EVENT_LISTENERS = {}

class TextNode {
    constructor(text) {
        this.text = text
    }
}

class HtmlElement {
    constructor(tag) {
        this.tag = tag
    }

    addEventListener(event, cb) {
        const key = `${this.__node_idx}:${event}`
        if (!(key in globalThis.__EVENT_LISTENERS)) {
            globalThis.__EVENT_LISTENERS[key] = []
        }
        globalThis.__EVENT_LISTENERS[key].push(cb)
    }

    appendChild(element) {
        if (!element) {
            throw new TypeError("Element is not an object")
        }

        if (!this.__node_idx) {
            throw new Error("Item has not been registered on rust backend yet")
        }

        if (element instanceof TextNode) {
            core.ops.op_append_text_child(this.__node_idx, element.text)
        } else {
            let attributes = {}

            for (const attr in ELEMENT_ATTRIBUTES) {
                if (element[attr] !== null && element[attr] !== undefined) {
                    attributes[attr] = element[attr]
                }
            }
            attributes = Object.fromEntries(Object.entries(attributes).filter(([k, v]) => v))

            core.ops.op_append_child(this.__node_idx, element.tag, attributes, element.innerHTML || element.textContent)
        }
    }

    hasChildNodes() {
        return core.ops.op_has_child_nodes(this.__node_idx)
    }

    removeChild(element) {
        if (!element) {
            throw new TypeError("Element is not an object")
        }

        if (element.__node_idx) {
            core.ops.op_remove_child(element.__node_idx)
        }
    }

    getAttribute(attr) {
        return this[attr]
    }

    setAttribute(attr, value) {
        this[attr] = value
    }

    // TODO: Implement this
    getComputedStyle() {
        return {}
    }

    get innerHTML() {
        return this._innerHTML
    }

    set innerHTML(value) {
        this._innerHTML = value
        if (this.__node_idx) {
            core.ops.op_set_inner_html(this.__node_idx, value);
        }
    }

    get textContent() {
        return this._textContent
    }

    // TODO: Don't handle this as HTML
    set textContent(value) {
        this._textContent = value
        if (this.__node_idx) {
            core.ops.op_set_inner_html(this.__node_idx, value);
        }
    }

    get classList() {
        return new ClassList(this.class, this)
    }

    // TODO: Handle deep updates and sync with rust backend
    get style() {
        return this.__style ?? {}
    }

    set style(value) {
        this.__style = value
    }
}

class SVGElement extends HtmlElement {
    //
}

class ClassList {
    constructor(str, element) {
        this.list = new Set((str || "").split(" "))
        this.element = element
    }

    // TODO: Hook this up to the rust backend
    sync() {
        this.element.class = Array.from(this.list).join(" ")
    }

    add(str) {
        this.list.add(str)
        this.sync()
    }

    toggle(str) {
        if (this.list.has(str)) {
            this.list.delete(str)
        } else {
            this.list.add(str)
        }
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
    const element = new HtmlElement(node.tag)
    for (const [key, value] of Object.entries(node.attributes)) {
        element[key] = value
    }
    element.__node_idx = node_idx
    return element
}

Object.defineProperty(globalThis, "HTMLElement", {
    value: SVGElement,
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

globalThis.document = {
    referrer: "",
    createElement(tag, ...args) {
        const element = tag === "svg" ? new SVGElement(tag, ...args) : new HtmlElement(tag, ...args)
        const node_idx = core.ops.op_create_element(element.tag)
        element.__node_idx = node_idx
        return element
    },
    getElementById(id) {
        const node = core.ops.op_get_element_by_id(id)
        return nodeToElement(node)
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
    createTextNode(text) {
        return new TextNode(text)
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

Object.defineProperty(globalThis, "__init_location", {
    value: location.setLocationHref,
    enumerable: true,
    configurable: true,
    writable: true
})
Object.defineProperty(globalThis, "location", location.locationDescriptor)

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
    // TODO: Don't hardcode this
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

// TODO: Implement this
class History {
    constructor() {
        this.state = null
    }

    replaceState() {
        this.state = null
    }
}

Object.defineProperty(globalThis, "history", {
    value: new History(),
    enumerable: true,
    configurable: true,
    writable: true,
})

globalThis.window = globalThis
globalThis.self = globalThis
