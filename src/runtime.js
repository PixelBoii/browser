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

const ELEMENT_ATTRIBUTES = ["src", "style", "id", "class"]

globalThis.__EVENT_LISTENERS = {}

class HtmlElement {
    constructor(tag) {
        this.tag = tag
    }

    addEventListener(event, cb) {
        console.log('addEventListener', event, cb)
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

        let attributes = {}

        for (const attr in ELEMENT_ATTRIBUTES) {
            if (this[attr] !== null && this[attr] !== undefined) {
                attributes[attr] = this[attr]
            }
        }
        attributes = Object.fromEntries(Object.entries(attributes).filter(([k, v]) => v))

        core.ops.op_append_child(this.__node_idx, element.tag, attributes, element.innerHTML || element.textContent)
    }

    setAttribute(attr, value) {
        this[attr] = value
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

globalThis.document = {
    createElement(...args) {
        return new HtmlElement(...args)
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

Object.defineProperty(globalThis, "location", {
    value: location.locationDescriptor,
    enumerable: true,
    configurable: true,
    writable: true,
})

Object.defineProperties(globalThis, {
    URL: { value: url.URL, configurable: true, writable: true },
    URLSearchParams: { value: url.URLSearchParams, configurable: true, writable: true },
    URLPattern: { value: urlPattern.URLPattern, configurable: true, writable: true },
});

globalThis.window = globalThis
globalThis.self = globalThis
