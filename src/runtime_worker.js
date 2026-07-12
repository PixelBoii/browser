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
import * as fetch from "ext:browser_worker/runtime_fetch.js";
import * as crypto from "ext:deno_crypto/00_crypto.js";
import { EventTarget } from "./event_target.js";
import { XMLHttpRequest } from "ext:browser_worker/xml_http_request.js";

denoEvent.saveGlobalThisReference(globalThis)

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

function clearAllTimers() {
    for (const timer of activeTimers.values()) {
        core.cancelTimer(timer)
    }
    activeTimers.clear()
}

function requestAnimationFrameImpl(callback) {
    return setTimeoutImpl(() => callback(Date.now()), 16)
}

function cancelAnimationFrameImpl(timerId) {
    clearTimeoutImpl(timerId)
}

function camelize(str) {
    return str.replace(/(?:^\w|[A-Z]|\b\w|\s+)/g, function(match, index) {
        if (+match === 0) return "";
        return index === 0 ? match.toLowerCase() : match.toUpperCase();
    });
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

Object.defineProperty(globalThis, "__clear_all_timers", {
  value: clearAllTimers,
  enumerable: false,
  configurable: true,
  writable: true,
});

function resolveBrowserUrl(value) {
    return new URL(value, globalThis.location?.href ?? "about:blank").href
}

Object.defineProperty(globalThis, "isSecureContext", {
    get() {
        return globalThis.location?.protocol === "https:" || globalThis.location?.hostname === "localhost"
    },
    enumerable: true,
    configurable: true,
})

Object.defineProperty(globalThis, "EventTarget", {
    value: EventTarget,
    enumerable: true,
    configurable: true,
    writable: true,
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

    console.log(`[fetch:worker] -> ${method} ${url}`)
    if (init?.body != null) {
        fetchLogBody(`[fetch:worker] request body ${method} ${url}`, init.body)
    } else if (typeof resolvedInput?.clone === "function" && !resolvedInput.bodyUsed && method !== "GET" && method !== "HEAD") {
        fetchLogBody(`[fetch:worker] request body ${method} ${url}`, resolvedInput.clone())
    }

    return fetch.fetch(resolvedInput, init).then(response => {
        const contentType = response.headers.get("content-type") ?? ""
        console.log(`[fetch:worker] <- ${response.status} ${response.statusText} ${method} ${response.url || url} content-type=${contentType}`)
        try {
            fetchLogBody(`[fetch:worker] response body ${response.status} ${method} ${response.url || url}`, response.clone())
        } catch (err) {
            console.error(`[fetch:worker] response body ${method} ${response.url || url} <failed to clone>`, err)
        }
        return response
    }, err => {
        console.error(`[fetch:worker] !! ${method} ${url}`, err)
        throw err
    })
}

Object.defineProperty(globalThis, "fetch", {
  value: browserFetch,
  enumerable: true,
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

Object.defineProperty(globalThis, "XMLHttpRequest", {
    value: XMLHttpRequest,
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
