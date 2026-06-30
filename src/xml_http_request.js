function resolveBrowserUrl(value) {
    return new URL(value, globalThis.location?.href ?? "about:blank").href
}

class XMLHttpRequest {
    constructor() {
        this.readyState = XMLHttpRequest.UNSENT
        this.status = 0
        this.statusText = ""
        this.response = ""
        this.responseText = ""
        this.responseURL = ""
        this.responseType = ""
        this.timeout = 0
        this.withCredentials = false
        this.onreadystatechange = null
        this.onload = null
        this.onerror = null
        this.onabort = null
        this.onloadend = null
        this.__listeners = {}
        this.__method = "GET"
        this.__url = ""
        this.__async = true
        this.__requestHeaders = {}
        this.__responseHeaders = new Headers()
        this.__abortController = null
        this.__sendFlag = false
    }

    addEventListener(event, cb) {
        if (!this.__listeners[event]) {
            this.__listeners[event] = []
        }
        this.__listeners[event].push(cb)
    }

    removeEventListener(event, cb) {
        const listeners = this.__listeners[event]
        if (!listeners) {
            return
        }

        const idx = listeners.indexOf(cb)
        if (idx !== -1) {
            listeners.splice(idx, 1)
        }
    }

    __dispatch(event) {
        const eventObject = new Event(event)
        eventObject.target = this
        eventObject.currentTarget = this

        const handler = this[`on${event}`]
        if (typeof handler === "function") {
            handler.call(this, eventObject)
        }

        for (const cb of this.__listeners[event] ?? []) {
            cb.call(this, eventObject)
        }
    }

    __setReadyState(readyState) {
        this.readyState = readyState
        this.__dispatch("readystatechange")
    }

    open(method, url, async = true) {
        this.__method = String(method).toUpperCase()
        this.__url = resolveBrowserUrl(url)
        this.__async = async !== false
        this.__requestHeaders = {}
        this.__responseHeaders = new Headers()
        this.__abortController = null
        this.__sendFlag = false
        this.__setReadyState(XMLHttpRequest.OPENED)
    }

    setRequestHeader(header, value) {
        this.__requestHeaders[String(header)] = String(value)
    }

    getResponseHeader(header) {
        return this.__responseHeaders.get(header)
    }

    getAllResponseHeaders() {
        let out = ""
        this.__responseHeaders.forEach((value, key) => {
            out += `${key}: ${value}\r\n`
        })
        return out
    }

    send(body = null) {
        const run = async () => {
            const abortController = new AbortController()
            this.__abortController = abortController
            this.__sendFlag = true

            try {
                const init = {
                    method: this.__method,
                    headers: this.__requestHeaders,
                    credentials: this.withCredentials ? "include" : "same-origin",
                    signal: abortController.signal,
                }

                if (this.__method !== "GET" && this.__method !== "HEAD") {
                    init.body = body
                }

                const response = await browserFetch(this.__url, init)

                this.status = response.status
                this.statusText = response.statusText
                this.responseURL = response.url
                this.__responseHeaders = response.headers
                this.__setReadyState(XMLHttpRequest.HEADERS_RECEIVED)
                this.__setReadyState(XMLHttpRequest.LOADING)

                const text = await response.text()
                if (abortController.signal.aborted) {
                    return
                }
                this.responseText = text
                this.response = text
                this.__sendFlag = false
                this.__abortController = null
                this.__setReadyState(XMLHttpRequest.DONE)
                this.__dispatch("load")
                this.__dispatch("loadend")
            } catch (err) {
                if (abortController.signal.aborted) {
                    return
                }
                this.__error = err
                this.__sendFlag = false
                this.__abortController = null
                this.__setReadyState(XMLHttpRequest.DONE)
                this.__dispatch("error")
                this.__dispatch("loadend")
            }
        }

        run()
    }

    abort() {
        const wasActive = this.__sendFlag
        this.__sendFlag = false

        if (this.__abortController) {
            this.__abortController.abort()
            this.__abortController = null
        }

        this.status = 0
        this.statusText = ""
        this.response = ""
        this.responseText = ""
        this.__responseHeaders = new Headers()

        if (wasActive) {
            this.__setReadyState(XMLHttpRequest.DONE)
            this.__dispatch("abort")
            this.__dispatch("loadend")
        }
    }
}

XMLHttpRequest.UNSENT = 0
XMLHttpRequest.OPENED = 1
XMLHttpRequest.HEADERS_RECEIVED = 2
XMLHttpRequest.LOADING = 3
XMLHttpRequest.DONE = 4
XMLHttpRequest.prototype.UNSENT = XMLHttpRequest.UNSENT
XMLHttpRequest.prototype.OPENED = XMLHttpRequest.OPENED
XMLHttpRequest.prototype.HEADERS_RECEIVED = XMLHttpRequest.HEADERS_RECEIVED
XMLHttpRequest.prototype.LOADING = XMLHttpRequest.LOADING
XMLHttpRequest.prototype.DONE = XMLHttpRequest.DONE

export {
    XMLHttpRequest
}
