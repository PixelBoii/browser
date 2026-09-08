import * as webidl from "ext:deno_webidl/00_webidl.js";
import { DOMException } from "ext:deno_web/01_dom_exception.js";
import { MessageEvent } from "ext:deno_web/02_event.js";
import * as messagePort from "ext:deno_web/13_message_port.js";

export function serializeWorkerMessage(message, transferOrOptions) {
    const options = transferOrOptions?.[Symbol.iterator] !== undefined
        ? { transfer: transferOrOptions }
        : transferOrOptions
    const { transfer } = webidl.converters.StructuredSerializeOptions(options)
    if (new Set(transfer).size !== transfer.length) {
        throw new DOMException("Duplicate transferable", "DataCloneError")
    }
    return messagePort.serializeJsMessageData(message, transfer)
}

export function deserializeWorkerMessage(serializedMessage) {
    const [data, transferables] = messagePort.deserializeJsMessageData(serializedMessage)
    const event = new MessageEvent("message")
    event.data = data
    event.ports = transferables.filter(value => value instanceof messagePort.MessagePort)
    return event
}
