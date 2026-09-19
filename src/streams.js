import { core } from "ext:core/mod.js";
const streams = core.loadExtScript("ext:deno_web/06_streams.js");

// Windows and workers expose the same stream interfaces.
for (const name of [
    "ReadableStream",
    "ReadableStreamDefaultReader",
    "ReadableStreamBYOBReader",
    "ReadableStreamDefaultController",
    "ReadableByteStreamController",
    "ReadableStreamBYOBRequest",
    "WritableStream",
    "WritableStreamDefaultWriter",
    "WritableStreamDefaultController",
    "TransformStream",
    "TransformStreamDefaultController",
    "ByteLengthQueuingStrategy",
    "CountQueuingStrategy",
]) {
    Object.defineProperty(globalThis, name, {
        value: streams[name],
        configurable: true,
        writable: true,
    })
}
