import { DOMException } from "ext:deno_web/01_dom_exception.js";

export const NodeFilter = {
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

const DOCUMENT_NODE = 9

const nodeIteratorToken = Symbol("NodeIterator")

export class NodeIterator {
    #root
    #whatToShow
    #filter
    #referenceNode
    #pointerBeforeReferenceNode = true
    #active = false

    constructor(token, root, whatToShow, filter) {
        if (token !== nodeIteratorToken) throw new TypeError("Illegal constructor")
        this.#root = root
        this.#referenceNode = root
        this.#whatToShow = whatToShow
        this.#filter = filter
    }

    get root() { return this.#root }
    get whatToShow() { return this.#whatToShow }
    get filter() { return this.#filter }
    get referenceNode() { return this.#referenceNode }
    get pointerBeforeReferenceNode() { return this.#pointerBeforeReferenceNode }

    #following(node) {
        // Document has no backend node; its only exposed child is documentElement.
        const child = node.nodeType === DOCUMENT_NODE ? node.documentElement : node.firstChild
        if (child) return child
        while (node && node !== this.#root) {
            const sibling = node.nextSibling
            if (sibling) return sibling
            node = node.parentNode
        }
        return null
    }

    #preceding(node) {
        if (node === this.#root) return null
        let sibling = node.previousSibling
        if (!sibling) {
            return node.parentNode ??
                (this.#root.nodeType === DOCUMENT_NODE && node === this.#root.documentElement ? this.#root : null)
        }
        let child
        while ((child = sibling.lastChild)) sibling = child
        return sibling
    }

    #accepts(node) {
        if (!(this.#whatToShow & (1 << (node.nodeType - 1)))) return false
        const filter = this.#filter
        if (filter === null) return true
        this.#active = true
        try {
            const result = typeof filter === "function" ? filter(node) : filter.acceptNode(node)
            return (+result & 0xFFFF) === NodeFilter.FILTER_ACCEPT
        } finally {
            this.#active = false
        }
    }

    #traverse(forward) {
        if (this.#active) {
            throw new DOMException("NodeIterator filter is already active", "InvalidStateError")
        }
        let node = this.#referenceNode
        let before = this.#pointerBeforeReferenceNode
        // TODO: Repair the cursor in native pre-removal hooks. Until then, stop
        // traversal if the reference node leaves the root.
        while (node && this.#root.contains(node)) {
            // Switching direction visits the reference node again.
            if (forward !== before) {
                node = forward ? this.#following(node) : this.#preceding(node)
            }
            if (!node) return null
            before = !forward
            // REJECT and SKIP both leave descendants eligible in a NodeIterator.
            if (this.#accepts(node)) {
                this.#referenceNode = node
                this.#pointerBeforeReferenceNode = before
                return node
            }
        }
        return null
    }

    nextNode() { return this.#traverse(true) }
    previousNode() { return this.#traverse(false) }
    detach() {}
}

export function createNodeIterator(root, whatToShow, filter) {
    return new NodeIterator(nodeIteratorToken, root, whatToShow, filter)
}
