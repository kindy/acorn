// @ts-check
import { SourceLocation } from "./locutil.js";

const node_ = /** @type {Node} */ (null);
export class Node {
  constructor(parser, pos, loc) {
    this.type = "";
    this.start = pos;
    this.end = 0;
    if (parser.options.locations) this.loc = new SourceLocation(parser, loc);
    if (parser.options.directSourceFile)
      this.sourceFile = parser.options.directSourceFile;
    if (parser.options.ranges) this.range = [pos, 0];

    this.consequent = this.declarations = this.params = this.properties = this.quasis = this.elements = this.expressions = this.arguments = /** @type {Node[]} */ ([]);
    this.operator = "";
    this.left = node_;
    this.right = node_;
    this.kind = this.bigint = this.name = "";
    this.regex = /** @type {any} */ null;
    this.value = /** @type {any} */ undefined;
    this.raw = /** @type {any} */ undefined;

    this.static = this.init = this.delegate = this.generator = this.async = this.method = this.shorthand = this.tail = this.computed = this.prefix = this.optional = false;
    this.imported = this.local = this.exported = this.key = this.id = this.param = this.meta = this.tag = this.quasi = this.callee = this.expression = this.argument = this.alternate = this.test = this.object = node_;
    this.property = node_;
    this.body = /** @type {Node | Node[]} */ (null);
  }
}

// Start an AST node, attaching a start offset.

// Finish an AST node, adding `type` and `end` properties.

export function finishNodeAt(node, type, pos, loc) {
  node.type = type;
  node.end = pos;
  if (this.options.locations) node.loc.end = loc;
  if (this.options.ranges) node.range[1] = pos;
  return node;
}
