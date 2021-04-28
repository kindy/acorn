// @ts-check
import {types as tt} from "./tokentype.js"
import {lineBreak, skipWhiteSpace} from "./whitespace.js"


// ## Parser utilities

export const literal = /^(?:'((?:\\.|[^'\\])*?)'|"((?:\\.|[^"\\])*?)")/

export function DestructuringErrors() {
  this.shorthandAssign =
  this.trailingComma =
  this.parenthesizedAssign =
  this.parenthesizedBind =
  this.doubleProto =
    -1
}
