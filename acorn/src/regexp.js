// @ts-check

import {isIdentifierStart, isIdentifierChar} from "./identifier.js"
import UNICODE_PROPERTY_VALUES from "./unicode-property-data.js"
import {has} from "./util.js"


export class RegExpValidationState {
  constructor(parser) {
    this.parser = parser
    this.validFlags = `gim${parser.options.ecmaVersion >= 6 ? "uy" : ""}${parser.options.ecmaVersion >= 9 ? "s" : ""}`
    this.unicodeProperties = UNICODE_PROPERTY_VALUES[parser.options.ecmaVersion >= 12 ? 12 : parser.options.ecmaVersion]
    this.source = ""
    this.flags = ""
    this.start = 0
    this.switchU = false
    this.switchN = false
    this.pos = 0
    this.lastIntValue = 0
    this.lastStringValue = ""
    this.lastAssertionIsQuantifiable = false
    this.numCapturingParens = 0
    this.maxBackReference = 0
    this.groupNames = []
    this.backReferenceNames = []
  }

  reset(start, pattern, flags) {
    const unicode = flags.indexOf("u") !== -1
    this.start = start | 0
    this.source = pattern + ""
    this.flags = flags
    this.switchU = unicode && this.parser.options.ecmaVersion >= 6
    this.switchN = unicode && this.parser.options.ecmaVersion >= 9
  }

  raise(message) {
    this.parser.raiseRecoverable(this.start, `Invalid regular expression: /${this.source}/: ${message}`)
  }

  // If u flag is given, this returns the code point at the index (it combines a surrogate pair).
  // Otherwise, this returns the code unit of the index (can be a part of a surrogate pair).
  at(i, forceU = false) {
    const s = this.source
    const l = s.length
    if (i >= l) {
      return -1
    }
    const c = s.charCodeAt(i)
    if (!(forceU || this.switchU) || c <= 0xD7FF || c >= 0xE000 || i + 1 >= l) {
      return c
    }
    const next = s.charCodeAt(i + 1)
    return next >= 0xDC00 && next <= 0xDFFF ? (c << 10) + next - 0x35FDC00 : c
  }

  nextIndex(i, forceU = false) {
    const s = this.source
    const l = s.length
    if (i >= l) {
      return l
    }
    let c = s.charCodeAt(i), next
    if (!(forceU || this.switchU) || c <= 0xD7FF || c >= 0xE000 || i + 1 >= l ||
        (next = s.charCodeAt(i + 1)) < 0xDC00 || next > 0xDFFF) {
      return i + 1
    }
    return i + 2
  }

  current(forceU = false) {
    return this.at(this.pos, forceU)
  }

  lookahead(forceU = false) {
    return this.at(this.nextIndex(this.pos, forceU), forceU)
  }

  advance(forceU = false) {
    this.pos = this.nextIndex(this.pos, forceU)
  }

  eat(ch, forceU = false) {
    if (this.current(forceU) === ch) {
      this.advance(forceU)
      return true
    }
    return false
  }
}

export function codePointToString(ch) {
  if (ch <= 0xFFFF) return String.fromCharCode(ch)
  ch -= 0x10000
  return String.fromCharCode((ch >> 10) + 0xD800, (ch & 0x03FF) + 0xDC00)
}

export function isSyntaxCharacter(ch) {
  return (
    ch === 0x24 /* $ */ ||
    ch >= 0x28 /* ( */ && ch <= 0x2B /* + */ ||
    ch === 0x2E /* . */ ||
    ch === 0x3F /* ? */ ||
    ch >= 0x5B /* [ */ && ch <= 0x5E /* ^ */ ||
    ch >= 0x7B /* { */ && ch <= 0x7D /* } */
  )
}

export function isRegExpIdentifierStart(ch) {
  return isIdentifierStart(ch, true) || ch === 0x24 /* $ */ || ch === 0x5F /* _ */
}
export function isRegExpIdentifierPart(ch) {
  return isIdentifierChar(ch, true) || ch === 0x24 /* $ */ || ch === 0x5F /* _ */ || ch === 0x200C /* <ZWNJ> */ || ch === 0x200D /* <ZWJ> */
}
export function isControlLetter(ch) {
  return (
    (ch >= 0x41 /* A */ && ch <= 0x5A /* Z */) ||
    (ch >= 0x61 /* a */ && ch <= 0x7A /* z */)
  )
}
export function isValidUnicode(ch) {
  return ch >= 0 && ch <= 0x10FFFF
}
export function isCharacterClassEscape(ch) {
  return (
    ch === 0x64 /* d */ ||
    ch === 0x44 /* D */ ||
    ch === 0x73 /* s */ ||
    ch === 0x53 /* S */ ||
    ch === 0x77 /* w */ ||
    ch === 0x57 /* W */
  )
}
export function isUnicodePropertyNameCharacter(ch) {
  return isControlLetter(ch) || ch === 0x5F /* _ */
}
export function isUnicodePropertyValueCharacter(ch) {
  return isUnicodePropertyNameCharacter(ch) || isDecimalDigit(ch)
}
export function isDecimalDigit(ch) {
  return ch >= 0x30 /* 0 */ && ch <= 0x39 /* 9 */
}
export function isHexDigit(ch) {
  return (
    (ch >= 0x30 /* 0 */ && ch <= 0x39 /* 9 */) ||
    (ch >= 0x41 /* A */ && ch <= 0x46 /* F */) ||
    (ch >= 0x61 /* a */ && ch <= 0x66 /* f */)
  )
}
export function hexToInt(ch) {
  if (ch >= 0x41 /* A */ && ch <= 0x46 /* F */) {
    return 10 + (ch - 0x41 /* A */)
  }
  if (ch >= 0x61 /* a */ && ch <= 0x66 /* f */) {
    return 10 + (ch - 0x61 /* a */)
  }
  return ch - 0x30 /* 0 */
}
export function isOctalDigit(ch) {
  return ch >= 0x30 /* 0 */ && ch <= 0x37 /* 7 */
}
