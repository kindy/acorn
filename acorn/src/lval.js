// @ts-check
import {types as tt} from "./tokentype.js"
import {has} from "./util.js"
import {BIND_NONE, BIND_OUTSIDE, BIND_LEXICAL} from "./scopeflags.js"

// Convert existing expression atom to assignable pattern
// if possible.
