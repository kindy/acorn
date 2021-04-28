// @ts-check
import {types as tt} from "./tokentype.js"
import {lineBreak, skipWhiteSpace} from "./whitespace.js"
import {isIdentifierStart, isIdentifierChar, keywordRelationalOperator} from "./identifier.js"
import {has} from "./util.js"
import {DestructuringErrors} from "./parseutil.js"
import {functionFlags, SCOPE_SIMPLE_CATCH, BIND_SIMPLE_CATCH, BIND_LEXICAL, BIND_VAR, BIND_FUNCTION} from "./scopeflags.js"

export const loopLabel = {kind: "loop"}, switchLabel = {kind: "switch"}

export const FUNC_STATEMENT = 1, FUNC_HANGING_STATEMENT = 2, FUNC_NULLABLE_ID = 4

// ### Statement parsing
