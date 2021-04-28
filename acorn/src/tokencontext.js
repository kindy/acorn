// @ts-check
// The algorithm used to determine whether a regexp can appear at a
// given point in the program is loosely based on sweet.js' approach.
// See https://github.com/mozilla/sweet.js/wiki/design

import {types as tt} from "./tokentype.js"
import {lineBreak} from "./whitespace.js"

export class TokContext {
  constructor(token, isExpr, preserveSpace, override, generator) {
    this.token = token
    this.isExpr = !!isExpr
    this.preserveSpace = !!preserveSpace
    this.override = override
    this.generator = !!generator
  }
}

export const types = {
  b_stat: new TokContext("{", false),
  b_expr: new TokContext("{", true),
  b_tmpl: new TokContext("${", false),
  p_stat: new TokContext("(", false),
  p_expr: new TokContext("(", true),
  q_tmpl: new TokContext("`", true, true, p => p.tryReadTemplateToken()),
  f_stat: new TokContext("function", false),
  f_expr: new TokContext("function", true),
  f_expr_gen: new TokContext("function", true, false, null, true),
  f_gen: new TokContext("function", false, false, null, true)
}

// Token-specific context update code

tt.parenR.updateContext = tt.braceR.updateContext = function() {
  if (this.context.length === 1) {
    this.exprAllowed = true
    return
  }
  let out = this.context.pop()
  if (out === types.b_stat && this.curContext().token === "function") {
    out = this.context.pop()
  }
  this.exprAllowed = !out.isExpr
}

tt.braceL.updateContext = function(prevType) {
  this.context.push(this.braceIsBlock(prevType) ? types.b_stat : types.b_expr)
  this.exprAllowed = true
}

tt.dollarBraceL.updateContext = function() {
  this.context.push(types.b_tmpl)
  this.exprAllowed = true
}

tt.parenL.updateContext = function(prevType) {
  let statementParens = prevType === tt._if || prevType === tt._for || prevType === tt._with || prevType === tt._while
  this.context.push(statementParens ? types.p_stat : types.p_expr)
  this.exprAllowed = true
}

tt.incDec.updateContext = function() {
  // tokExprAllowed stays unchanged
}

tt._function.updateContext = tt._class.updateContext = function(prevType) {
  if (prevType.beforeExpr && prevType !== tt._else &&
      !(prevType === tt.semi && this.curContext() !== types.p_stat) &&
      !(prevType === tt._return && lineBreak.test(this.input.slice(this.lastTokEnd, this.start))) &&
      !((prevType === tt.colon || prevType === tt.braceL) && this.curContext() === types.b_stat))
    this.context.push(types.f_expr)
  else
    this.context.push(types.f_stat)
  this.exprAllowed = false
}

tt.backQuote.updateContext = function() {
  if (this.curContext() === types.q_tmpl)
    this.context.pop()
  else
    this.context.push(types.q_tmpl)
  this.exprAllowed = false
}

tt.star.updateContext = function(prevType) {
  if (prevType === tt._function) {
    let index = this.context.length - 1
    if (this.context[index] === types.f_expr)
      this.context[index] = types.f_expr_gen
    else
      this.context[index] = types.f_gen
  }
  this.exprAllowed = true
}

tt.name.updateContext = function(prevType) {
  let allowed = false
  if (this.options.ecmaVersion >= 6 && prevType !== tt.dot) {
    if (this.value === "of" && !this.exprAllowed ||
        this.value === "yield" && this.inGeneratorContext())
      allowed = true
  }
  this.exprAllowed = allowed
}
