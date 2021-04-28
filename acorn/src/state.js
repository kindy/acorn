// @ts-check

import {
  reservedWords,
  keywords,
  isIdentifierChar,
  isIdentifierStart,
  keywordRelationalOperator,
} from "./identifier.js";
import { types as tt, keywords as keywordTypes } from "./tokentype.js";
import {
  isNewLine,
  lineBreak,
  lineBreakG,
  nonASCIIwhitespace,
  skipWhiteSpace,
} from "./whitespace.js";
import { getOptions } from "./options.js";
import { has, wordsRegexp } from "./util.js";
import {
  SCOPE_TOP,
  SCOPE_FUNCTION,
  SCOPE_ASYNC,
  SCOPE_GENERATOR,
  SCOPE_SUPER,
  SCOPE_DIRECT_SUPER,
  BIND_OUTSIDE,
  BIND_VAR,
  functionFlags,
  SCOPE_ARROW,
  BIND_FUNCTION,
  BIND_LEXICAL,
  BIND_SIMPLE_CATCH,
  SCOPE_SIMPLE_CATCH,
  SCOPE_VAR,
  BIND_NONE,
} from "./scopeflags.js";
import {
  codePointToString,
  hexToInt,
  isCharacterClassEscape,
  isControlLetter,
  isDecimalDigit,
  isHexDigit,
  isOctalDigit,
  isRegExpIdentifierPart,
  isRegExpIdentifierStart,
  isSyntaxCharacter,
  isUnicodePropertyNameCharacter,
  isUnicodePropertyValueCharacter,
  isValidUnicode,
  RegExpValidationState,
} from "./regexp.js";
import { getLineInfo, Position } from "./locutil.js";
import { DestructuringErrors, literal } from "./parseutil.js";
import { finishNodeAt, Node } from "./node.js";
import { stringToBigInt, stringToNumber, Token } from "./tokenize.js";
import { Scope } from "./scope.js";
import {
  loopLabel,
  FUNC_STATEMENT,
  FUNC_HANGING_STATEMENT,
  switchLabel,
  FUNC_NULLABLE_ID,
} from "./statement.js";
import { types } from "./tokencontext.js";

const empty = [];
const INVALID_TEMPLATE_ESCAPE_ERROR = {};
// Reused empty array added for node fields that are always empty.
const emptyStmt = [];

export class Parser {
  constructor(options, input, startPos) {
    this.options = options = /** @type {any} */ (getOptions(options));
    this.sourceFile = options.sourceFile;
    this.keywords = wordsRegexp(
      keywords[
        options.ecmaVersion >= 6
          ? 6
          : options.sourceType === "module"
          ? "5module"
          : 5
      ]
    );
    let reserved = "";
    if (options.allowReserved !== true) {
      reserved =
        reservedWords[
          options.ecmaVersion >= 6 ? 6 : options.ecmaVersion === 5 ? 5 : 3
        ];
      if (options.sourceType === "module") reserved += " await";
    }
    this.reservedWords = wordsRegexp(reserved);
    let reservedStrict =
      (reserved ? reserved + " " : "") + reservedWords.strict;
    this.reservedWordsStrict = wordsRegexp(reservedStrict);
    this.reservedWordsStrictBind = wordsRegexp(
      reservedStrict + " " + reservedWords.strictBind
    );
    this.input = String(input);

    // Used to signal to callers of `readWord1` whether the word
    // contained any escape sequences. This is needed because words with
    // escape sequences must not be interpreted as keywords.
    this.containsEsc = false;

    // Set up token state

    // The current position of the tokenizer in the input.
    if (startPos) {
      this.pos = startPos;
      this.lineStart = this.input.lastIndexOf("\n", startPos - 1) + 1;
      this.curLine = this.input
        .slice(0, this.lineStart)
        .split(lineBreak).length;
    } else {
      this.pos = this.lineStart = 0;
      this.curLine = 1;
    }

    // Properties of the current token:
    // Its type
    this.type = tt.eof;
    // For tokens that include more information than their type, the value
    this.value = /** @type {null|string} */ (null);
    // Its start and end offset
    this.start = this.end = this.pos;
    // And, if locations are used, the {line, column} object
    // corresponding to those offsets
    this.startLoc = this.endLoc = this.curPosition();

    // Position information for the previous token
    this.lastTokEndLoc = this.lastTokStartLoc = null;
    this.lastTokStart = this.lastTokEnd = this.pos;

    // The context stack is used to superficially track syntactic
    // context to predict whether a regular expression is allowed in a
    // given position.
    this.context = this.initialContext();
    this.exprAllowed = true;

    // Figure out if it's a module code.
    this.inModule = options.sourceType === "module";
    this.strict = this.inModule || this.strictDirective(this.pos);

    // Used to signify the start of a potential arrow function
    this.potentialArrowAt = -1;

    // Positions to delayed-check that yield/await does not exist in default parameters.
    this.yieldPos = this.awaitPos = this.awaitIdentPos = 0;
    // Labels in scope.
    this.labels = [];
    // Thus-far undefined exports.
    this.undefinedExports = Object.create(null);

    // If enabled, skip leading hashbang line.
    if (
      this.pos === 0 &&
      options.allowHashBang &&
      this.input.slice(0, 2) === "#!"
    )
      this.skipLineComment(2);

    // Scope tracking for duplicate variable names (see scope.js)
    this.scopeStack = [];
    this.enterScope(SCOPE_TOP);

    // For RegExp validation
    this.regexpState = null;
  }

  parse() {
    let node = this.options.program || this.startNode();
    this.nextToken();
    return this.parseTopLevel(node);
  }

  get inFunction() {
    return (this.currentVarScope().flags & SCOPE_FUNCTION) > 0;
  }
  get inGenerator() {
    return (this.currentVarScope().flags & SCOPE_GENERATOR) > 0;
  }
  get inAsync() {
    return (this.currentVarScope().flags & SCOPE_ASYNC) > 0;
  }
  get allowSuper() {
    return (this.currentThisScope().flags & SCOPE_SUPER) > 0;
  }
  get allowDirectSuper() {
    return (this.currentThisScope().flags & SCOPE_DIRECT_SUPER) > 0;
  }
  get treatFunctionsAsVar() {
    return this.treatFunctionsAsVarInScope(this.currentScope());
  }
  get inNonArrowFunction() {
    return (this.currentThisScope().flags & SCOPE_FUNCTION) > 0;
  }

  /**
   * Validate the flags part of a given RegExpLiteral.
   *
   * @param {RegExpValidationState} state The state to validate RegExp.
   * @returns {void}
   */
  validateRegExpFlags(state) {
    const validFlags = state.validFlags;
    const flags = state.flags;

    for (let i = 0; i < flags.length; i++) {
      const flag = flags.charAt(i);
      if (validFlags.indexOf(flag) === -1) {
        this.raise(state.start, "Invalid regular expression flag");
      }
      if (flags.indexOf(flag, i + 1) > -1) {
        this.raise(state.start, "Duplicate regular expression flag");
      }
    }
  }

  /**
   * Validate the pattern part of a given RegExpLiteral.
   *
   * @param {RegExpValidationState} state The state to validate RegExp.
   * @returns {void}
   */
  validateRegExpPattern(state) {
    this.regexp_pattern(state);

    // The goal symbol for the parse is |Pattern[~U, ~N]|. If the result of
    // parsing contains a |GroupName|, reparse with the goal symbol
    // |Pattern[~U, +N]| and use this result instead. Throw a *SyntaxError*
    // exception if _P_ did not conform to the grammar, if any elements of _P_
    // were not matched by the parse, or if any Early Error conditions exist.
    if (
      !state.switchN &&
      this.options.ecmaVersion >= 9 &&
      state.groupNames.length > 0
    ) {
      state.switchN = true;
      this.regexp_pattern(state);
    }
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-Pattern
  regexp_pattern(state) {
    state.pos = 0;
    state.lastIntValue = 0;
    state.lastStringValue = "";
    state.lastAssertionIsQuantifiable = false;
    state.numCapturingParens = 0;
    state.maxBackReference = 0;
    state.groupNames.length = 0;
    state.backReferenceNames.length = 0;

    this.regexp_disjunction(state);

    if (state.pos !== state.source.length) {
      // Make the same messages as V8.
      if (state.eat(0x29 /* ) */)) {
        state.raise("Unmatched ')'");
      }
      if (state.eat(0x5d /* ] */) || state.eat(0x7d /* } */)) {
        state.raise("Lone quantifier brackets");
      }
    }
    if (state.maxBackReference > state.numCapturingParens) {
      state.raise("Invalid escape");
    }
    for (const name of state.backReferenceNames) {
      if (state.groupNames.indexOf(name) === -1) {
        state.raise("Invalid named capture referenced");
      }
    }
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-Disjunction
  regexp_disjunction(state) {
    this.regexp_alternative(state);
    while (state.eat(0x7c /* | */)) {
      this.regexp_alternative(state);
    }

    // Make the same message as V8.
    if (this.regexp_eatQuantifier(state, true)) {
      state.raise("Nothing to repeat");
    }
    if (state.eat(0x7b /* { */)) {
      state.raise("Lone quantifier brackets");
    }
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-Alternative
  regexp_alternative(state) {
    while (state.pos < state.source.length && this.regexp_eatTerm(state));
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-annexB-Term
  regexp_eatTerm(state) {
    if (this.regexp_eatAssertion(state)) {
      // Handle `QuantifiableAssertion Quantifier` alternative.
      // `state.lastAssertionIsQuantifiable` is true if the last eaten Assertion
      // is a QuantifiableAssertion.
      if (
        state.lastAssertionIsQuantifiable &&
        this.regexp_eatQuantifier(state)
      ) {
        // Make the same message as V8.
        if (state.switchU) {
          state.raise("Invalid quantifier");
        }
      }
      return true;
    }

    if (
      state.switchU
        ? this.regexp_eatAtom(state)
        : this.regexp_eatExtendedAtom(state)
    ) {
      this.regexp_eatQuantifier(state);
      return true;
    }

    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-annexB-Assertion
  regexp_eatAssertion(state) {
    const start = state.pos;
    state.lastAssertionIsQuantifiable = false;

    // ^, $
    if (state.eat(0x5e /* ^ */) || state.eat(0x24 /* $ */)) {
      return true;
    }

    // \b \B
    if (state.eat(0x5c /* \ */)) {
      if (state.eat(0x42 /* B */) || state.eat(0x62 /* b */)) {
        return true;
      }
      state.pos = start;
    }

    // Lookahead / Lookbehind
    if (state.eat(0x28 /* ( */) && state.eat(0x3f /* ? */)) {
      let lookbehind = false;
      if (this.options.ecmaVersion >= 9) {
        lookbehind = state.eat(0x3c /* < */);
      }
      if (state.eat(0x3d /* = */) || state.eat(0x21 /* ! */)) {
        this.regexp_disjunction(state);
        if (!state.eat(0x29 /* ) */)) {
          state.raise("Unterminated group");
        }
        state.lastAssertionIsQuantifiable = !lookbehind;
        return true;
      }
    }

    state.pos = start;
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-Quantifier
  regexp_eatQuantifier(state, noError = false) {
    if (this.regexp_eatQuantifierPrefix(state, noError)) {
      state.eat(0x3f /* ? */);
      return true;
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-QuantifierPrefix
  regexp_eatQuantifierPrefix(state, noError) {
    return (
      state.eat(0x2a /* * */) ||
      state.eat(0x2b /* + */) ||
      state.eat(0x3f /* ? */) ||
      this.regexp_eatBracedQuantifier(state, noError)
    );
  }
  regexp_eatBracedQuantifier(state, noError) {
    const start = state.pos;
    if (state.eat(0x7b /* { */)) {
      let min = 0,
        max = -1;
      if (this.regexp_eatDecimalDigits(state)) {
        min = state.lastIntValue;
        if (state.eat(0x2c /* , */) && this.regexp_eatDecimalDigits(state)) {
          max = state.lastIntValue;
        }
        if (state.eat(0x7d /* } */)) {
          // SyntaxError in https://www.ecma-international.org/ecma-262/8.0/#sec-term
          if (max !== -1 && max < min && !noError) {
            state.raise("numbers out of order in {} quantifier");
          }
          return true;
        }
      }
      if (state.switchU && !noError) {
        state.raise("Incomplete quantifier");
      }
      state.pos = start;
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-Atom
  regexp_eatAtom(state) {
    return (
      this.regexp_eatPatternCharacters(state) ||
      state.eat(0x2e /* . */) ||
      this.regexp_eatReverseSolidusAtomEscape(state) ||
      this.regexp_eatCharacterClass(state) ||
      this.regexp_eatUncapturingGroup(state) ||
      this.regexp_eatCapturingGroup(state)
    );
  }
  regexp_eatReverseSolidusAtomEscape(state) {
    const start = state.pos;
    if (state.eat(0x5c /* \ */)) {
      if (this.regexp_eatAtomEscape(state)) {
        return true;
      }
      state.pos = start;
    }
    return false;
  }
  regexp_eatUncapturingGroup(state) {
    const start = state.pos;
    if (state.eat(0x28 /* ( */)) {
      if (state.eat(0x3f /* ? */) && state.eat(0x3a /* : */)) {
        this.regexp_disjunction(state);
        if (state.eat(0x29 /* ) */)) {
          return true;
        }
        state.raise("Unterminated group");
      }
      state.pos = start;
    }
    return false;
  }
  regexp_eatCapturingGroup(state) {
    if (state.eat(0x28 /* ( */)) {
      if (this.options.ecmaVersion >= 9) {
        this.regexp_groupSpecifier(state);
      } else if (state.current() === 0x3f /* ? */) {
        state.raise("Invalid group");
      }
      this.regexp_disjunction(state);
      if (state.eat(0x29 /* ) */)) {
        state.numCapturingParens += 1;
        return true;
      }
      state.raise("Unterminated group");
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-annexB-ExtendedAtom
  regexp_eatExtendedAtom(state) {
    return (
      state.eat(0x2e /* . */) ||
      this.regexp_eatReverseSolidusAtomEscape(state) ||
      this.regexp_eatCharacterClass(state) ||
      this.regexp_eatUncapturingGroup(state) ||
      this.regexp_eatCapturingGroup(state) ||
      this.regexp_eatInvalidBracedQuantifier(state) ||
      this.regexp_eatExtendedPatternCharacter(state)
    );
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-annexB-InvalidBracedQuantifier
  regexp_eatInvalidBracedQuantifier(state) {
    if (this.regexp_eatBracedQuantifier(state, true)) {
      state.raise("Nothing to repeat");
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-SyntaxCharacter
  regexp_eatSyntaxCharacter(state) {
    const ch = state.current();
    if (isSyntaxCharacter(ch)) {
      state.lastIntValue = ch;
      state.advance();
      return true;
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-PatternCharacter
  // But eat eager.
  regexp_eatPatternCharacters(state) {
    const start = state.pos;
    let ch = 0;
    while ((ch = state.current()) !== -1 && !isSyntaxCharacter(ch)) {
      state.advance();
    }
    return state.pos !== start;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-annexB-ExtendedPatternCharacter
  regexp_eatExtendedPatternCharacter(state) {
    const ch = state.current();
    if (
      ch !== -1 &&
      ch !== 0x24 /* $ */ &&
      !((ch >= 0x28 /* ( */ && ch <= 0x2b) /* + */) &&
      ch !== 0x2e /* . */ &&
      ch !== 0x3f /* ? */ &&
      ch !== 0x5b /* [ */ &&
      ch !== 0x5e /* ^ */ &&
      ch !== 0x7c /* | */
    ) {
      state.advance();
      return true;
    }
    return false;
  }

  // GroupSpecifier ::
  //   [empty]
  //   `?` GroupName
  regexp_groupSpecifier(state) {
    if (state.eat(0x3f /* ? */)) {
      if (this.regexp_eatGroupName(state)) {
        if (state.groupNames.indexOf(state.lastStringValue) !== -1) {
          state.raise("Duplicate capture group name");
        }
        state.groupNames.push(state.lastStringValue);
        return;
      }
      state.raise("Invalid group");
    }
  }

  // GroupName ::
  //   `<` RegExpIdentifierName `>`
  // Note: this updates `state.lastStringValue` property with the eaten name.
  regexp_eatGroupName(state) {
    state.lastStringValue = "";
    if (state.eat(0x3c /* < */)) {
      if (
        this.regexp_eatRegExpIdentifierName(state) &&
        state.eat(0x3e /* > */)
      ) {
        return true;
      }
      state.raise("Invalid capture group name");
    }
    return false;
  }

  // RegExpIdentifierName ::
  //   RegExpIdentifierStart
  //   RegExpIdentifierName RegExpIdentifierPart
  // Note: this updates `state.lastStringValue` property with the eaten name.
  regexp_eatRegExpIdentifierName(state) {
    state.lastStringValue = "";
    if (this.regexp_eatRegExpIdentifierStart(state)) {
      state.lastStringValue += codePointToString(state.lastIntValue);
      while (this.regexp_eatRegExpIdentifierPart(state)) {
        state.lastStringValue += codePointToString(state.lastIntValue);
      }
      return true;
    }
    return false;
  }

  // RegExpIdentifierStart ::
  //   UnicodeIDStart
  //   `$`
  //   `_`
  //   `\` RegExpUnicodeEscapeSequence[+U]
  regexp_eatRegExpIdentifierStart(state) {
    const start = state.pos;
    const forceU = this.options.ecmaVersion >= 11;
    let ch = state.current(forceU);
    state.advance(forceU);

    if (
      ch === 0x5c /* \ */ &&
      this.regexp_eatRegExpUnicodeEscapeSequence(state, forceU)
    ) {
      ch = state.lastIntValue;
    }
    if (isRegExpIdentifierStart(ch)) {
      state.lastIntValue = ch;
      return true;
    }

    state.pos = start;
    return false;
  }

  // RegExpIdentifierPart ::
  //   UnicodeIDContinue
  //   `$`
  //   `_`
  //   `\` RegExpUnicodeEscapeSequence[+U]
  //   <ZWNJ>
  //   <ZWJ>
  regexp_eatRegExpIdentifierPart(state) {
    const start = state.pos;
    const forceU = this.options.ecmaVersion >= 11;
    let ch = state.current(forceU);
    state.advance(forceU);

    if (
      ch === 0x5c /* \ */ &&
      this.regexp_eatRegExpUnicodeEscapeSequence(state, forceU)
    ) {
      ch = state.lastIntValue;
    }
    if (isRegExpIdentifierPart(ch)) {
      state.lastIntValue = ch;
      return true;
    }

    state.pos = start;
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-annexB-AtomEscape
  regexp_eatAtomEscape(state) {
    if (
      this.regexp_eatBackReference(state) ||
      this.regexp_eatCharacterClassEscape(state) ||
      this.regexp_eatCharacterEscape(state) ||
      (state.switchN && this.regexp_eatKGroupName(state))
    ) {
      return true;
    }
    if (state.switchU) {
      // Make the same message as V8.
      if (state.current() === 0x63 /* c */) {
        state.raise("Invalid unicode escape");
      }
      state.raise("Invalid escape");
    }
    return false;
  }
  regexp_eatBackReference(state) {
    const start = state.pos;
    if (this.regexp_eatDecimalEscape(state)) {
      const n = state.lastIntValue;
      if (state.switchU) {
        // For SyntaxError in https://www.ecma-international.org/ecma-262/8.0/#sec-atomescape
        if (n > state.maxBackReference) {
          state.maxBackReference = n;
        }
        return true;
      }
      if (n <= state.numCapturingParens) {
        return true;
      }
      state.pos = start;
    }
    return false;
  }
  regexp_eatKGroupName(state) {
    if (state.eat(0x6b /* k */)) {
      if (this.regexp_eatGroupName(state)) {
        state.backReferenceNames.push(state.lastStringValue);
        return true;
      }
      state.raise("Invalid named reference");
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-annexB-CharacterEscape
  regexp_eatCharacterEscape(state) {
    return (
      this.regexp_eatControlEscape(state) ||
      this.regexp_eatCControlLetter(state) ||
      this.regexp_eatZero(state) ||
      this.regexp_eatHexEscapeSequence(state) ||
      this.regexp_eatRegExpUnicodeEscapeSequence(state, false) ||
      (!state.switchU && this.regexp_eatLegacyOctalEscapeSequence(state)) ||
      this.regexp_eatIdentityEscape(state)
    );
  }
  regexp_eatCControlLetter(state) {
    const start = state.pos;
    if (state.eat(0x63 /* c */)) {
      if (this.regexp_eatControlLetter(state)) {
        return true;
      }
      state.pos = start;
    }
    return false;
  }
  regexp_eatZero(state) {
    if (
      state.current() === 0x30 /* 0 */ &&
      !isDecimalDigit(state.lookahead())
    ) {
      state.lastIntValue = 0;
      state.advance();
      return true;
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-ControlEscape
  regexp_eatControlEscape(state) {
    const ch = state.current();
    if (ch === 0x74 /* t */) {
      state.lastIntValue = 0x09; /* \t */
      state.advance();
      return true;
    }
    if (ch === 0x6e /* n */) {
      state.lastIntValue = 0x0a; /* \n */
      state.advance();
      return true;
    }
    if (ch === 0x76 /* v */) {
      state.lastIntValue = 0x0b; /* \v */
      state.advance();
      return true;
    }
    if (ch === 0x66 /* f */) {
      state.lastIntValue = 0x0c; /* \f */
      state.advance();
      return true;
    }
    if (ch === 0x72 /* r */) {
      state.lastIntValue = 0x0d; /* \r */
      state.advance();
      return true;
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-ControlLetter
  regexp_eatControlLetter(state) {
    const ch = state.current();
    if (isControlLetter(ch)) {
      state.lastIntValue = ch % 0x20;
      state.advance();
      return true;
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-RegExpUnicodeEscapeSequence
  regexp_eatRegExpUnicodeEscapeSequence(state, forceU = false) {
    const start = state.pos;
    const switchU = forceU || state.switchU;

    if (state.eat(0x75 /* u */)) {
      if (this.regexp_eatFixedHexDigits(state, 4)) {
        const lead = state.lastIntValue;
        if (switchU && lead >= 0xd800 && lead <= 0xdbff) {
          const leadSurrogateEnd = state.pos;
          if (
            state.eat(0x5c /* \ */) &&
            state.eat(0x75 /* u */) &&
            this.regexp_eatFixedHexDigits(state, 4)
          ) {
            const trail = state.lastIntValue;
            if (trail >= 0xdc00 && trail <= 0xdfff) {
              state.lastIntValue =
                (lead - 0xd800) * 0x400 + (trail - 0xdc00) + 0x10000;
              return true;
            }
          }
          state.pos = leadSurrogateEnd;
          state.lastIntValue = lead;
        }
        return true;
      }
      if (
        switchU &&
        state.eat(0x7b /* { */) &&
        this.regexp_eatHexDigits(state) &&
        state.eat(0x7d /* } */) &&
        isValidUnicode(state.lastIntValue)
      ) {
        return true;
      }
      if (switchU) {
        state.raise("Invalid unicode escape");
      }
      state.pos = start;
    }

    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-annexB-IdentityEscape
  regexp_eatIdentityEscape(state) {
    if (state.switchU) {
      if (this.regexp_eatSyntaxCharacter(state)) {
        return true;
      }
      if (state.eat(0x2f /* / */)) {
        state.lastIntValue = 0x2f; /* / */
        return true;
      }
      return false;
    }

    const ch = state.current();
    if (ch !== 0x63 /* c */ && (!state.switchN || ch !== 0x6b) /* k */) {
      state.lastIntValue = ch;
      state.advance();
      return true;
    }

    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-DecimalEscape
  regexp_eatDecimalEscape(state) {
    state.lastIntValue = 0;
    let ch = state.current();
    if (ch >= 0x31 /* 1 */ && ch <= 0x39 /* 9 */) {
      do {
        state.lastIntValue = 10 * state.lastIntValue + (ch - 0x30) /* 0 */;
        state.advance();
      } while ((ch = state.current()) >= 0x30 /* 0 */ && ch <= 0x39 /* 9 */);
      return true;
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-CharacterClassEscape
  regexp_eatCharacterClassEscape(state) {
    const ch = state.current();

    if (isCharacterClassEscape(ch)) {
      state.lastIntValue = -1;
      state.advance();
      return true;
    }

    if (
      state.switchU &&
      this.options.ecmaVersion >= 9 &&
      (ch === 0x50 /* P */ || ch === 0x70) /* p */
    ) {
      state.lastIntValue = -1;
      state.advance();
      if (
        state.eat(0x7b /* { */) &&
        this.regexp_eatUnicodePropertyValueExpression(state) &&
        state.eat(0x7d /* } */)
      ) {
        return true;
      }
      state.raise("Invalid property name");
    }

    return false;
  }

  // UnicodePropertyValueExpression ::
  //   UnicodePropertyName `=` UnicodePropertyValue
  //   LoneUnicodePropertyNameOrValue
  regexp_eatUnicodePropertyValueExpression(state) {
    const start = state.pos;

    // UnicodePropertyName `=` UnicodePropertyValue
    if (this.regexp_eatUnicodePropertyName(state) && state.eat(0x3d /* = */)) {
      const name = state.lastStringValue;
      if (this.regexp_eatUnicodePropertyValue(state)) {
        const value = state.lastStringValue;
        this.regexp_validateUnicodePropertyNameAndValue(state, name, value);
        return true;
      }
    }
    state.pos = start;

    // LoneUnicodePropertyNameOrValue
    if (this.regexp_eatLoneUnicodePropertyNameOrValue(state)) {
      const nameOrValue = state.lastStringValue;
      this.regexp_validateUnicodePropertyNameOrValue(state, nameOrValue);
      return true;
    }
    return false;
  }
  regexp_validateUnicodePropertyNameAndValue(state, name, value) {
    if (!has(state.unicodeProperties.nonBinary, name))
      state.raise("Invalid property name");
    if (!state.unicodeProperties.nonBinary[name].test(value))
      state.raise("Invalid property value");
  }
  regexp_validateUnicodePropertyNameOrValue(state, nameOrValue) {
    if (!state.unicodeProperties.binary.test(nameOrValue))
      state.raise("Invalid property name");
  }

  // UnicodePropertyName ::
  //   UnicodePropertyNameCharacters
  regexp_eatUnicodePropertyName(state) {
    let ch = 0;
    state.lastStringValue = "";
    while (isUnicodePropertyNameCharacter((ch = state.current()))) {
      state.lastStringValue += codePointToString(ch);
      state.advance();
    }
    return state.lastStringValue !== "";
  }

  // UnicodePropertyValue ::
  //   UnicodePropertyValueCharacters
  regexp_eatUnicodePropertyValue(state) {
    let ch = 0;
    state.lastStringValue = "";
    while (isUnicodePropertyValueCharacter((ch = state.current()))) {
      state.lastStringValue += codePointToString(ch);
      state.advance();
    }
    return state.lastStringValue !== "";
  }

  // LoneUnicodePropertyNameOrValue ::
  //   UnicodePropertyValueCharacters
  regexp_eatLoneUnicodePropertyNameOrValue(state) {
    return this.regexp_eatUnicodePropertyValue(state);
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-CharacterClass
  regexp_eatCharacterClass(state) {
    if (state.eat(0x5b /* [ */)) {
      state.eat(0x5e /* ^ */);
      this.regexp_classRanges(state);
      if (state.eat(0x5d /* ] */)) {
        return true;
      }
      // Unreachable since it threw "unterminated regular expression" error before.
      state.raise("Unterminated character class");
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-ClassRanges
  // https://www.ecma-international.org/ecma-262/8.0/#prod-NonemptyClassRanges
  // https://www.ecma-international.org/ecma-262/8.0/#prod-NonemptyClassRangesNoDash
  regexp_classRanges(state) {
    while (this.regexp_eatClassAtom(state)) {
      const left = state.lastIntValue;
      if (state.eat(0x2d /* - */) && this.regexp_eatClassAtom(state)) {
        const right = state.lastIntValue;
        if (state.switchU && (left === -1 || right === -1)) {
          state.raise("Invalid character class");
        }
        if (left !== -1 && right !== -1 && left > right) {
          state.raise("Range out of order in character class");
        }
      }
    }
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-ClassAtom
  // https://www.ecma-international.org/ecma-262/8.0/#prod-ClassAtomNoDash
  regexp_eatClassAtom(state) {
    const start = state.pos;

    if (state.eat(0x5c /* \ */)) {
      if (this.regexp_eatClassEscape(state)) {
        return true;
      }
      if (state.switchU) {
        // Make the same message as V8.
        const ch = state.current();
        if (ch === 0x63 /* c */ || isOctalDigit(ch)) {
          state.raise("Invalid class escape");
        }
        state.raise("Invalid escape");
      }
      state.pos = start;
    }

    const ch = state.current();
    if (ch !== 0x5d /* ] */) {
      state.lastIntValue = ch;
      state.advance();
      return true;
    }

    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-annexB-ClassEscape
  regexp_eatClassEscape(state) {
    const start = state.pos;

    if (state.eat(0x62 /* b */)) {
      state.lastIntValue = 0x08; /* <BS> */
      return true;
    }

    if (state.switchU && state.eat(0x2d /* - */)) {
      state.lastIntValue = 0x2d; /* - */
      return true;
    }

    if (!state.switchU && state.eat(0x63 /* c */)) {
      if (this.regexp_eatClassControlLetter(state)) {
        return true;
      }
      state.pos = start;
    }

    return (
      this.regexp_eatCharacterClassEscape(state) ||
      this.regexp_eatCharacterEscape(state)
    );
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-annexB-ClassControlLetter
  regexp_eatClassControlLetter(state) {
    const ch = state.current();
    if (isDecimalDigit(ch) || ch === 0x5f /* _ */) {
      state.lastIntValue = ch % 0x20;
      state.advance();
      return true;
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-HexEscapeSequence
  regexp_eatHexEscapeSequence(state) {
    const start = state.pos;
    if (state.eat(0x78 /* x */)) {
      if (this.regexp_eatFixedHexDigits(state, 2)) {
        return true;
      }
      if (state.switchU) {
        state.raise("Invalid escape");
      }
      state.pos = start;
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-DecimalDigits
  regexp_eatDecimalDigits(state) {
    const start = state.pos;
    let ch = 0;
    state.lastIntValue = 0;
    while (isDecimalDigit((ch = state.current()))) {
      state.lastIntValue = 10 * state.lastIntValue + (ch - 0x30) /* 0 */;
      state.advance();
    }
    return state.pos !== start;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-HexDigits
  regexp_eatHexDigits(state) {
    const start = state.pos;
    let ch = 0;
    state.lastIntValue = 0;
    while (isHexDigit((ch = state.current()))) {
      state.lastIntValue = 16 * state.lastIntValue + hexToInt(ch);
      state.advance();
    }
    return state.pos !== start;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-annexB-LegacyOctalEscapeSequence
  // Allows only 0-377(octal) i.e. 0-255(decimal).
  regexp_eatLegacyOctalEscapeSequence(state) {
    if (this.regexp_eatOctalDigit(state)) {
      const n1 = state.lastIntValue;
      if (this.regexp_eatOctalDigit(state)) {
        const n2 = state.lastIntValue;
        if (n1 <= 3 && this.regexp_eatOctalDigit(state)) {
          state.lastIntValue = n1 * 64 + n2 * 8 + state.lastIntValue;
        } else {
          state.lastIntValue = n1 * 8 + n2;
        }
      } else {
        state.lastIntValue = n1;
      }
      return true;
    }
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-OctalDigit
  regexp_eatOctalDigit(state) {
    const ch = state.current();
    if (isOctalDigit(ch)) {
      state.lastIntValue = ch - 0x30; /* 0 */
      state.advance();
      return true;
    }
    state.lastIntValue = 0;
    return false;
  }

  // https://www.ecma-international.org/ecma-262/8.0/#prod-Hex4Digits
  // https://www.ecma-international.org/ecma-262/8.0/#prod-HexDigit
  // And HexDigit HexDigit in https://www.ecma-international.org/ecma-262/8.0/#prod-HexEscapeSequence
  regexp_eatFixedHexDigits(state, length) {
    const start = state.pos;
    state.lastIntValue = 0;
    for (let i = 0; i < length; ++i) {
      const ch = state.current();
      if (!isHexDigit(ch)) {
        state.pos = start;
        return false;
      }
      state.lastIntValue = 16 * state.lastIntValue + hexToInt(ch);
      state.advance();
    }
    return true;
  }

  checkPropClash(prop, propHash, refDestructuringErrors) {
    if (this.options.ecmaVersion >= 9 && prop.type === "SpreadElement") return;
    if (
      this.options.ecmaVersion >= 6 &&
      (prop.computed || prop.method || prop.shorthand)
    )
      return;
    let { key } = prop,
      name;
    switch (key.type) {
      case "Identifier":
        name = key.name;
        break;
      case "Literal":
        name = String(key.value);
        break;
      default:
        return;
    }
    let { kind } = prop;
    if (this.options.ecmaVersion >= 6) {
      if (name === "__proto__" && kind === "init") {
        if (propHash.proto) {
          if (refDestructuringErrors) {
            if (refDestructuringErrors.doubleProto < 0)
              refDestructuringErrors.doubleProto = key.start;
            // Backwards-compat kludge. Can be removed in version 6.0
          } else
            this.raiseRecoverable(
              key.start,
              "Redefinition of __proto__ property"
            );
        }
        propHash.proto = true;
      }
      return;
    }
    name = "$" + name;
    let other = propHash[name];
    if (other) {
      let redefinition;
      if (kind === "init") {
        redefinition = (this.strict && other.init) || other.get || other.set;
      } else {
        redefinition = other.init || other[kind];
      }
      if (redefinition)
        this.raiseRecoverable(key.start, "Redefinition of property");
    } else {
      other = propHash[name] = {
        init: false,
        get: false,
        set: false,
      };
    }
    other[kind] = true;
  }

  // ### Expression parsing

  // These nest, from the most general expression type at the top to
  // 'atomic', nondivisible expression types at the bottom. Most of
  // the functions will simply let the function(s) below them parse,
  // and, *if* the syntactic construct they handle is present, wrap
  // the AST node that the inner parser gave them in another node.

  // Parse a full expression. The optional arguments are used to
  // forbid the `in` operator (in for loops initalization expressions)
  // and provide reference for storing '=' operator inside shorthand
  // property assignment in contexts where both object expression
  // and object pattern might appear (so it's possible to raise
  // delayed syntax error at correct position).

  /** @returns {Node} */
  parseExpression(noIn, refDestructuringErrors) {
    let startPos = this.start,
      startLoc = this.startLoc;
    let expr = this.parseMaybeAssign(noIn, refDestructuringErrors);
    if (this.type === tt.comma) {
      let node = this.startNodeAt(startPos, startLoc);
      node.expressions = [expr];
      while (this.eat(tt.comma))
        node.expressions.push(
          this.parseMaybeAssign(noIn, refDestructuringErrors)
        );
      return this.finishNode(node, "SequenceExpression");
    }
    return expr;
  }

  // Parse an assignment expression. This includes applications of
  // operators like `+=`.

  parseMaybeAssign(noIn, refDestructuringErrors, afterLeftParse) {
    if (this.isContextual("yield")) {
      if (this.inGenerator) return this.parseYield(noIn);
      // The tokenizer will assume an expression is allowed after
      // `yield`, but this isn't that kind of yield
      else this.exprAllowed = false;
    }

    let ownDestructuringErrors = false,
      oldParenAssign = -1,
      oldTrailingComma = -1;
    if (refDestructuringErrors) {
      oldParenAssign = refDestructuringErrors.parenthesizedAssign;
      oldTrailingComma = refDestructuringErrors.trailingComma;
      refDestructuringErrors.parenthesizedAssign = refDestructuringErrors.trailingComma = -1;
    } else {
      refDestructuringErrors = new DestructuringErrors();
      ownDestructuringErrors = true;
    }

    let startPos = this.start,
      startLoc = this.startLoc;
    if (this.type === tt.parenL || this.type === tt.name)
      this.potentialArrowAt = this.start;
    let left = this.parseMaybeConditional(noIn, refDestructuringErrors);
    if (afterLeftParse)
      left = afterLeftParse.call(this, left, startPos, startLoc);
    if (this.type.isAssign) {
      let node = this.startNodeAt(startPos, startLoc);
      node.operator = this.value;
      if (this.type === tt.eq)
        left = this.toAssignable(left, false, refDestructuringErrors);
      if (!ownDestructuringErrors) {
        refDestructuringErrors.parenthesizedAssign = refDestructuringErrors.trailingComma = refDestructuringErrors.doubleProto = -1;
      }
      if (refDestructuringErrors.shorthandAssign >= left.start)
        refDestructuringErrors.shorthandAssign = -1; // reset because shorthand default was used correctly
      if (this.type === tt.eq) this.checkLValPattern(left);
      else this.checkLValSimple(left);
      node.left = left;
      this.next();
      node.right = this.parseMaybeAssign(noIn);
      return this.finishNode(node, "AssignmentExpression");
    } else {
      if (ownDestructuringErrors)
        this.checkExpressionErrors(refDestructuringErrors, true);
    }
    if (oldParenAssign > -1)
      refDestructuringErrors.parenthesizedAssign = oldParenAssign;
    if (oldTrailingComma > -1)
      refDestructuringErrors.trailingComma = oldTrailingComma;
    return left;
  }

  // Parse a ternary conditional (`?:`) operator.

  parseMaybeConditional(noIn, refDestructuringErrors) {
    let startPos = this.start,
      startLoc = this.startLoc;
    let expr = this.parseExprOps(noIn, refDestructuringErrors);
    if (this.checkExpressionErrors(refDestructuringErrors)) return expr;
    if (this.eat(tt.question)) {
      let node = this.startNodeAt(startPos, startLoc);
      node.test = expr;
      node.consequent = this.parseMaybeAssign();
      this.expect(tt.colon);
      node.alternate = this.parseMaybeAssign(noIn);
      return this.finishNode(node, "ConditionalExpression");
    }
    return expr;
  }

  // Start the precedence parser.

  parseExprOps(noIn, refDestructuringErrors) {
    let startPos = this.start,
      startLoc = this.startLoc;
    let expr = this.parseMaybeUnary(refDestructuringErrors, false);
    if (this.checkExpressionErrors(refDestructuringErrors)) return expr;
    return expr.start === startPos && expr.type === "ArrowFunctionExpression"
      ? expr
      : this.parseExprOp(expr, startPos, startLoc, -1, noIn);
  }

  // Parse binary operators with the operator precedence parsing
  // algorithm. `left` is the left-hand side of the operator.
  // `minPrec` provides context that allows the function to stop and
  // defer further parser to one of its callers when it encounters an
  // operator that has a lower precedence than the set it is parsing.

  parseExprOp(left, leftStartPos, leftStartLoc, minPrec, noIn) {
    let prec = this.type.binop;
    if (prec != null && (!noIn || this.type !== tt._in)) {
      if (prec > minPrec) {
        let logical = this.type === tt.logicalOR || this.type === tt.logicalAND;
        let coalesce = this.type === tt.coalesce;
        if (coalesce) {
          // Handle the precedence of `tt.coalesce` as equal to the range of logical expressions.
          // In other words, `node.right` shouldn't contain logical expressions in order to check the mixed error.
          prec = tt.logicalAND.binop;
        }
        let op = this.value;
        this.next();
        let startPos = this.start,
          startLoc = this.startLoc;
        let right = this.parseExprOp(
          this.parseMaybeUnary(null, false),
          startPos,
          startLoc,
          prec,
          noIn
        );
        let node = this.buildBinary(
          leftStartPos,
          leftStartLoc,
          left,
          right,
          op,
          logical || coalesce
        );
        if (
          (logical && this.type === tt.coalesce) ||
          (coalesce &&
            (this.type === tt.logicalOR || this.type === tt.logicalAND))
        ) {
          this.raiseRecoverable(
            this.start,
            "Logical expressions and coalesce expressions cannot be mixed. Wrap either by parentheses"
          );
        }
        return this.parseExprOp(
          node,
          leftStartPos,
          leftStartLoc,
          minPrec,
          noIn
        );
      }
    }
    return left;
  }

  buildBinary(startPos, startLoc, left, right, op, logical) {
    let node = this.startNodeAt(startPos, startLoc);
    node.left = left;
    node.operator = op;
    node.right = right;
    return this.finishNode(
      node,
      logical ? "LogicalExpression" : "BinaryExpression"
    );
  }

  // Parse unary operators, both prefix and postfix.

  parseMaybeUnary(refDestructuringErrors, sawUnary) {
    let startPos = this.start,
      startLoc = this.startLoc,
      expr;
    if (
      this.isContextual("await") &&
      (this.inAsync ||
        (!this.inFunction && this.options.allowAwaitOutsideFunction))
    ) {
      expr = this.parseAwait();
      sawUnary = true;
    } else if (this.type.prefix) {
      let node = this.startNode(),
        update = this.type === tt.incDec;
      node.operator = this.value;
      node.prefix = true;
      this.next();
      node.argument = this.parseMaybeUnary(null, true);
      this.checkExpressionErrors(refDestructuringErrors, true);
      if (update) this.checkLValSimple(node.argument);
      else if (
        this.strict &&
        node.operator === "delete" &&
        node.argument.type === "Identifier"
      )
        this.raiseRecoverable(
          node.start,
          "Deleting local variable in strict mode"
        );
      else sawUnary = true;
      expr = this.finishNode(
        node,
        update ? "UpdateExpression" : "UnaryExpression"
      );
    } else {
      expr = this.parseExprSubscripts(refDestructuringErrors);
      if (this.checkExpressionErrors(refDestructuringErrors)) return expr;
      while (this.type.postfix && !this.canInsertSemicolon()) {
        let node = this.startNodeAt(startPos, startLoc);
        node.operator = this.value;
        node.prefix = false;
        node.argument = expr;
        this.checkLValSimple(expr);
        this.next();
        expr = this.finishNode(node, "UpdateExpression");
      }
    }

    if (!sawUnary && this.eat(tt.starstar))
      return this.buildBinary(
        startPos,
        startLoc,
        expr,
        this.parseMaybeUnary(null, false),
        "**",
        false
      );
    else return expr;
  }

  // Parse call, dot, and `[]`-subscript expressions.

  parseExprSubscripts(refDestructuringErrors) {
    let startPos = this.start,
      startLoc = this.startLoc;
    let expr = this.parseExprAtom(refDestructuringErrors);
    if (
      expr.type === "ArrowFunctionExpression" &&
      this.input.slice(this.lastTokStart, this.lastTokEnd) !== ")"
    )
      return expr;
    let result = this.parseSubscripts(expr, startPos, startLoc);
    if (refDestructuringErrors && result.type === "MemberExpression") {
      if (refDestructuringErrors.parenthesizedAssign >= result.start)
        refDestructuringErrors.parenthesizedAssign = -1;
      if (refDestructuringErrors.parenthesizedBind >= result.start)
        refDestructuringErrors.parenthesizedBind = -1;
      if (refDestructuringErrors.trailingComma >= result.start)
        refDestructuringErrors.trailingComma = -1;
    }
    return result;
  }

  parseSubscripts(base, startPos, startLoc, noCalls) {
    let maybeAsyncArrow =
      this.options.ecmaVersion >= 8 &&
      base.type === "Identifier" &&
      base.name === "async" &&
      this.lastTokEnd === base.end &&
      !this.canInsertSemicolon() &&
      base.end - base.start === 5 &&
      this.potentialArrowAt === base.start;
    let optionalChained = false;

    while (true) {
      let element = this.parseSubscript(
        base,
        startPos,
        startLoc,
        noCalls,
        maybeAsyncArrow,
        optionalChained
      );

      if (element.optional) optionalChained = true;
      if (element === base || element.type === "ArrowFunctionExpression") {
        if (optionalChained) {
          const chainNode = this.startNodeAt(startPos, startLoc);
          chainNode.expression = element;
          element = this.finishNode(chainNode, "ChainExpression");
        }
        return element;
      }

      base = element;
    }
  }

  /**
   * @param {Node} base
   */
  parseSubscript(
    base,
    startPos,
    startLoc,
    noCalls,
    maybeAsyncArrow,
    optionalChained
  ) {
    let optionalSupported = this.options.ecmaVersion >= 11;
    let optional = optionalSupported && this.eat(tt.questionDot);
    if (noCalls && optional)
      this.raise(
        this.lastTokStart,
        "Optional chaining cannot appear in the callee of new expressions"
      );

    let computed = this.eat(tt.bracketL);
    if (
      computed ||
      (optional && this.type !== tt.parenL && this.type !== tt.backQuote) ||
      this.eat(tt.dot)
    ) {
      let node = this.startNodeAt(startPos, startLoc);
      node.object = base;
      node.property = computed
        ? this.parseExpression()
        : this.parseIdent(this.options.allowReserved !== "never");
      node.computed = !!computed;
      if (computed) this.expect(tt.bracketR);
      if (optionalSupported) {
        node.optional = optional;
      }
      base = this.finishNode(node, "MemberExpression");
    } else if (!noCalls && this.eat(tt.parenL)) {
      let refDestructuringErrors = new DestructuringErrors(),
        oldYieldPos = this.yieldPos,
        oldAwaitPos = this.awaitPos,
        oldAwaitIdentPos = this.awaitIdentPos;
      this.yieldPos = 0;
      this.awaitPos = 0;
      this.awaitIdentPos = 0;
      let exprList = this.parseExprList(
        tt.parenR,
        this.options.ecmaVersion >= 8,
        false,
        refDestructuringErrors
      );
      if (
        maybeAsyncArrow &&
        !optional &&
        !this.canInsertSemicolon() &&
        this.eat(tt.arrow)
      ) {
        this.checkPatternErrors(refDestructuringErrors, false);
        this.checkYieldAwaitInDefaultParams();
        if (this.awaitIdentPos > 0)
          this.raise(
            this.awaitIdentPos,
            "Cannot use 'await' as identifier inside an async function"
          );
        this.yieldPos = oldYieldPos;
        this.awaitPos = oldAwaitPos;
        this.awaitIdentPos = oldAwaitIdentPos;
        return this.parseArrowExpression(
          this.startNodeAt(startPos, startLoc),
          exprList,
          true
        );
      }
      this.checkExpressionErrors(refDestructuringErrors, true);
      this.yieldPos = oldYieldPos || this.yieldPos;
      this.awaitPos = oldAwaitPos || this.awaitPos;
      this.awaitIdentPos = oldAwaitIdentPos || this.awaitIdentPos;
      let node = this.startNodeAt(startPos, startLoc);
      node.callee = base;
      node.arguments = exprList;
      if (optionalSupported) {
        node.optional = optional;
      }
      base = this.finishNode(node, "CallExpression");
    } else if (this.type === tt.backQuote) {
      if (optional || optionalChained) {
        this.raise(
          this.start,
          "Optional chaining cannot appear in the tag of tagged template expressions"
        );
      }
      let node = this.startNodeAt(startPos, startLoc);
      node.tag = base;
      node.quasi = this.parseTemplate({ isTagged: true });
      base = this.finishNode(node, "TaggedTemplateExpression");
    }
    return base;
  }

  // Parse an atomic expression — either a single token that is an
  // expression, an expression started by a keyword like `function` or
  // `new`, or an expression wrapped in punctuation like `()`, `[]`,
  // or `{}`.

  parseExprAtom(refDestructuringErrors) {
    // If a division operator appears in an expression position, the
    // tokenizer got confused, and we force it to read a regexp instead.
    if (this.type === tt.slash) this.readRegexp();

    let node,
      canBeArrow = this.potentialArrowAt === this.start;
    switch (this.type) {
      case tt._super:
        if (!this.allowSuper)
          this.raise(this.start, "'super' keyword outside a method");
        node = this.startNode();
        this.next();
        if (this.type === tt.parenL && !this.allowDirectSuper)
          this.raise(
            node.start,
            "super() call outside constructor of a subclass"
          );
        // The `super` keyword can appear at below:
        // SuperProperty:
        //     super [ Expression ]
        //     super . IdentifierName
        // SuperCall:
        //     super ( Arguments )
        if (
          this.type !== tt.dot &&
          this.type !== tt.bracketL &&
          this.type !== tt.parenL
        )
          this.unexpected();
        return this.finishNode(node, "Super");

      case tt._this:
        node = this.startNode();
        this.next();
        return this.finishNode(node, "ThisExpression");

      case tt.name:
        let startPos = this.start,
          startLoc = this.startLoc,
          containsEsc = this.containsEsc;
        let id = this.parseIdent(false);
        if (
          this.options.ecmaVersion >= 8 &&
          !containsEsc &&
          id.name === "async" &&
          !this.canInsertSemicolon() &&
          this.eat(tt._function)
        )
          return this.parseFunction(
            this.startNodeAt(startPos, startLoc),
            0,
            false,
            true
          );
        if (canBeArrow && !this.canInsertSemicolon()) {
          if (this.eat(tt.arrow))
            return this.parseArrowExpression(
              this.startNodeAt(startPos, startLoc),
              [id],
              false
            );
          if (
            this.options.ecmaVersion >= 8 &&
            id.name === "async" &&
            this.type === tt.name &&
            !containsEsc
          ) {
            id = this.parseIdent(false);
            if (this.canInsertSemicolon() || !this.eat(tt.arrow))
              this.unexpected();
            return this.parseArrowExpression(
              this.startNodeAt(startPos, startLoc),
              [id],
              true
            );
          }
        }
        return id;

      case tt.regexp:
        let value = /** @type {any} */ (this.value);
        node = this.parseLiteral(value.value);
        node.regex = { pattern: value.pattern, flags: value.flags };
        return node;

      case tt.num:
      case tt.string:
        return this.parseLiteral(this.value);

      case tt._null:
      case tt._true:
      case tt._false:
        node = this.startNode();
        node.value = this.type === tt._null ? null : this.type === tt._true;
        node.raw = this.type.keyword;
        this.next();
        return this.finishNode(node, "Literal");

      case tt.parenL:
        let start = this.start,
          expr = this.parseParenAndDistinguishExpression(canBeArrow);
        if (refDestructuringErrors) {
          if (
            refDestructuringErrors.parenthesizedAssign < 0 &&
            !this.isSimpleAssignTarget(expr)
          )
            refDestructuringErrors.parenthesizedAssign = start;
          if (refDestructuringErrors.parenthesizedBind < 0)
            refDestructuringErrors.parenthesizedBind = start;
        }
        return expr;

      case tt.bracketL:
        node = this.startNode();
        this.next();
        node.elements = this.parseExprList(
          tt.bracketR,
          true,
          true,
          refDestructuringErrors
        );
        return this.finishNode(node, "ArrayExpression");

      case tt.braceL:
        return this.parseObj(false, refDestructuringErrors);

      case tt._function:
        node = this.startNode();
        this.next();
        return this.parseFunction(node, 0);

      case tt._class:
        return this.parseClass(this.startNode(), false);

      case tt._new:
        return this.parseNew();

      case tt.backQuote:
        return this.parseTemplate();

      case tt._import:
        if (this.options.ecmaVersion >= 11) {
          return this.parseExprImport();
        } else {
          return this.unexpected();
        }

      default:
        this.unexpected();
    }
  }

  parseExprImport() {
    const node = this.startNode();

    // Consume `import` as an identifier for `import.meta`.
    // Because `this.parseIdent(true)` doesn't check escape sequences, it needs the check of `this.containsEsc`.
    if (this.containsEsc)
      this.raiseRecoverable(this.start, "Escape sequence in keyword import");
    const meta = this.parseIdent(true);

    switch (this.type) {
      case tt.parenL:
        return this.parseDynamicImport(node);
      case tt.dot:
        node.meta = meta;
        return this.parseImportMeta(node);
      default:
        this.unexpected();
    }
  }

  parseDynamicImport(node) {
    this.next(); // skip `(`

    // Parse node.source.
    node.source = this.parseMaybeAssign();

    // Verify ending.
    if (!this.eat(tt.parenR)) {
      const errorPos = this.start;
      if (this.eat(tt.comma) && this.eat(tt.parenR)) {
        this.raiseRecoverable(
          errorPos,
          "Trailing comma is not allowed in import()"
        );
      } else {
        this.unexpected(errorPos);
      }
    }

    return this.finishNode(node, "ImportExpression");
  }

  parseImportMeta(node) {
    this.next(); // skip `.`

    const containsEsc = this.containsEsc;
    node.property = this.parseIdent(true);

    if (node.property.name !== "meta")
      this.raiseRecoverable(
        node.property.start,
        "The only valid meta property for import is 'import.meta'"
      );
    if (containsEsc)
      this.raiseRecoverable(
        node.start,
        "'import.meta' must not contain escaped characters"
      );
    if (
      this.options.sourceType !== "module" &&
      !this.options.allowImportExportEverywhere
    )
      this.raiseRecoverable(
        node.start,
        "Cannot use 'import.meta' outside a module"
      );

    return this.finishNode(node, "MetaProperty");
  }

  parseLiteral(value) {
    let node = this.startNode();
    node.value = value;
    node.raw = this.input.slice(this.start, this.end);
    if (node.raw.charCodeAt(node.raw.length - 1) === 110)
      node.bigint = node.raw.slice(0, -1).replace(/_/g, "");
    this.next();
    return this.finishNode(node, "Literal");
  }

  parseParenExpression() {
    this.expect(tt.parenL);
    let val = this.parseExpression();
    this.expect(tt.parenR);
    return val;
  }

  parseParenAndDistinguishExpression(canBeArrow) {
    let startPos = this.start,
      startLoc = this.startLoc,
      val,
      allowTrailingComma = this.options.ecmaVersion >= 8;
    if (this.options.ecmaVersion >= 6) {
      this.next();

      let innerStartPos = this.start,
        innerStartLoc = this.startLoc;
      let exprList = [],
        first = true,
        lastIsComma = false;
      let refDestructuringErrors = new DestructuringErrors(),
        oldYieldPos = this.yieldPos,
        oldAwaitPos = this.awaitPos,
        spreadStart;
      this.yieldPos = 0;
      this.awaitPos = 0;
      // Do not save awaitIdentPos to allow checking awaits nested in parameters
      while (this.type !== tt.parenR) {
        first ? (first = false) : this.expect(tt.comma);
        if (allowTrailingComma && this.afterTrailingComma(tt.parenR, true)) {
          lastIsComma = true;
          break;
        } else if (this.type === tt.ellipsis) {
          spreadStart = this.start;
          exprList.push(this.parseParenItem(this.parseRestBinding()));
          if (this.type === tt.comma)
            this.raise(
              this.start,
              "Comma is not permitted after the rest element"
            );
          break;
        } else {
          exprList.push(
            this.parseMaybeAssign(
              false,
              refDestructuringErrors,
              this.parseParenItem
            )
          );
        }
      }
      let innerEndPos = this.start,
        innerEndLoc = this.startLoc;
      this.expect(tt.parenR);

      if (canBeArrow && !this.canInsertSemicolon() && this.eat(tt.arrow)) {
        this.checkPatternErrors(refDestructuringErrors, false);
        this.checkYieldAwaitInDefaultParams();
        this.yieldPos = oldYieldPos;
        this.awaitPos = oldAwaitPos;
        return this.parseParenArrowList(startPos, startLoc, exprList);
      }

      if (!exprList.length || lastIsComma) this.unexpected(this.lastTokStart);
      if (spreadStart) this.unexpected(spreadStart);
      this.checkExpressionErrors(refDestructuringErrors, true);
      this.yieldPos = oldYieldPos || this.yieldPos;
      this.awaitPos = oldAwaitPos || this.awaitPos;

      if (exprList.length > 1) {
        val = this.startNodeAt(innerStartPos, innerStartLoc);
        val.expressions = exprList;
        this.finishNodeAt(val, "SequenceExpression", innerEndPos, innerEndLoc);
      } else {
        val = exprList[0];
      }
    } else {
      val = this.parseParenExpression();
    }

    if (this.options.preserveParens) {
      let par = this.startNodeAt(startPos, startLoc);
      par.expression = val;
      return this.finishNode(par, "ParenthesizedExpression");
    } else {
      return val;
    }
  }

  parseParenItem(item) {
    return item;
  }

  parseParenArrowList(startPos, startLoc, exprList) {
    return this.parseArrowExpression(
      this.startNodeAt(startPos, startLoc),
      exprList
    );
  }

  // New's precedence is slightly tricky. It must allow its argument to
  // be a `[]` or dot subscript expression, but not a call — at least,
  // not without wrapping it in parentheses. Thus, it uses the noCalls
  // argument to parseSubscripts to prevent it from consuming the
  // argument list.

  parseNew() {
    if (this.containsEsc)
      this.raiseRecoverable(this.start, "Escape sequence in keyword new");
    let node = this.startNode();
    let meta = this.parseIdent(true);
    if (this.options.ecmaVersion >= 6 && this.eat(tt.dot)) {
      node.meta = meta;
      let containsEsc = this.containsEsc;
      node.property = this.parseIdent(true);
      if (node.property.name !== "target")
        this.raiseRecoverable(
          node.property.start,
          "The only valid meta property for new is 'new.target'"
        );
      if (containsEsc)
        this.raiseRecoverable(
          node.start,
          "'new.target' must not contain escaped characters"
        );
      if (!this.inNonArrowFunction)
        this.raiseRecoverable(
          node.start,
          "'new.target' can only be used in functions"
        );
      return this.finishNode(node, "MetaProperty");
    }
    let startPos = this.start,
      startLoc = this.startLoc,
      isImport = this.type === tt._import;
    node.callee = this.parseSubscripts(
      this.parseExprAtom(),
      startPos,
      startLoc,
      true
    );
    if (isImport && node.callee.type === "ImportExpression") {
      this.raise(startPos, "Cannot use new with import()");
    }
    if (this.eat(tt.parenL))
      node.arguments = this.parseExprList(
        tt.parenR,
        this.options.ecmaVersion >= 8,
        false
      );
    else node.arguments = empty;
    return this.finishNode(node, "NewExpression");
  }

  // Parse template expression.

  parseTemplateElement({ isTagged }) {
    let elem = this.startNode();
    if (this.type === tt.invalidTemplate) {
      if (!isTagged) {
        this.raiseRecoverable(
          this.start,
          "Bad escape sequence in untagged template literal"
        );
      }
      elem.value = {
        raw: this.value,
        cooked: null,
      };
    } else {
      elem.value = {
        raw: this.input.slice(this.start, this.end).replace(/\r\n?/g, "\n"),
        cooked: this.value,
      };
    }
    this.next();
    elem.tail = this.type === tt.backQuote;
    return this.finishNode(elem, "TemplateElement");
  }

  parseTemplate({ isTagged = false } = {}) {
    let node = this.startNode();
    this.next();
    node.expressions = [];
    let curElt = this.parseTemplateElement({ isTagged });
    node.quasis = [curElt];
    while (!curElt.tail) {
      if (this.type === tt.eof)
        this.raise(this.pos, "Unterminated template literal");
      this.expect(tt.dollarBraceL);
      node.expressions.push(this.parseExpression());
      this.expect(tt.braceR);
      node.quasis.push((curElt = this.parseTemplateElement({ isTagged })));
    }
    this.next();
    return this.finishNode(node, "TemplateLiteral");
  }

  isAsyncProp(prop) {
    return (
      !prop.computed &&
      prop.key.type === "Identifier" &&
      prop.key.name === "async" &&
      (this.type === tt.name ||
        this.type === tt.num ||
        this.type === tt.string ||
        this.type === tt.bracketL ||
        this.type.keyword ||
        (this.options.ecmaVersion >= 9 && this.type === tt.star)) &&
      !lineBreak.test(this.input.slice(this.lastTokEnd, this.start))
    );
  }

  // Parse an object literal or binding pattern.

  parseObj(isPattern, refDestructuringErrors) {
    let node = this.startNode(),
      first = true,
      propHash = {};
    node.properties = [];
    this.next();
    while (!this.eat(tt.braceR)) {
      if (!first) {
        this.expect(tt.comma);
        if (this.options.ecmaVersion >= 5 && this.afterTrailingComma(tt.braceR))
          break;
      } else first = false;

      const prop = this.parseProperty(isPattern, refDestructuringErrors);
      if (!isPattern)
        this.checkPropClash(prop, propHash, refDestructuringErrors);
      node.properties.push(prop);
    }
    return this.finishNode(
      node,
      isPattern ? "ObjectPattern" : "ObjectExpression"
    );
  }

  parseProperty(isPattern, refDestructuringErrors) {
    let prop = this.startNode(),
      isGenerator,
      isAsync,
      startPos,
      startLoc;
    if (this.options.ecmaVersion >= 9 && this.eat(tt.ellipsis)) {
      if (isPattern) {
        prop.argument = this.parseIdent(false);
        if (this.type === tt.comma) {
          this.raise(
            this.start,
            "Comma is not permitted after the rest element"
          );
        }
        return this.finishNode(prop, "RestElement");
      }
      // To disallow parenthesized identifier via `this.toAssignable()`.
      if (this.type === tt.parenL && refDestructuringErrors) {
        if (refDestructuringErrors.parenthesizedAssign < 0) {
          refDestructuringErrors.parenthesizedAssign = this.start;
        }
        if (refDestructuringErrors.parenthesizedBind < 0) {
          refDestructuringErrors.parenthesizedBind = this.start;
        }
      }
      // Parse argument.
      prop.argument = this.parseMaybeAssign(false, refDestructuringErrors);
      // To disallow trailing comma via `this.toAssignable()`.
      if (
        this.type === tt.comma &&
        refDestructuringErrors &&
        refDestructuringErrors.trailingComma < 0
      ) {
        refDestructuringErrors.trailingComma = this.start;
      }
      // Finish
      return this.finishNode(prop, "SpreadElement");
    }
    if (this.options.ecmaVersion >= 6) {
      prop.method = false;
      prop.shorthand = false;
      if (isPattern || refDestructuringErrors) {
        startPos = this.start;
        startLoc = this.startLoc;
      }
      if (!isPattern) isGenerator = this.eat(tt.star);
    }
    let containsEsc = this.containsEsc;
    this.parsePropertyName(prop);
    if (
      !isPattern &&
      !containsEsc &&
      this.options.ecmaVersion >= 8 &&
      !isGenerator &&
      this.isAsyncProp(prop)
    ) {
      isAsync = true;
      isGenerator = this.options.ecmaVersion >= 9 && this.eat(tt.star);
      this.parsePropertyName(prop);
    } else {
      isAsync = false;
    }
    this.parsePropertyValue(
      prop,
      isPattern,
      isGenerator,
      isAsync,
      startPos,
      startLoc,
      refDestructuringErrors,
      containsEsc
    );
    return this.finishNode(prop, "Property");
  }

  parsePropertyValue(
    prop,
    isPattern,
    isGenerator,
    isAsync,
    startPos,
    startLoc,
    refDestructuringErrors,
    containsEsc
  ) {
    if ((isGenerator || isAsync) && this.type === tt.colon) this.unexpected();

    if (this.eat(tt.colon)) {
      prop.value = isPattern
        ? this.parseMaybeDefault(this.start, this.startLoc)
        : this.parseMaybeAssign(false, refDestructuringErrors);
      prop.kind = "init";
    } else if (this.options.ecmaVersion >= 6 && this.type === tt.parenL) {
      if (isPattern) this.unexpected();
      prop.kind = "init";
      prop.method = true;
      prop.value = this.parseMethod(isGenerator, isAsync);
    } else if (
      !isPattern &&
      !containsEsc &&
      this.options.ecmaVersion >= 5 &&
      !prop.computed &&
      prop.key.type === "Identifier" &&
      (prop.key.name === "get" || prop.key.name === "set") &&
      this.type !== tt.comma &&
      this.type !== tt.braceR &&
      this.type !== tt.eq
    ) {
      if (isGenerator || isAsync) this.unexpected();
      prop.kind = prop.key.name;
      this.parsePropertyName(prop);
      prop.value = this.parseMethod(false);
      let paramCount = prop.kind === "get" ? 0 : 1;
      if (prop.value.params.length !== paramCount) {
        let start = prop.value.start;
        if (prop.kind === "get")
          this.raiseRecoverable(start, "getter should have no params");
        else
          this.raiseRecoverable(start, "setter should have exactly one param");
      } else {
        if (prop.kind === "set" && prop.value.params[0].type === "RestElement")
          this.raiseRecoverable(
            prop.value.params[0].start,
            "Setter cannot use rest params"
          );
      }
    } else if (
      this.options.ecmaVersion >= 6 &&
      !prop.computed &&
      prop.key.type === "Identifier"
    ) {
      if (isGenerator || isAsync) this.unexpected();
      this.checkUnreserved(prop.key);
      if (prop.key.name === "await" && !this.awaitIdentPos)
        this.awaitIdentPos = startPos;
      prop.kind = "init";
      if (isPattern) {
        prop.value = this.parseMaybeDefault(
          startPos,
          startLoc,
          this.copyNode(prop.key)
        );
      } else if (this.type === tt.eq && refDestructuringErrors) {
        if (refDestructuringErrors.shorthandAssign < 0)
          refDestructuringErrors.shorthandAssign = this.start;
        prop.value = this.parseMaybeDefault(
          startPos,
          startLoc,
          this.copyNode(prop.key)
        );
      } else {
        prop.value = this.copyNode(prop.key);
      }
      prop.shorthand = true;
    } else this.unexpected();
  }

  parsePropertyName(prop) {
    if (this.options.ecmaVersion >= 6) {
      if (this.eat(tt.bracketL)) {
        prop.computed = true;
        prop.key = this.parseMaybeAssign();
        this.expect(tt.bracketR);
        return prop.key;
      } else {
        prop.computed = false;
      }
    }
    return (prop.key =
      this.type === tt.num || this.type === tt.string
        ? this.parseExprAtom()
        : this.parseIdent(this.options.allowReserved !== "never"));
  }

  // Initialize empty function node.

  initFunction(node) {
    node.id = null;
    if (this.options.ecmaVersion >= 6) node.generator = node.expression = false;
    if (this.options.ecmaVersion >= 8) node.async = false;
  }

  // Parse object or class method.

  parseMethod(isGenerator, isAsync, allowDirectSuper) {
    let node = this.startNode(),
      oldYieldPos = this.yieldPos,
      oldAwaitPos = this.awaitPos,
      oldAwaitIdentPos = this.awaitIdentPos;

    this.initFunction(node);
    if (this.options.ecmaVersion >= 6) node.generator = isGenerator;
    if (this.options.ecmaVersion >= 8) node.async = !!isAsync;

    this.yieldPos = 0;
    this.awaitPos = 0;
    this.awaitIdentPos = 0;
    this.enterScope(
      functionFlags(isAsync, node.generator) |
        SCOPE_SUPER |
        (allowDirectSuper ? SCOPE_DIRECT_SUPER : 0)
    );

    this.expect(tt.parenL);
    node.params = this.parseBindingList(
      tt.parenR,
      false,
      this.options.ecmaVersion >= 8
    );
    this.checkYieldAwaitInDefaultParams();
    this.parseFunctionBody(node, false, true);

    this.yieldPos = oldYieldPos;
    this.awaitPos = oldAwaitPos;
    this.awaitIdentPos = oldAwaitIdentPos;
    return this.finishNode(node, "FunctionExpression");
  }

  // Parse arrow function expression with given parameters.

  parseArrowExpression(node, params, isAsync) {
    let oldYieldPos = this.yieldPos,
      oldAwaitPos = this.awaitPos,
      oldAwaitIdentPos = this.awaitIdentPos;

    this.enterScope(functionFlags(isAsync, false) | SCOPE_ARROW);
    this.initFunction(node);
    if (this.options.ecmaVersion >= 8) node.async = !!isAsync;

    this.yieldPos = 0;
    this.awaitPos = 0;
    this.awaitIdentPos = 0;

    node.params = this.toAssignableList(params, true);
    this.parseFunctionBody(node, true, false);

    this.yieldPos = oldYieldPos;
    this.awaitPos = oldAwaitPos;
    this.awaitIdentPos = oldAwaitIdentPos;
    return this.finishNode(node, "ArrowFunctionExpression");
  }

  // Parse function body and check parameters.

  parseFunctionBody(node, isArrowFunction, isMethod) {
    let isExpression = isArrowFunction && this.type !== tt.braceL;
    let oldStrict = this.strict,
      useStrict = false;

    if (isExpression) {
      node.body = this.parseMaybeAssign();
      node.expression = true;
      this.checkParams(node, false);
    } else {
      let nonSimple =
        this.options.ecmaVersion >= 7 && !this.isSimpleParamList(node.params);
      if (!oldStrict || nonSimple) {
        useStrict = this.strictDirective(this.end);
        // If this is a strict mode function, verify that argument names
        // are not repeated, and it does not try to bind the words `eval`
        // or `arguments`.
        if (useStrict && nonSimple)
          this.raiseRecoverable(
            node.start,
            "Illegal 'use strict' directive in function with non-simple parameter list"
          );
      }
      // Start a new scope with regard to labels and the `inFunction`
      // flag (restore them to their old value afterwards).
      let oldLabels = this.labels;
      this.labels = [];
      if (useStrict) this.strict = true;

      // Add the params to varDeclaredNames to ensure that an error is thrown
      // if a let/const declaration in the function clashes with one of the params.
      this.checkParams(
        node,
        !oldStrict &&
          !useStrict &&
          !isArrowFunction &&
          !isMethod &&
          this.isSimpleParamList(node.params)
      );
      // Ensure the function name isn't a forbidden identifier in strict mode, e.g. 'eval'
      if (this.strict && node.id) this.checkLValSimple(node.id, BIND_OUTSIDE);
      node.body = this.parseBlock(false, undefined, useStrict && !oldStrict);
      node.expression = false;
      this.adaptDirectivePrologue(node.body.body);
      this.labels = oldLabels;
    }
    this.exitScope();
  }

  isSimpleParamList(params) {
    for (let param of params) if (param.type !== "Identifier") return false;
    return true;
  }

  // Checks function params for various disallowed patterns such as using "eval"
  // or "arguments" and duplicate parameters.

  checkParams(node, allowDuplicates) {
    let nameHash = Object.create(null);
    for (let param of node.params)
      this.checkLValInnerPattern(
        param,
        BIND_VAR,
        allowDuplicates ? null : nameHash
      );
  }

  // Parses a comma-separated list of expressions, and returns them as
  // an array. `close` is the token type that ends the list, and
  // `allowEmpty` can be turned on to allow subsequent commas with
  // nothing in between them to be parsed as `null` (which is needed
  // for array literals).

  parseExprList(close, allowTrailingComma, allowEmpty, refDestructuringErrors) {
    let elts = /** @type {Node[]} */ ([]),
      first = true;
    while (!this.eat(close)) {
      if (!first) {
        this.expect(tt.comma);
        if (allowTrailingComma && this.afterTrailingComma(close)) break;
      } else first = false;

      let elt;
      if (allowEmpty && this.type === tt.comma) elt = null;
      else if (this.type === tt.ellipsis) {
        elt = this.parseSpread(refDestructuringErrors);
        if (
          refDestructuringErrors &&
          this.type === tt.comma &&
          refDestructuringErrors.trailingComma < 0
        )
          refDestructuringErrors.trailingComma = this.start;
      } else {
        elt = this.parseMaybeAssign(false, refDestructuringErrors);
      }
      elts.push(elt);
    }
    return elts;
  }

  checkUnreserved({ start, end, name }) {
    if (this.inGenerator && name === "yield")
      this.raiseRecoverable(
        start,
        "Cannot use 'yield' as identifier inside a generator"
      );
    if (this.inAsync && name === "await")
      this.raiseRecoverable(
        start,
        "Cannot use 'await' as identifier inside an async function"
      );
    if (this.keywords.test(name))
      this.raise(start, `Unexpected keyword '${name}'`);
    if (
      this.options.ecmaVersion < 6 &&
      this.input.slice(start, end).indexOf("\\") !== -1
    )
      return;
    const re = this.strict ? this.reservedWordsStrict : this.reservedWords;
    if (re.test(name)) {
      if (!this.inAsync && name === "await")
        this.raiseRecoverable(
          start,
          "Cannot use keyword 'await' outside an async function"
        );
      this.raiseRecoverable(start, `The keyword '${name}' is reserved`);
    }
  }

  // Parse the next token as an identifier. If `liberal` is true (used
  // when parsing properties), it will also convert keywords into
  // identifiers.

  parseIdent(liberal, isBinding) {
    let node = this.startNode();
    if (this.type === tt.name) {
      node.name = this.value;
    } else if (this.type.keyword) {
      node.name = this.type.keyword;

      // To fix https://github.com/acornjs/acorn/issues/575
      // `class` and `function` keywords push new context into this.context.
      // But there is no chance to pop the context if the keyword is consumed as an identifier such as a property name.
      // If the previous token is a dot, this does not apply because the context-managing code already ignored the keyword
      if (
        (node.name === "class" || node.name === "function") &&
        (this.lastTokEnd !== this.lastTokStart + 1 ||
          this.input.charCodeAt(this.lastTokStart) !== 46)
      ) {
        this.context.pop();
      }
    } else {
      this.unexpected();
    }
    this.next(!!liberal);
    this.finishNode(node, "Identifier");
    if (!liberal) {
      this.checkUnreserved(node);
      if (node.name === "await" && !this.awaitIdentPos)
        this.awaitIdentPos = node.start;
    }
    return node;
  }

  // Parses yield expression inside generator.

  parseYield(noIn) {
    if (!this.yieldPos) this.yieldPos = this.start;

    let node = this.startNode();
    this.next();
    if (
      this.type === tt.semi ||
      this.canInsertSemicolon() ||
      (this.type !== tt.star && !this.type.startsExpr)
    ) {
      node.delegate = false;
      node.argument = null;
    } else {
      node.delegate = this.eat(tt.star);
      node.argument = this.parseMaybeAssign(noIn);
    }
    return this.finishNode(node, "YieldExpression");
  }

  parseAwait() {
    if (!this.awaitPos) this.awaitPos = this.start;

    let node = this.startNode();
    this.next();
    node.argument = this.parseMaybeUnary(null, true);
    return this.finishNode(node, "AwaitExpression");
  }

  raise(pos, message) {
    let loc = getLineInfo(this.input, pos);
    message += " (" + loc.line + ":" + loc.column + ")";
    let err = /** @type {any} */ (new SyntaxError(message));
    err.pos = pos;
    err.loc = loc;
    err.raisedAt = this.pos;
    throw err;
  }

  raiseRecoverable(...args) {
    return this.raise(...args);
  }

  curPosition() {
    if (this.options.locations) {
      return new Position(this.curLine, this.pos - this.lineStart);
    }
  }

  // The functions in this module keep track of declared variables in the current scope in order to detect duplicate variable names.

  enterScope(flags) {
    this.scopeStack.push(new Scope(flags));
  }

  exitScope() {
    this.scopeStack.pop();
  }

  // The spec says:
  // > At the top level of a function, or script, function declarations are
  // > treated like var declarations rather than like lexical declarations.
  treatFunctionsAsVarInScope(scope) {
    return (
      scope.flags & SCOPE_FUNCTION ||
      (!this.inModule && scope.flags & SCOPE_TOP)
    );
  }

  declareName(name, bindingType, pos) {
    let redeclared = false;
    if (bindingType === BIND_LEXICAL) {
      const scope = this.currentScope();
      redeclared =
        scope.lexical.indexOf(name) > -1 ||
        scope.functions.indexOf(name) > -1 ||
        scope.var.indexOf(name) > -1;
      scope.lexical.push(name);
      if (this.inModule && scope.flags & SCOPE_TOP)
        delete this.undefinedExports[name];
    } else if (bindingType === BIND_SIMPLE_CATCH) {
      const scope = this.currentScope();
      scope.lexical.push(name);
    } else if (bindingType === BIND_FUNCTION) {
      const scope = this.currentScope();
      if (this.treatFunctionsAsVar)
        redeclared = scope.lexical.indexOf(name) > -1;
      else
        redeclared =
          scope.lexical.indexOf(name) > -1 || scope.var.indexOf(name) > -1;
      scope.functions.push(name);
    } else {
      for (let i = this.scopeStack.length - 1; i >= 0; --i) {
        const scope = this.scopeStack[i];
        if (
          (scope.lexical.indexOf(name) > -1 &&
            !(scope.flags & SCOPE_SIMPLE_CATCH && scope.lexical[0] === name)) ||
          (!this.treatFunctionsAsVarInScope(scope) &&
            scope.functions.indexOf(name) > -1)
        ) {
          redeclared = true;
          break;
        }
        scope.var.push(name);
        if (this.inModule && scope.flags & SCOPE_TOP)
          delete this.undefinedExports[name];
        if (scope.flags & SCOPE_VAR) break;
      }
    }
    if (redeclared)
      this.raiseRecoverable(
        pos,
        `Identifier '${name}' has already been declared`
      );
  }

  checkLocalExport(id) {
    // scope.functions must be empty as Module code is always strict.
    if (
      this.scopeStack[0].lexical.indexOf(id.name) === -1 &&
      this.scopeStack[0].var.indexOf(id.name) === -1
    ) {
      this.undefinedExports[id.name] = id;
    }
  }

  currentScope() {
    return this.scopeStack[this.scopeStack.length - 1];
  }

  currentVarScope() {
    for (let i = this.scopeStack.length - 1; ; i--) {
      let scope = this.scopeStack[i];
      if (scope.flags & SCOPE_VAR) return scope;
    }
  }

  // Could be useful for `this`, `new.target`, `super()`, `super.property`, and `super[property]`.
  currentThisScope() {
    for (let i = this.scopeStack.length - 1; ; i--) {
      let scope = this.scopeStack[i];
      if (scope.flags & SCOPE_VAR && !(scope.flags & SCOPE_ARROW)) return scope;
    }
  }

  startNode() {
    return new Node(this, this.start, this.startLoc);
  }

  startNodeAt(pos, loc) {
    return new Node(this, pos, loc);
  }

  /**
   * @param node {Node}
   * @returns {Node}
   */
  finishNode(node, type) {
    return finishNodeAt.call(
      this,
      node,
      type,
      this.lastTokEnd,
      this.lastTokEndLoc
    );
  }

  // Finish node at given position

  finishNodeAt(node, type, pos, loc) {
    return finishNodeAt.call(this, node, type, pos, loc);
  }

  copyNode(node) {
    let newNode = new Node(this, node.start, this.startLoc);
    for (let prop in node) newNode[prop] = node[prop];
    return newNode;
  }

  // Move to the next token

  next(ignoreEscapeSequenceInKeyword) {
    if (!ignoreEscapeSequenceInKeyword && this.type.keyword && this.containsEsc)
      this.raiseRecoverable(
        this.start,
        "Escape sequence in keyword " + this.type.keyword
      );
    if (this.options.onToken) this.options.onToken(new Token(this));

    this.lastTokEnd = this.end;
    this.lastTokStart = this.start;
    this.lastTokEndLoc = this.endLoc;
    this.lastTokStartLoc = this.startLoc;
    this.nextToken();
  }

  getToken() {
    this.next();
    return new Token(this);
  }

  // Toggle strict mode. Re-reads the next number or string to please
  // pedantic tests (`"use strict"; 010;` should fail).

  curContext() {
    return this.context[this.context.length - 1];
  }

  // Read a single token, updating the parser object's token-related
  // properties.

  nextToken() {
    let curContext = this.curContext();
    if (!curContext || !curContext.preserveSpace) this.skipSpace();

    this.start = this.pos;
    if (this.options.locations) this.startLoc = this.curPosition();
    if (this.pos >= this.input.length) return this.finishToken(tt.eof);

    if (curContext.override) return curContext.override(this);
    else this.readToken(this.fullCharCodeAtPos());
  }

  readToken(code) {
    // Identifier or keyword. '\uXXXX' sequences are allowed in
    // identifiers, so '\' also dispatches to that.
    if (
      isIdentifierStart(code, this.options.ecmaVersion >= 6) ||
      code === 92 /* '\' */
    )
      return this.readWord();

    return this.getTokenFromCode(code);
  }

  fullCharCodeAtPos() {
    let code = this.input.charCodeAt(this.pos);
    if (code <= 0xd7ff || code >= 0xe000) return code;
    let next = this.input.charCodeAt(this.pos + 1);
    return (code << 10) + next - 0x35fdc00;
  }

  skipBlockComment() {
    let startLoc = this.options.onComment && this.curPosition();
    let start = this.pos,
      end = this.input.indexOf("*/", (this.pos += 2));
    if (end === -1) this.raise(this.pos - 2, "Unterminated comment");
    this.pos = end + 2;
    if (this.options.locations) {
      lineBreakG.lastIndex = start;
      let match;
      while ((match = lineBreakG.exec(this.input)) && match.index < this.pos) {
        ++this.curLine;
        this.lineStart = match.index + match[0].length;
      }
    }
    if (this.options.onComment)
      this.options.onComment(
        true,
        this.input.slice(start + 2, end),
        start,
        this.pos,
        startLoc,
        this.curPosition()
      );
  }

  skipLineComment(startSkip) {
    let start = this.pos;
    let startLoc = this.options.onComment && this.curPosition();
    let ch = this.input.charCodeAt((this.pos += startSkip));
    while (this.pos < this.input.length && !isNewLine(ch)) {
      ch = this.input.charCodeAt(++this.pos);
    }
    if (this.options.onComment)
      this.options.onComment(
        false,
        this.input.slice(start + startSkip, this.pos),
        start,
        this.pos,
        startLoc,
        this.curPosition()
      );
  }

  // Called at the start of the parse and after every token. Skips
  // whitespace and comments, and.

  skipSpace() {
    loop: while (this.pos < this.input.length) {
      let ch = this.input.charCodeAt(this.pos);
      switch (ch) {
        case 32:
        case 160: // ' '
          ++this.pos;
          break;
        case 13:
          if (this.input.charCodeAt(this.pos + 1) === 10) {
            ++this.pos;
          }
        case 10:
        case 8232:
        case 8233:
          ++this.pos;
          if (this.options.locations) {
            ++this.curLine;
            this.lineStart = this.pos;
          }
          break;
        case 47: // '/'
          switch (this.input.charCodeAt(this.pos + 1)) {
            case 42: // '*'
              this.skipBlockComment();
              break;
            case 47:
              this.skipLineComment(2);
              break;
            default:
              break loop;
          }
          break;
        default:
          if (
            (ch > 8 && ch < 14) ||
            (ch >= 5760 && nonASCIIwhitespace.test(String.fromCharCode(ch)))
          ) {
            ++this.pos;
          } else {
            break loop;
          }
      }
    }
  }

  // Called at the end of every token. Sets `end`, `val`, and
  // maintains `context` and `exprAllowed`, and skips the space after
  // the token, so that the next one's `start` will point at the
  // right position.

  finishToken(type, val) {
    this.end = this.pos;
    if (this.options.locations) this.endLoc = this.curPosition();
    let prevType = this.type;
    this.type = type;
    this.value = val;

    this.updateContext(prevType);
  }

  // ### Token reading

  // This is the function that is called to fetch the next token. It
  // is somewhat obscure, because it works in character codes rather
  // than characters, and because operator parsing has been inlined
  // into it.
  //
  // All in the name of speed.
  //
  readToken_dot() {
    let next = this.input.charCodeAt(this.pos + 1);
    if (next >= 48 && next <= 57) return this.readNumber(true);
    let next2 = this.input.charCodeAt(this.pos + 2);
    if (this.options.ecmaVersion >= 6 && next === 46 && next2 === 46) {
      // 46 = dot '.'
      this.pos += 3;
      return this.finishToken(tt.ellipsis);
    } else {
      ++this.pos;
      return this.finishToken(tt.dot);
    }
  }

  readToken_slash() {
    // '/'
    let next = this.input.charCodeAt(this.pos + 1);
    if (this.exprAllowed) {
      ++this.pos;
      return this.readRegexp();
    }
    if (next === 61) return this.finishOp(tt.assign, 2);
    return this.finishOp(tt.slash, 1);
  }

  readToken_mult_modulo_exp(code) {
    // '%*'
    let next = this.input.charCodeAt(this.pos + 1);
    let size = 1;
    let tokentype = code === 42 ? tt.star : tt.modulo;

    // exponentiation operator ** and **=
    if (this.options.ecmaVersion >= 7 && code === 42 && next === 42) {
      ++size;
      tokentype = tt.starstar;
      next = this.input.charCodeAt(this.pos + 2);
    }

    if (next === 61) return this.finishOp(tt.assign, size + 1);
    return this.finishOp(tokentype, size);
  }

  readToken_pipe_amp(code) {
    // '|&'
    let next = this.input.charCodeAt(this.pos + 1);
    if (next === code) {
      if (this.options.ecmaVersion >= 12) {
        let next2 = this.input.charCodeAt(this.pos + 2);
        if (next2 === 61) return this.finishOp(tt.assign, 3);
      }
      return this.finishOp(code === 124 ? tt.logicalOR : tt.logicalAND, 2);
    }
    if (next === 61) return this.finishOp(tt.assign, 2);
    return this.finishOp(code === 124 ? tt.bitwiseOR : tt.bitwiseAND, 1);
  }

  readToken_caret() {
    // '^'
    let next = this.input.charCodeAt(this.pos + 1);
    if (next === 61) return this.finishOp(tt.assign, 2);
    return this.finishOp(tt.bitwiseXOR, 1);
  }

  readToken_plus_min(code) {
    // '+-'
    let next = this.input.charCodeAt(this.pos + 1);
    if (next === code) {
      if (
        next === 45 &&
        !this.inModule &&
        this.input.charCodeAt(this.pos + 2) === 62 &&
        (this.lastTokEnd === 0 ||
          lineBreak.test(this.input.slice(this.lastTokEnd, this.pos)))
      ) {
        // A `-->` line comment
        this.skipLineComment(3);
        this.skipSpace();
        return this.nextToken();
      }
      return this.finishOp(tt.incDec, 2);
    }
    if (next === 61) return this.finishOp(tt.assign, 2);
    return this.finishOp(tt.plusMin, 1);
  }

  readToken_lt_gt(code) {
    // '<>'
    let next = this.input.charCodeAt(this.pos + 1);
    let size = 1;
    if (next === code) {
      size = code === 62 && this.input.charCodeAt(this.pos + 2) === 62 ? 3 : 2;
      if (this.input.charCodeAt(this.pos + size) === 61)
        return this.finishOp(tt.assign, size + 1);
      return this.finishOp(tt.bitShift, size);
    }
    if (
      next === 33 &&
      code === 60 &&
      !this.inModule &&
      this.input.charCodeAt(this.pos + 2) === 45 &&
      this.input.charCodeAt(this.pos + 3) === 45
    ) {
      // `<!--`, an XML-style comment that should be interpreted as a line comment
      this.skipLineComment(4);
      this.skipSpace();
      return this.nextToken();
    }
    if (next === 61) size = 2;
    return this.finishOp(tt.relational, size);
  }

  readToken_eq_excl(code) {
    // '=!'
    let next = this.input.charCodeAt(this.pos + 1);
    if (next === 61)
      return this.finishOp(
        tt.equality,
        this.input.charCodeAt(this.pos + 2) === 61 ? 3 : 2
      );
    if (code === 61 && next === 62 && this.options.ecmaVersion >= 6) {
      // '=>'
      this.pos += 2;
      return this.finishToken(tt.arrow);
    }
    return this.finishOp(code === 61 ? tt.eq : tt.prefix, 1);
  }

  readToken_question() {
    // '?'
    const ecmaVersion = this.options.ecmaVersion;
    if (ecmaVersion >= 11) {
      let next = this.input.charCodeAt(this.pos + 1);
      if (next === 46) {
        let next2 = this.input.charCodeAt(this.pos + 2);
        if (next2 < 48 || next2 > 57) return this.finishOp(tt.questionDot, 2);
      }
      if (next === 63) {
        if (ecmaVersion >= 12) {
          let next2 = this.input.charCodeAt(this.pos + 2);
          if (next2 === 61) return this.finishOp(tt.assign, 3);
        }
        return this.finishOp(tt.coalesce, 2);
      }
    }
    return this.finishOp(tt.question, 1);
  }

  getTokenFromCode(code) {
    switch (code) {
      // The interpretation of a dot depends on whether it is followed
      // by a digit or another two dots.
      case 46: // '.'
        return this.readToken_dot();

      // Punctuation tokens.
      case 40:
        ++this.pos;
        return this.finishToken(tt.parenL);
      case 41:
        ++this.pos;
        return this.finishToken(tt.parenR);
      case 59:
        ++this.pos;
        return this.finishToken(tt.semi);
      case 44:
        ++this.pos;
        return this.finishToken(tt.comma);
      case 91:
        ++this.pos;
        return this.finishToken(tt.bracketL);
      case 93:
        ++this.pos;
        return this.finishToken(tt.bracketR);
      case 123:
        ++this.pos;
        return this.finishToken(tt.braceL);
      case 125:
        ++this.pos;
        return this.finishToken(tt.braceR);
      case 58:
        ++this.pos;
        return this.finishToken(tt.colon);

      case 96: // '`'
        if (this.options.ecmaVersion < 6) break;
        ++this.pos;
        return this.finishToken(tt.backQuote);

      case 48: // '0'
        let next = this.input.charCodeAt(this.pos + 1);
        if (next === 120 || next === 88) return this.readRadixNumber(16); // '0x', '0X' - hex number
        if (this.options.ecmaVersion >= 6) {
          if (next === 111 || next === 79) return this.readRadixNumber(8); // '0o', '0O' - octal number
          if (next === 98 || next === 66) return this.readRadixNumber(2); // '0b', '0B' - binary number
        }

      // Anything else beginning with a digit is an integer, octal
      // number, or float.
      case 49:
      case 50:
      case 51:
      case 52:
      case 53:
      case 54:
      case 55:
      case 56:
      case 57: // 1-9
        return this.readNumber(false);

      // Quotes produce strings.
      case 34:
      case 39: // '"', "'"
        return this.readString(code);

      // Operators are parsed inline in tiny state machines. '=' (61) is
      // often referred to. `finishOp` simply skips the amount of
      // characters it is given as second argument, and returns a token
      // of the type given by its first argument.

      case 47: // '/'
        return this.readToken_slash();

      case 37:
      case 42: // '%*'
        return this.readToken_mult_modulo_exp(code);

      case 124:
      case 38: // '|&'
        return this.readToken_pipe_amp(code);

      case 94: // '^'
        return this.readToken_caret();

      case 43:
      case 45: // '+-'
        return this.readToken_plus_min(code);

      case 60:
      case 62: // '<>'
        return this.readToken_lt_gt(code);

      case 61:
      case 33: // '=!'
        return this.readToken_eq_excl(code);

      case 63: // '?'
        return this.readToken_question();

      case 126: // '~'
        return this.finishOp(tt.prefix, 1);
    }

    this.raise(
      this.pos,
      "Unexpected character '" + codePointToString(code) + "'"
    );
  }

  finishOp(type, size) {
    let str = this.input.slice(this.pos, this.pos + size);
    this.pos += size;
    return this.finishToken(type, str);
  }

  readRegexp() {
    let escaped,
      inClass,
      start = this.pos;
    for (;;) {
      if (this.pos >= this.input.length)
        this.raise(start, "Unterminated regular expression");
      let ch = this.input.charAt(this.pos);
      if (lineBreak.test(ch))
        this.raise(start, "Unterminated regular expression");
      if (!escaped) {
        if (ch === "[") inClass = true;
        else if (ch === "]" && inClass) inClass = false;
        else if (ch === "/" && !inClass) break;
        escaped = ch === "\\";
      } else escaped = false;
      ++this.pos;
    }
    let pattern = this.input.slice(start, this.pos);
    ++this.pos;
    let flagsStart = this.pos;
    let flags = this.readWord1();
    if (this.containsEsc) this.unexpected(flagsStart);

    // Validate pattern
    const state =
      this.regexpState || (this.regexpState = new RegExpValidationState(this));
    state.reset(start, pattern, flags);
    this.validateRegExpFlags(state);
    this.validateRegExpPattern(state);

    // Create Literal#value property value.
    let value = null;
    try {
      value = new RegExp(pattern, flags);
    } catch (e) {
      // ESTree requires null if it failed to instantiate RegExp object.
      // https://github.com/estree/estree/blob/a27003adf4fd7bfad44de9cef372a2eacd527b1c/es5.md#regexpliteral
    }

    return this.finishToken(tt.regexp, { pattern, flags, value });
  }

  // Read an integer in the given radix. Return null if zero digits
  // were read, the integer value otherwise. When `len` is given, this
  // will return `null` unless the integer has exactly `len` digits.

  readInt(radix, len, maybeLegacyOctalNumericLiteral) {
    // `len` is used for character escape sequences. In that case, disallow separators.
    const allowSeparators = this.options.ecmaVersion >= 12 && len === undefined;

    // `maybeLegacyOctalNumericLiteral` is true if it doesn't have prefix (0x,0o,0b)
    // and isn't fraction part nor exponent part. In that case, if the first digit
    // is zero then disallow separators.
    const isLegacyOctalNumericLiteral =
      maybeLegacyOctalNumericLiteral && this.input.charCodeAt(this.pos) === 48;

    let start = this.pos,
      total = 0,
      lastCode = 0;
    for (let i = 0, e = len == null ? Infinity : len; i < e; ++i, ++this.pos) {
      let code = this.input.charCodeAt(this.pos),
        val;

      if (allowSeparators && code === 95) {
        if (isLegacyOctalNumericLiteral)
          this.raiseRecoverable(
            this.pos,
            "Numeric separator is not allowed in legacy octal numeric literals"
          );
        if (lastCode === 95)
          this.raiseRecoverable(
            this.pos,
            "Numeric separator must be exactly one underscore"
          );
        if (i === 0)
          this.raiseRecoverable(
            this.pos,
            "Numeric separator is not allowed at the first of digits"
          );
        lastCode = code;
        continue;
      }

      if (code >= 97) val = code - 97 + 10;
      // a
      else if (code >= 65) val = code - 65 + 10;
      // A
      else if (code >= 48 && code <= 57) val = code - 48;
      // 0-9
      else val = Infinity;
      if (val >= radix) break;
      lastCode = code;
      total = total * radix + val;
    }

    if (allowSeparators && lastCode === 95)
      this.raiseRecoverable(
        this.pos - 1,
        "Numeric separator is not allowed at the last of digits"
      );
    if (this.pos === start || (len != null && this.pos - start !== len))
      return null;

    return total;
  }

  readRadixNumber(radix) {
    let start = this.pos;
    this.pos += 2; // 0x
    let val = /** @type {BigInt | number} */ (this.readInt(radix));
    if (val == null)
      this.raise(this.start + 2, "Expected number in radix " + radix);
    if (
      this.options.ecmaVersion >= 11 &&
      this.input.charCodeAt(this.pos) === 110
    ) {
      val = stringToBigInt(this.input.slice(start, this.pos));
      ++this.pos;
    } else if (isIdentifierStart(this.fullCharCodeAtPos()))
      this.raise(this.pos, "Identifier directly after number");
    return this.finishToken(tt.num, val);
  }

  // Read an integer, octal integer, or floating-point number.

  readNumber(startsWithDot) {
    let start = this.pos;
    if (!startsWithDot && this.readInt(10, undefined, true) === null)
      this.raise(start, "Invalid number");
    let octal = this.pos - start >= 2 && this.input.charCodeAt(start) === 48;
    if (octal && this.strict) this.raise(start, "Invalid number");
    let next = this.input.charCodeAt(this.pos);
    if (
      !octal &&
      !startsWithDot &&
      this.options.ecmaVersion >= 11 &&
      next === 110
    ) {
      let val = stringToBigInt(this.input.slice(start, this.pos));
      ++this.pos;
      if (isIdentifierStart(this.fullCharCodeAtPos()))
        this.raise(this.pos, "Identifier directly after number");
      return this.finishToken(tt.num, val);
    }
    if (octal && /[89]/.test(this.input.slice(start, this.pos))) octal = false;
    if (next === 46 && !octal) {
      // '.'
      ++this.pos;
      this.readInt(10);
      next = this.input.charCodeAt(this.pos);
    }
    if ((next === 69 || next === 101) && !octal) {
      // 'eE'
      next = this.input.charCodeAt(++this.pos);
      if (next === 43 || next === 45) ++this.pos; // '+-'
      if (this.readInt(10) === null) this.raise(start, "Invalid number");
    }
    if (isIdentifierStart(this.fullCharCodeAtPos()))
      this.raise(this.pos, "Identifier directly after number");

    let val = stringToNumber(this.input.slice(start, this.pos), octal);
    return this.finishToken(tt.num, val);
  }

  // Read a string value, interpreting backslash-escapes.

  readCodePoint() {
    let ch = this.input.charCodeAt(this.pos),
      code;

    if (ch === 123) {
      // '{'
      if (this.options.ecmaVersion < 6) this.unexpected();
      let codePos = ++this.pos;
      code = this.readHexChar(this.input.indexOf("}", this.pos) - this.pos);
      ++this.pos;
      if (code > 0x10ffff)
        this.invalidStringToken(codePos, "Code point out of bounds");
    } else {
      code = this.readHexChar(4);
    }
    return code;
  }

  readString(quote) {
    let out = "",
      chunkStart = ++this.pos;
    for (;;) {
      if (this.pos >= this.input.length)
        this.raise(this.start, "Unterminated string constant");
      let ch = this.input.charCodeAt(this.pos);
      if (ch === quote) break;
      if (ch === 92) {
        // '\'
        out += this.input.slice(chunkStart, this.pos);
        out += this.readEscapedChar(false);
        chunkStart = this.pos;
      } else {
        if (isNewLine(ch, this.options.ecmaVersion >= 10))
          this.raise(this.start, "Unterminated string constant");
        ++this.pos;
      }
    }
    out += this.input.slice(chunkStart, this.pos++);
    return this.finishToken(tt.string, out);
  }

  // Reads template string tokens.

  tryReadTemplateToken() {
    this.inTemplateElement = true;
    try {
      this.readTmplToken();
    } catch (err) {
      if (err === INVALID_TEMPLATE_ESCAPE_ERROR) {
        this.readInvalidTemplateToken();
      } else {
        throw err;
      }
    }

    this.inTemplateElement = false;
  }

  invalidStringToken(position, message) {
    if (this.inTemplateElement && this.options.ecmaVersion >= 9) {
      throw INVALID_TEMPLATE_ESCAPE_ERROR;
    } else {
      this.raise(position, message);
    }
  }

  readTmplToken() {
    let out = "",
      chunkStart = this.pos;
    for (;;) {
      if (this.pos >= this.input.length)
        this.raise(this.start, "Unterminated template");
      let ch = this.input.charCodeAt(this.pos);
      if (
        ch === 96 ||
        (ch === 36 && this.input.charCodeAt(this.pos + 1) === 123)
      ) {
        // '`', '${'
        if (
          this.pos === this.start &&
          (this.type === tt.template || this.type === tt.invalidTemplate)
        ) {
          if (ch === 36) {
            this.pos += 2;
            return this.finishToken(tt.dollarBraceL);
          } else {
            ++this.pos;
            return this.finishToken(tt.backQuote);
          }
        }
        out += this.input.slice(chunkStart, this.pos);
        return this.finishToken(tt.template, out);
      }
      if (ch === 92) {
        // '\'
        out += this.input.slice(chunkStart, this.pos);
        out += this.readEscapedChar(true);
        chunkStart = this.pos;
      } else if (isNewLine(ch)) {
        out += this.input.slice(chunkStart, this.pos);
        ++this.pos;
        switch (ch) {
          case 13:
            if (this.input.charCodeAt(this.pos) === 10) ++this.pos;
          case 10:
            out += "\n";
            break;
          default:
            out += String.fromCharCode(ch);
            break;
        }
        if (this.options.locations) {
          ++this.curLine;
          this.lineStart = this.pos;
        }
        chunkStart = this.pos;
      } else {
        ++this.pos;
      }
    }
  }

  // Reads a template token to search for the end, without validating any escape sequences
  readInvalidTemplateToken() {
    for (; this.pos < this.input.length; this.pos++) {
      switch (this.input[this.pos]) {
        case "\\":
          ++this.pos;
          break;

        case "$":
          if (this.input[this.pos + 1] !== "{") {
            break;
          }
        // falls through

        case "`":
          return this.finishToken(
            tt.invalidTemplate,
            this.input.slice(this.start, this.pos)
          );

        // no default
      }
    }
    this.raise(this.start, "Unterminated template");
  }

  // Used to read escaped characters

  readEscapedChar(inTemplate) {
    let ch = this.input.charCodeAt(++this.pos);
    ++this.pos;
    switch (ch) {
      case 110:
        return "\n"; // 'n' -> '\n'
      case 114:
        return "\r"; // 'r' -> '\r'
      case 120:
        return String.fromCharCode(this.readHexChar(2)); // 'x'
      case 117:
        return codePointToString(this.readCodePoint()); // 'u'
      case 116:
        return "\t"; // 't' -> '\t'
      case 98:
        return "\b"; // 'b' -> '\b'
      case 118:
        return "\u000b"; // 'v' -> '\u000b'
      case 102:
        return "\f"; // 'f' -> '\f'
      case 13:
        if (this.input.charCodeAt(this.pos) === 10) ++this.pos; // '\r\n'
      case 10: // ' \n'
        if (this.options.locations) {
          this.lineStart = this.pos;
          ++this.curLine;
        }
        return "";
      case 56:
      case 57:
        if (this.strict) {
          this.invalidStringToken(this.pos - 1, "Invalid escape sequence");
        }
        if (inTemplate) {
          const codePos = this.pos - 1;

          this.invalidStringToken(
            codePos,
            "Invalid escape sequence in template string"
          );

          return null;
        }
      default:
        if (ch >= 48 && ch <= 55) {
          let octalStr = this.input.substr(this.pos - 1, 3).match(/^[0-7]+/)[0];
          let octal = parseInt(octalStr, 8);
          if (octal > 255) {
            octalStr = octalStr.slice(0, -1);
            octal = parseInt(octalStr, 8);
          }
          this.pos += octalStr.length - 1;
          ch = this.input.charCodeAt(this.pos);
          if (
            (octalStr !== "0" || ch === 56 || ch === 57) &&
            (this.strict || inTemplate)
          ) {
            this.invalidStringToken(
              this.pos - 1 - octalStr.length,
              inTemplate
                ? "Octal literal in template string"
                : "Octal literal in strict mode"
            );
          }
          return String.fromCharCode(octal);
        }
        if (isNewLine(ch)) {
          // Unicode new line characters after \ get removed from output in both
          // template literals and strings
          return "";
        }
        return String.fromCharCode(ch);
    }
  }

  // Used to read character escape sequences ('\x', '\u', '\U').

  readHexChar(len) {
    let codePos = this.pos;
    let n = this.readInt(16, len);
    if (n === null)
      this.invalidStringToken(codePos, "Bad character escape sequence");
    return n;
  }

  // Read an identifier, and return it as a string. Sets `this.containsEsc`
  // to whether the word contained a '\u' escape.
  //
  // Incrementally adds only escaped chars, adding other chunks as-is
  // as a micro-optimization.

  readWord1() {
    this.containsEsc = false;
    let word = "",
      first = true,
      chunkStart = this.pos;
    let astral = this.options.ecmaVersion >= 6;
    while (this.pos < this.input.length) {
      let ch = this.fullCharCodeAtPos();
      if (isIdentifierChar(ch, astral)) {
        this.pos += ch <= 0xffff ? 1 : 2;
      } else if (ch === 92) {
        // "\"
        this.containsEsc = true;
        word += this.input.slice(chunkStart, this.pos);
        let escStart = this.pos;
        if (this.input.charCodeAt(++this.pos) !== 117)
          // "u"
          this.invalidStringToken(
            this.pos,
            "Expecting Unicode escape sequence \\uXXXX"
          );
        ++this.pos;
        let esc = this.readCodePoint();
        if (!(first ? isIdentifierStart : isIdentifierChar)(esc, astral))
          this.invalidStringToken(escStart, "Invalid Unicode escape");
        word += codePointToString(esc);
        chunkStart = this.pos;
      } else {
        break;
      }
      first = false;
    }
    return word + this.input.slice(chunkStart, this.pos);
  }

  // Read an identifier or keyword token. Will check for reserved
  // words when necessary.

  readWord() {
    let word = this.readWord1();
    let type = tt.name;
    if (this.keywords.test(word)) {
      type = keywordTypes[word];
    }
    return this.finishToken(type, word);
  }

  toAssignable(node, isBinding, refDestructuringErrors) {
    if (this.options.ecmaVersion >= 6 && node) {
      switch (node.type) {
        case "Identifier":
          if (this.inAsync && node.name === "await")
            this.raise(
              node.start,
              "Cannot use 'await' as identifier inside an async function"
            );
          break;

        case "ObjectPattern":
        case "ArrayPattern":
        case "AssignmentPattern":
        case "RestElement":
          break;

        case "ObjectExpression":
          node.type = "ObjectPattern";
          if (refDestructuringErrors)
            this.checkPatternErrors(refDestructuringErrors, true);
          for (let prop of node.properties) {
            this.toAssignable(prop, isBinding);
            // Early error:
            //   AssignmentRestProperty[Yield, Await] :
            //     `...` DestructuringAssignmentTarget[Yield, Await]
            //
            //   It is a Syntax Error if |DestructuringAssignmentTarget| is an |ArrayLiteral| or an |ObjectLiteral|.
            if (
              prop.type === "RestElement" &&
              (prop.argument.type === "ArrayPattern" ||
                prop.argument.type === "ObjectPattern")
            ) {
              this.raise(prop.argument.start, "Unexpected token");
            }
          }
          break;

        case "Property":
          // AssignmentProperty has type === "Property"
          if (node.kind !== "init")
            this.raise(
              node.key.start,
              "Object pattern can't contain getter or setter"
            );
          this.toAssignable(node.value, isBinding);
          break;

        case "ArrayExpression":
          node.type = "ArrayPattern";
          if (refDestructuringErrors)
            this.checkPatternErrors(refDestructuringErrors, true);
          this.toAssignableList(node.elements, isBinding);
          break;

        case "SpreadElement":
          node.type = "RestElement";
          this.toAssignable(node.argument, isBinding);
          if (node.argument.type === "AssignmentPattern")
            this.raise(
              node.argument.start,
              "Rest elements cannot have a default value"
            );
          break;

        case "AssignmentExpression":
          if (node.operator !== "=")
            this.raise(
              node.left.end,
              "Only '=' operator can be used for specifying default value."
            );
          node.type = "AssignmentPattern";
          delete node.operator;
          this.toAssignable(node.left, isBinding);
          break;

        case "ParenthesizedExpression":
          this.toAssignable(node.expression, isBinding, refDestructuringErrors);
          break;

        case "ChainExpression":
          this.raiseRecoverable(
            node.start,
            "Optional chaining cannot appear in left-hand side"
          );
          break;

        case "MemberExpression":
          if (!isBinding) break;

        default:
          this.raise(node.start, "Assigning to rvalue");
      }
    } else if (refDestructuringErrors)
      this.checkPatternErrors(refDestructuringErrors, true);
    return node;
  }

  // Convert list of expression atoms to binding list.

  toAssignableList(exprList, isBinding) {
    let end = exprList.length;
    for (let i = 0; i < end; i++) {
      let elt = exprList[i];
      if (elt) this.toAssignable(elt, isBinding);
    }
    if (end) {
      let last = exprList[end - 1];
      if (
        this.options.ecmaVersion === 6 &&
        isBinding &&
        last &&
        last.type === "RestElement" &&
        last.argument.type !== "Identifier"
      )
        this.unexpected(last.argument.start);
    }
    return exprList;
  }

  // Parses spread element.

  parseSpread(refDestructuringErrors) {
    let node = this.startNode();
    this.next();
    node.argument = this.parseMaybeAssign(false, refDestructuringErrors);
    return this.finishNode(node, "SpreadElement");
  }

  parseRestBinding() {
    let node = this.startNode();
    this.next();

    // RestElement inside of a function parameter must be an identifier
    if (this.options.ecmaVersion === 6 && this.type !== tt.name)
      this.unexpected();

    node.argument = this.parseBindingAtom();

    return this.finishNode(node, "RestElement");
  }

  // Parses lvalue (assignable) atom.

  parseBindingAtom() {
    if (this.options.ecmaVersion >= 6) {
      switch (this.type) {
        case tt.bracketL:
          let node = this.startNode();
          this.next();
          node.elements = this.parseBindingList(tt.bracketR, true, true);
          return this.finishNode(node, "ArrayPattern");

        case tt.braceL:
          return this.parseObj(true);
      }
    }
    return this.parseIdent();
  }

  parseBindingList(close, allowEmpty, allowTrailingComma) {
    let elts = [],
      first = true;
    while (!this.eat(close)) {
      if (first) first = false;
      else this.expect(tt.comma);
      if (allowEmpty && this.type === tt.comma) {
        elts.push(null);
      } else if (allowTrailingComma && this.afterTrailingComma(close)) {
        break;
      } else if (this.type === tt.ellipsis) {
        let rest = this.parseRestBinding();
        this.parseBindingListItem(rest);
        elts.push(rest);
        if (this.type === tt.comma)
          this.raise(
            this.start,
            "Comma is not permitted after the rest element"
          );
        this.expect(close);
        break;
      } else {
        let elem = this.parseMaybeDefault(this.start, this.startLoc);
        this.parseBindingListItem(elem);
        elts.push(elem);
      }
    }
    return elts;
  }

  parseBindingListItem(param) {
    return param;
  }

  // Parses assignment pattern around given atom if possible.

  parseMaybeDefault(startPos, startLoc, left) {
    left = left || this.parseBindingAtom();
    if (this.options.ecmaVersion < 6 || !this.eat(tt.eq)) return left;
    let node = this.startNodeAt(startPos, startLoc);
    node.left = left;
    node.right = this.parseMaybeAssign();
    return this.finishNode(node, "AssignmentPattern");
  }

  // The following three functions all verify that a node is an lvalue —
  // something that can be bound, or assigned to. In order to do so, they perform
  // a variety of checks:
  //
  // - Check that none of the bound/assigned-to identifiers are reserved words.
  // - Record name declarations for bindings in the appropriate scope.
  // - Check duplicate argument names, if checkClashes is set.
  //
  // If a complex binding pattern is encountered (e.g., object and array
  // destructuring), the entire pattern is recursively checked.
  //
  // There are three versions of checkLVal*() appropriate for different
  // circumstances:
  //
  // - checkLValSimple() shall be used if the syntactic construct supports
  //   nothing other than identifiers and member expressions. Parenthesized
  //   expressions are also correctly handled. This is generally appropriate for
  //   constructs for which the spec says
  //
  //   > It is a Syntax Error if AssignmentTargetType of [the production] is not
  //   > simple.
  //
  //   It is also appropriate for checking if an identifier is valid and not
  //   defined elsewhere, like import declarations or function/class identifiers.
  //
  //   Examples where this is used include:
  //     a += …;
  //     import a from '…';
  //   where a is the node to be checked.
  //
  // - checkLValPattern() shall be used if the syntactic construct supports
  //   anything checkLValSimple() supports, as well as object and array
  //   destructuring patterns. This is generally appropriate for constructs for
  //   which the spec says
  //
  //   > It is a Syntax Error if [the production] is neither an ObjectLiteral nor
  //   > an ArrayLiteral and AssignmentTargetType of [the production] is not
  //   > simple.
  //
  //   Examples where this is used include:
  //     (a = …);
  //     const a = …;
  //     try { … } catch (a) { … }
  //   where a is the node to be checked.
  //
  // - checkLValInnerPattern() shall be used if the syntactic construct supports
  //   anything checkLValPattern() supports, as well as default assignment
  //   patterns, rest elements, and other constructs that may appear within an
  //   object or array destructuring pattern.
  //
  //   As a special case, function parameters also use checkLValInnerPattern(),
  //   as they also support defaults and rest constructs.
  //
  // These functions deliberately support both assignment and binding constructs,
  // as the logic for both is exceedingly similar. If the node is the target of
  // an assignment, then bindingType should be set to BIND_NONE. Otherwise, it
  // should be set to the appropriate BIND_* constant, like BIND_VAR or
  // BIND_LEXICAL.
  //
  // If the function is called with a non-BIND_NONE bindingType, then
  // additionally a checkClashes object may be specified to allow checking for
  // duplicate argument names. checkClashes is ignored if the provided construct
  // is an assignment (i.e., bindingType is BIND_NONE).

  checkLValSimple(expr, bindingType = BIND_NONE, checkClashes) {
    const isBind = bindingType !== BIND_NONE;

    switch (expr.type) {
      case "Identifier":
        if (this.strict && this.reservedWordsStrictBind.test(expr.name))
          this.raiseRecoverable(
            expr.start,
            (isBind ? "Binding " : "Assigning to ") +
              expr.name +
              " in strict mode"
          );
        if (isBind) {
          if (bindingType === BIND_LEXICAL && expr.name === "let")
            this.raiseRecoverable(
              expr.start,
              "let is disallowed as a lexically bound name"
            );
          if (checkClashes) {
            if (has(checkClashes, expr.name))
              this.raiseRecoverable(expr.start, "Argument name clash");
            checkClashes[expr.name] = true;
          }
          if (bindingType !== BIND_OUTSIDE)
            this.declareName(expr.name, bindingType, expr.start);
        }
        break;

      case "ChainExpression":
        this.raiseRecoverable(
          expr.start,
          "Optional chaining cannot appear in left-hand side"
        );
        break;

      case "MemberExpression":
        if (isBind)
          this.raiseRecoverable(expr.start, "Binding member expression");
        break;

      case "ParenthesizedExpression":
        if (isBind)
          this.raiseRecoverable(expr.start, "Binding parenthesized expression");
        return this.checkLValSimple(expr.expression, bindingType, checkClashes);

      default:
        this.raise(
          expr.start,
          (isBind ? "Binding" : "Assigning to") + " rvalue"
        );
    }
  }

  checkLValPattern(expr, bindingType = BIND_NONE, checkClashes) {
    switch (expr.type) {
      case "ObjectPattern":
        for (let prop of expr.properties) {
          this.checkLValInnerPattern(prop, bindingType, checkClashes);
        }
        break;

      case "ArrayPattern":
        for (let elem of expr.elements) {
          if (elem) this.checkLValInnerPattern(elem, bindingType, checkClashes);
        }
        break;

      default:
        this.checkLValSimple(expr, bindingType, checkClashes);
    }
  }

  checkLValInnerPattern(expr, bindingType = BIND_NONE, checkClashes) {
    switch (expr.type) {
      case "Property":
        // AssignmentProperty has type === "Property"
        this.checkLValInnerPattern(expr.value, bindingType, checkClashes);
        break;

      case "AssignmentPattern":
        this.checkLValPattern(expr.left, bindingType, checkClashes);
        break;

      case "RestElement":
        this.checkLValPattern(expr.argument, bindingType, checkClashes);
        break;

      default:
        this.checkLValPattern(expr, bindingType, checkClashes);
    }
  }

  strictDirective(start) {
    for (;;) {
      // Try to find string literal.
      skipWhiteSpace.lastIndex = start;
      start += skipWhiteSpace.exec(this.input)[0].length;
      let match = literal.exec(this.input.slice(start));
      if (!match) return false;
      if ((match[1] || match[2]) === "use strict") {
        skipWhiteSpace.lastIndex = start + match[0].length;
        let spaceAfter = skipWhiteSpace.exec(this.input),
          end = spaceAfter.index + spaceAfter[0].length;
        let next = this.input.charAt(end);
        return (
          next === ";" ||
          next === "}" ||
          (lineBreak.test(spaceAfter[0]) &&
            !(
              /[(`.[+\-/*%<>=,?^&]/.test(next) ||
              (next === "!" && this.input.charAt(end + 1) === "=")
            ))
        );
      }
      start += match[0].length;

      // Skip semicolon, if any.
      skipWhiteSpace.lastIndex = start;
      start += skipWhiteSpace.exec(this.input)[0].length;
      if (this.input[start] === ";") start++;
    }
  }

  // Predicate that tests whether the next token is of the given
  // type, and if yes, consumes it as a side effect.

  eat(type) {
    if (this.type === type) {
      this.next();
      return true;
    } else {
      return false;
    }
  }

  // Tests whether parsed token is a contextual keyword.

  isContextual(name) {
    return this.type === tt.name && this.value === name && !this.containsEsc;
  }

  // Consumes contextual keyword if possible.

  eatContextual(name) {
    if (!this.isContextual(name)) return false;
    this.next();
    return true;
  }

  // Asserts that following token is given contextual keyword.

  expectContextual(name) {
    if (!this.eatContextual(name)) this.unexpected();
  }

  // Test whether a semicolon can be inserted at the current position.

  canInsertSemicolon() {
    return (
      this.type === tt.eof ||
      this.type === tt.braceR ||
      lineBreak.test(this.input.slice(this.lastTokEnd, this.start))
    );
  }

  insertSemicolon() {
    if (this.canInsertSemicolon()) {
      if (this.options.onInsertedSemicolon)
        this.options.onInsertedSemicolon(this.lastTokEnd, this.lastTokEndLoc);
      return true;
    }
  }

  // Consume a semicolon, or, failing that, see if we are allowed to
  // pretend that there is a semicolon at this position.

  semicolon() {
    if (!this.eat(tt.semi) && !this.insertSemicolon()) this.unexpected();
  }

  afterTrailingComma(tokType, notNext) {
    if (this.type === tokType) {
      if (this.options.onTrailingComma)
        this.options.onTrailingComma(this.lastTokStart, this.lastTokStartLoc);
      if (!notNext) this.next();
      return true;
    }
  }

  // Expect a token of a given type. If found, consume it, otherwise,
  // raise an unexpected token error.

  expect(type) {
    this.eat(type) || this.unexpected();
  }

  // Raise an unexpected token error.

  unexpected(pos) {
    this.raise(pos != null ? pos : this.start, "Unexpected token");
  }

  checkPatternErrors(refDestructuringErrors, isAssign) {
    if (!refDestructuringErrors) return;
    if (refDestructuringErrors.trailingComma > -1)
      this.raiseRecoverable(
        refDestructuringErrors.trailingComma,
        "Comma is not permitted after the rest element"
      );
    let parens = isAssign
      ? refDestructuringErrors.parenthesizedAssign
      : refDestructuringErrors.parenthesizedBind;
    if (parens > -1) this.raiseRecoverable(parens, "Parenthesized pattern");
  }

  checkExpressionErrors(refDestructuringErrors, andThrow) {
    if (!refDestructuringErrors) return false;
    let { shorthandAssign, doubleProto } = refDestructuringErrors;
    if (!andThrow) return shorthandAssign >= 0 || doubleProto >= 0;
    if (shorthandAssign >= 0)
      this.raise(
        shorthandAssign,
        "Shorthand property assignments are valid only in destructuring patterns"
      );
    if (doubleProto >= 0)
      this.raiseRecoverable(doubleProto, "Redefinition of __proto__ property");
  }

  checkYieldAwaitInDefaultParams() {
    if (this.yieldPos && (!this.awaitPos || this.yieldPos < this.awaitPos))
      this.raise(this.yieldPos, "Yield expression cannot be a default value");
    if (this.awaitPos)
      this.raise(this.awaitPos, "Await expression cannot be a default value");
  }

  isSimpleAssignTarget(expr) {
    if (expr.type === "ParenthesizedExpression")
      return this.isSimpleAssignTarget(expr.expression);
    return expr.type === "Identifier" || expr.type === "MemberExpression";
  }

  // Parse a program. Initializes the parser, reads any number of
  // statements, and wraps them in a Program node.  Optionally takes a
  // `program` argument.  If present, the statements will be appended
  // to its body instead of creating a new node.

  parseTopLevel(node) {
    let exports = Object.create(null);
    if (!node.body) node.body = [];
    while (this.type !== tt.eof) {
      let stmt = this.parseStatement(null, true, exports);
      node.body.push(stmt);
    }
    if (this.inModule)
      for (let name of Object.keys(this.undefinedExports))
        this.raiseRecoverable(
          this.undefinedExports[name].start,
          `Export '${name}' is not defined`
        );
    this.adaptDirectivePrologue(node.body);
    this.next();
    node.sourceType = this.options.sourceType;
    return this.finishNode(node, "Program");
  }

  isLet(context) {
    if (this.options.ecmaVersion < 6 || !this.isContextual("let")) return false;
    skipWhiteSpace.lastIndex = this.pos;
    let skip = skipWhiteSpace.exec(this.input);
    let next = this.pos + skip[0].length,
      nextCh = this.input.charCodeAt(next);
    // For ambiguous cases, determine if a LexicalDeclaration (or only a
    // Statement) is allowed here. If context is not empty then only a Statement
    // is allowed. However, `let [` is an explicit negative lookahead for
    // ExpressionStatement, so special-case it first.
    if (nextCh === 91) return true; // '['
    if (context) return false;

    if (nextCh === 123) return true; // '{'
    if (isIdentifierStart(nextCh, true)) {
      let pos = next + 1;
      while (isIdentifierChar(this.input.charCodeAt(pos), true)) ++pos;
      let ident = this.input.slice(next, pos);
      if (!keywordRelationalOperator.test(ident)) return true;
    }
    return false;
  }

  // check 'async [no LineTerminator here] function'
  // - 'async /*foo*/ function' is OK.
  // - 'async /*\n*/ function' is invalid.
  isAsyncFunction() {
    if (this.options.ecmaVersion < 8 || !this.isContextual("async"))
      return false;

    skipWhiteSpace.lastIndex = this.pos;
    let skip = skipWhiteSpace.exec(this.input);
    let next = this.pos + skip[0].length;
    return (
      !lineBreak.test(this.input.slice(this.pos, next)) &&
      this.input.slice(next, next + 8) === "function" &&
      (next + 8 === this.input.length ||
        !isIdentifierChar(this.input.charAt(next + 8)))
    );
  }

  // Parse a single statement.
  //
  // If expecting a statement and finding a slash operator, parse a
  // regular expression literal. This is to handle cases like
  // `if (foo) /blah/.exec(foo)`, where looking at the previous token
  // does not help.

  parseStatement(context, topLevel, exports) {
    let starttype = this.type,
      node = this.startNode(),
      kind;

    if (this.isLet(context)) {
      starttype = tt._var;
      kind = "let";
    }

    // Most types of statements are recognized by the keyword they
    // start with. Many are trivial to parse, some require a bit of
    // complexity.

    switch (starttype) {
      case tt._break:
      case tt._continue:
        return this.parseBreakContinueStatement(node, starttype.keyword);
      case tt._debugger:
        return this.parseDebuggerStatement(node);
      case tt._do:
        return this.parseDoStatement(node);
      case tt._for:
        return this.parseForStatement(node);
      case tt._function:
        // Function as sole body of either an if statement or a labeled statement
        // works, but not when it is part of a labeled statement that is the sole
        // body of an if statement.
        if (
          context &&
          (this.strict || (context !== "if" && context !== "label")) &&
          this.options.ecmaVersion >= 6
        )
          this.unexpected();
        return this.parseFunctionStatement(node, false, !context);
      case tt._class:
        if (context) this.unexpected();
        return this.parseClass(node, true);
      case tt._if:
        return this.parseIfStatement(node);
      case tt._return:
        return this.parseReturnStatement(node);
      case tt._switch:
        return this.parseSwitchStatement(node);
      case tt._throw:
        return this.parseThrowStatement(node);
      case tt._try:
        return this.parseTryStatement(node);
      case tt._const:
      case tt._var:
        kind = kind || this.value;
        if (context && kind !== "var") this.unexpected();
        return this.parseVarStatement(node, kind);
      case tt._while:
        return this.parseWhileStatement(node);
      case tt._with:
        return this.parseWithStatement(node);
      case tt.braceL:
        return this.parseBlock(true, node);
      case tt.semi:
        return this.parseEmptyStatement(node);
      case tt._export:
      case tt._import:
        if (this.options.ecmaVersion > 10 && starttype === tt._import) {
          skipWhiteSpace.lastIndex = this.pos;
          let skip = skipWhiteSpace.exec(this.input);
          let next = this.pos + skip[0].length,
            nextCh = this.input.charCodeAt(next);
          if (nextCh === 40 || nextCh === 46)
            // '(' or '.'
            return this.parseExpressionStatement(node, this.parseExpression());
        }

        if (!this.options.allowImportExportEverywhere) {
          if (!topLevel)
            this.raise(
              this.start,
              "'import' and 'export' may only appear at the top level"
            );
          if (!this.inModule)
            this.raise(
              this.start,
              "'import' and 'export' may appear only with 'sourceType: module'"
            );
        }
        return starttype === tt._import
          ? this.parseImport(node)
          : this.parseExport(node, exports);

      // If the statement does not start with a statement keyword or a
      // brace, it's an ExpressionStatement or LabeledStatement. We
      // simply start parsing an expression, and afterwards, if the
      // next token is a colon and the expression was a simple
      // Identifier node, we switch to interpreting it as a label.
      default:
        if (this.isAsyncFunction()) {
          if (context) this.unexpected();
          this.next();
          return this.parseFunctionStatement(node, true, !context);
        }

        let maybeName = this.value,
          expr = this.parseExpression();
        if (
          starttype === tt.name &&
          expr.type === "Identifier" &&
          this.eat(tt.colon)
        )
          return this.parseLabeledStatement(node, maybeName, expr, context);
        else return this.parseExpressionStatement(node, expr);
    }
  }

  parseBreakContinueStatement(node, keyword) {
    let isBreak = keyword === "break";
    this.next();
    if (this.eat(tt.semi) || this.insertSemicolon()) node.label = null;
    else if (this.type !== tt.name) this.unexpected();
    else {
      node.label = this.parseIdent();
      this.semicolon();
    }

    // Verify that there is an actual destination to break or
    // continue to.
    let i = 0;
    for (; i < this.labels.length; ++i) {
      let lab = this.labels[i];
      if (node.label == null || lab.name === node.label.name) {
        if (lab.kind != null && (isBreak || lab.kind === "loop")) break;
        if (node.label && isBreak) break;
      }
    }
    if (i === this.labels.length)
      this.raise(node.start, "Unsyntactic " + keyword);
    return this.finishNode(
      node,
      isBreak ? "BreakStatement" : "ContinueStatement"
    );
  }

  parseDebuggerStatement(node) {
    this.next();
    this.semicolon();
    return this.finishNode(node, "DebuggerStatement");
  }

  parseDoStatement(node) {
    this.next();
    this.labels.push(loopLabel);
    node.body = this.parseStatement("do");
    this.labels.pop();
    this.expect(tt._while);
    node.test = this.parseParenExpression();
    if (this.options.ecmaVersion >= 6) this.eat(tt.semi);
    else this.semicolon();
    return this.finishNode(node, "DoWhileStatement");
  }

  // Disambiguating between a `for` and a `for`/`in` or `for`/`of`
  // loop is non-trivial. Basically, we have to parse the init `var`
  // statement or expression, disallowing the `in` operator (see
  // the second parameter to `parseExpression`), and then check
  // whether the next token is `in` or `of`. When there is no init
  // part (semicolon immediately after the opening parenthesis), it
  // is a regular `for` loop.

  parseForStatement(node) {
    this.next();
    let awaitAt =
      this.options.ecmaVersion >= 9 &&
      (this.inAsync ||
        (!this.inFunction && this.options.allowAwaitOutsideFunction)) &&
      this.eatContextual("await")
        ? this.lastTokStart
        : -1;
    this.labels.push(loopLabel);
    this.enterScope(0);
    this.expect(tt.parenL);
    if (this.type === tt.semi) {
      if (awaitAt > -1) this.unexpected(awaitAt);
      return this.parseFor(node, null);
    }
    let isLet = this.isLet();
    if (this.type === tt._var || this.type === tt._const || isLet) {
      let init = this.startNode(),
        kind = isLet ? "let" : this.value;
      this.next();
      this.parseVar(init, true, kind);
      this.finishNode(init, "VariableDeclaration");
      if (
        (this.type === tt._in ||
          (this.options.ecmaVersion >= 6 && this.isContextual("of"))) &&
        init.declarations.length === 1
      ) {
        if (this.options.ecmaVersion >= 9) {
          if (this.type === tt._in) {
            if (awaitAt > -1) this.unexpected(awaitAt);
          } else node.await = awaitAt > -1;
        }
        return this.parseForIn(node, init);
      }
      if (awaitAt > -1) this.unexpected(awaitAt);
      return this.parseFor(node, init);
    }
    let refDestructuringErrors = new DestructuringErrors();
    let init = this.parseExpression(true, refDestructuringErrors);
    if (
      this.type === tt._in ||
      (this.options.ecmaVersion >= 6 && this.isContextual("of"))
    ) {
      if (this.options.ecmaVersion >= 9) {
        if (this.type === tt._in) {
          if (awaitAt > -1) this.unexpected(awaitAt);
        } else node.await = awaitAt > -1;
      }
      this.toAssignable(init, false, refDestructuringErrors);
      this.checkLValPattern(init);
      return this.parseForIn(node, init);
    } else {
      this.checkExpressionErrors(refDestructuringErrors, true);
    }
    if (awaitAt > -1) this.unexpected(awaitAt);
    return this.parseFor(node, init);
  }

  parseFunctionStatement(node, isAsync, declarationPosition) {
    this.next();
    return this.parseFunction(
      node,
      FUNC_STATEMENT | (declarationPosition ? 0 : FUNC_HANGING_STATEMENT),
      false,
      isAsync
    );
  }

  parseIfStatement(node) {
    this.next();
    node.test = this.parseParenExpression();
    // allow function declarations in branches, but only in non-strict mode
    node.consequent = this.parseStatement("if");
    node.alternate = this.eat(tt._else) ? this.parseStatement("if") : null;
    return this.finishNode(node, "IfStatement");
  }

  parseReturnStatement(node) {
    if (!this.inFunction && !this.options.allowReturnOutsideFunction)
      this.raise(this.start, "'return' outside of function");
    this.next();

    // In `return` (and `break`/`continue`), the keywords with
    // optional arguments, we eagerly look for a semicolon or the
    // possibility to insert one.

    if (this.eat(tt.semi) || this.insertSemicolon()) node.argument = null;
    else {
      node.argument = this.parseExpression();
      this.semicolon();
    }
    return this.finishNode(node, "ReturnStatement");
  }

  parseSwitchStatement(node) {
    this.next();
    node.discriminant = this.parseParenExpression();
    node.cases = [];
    this.expect(tt.braceL);
    this.labels.push(switchLabel);
    this.enterScope(0);

    // Statements under must be grouped (by label) in SwitchCase
    // nodes. `cur` is used to keep the node that we are currently
    // adding statements to.

    let cur;
    for (let sawDefault = false; this.type !== tt.braceR; ) {
      if (this.type === tt._case || this.type === tt._default) {
        let isCase = this.type === tt._case;
        if (cur) this.finishNode(cur, "SwitchCase");
        node.cases.push((cur = this.startNode()));
        cur.consequent = [];
        this.next();
        if (isCase) {
          cur.test = this.parseExpression();
        } else {
          if (sawDefault)
            this.raiseRecoverable(
              this.lastTokStart,
              "Multiple default clauses"
            );
          sawDefault = true;
          cur.test = null;
        }
        this.expect(tt.colon);
      } else {
        if (!cur) this.unexpected();
        cur.consequent.push(this.parseStatement(null));
      }
    }
    this.exitScope();
    if (cur) this.finishNode(cur, "SwitchCase");
    this.next(); // Closing brace
    this.labels.pop();
    return this.finishNode(node, "SwitchStatement");
  }

  parseThrowStatement(node) {
    this.next();
    if (lineBreak.test(this.input.slice(this.lastTokEnd, this.start)))
      this.raise(this.lastTokEnd, "Illegal newline after throw");
    node.argument = this.parseExpression();
    this.semicolon();
    return this.finishNode(node, "ThrowStatement");
  }

  parseTryStatement(node) {
    this.next();
    node.block = this.parseBlock();
    node.handler = null;
    if (this.type === tt._catch) {
      let clause = this.startNode();
      this.next();
      if (this.eat(tt.parenL)) {
        clause.param = this.parseBindingAtom();
        let simple = clause.param.type === "Identifier";
        this.enterScope(simple ? SCOPE_SIMPLE_CATCH : 0);
        this.checkLValPattern(
          clause.param,
          simple ? BIND_SIMPLE_CATCH : BIND_LEXICAL
        );
        this.expect(tt.parenR);
      } else {
        if (this.options.ecmaVersion < 10) this.unexpected();
        clause.param = null;
        this.enterScope(0);
      }
      clause.body = this.parseBlock(false);
      this.exitScope();
      node.handler = this.finishNode(clause, "CatchClause");
    }
    node.finalizer = this.eat(tt._finally) ? this.parseBlock() : null;
    if (!node.handler && !node.finalizer)
      this.raise(node.start, "Missing catch or finally clause");
    return this.finishNode(node, "TryStatement");
  }

  parseVarStatement(node, kind) {
    this.next();
    this.parseVar(node, false, kind);
    this.semicolon();
    return this.finishNode(node, "VariableDeclaration");
  }

  parseWhileStatement(node) {
    this.next();
    node.test = this.parseParenExpression();
    this.labels.push(loopLabel);
    node.body = this.parseStatement("while");
    this.labels.pop();
    return this.finishNode(node, "WhileStatement");
  }

  parseWithStatement(node) {
    if (this.strict) this.raise(this.start, "'with' in strict mode");
    this.next();
    node.object = this.parseParenExpression();
    node.body = this.parseStatement("with");
    return this.finishNode(node, "WithStatement");
  }

  parseEmptyStatement(node) {
    this.next();
    return this.finishNode(node, "EmptyStatement");
  }

  parseLabeledStatement(node, maybeName, expr, context) {
    for (let label of this.labels)
      if (label.name === maybeName)
        this.raise(expr.start, "Label '" + maybeName + "' is already declared");
    let kind = this.type.isLoop
      ? "loop"
      : this.type === tt._switch
      ? "switch"
      : null;
    for (let i = this.labels.length - 1; i >= 0; i--) {
      let label = this.labels[i];
      if (label.statementStart === node.start) {
        // Update information about previous labels on this node
        label.statementStart = this.start;
        label.kind = kind;
      } else break;
    }
    this.labels.push({ name: maybeName, kind, statementStart: this.start });
    node.body = this.parseStatement(
      context
        ? context.indexOf("label") === -1
          ? context + "label"
          : context
        : "label"
    );
    this.labels.pop();
    node.label = expr;
    return this.finishNode(node, "LabeledStatement");
  }

  parseExpressionStatement(node, expr) {
    node.expression = expr;
    this.semicolon();
    return this.finishNode(node, "ExpressionStatement");
  }

  // Parse a semicolon-enclosed block of statements, handling `"use
  // strict"` declarations when `allowStrict` is true (used for
  // function bodies).

  parseBlock(
    createNewLexicalScope = true,
    node = this.startNode(),
    exitStrict
  ) {
    node.body = [];
    this.expect(tt.braceL);
    if (createNewLexicalScope) this.enterScope(0);
    while (this.type !== tt.braceR) {
      let stmt = this.parseStatement(null);
      node.body.push(stmt);
    }
    if (exitStrict) this.strict = false;
    this.next();
    if (createNewLexicalScope) this.exitScope();
    return this.finishNode(node, "BlockStatement");
  }

  // Parse a regular `for` loop. The disambiguation code in
  // `parseStatement` will already have parsed the init statement or
  // expression.

  parseFor(node, init) {
    node.init = init;
    this.expect(tt.semi);
    node.test = this.type === tt.semi ? null : this.parseExpression();
    this.expect(tt.semi);
    node.update = this.type === tt.parenR ? null : this.parseExpression();
    this.expect(tt.parenR);
    node.body = this.parseStatement("for");
    this.exitScope();
    this.labels.pop();
    return this.finishNode(node, "ForStatement");
  }

  // Parse a `for`/`in` and `for`/`of` loop, which are almost
  // same from parser's perspective.

  parseForIn(node, init) {
    const isForIn = this.type === tt._in;
    this.next();

    if (
      init.type === "VariableDeclaration" &&
      init.declarations[0].init != null &&
      (!isForIn ||
        this.options.ecmaVersion < 8 ||
        this.strict ||
        init.kind !== "var" ||
        init.declarations[0].id.type !== "Identifier")
    ) {
      this.raise(
        init.start,
        `${
          isForIn ? "for-in" : "for-of"
        } loop variable declaration may not have an initializer`
      );
    }
    node.left = init;
    node.right = isForIn ? this.parseExpression() : this.parseMaybeAssign();
    this.expect(tt.parenR);
    node.body = this.parseStatement("for");
    this.exitScope();
    this.labels.pop();
    return this.finishNode(node, isForIn ? "ForInStatement" : "ForOfStatement");
  }

  // Parse a list of variable declarations.

  parseVar(node, isFor, kind) {
    node.declarations = [];
    node.kind = kind;
    for (;;) {
      let decl = this.startNode();
      this.parseVarId(decl, kind);
      if (this.eat(tt.eq)) {
        decl.init = this.parseMaybeAssign(isFor);
      } else if (
        kind === "const" &&
        !(
          this.type === tt._in ||
          (this.options.ecmaVersion >= 6 && this.isContextual("of"))
        )
      ) {
        this.unexpected();
      } else if (
        decl.id.type !== "Identifier" &&
        !(isFor && (this.type === tt._in || this.isContextual("of")))
      ) {
        this.raise(
          this.lastTokEnd,
          "Complex binding patterns require an initialization value"
        );
      } else {
        decl.init = null;
      }
      node.declarations.push(this.finishNode(decl, "VariableDeclarator"));
      if (!this.eat(tt.comma)) break;
    }
    return node;
  }

  parseVarId(decl, kind) {
    decl.id = this.parseBindingAtom();
    this.checkLValPattern(
      decl.id,
      kind === "var" ? BIND_VAR : BIND_LEXICAL,
      false
    );
  }

  // Parse a function declaration or literal (depending on the
  // `statement & FUNC_STATEMENT`).

  // Remove `allowExpressionBody` for 7.0.0, as it is only called with false
  parseFunction(node, statement, allowExpressionBody, isAsync) {
    this.initFunction(node);
    if (
      this.options.ecmaVersion >= 9 ||
      (this.options.ecmaVersion >= 6 && !isAsync)
    ) {
      if (this.type === tt.star && statement & FUNC_HANGING_STATEMENT)
        this.unexpected();
      node.generator = this.eat(tt.star);
    }
    if (this.options.ecmaVersion >= 8) node.async = !!isAsync;

    if (statement & FUNC_STATEMENT) {
      node.id =
        statement & FUNC_NULLABLE_ID && this.type !== tt.name
          ? null
          : this.parseIdent();
      if (node.id && !(statement & FUNC_HANGING_STATEMENT))
        // If it is a regular function declaration in sloppy mode, then it is
        // subject to Annex B semantics (BIND_FUNCTION). Otherwise, the binding
        // mode depends on properties of the current scope (see
        // treatFunctionsAsVar).
        this.checkLValSimple(
          node.id,
          this.strict || node.generator || node.async
            ? this.treatFunctionsAsVar
              ? BIND_VAR
              : BIND_LEXICAL
            : BIND_FUNCTION
        );
    }

    let oldYieldPos = this.yieldPos,
      oldAwaitPos = this.awaitPos,
      oldAwaitIdentPos = this.awaitIdentPos;
    this.yieldPos = 0;
    this.awaitPos = 0;
    this.awaitIdentPos = 0;
    this.enterScope(functionFlags(node.async, node.generator));

    if (!(statement & FUNC_STATEMENT))
      node.id = this.type === tt.name ? this.parseIdent() : null;

    this.parseFunctionParams(node);
    this.parseFunctionBody(node, allowExpressionBody, false);

    this.yieldPos = oldYieldPos;
    this.awaitPos = oldAwaitPos;
    this.awaitIdentPos = oldAwaitIdentPos;
    return this.finishNode(
      node,
      statement & FUNC_STATEMENT ? "FunctionDeclaration" : "FunctionExpression"
    );
  }

  parseFunctionParams(node) {
    this.expect(tt.parenL);
    node.params = this.parseBindingList(
      tt.parenR,
      false,
      this.options.ecmaVersion >= 8
    );
    this.checkYieldAwaitInDefaultParams();
  }

  // Parse a class declaration or literal (depending on the
  // `isStatement` parameter).

  parseClass(node, isStatement) {
    this.next();

    // ecma-262 14.6 Class Definitions
    // A class definition is always strict mode code.
    const oldStrict = this.strict;
    this.strict = true;

    this.parseClassId(node, isStatement);
    this.parseClassSuper(node);
    let classBody = this.startNode();
    let hadConstructor = false;
    classBody.body = [];
    this.expect(tt.braceL);
    while (this.type !== tt.braceR) {
      const element = this.parseClassElement(node.superClass !== null);
      if (element) {
        classBody.body.push(element);
        if (
          element.type === "MethodDefinition" &&
          element.kind === "constructor"
        ) {
          if (hadConstructor)
            this.raise(
              element.start,
              "Duplicate constructor in the same class"
            );
          hadConstructor = true;
        }
      }
    }
    this.strict = oldStrict;
    this.next();
    node.body = this.finishNode(classBody, "ClassBody");
    return this.finishNode(
      node,
      isStatement ? "ClassDeclaration" : "ClassExpression"
    );
  }

  parseClassElement(constructorAllowsSuper) {
    if (this.eat(tt.semi)) return null;

    let method = this.startNode();
    const tryContextual = (k, noLineBreak = false) => {
      const start = this.start,
        startLoc = this.startLoc;
      if (!this.eatContextual(k)) return false;
      if (
        this.type !== tt.parenL &&
        (!noLineBreak || !this.canInsertSemicolon())
      )
        return true;
      if (method.key) this.unexpected();
      method.computed = false;
      method.key = this.startNodeAt(start, startLoc);
      method.key.name = k;
      this.finishNode(method.key, "Identifier");
      return false;
    };

    method.kind = "method";
    method.static = tryContextual("static");
    let isGenerator = this.eat(tt.star);
    let isAsync = false;
    if (!isGenerator) {
      if (this.options.ecmaVersion >= 8 && tryContextual("async", true)) {
        isAsync = true;
        isGenerator = this.options.ecmaVersion >= 9 && this.eat(tt.star);
      } else if (tryContextual("get")) {
        method.kind = "get";
      } else if (tryContextual("set")) {
        method.kind = "set";
      }
    }
    if (!method.key) this.parsePropertyName(method);
    let { key } = method;
    let allowsDirectSuper = false;
    if (
      !method.computed &&
      !method.static &&
      ((key.type === "Identifier" && key.name === "constructor") ||
        (key.type === "Literal" && key.value === "constructor"))
    ) {
      if (method.kind !== "method")
        this.raise(key.start, "Constructor can't have get/set modifier");
      if (isGenerator)
        this.raise(key.start, "Constructor can't be a generator");
      if (isAsync)
        this.raise(key.start, "Constructor can't be an async method");
      method.kind = "constructor";
      allowsDirectSuper = constructorAllowsSuper;
    } else if (
      method.static &&
      key.type === "Identifier" &&
      key.name === "prototype"
    ) {
      this.raise(
        key.start,
        "Classes may not have a static property named prototype"
      );
    }
    this.parseClassMethod(method, isGenerator, isAsync, allowsDirectSuper);
    if (method.kind === "get" && method.value.params.length !== 0)
      this.raiseRecoverable(method.value.start, "getter should have no params");
    if (method.kind === "set" && method.value.params.length !== 1)
      this.raiseRecoverable(
        method.value.start,
        "setter should have exactly one param"
      );
    if (method.kind === "set" && method.value.params[0].type === "RestElement")
      this.raiseRecoverable(
        method.value.params[0].start,
        "Setter cannot use rest params"
      );
    return method;
  }

  parseClassMethod(method, isGenerator, isAsync, allowsDirectSuper) {
    method.value = this.parseMethod(isGenerator, isAsync, allowsDirectSuper);
    return this.finishNode(method, "MethodDefinition");
  }

  parseClassId(node, isStatement) {
    if (this.type === tt.name) {
      node.id = this.parseIdent();
      if (isStatement) this.checkLValSimple(node.id, BIND_LEXICAL, false);
    } else {
      if (isStatement === true) this.unexpected();
      node.id = null;
    }
  }

  parseClassSuper(node) {
    node.superClass = this.eat(tt._extends) ? this.parseExprSubscripts() : null;
  }

  // Parses module export declaration.

  parseExport(node, exports) {
    this.next();
    // export * from '...'
    if (this.eat(tt.star)) {
      if (this.options.ecmaVersion >= 11) {
        if (this.eatContextual("as")) {
          node.exported = this.parseIdent(true);
          this.checkExport(exports, node.exported.name, this.lastTokStart);
        } else {
          node.exported = null;
        }
      }
      this.expectContextual("from");
      if (this.type !== tt.string) this.unexpected();
      node.source = this.parseExprAtom();
      this.semicolon();
      return this.finishNode(node, "ExportAllDeclaration");
    }
    if (this.eat(tt._default)) {
      // export default ...
      this.checkExport(exports, "default", this.lastTokStart);
      let isAsync;
      if (this.type === tt._function || (isAsync = this.isAsyncFunction())) {
        let fNode = this.startNode();
        this.next();
        if (isAsync) this.next();
        node.declaration = this.parseFunction(
          fNode,
          FUNC_STATEMENT | FUNC_NULLABLE_ID,
          false,
          isAsync
        );
      } else if (this.type === tt._class) {
        let cNode = this.startNode();
        node.declaration = this.parseClass(cNode, "nullableID");
      } else {
        node.declaration = this.parseMaybeAssign();
        this.semicolon();
      }
      return this.finishNode(node, "ExportDefaultDeclaration");
    }
    // export var|const|let|function|class ...
    if (this.shouldParseExportStatement()) {
      node.declaration = this.parseStatement(null);
      if (node.declaration.type === "VariableDeclaration")
        this.checkVariableExport(exports, node.declaration.declarations);
      else
        this.checkExport(
          exports,
          node.declaration.id.name,
          node.declaration.id.start
        );
      node.specifiers = [];
      node.source = null;
    } else {
      // export { x, y as z } [from '...']
      node.declaration = null;
      node.specifiers = this.parseExportSpecifiers(exports);
      if (this.eatContextual("from")) {
        if (this.type !== tt.string) this.unexpected();
        node.source = this.parseExprAtom();
      } else {
        for (let spec of node.specifiers) {
          // check for keywords used as local names
          this.checkUnreserved(spec.local);
          // check if export is defined
          this.checkLocalExport(spec.local);
        }

        node.source = null;
      }
      this.semicolon();
    }
    return this.finishNode(node, "ExportNamedDeclaration");
  }

  checkExport(exports, name, pos) {
    if (!exports) return;
    if (has(exports, name))
      this.raiseRecoverable(pos, "Duplicate export '" + name + "'");
    exports[name] = true;
  }

  checkPatternExport(exports, pat) {
    let type = pat.type;
    if (type === "Identifier") this.checkExport(exports, pat.name, pat.start);
    else if (type === "ObjectPattern")
      for (let prop of pat.properties) this.checkPatternExport(exports, prop);
    else if (type === "ArrayPattern")
      for (let elt of pat.elements) {
        if (elt) this.checkPatternExport(exports, elt);
      }
    else if (type === "Property") this.checkPatternExport(exports, pat.value);
    else if (type === "AssignmentPattern")
      this.checkPatternExport(exports, pat.left);
    else if (type === "RestElement")
      this.checkPatternExport(exports, pat.argument);
    else if (type === "ParenthesizedExpression")
      this.checkPatternExport(exports, pat.expression);
  }

  checkVariableExport(exports, decls) {
    if (!exports) return;
    for (let decl of decls) this.checkPatternExport(exports, decl.id);
  }

  shouldParseExportStatement() {
    return (
      this.type.keyword === "var" ||
      this.type.keyword === "const" ||
      this.type.keyword === "class" ||
      this.type.keyword === "function" ||
      this.isLet() ||
      this.isAsyncFunction()
    );
  }

  // Parses a comma-separated list of module exports.

  parseExportSpecifiers(exports) {
    let nodes = [],
      first = true;
    // export { x, y as z } [from '...']
    this.expect(tt.braceL);
    while (!this.eat(tt.braceR)) {
      if (!first) {
        this.expect(tt.comma);
        if (this.afterTrailingComma(tt.braceR)) break;
      } else first = false;

      let node = this.startNode();
      node.local = this.parseIdent(true);
      node.exported = this.eatContextual("as")
        ? this.parseIdent(true)
        : node.local;
      this.checkExport(exports, node.exported.name, node.exported.start);
      nodes.push(this.finishNode(node, "ExportSpecifier"));
    }
    return nodes;
  }

  // Parses import declaration.

  parseImport(node) {
    this.next();
    // import '...'
    if (this.type === tt.string) {
      node.specifiers = emptyStmt;
      node.source = this.parseExprAtom();
    } else {
      node.specifiers = this.parseImportSpecifiers();
      this.expectContextual("from");
      node.source =
        this.type === tt.string ? this.parseExprAtom() : this.unexpected();
    }
    this.semicolon();
    return this.finishNode(node, "ImportDeclaration");
  }

  // Parses a comma-separated list of module imports.

  parseImportSpecifiers() {
    let nodes = [],
      first = true;
    if (this.type === tt.name) {
      // import defaultObj, { x, y as z } from '...'
      let node = this.startNode();
      node.local = this.parseIdent();
      this.checkLValSimple(node.local, BIND_LEXICAL);
      nodes.push(this.finishNode(node, "ImportDefaultSpecifier"));
      if (!this.eat(tt.comma)) return nodes;
    }
    if (this.type === tt.star) {
      let node = this.startNode();
      this.next();
      this.expectContextual("as");
      node.local = this.parseIdent();
      this.checkLValSimple(node.local, BIND_LEXICAL);
      nodes.push(this.finishNode(node, "ImportNamespaceSpecifier"));
      return nodes;
    }
    this.expect(tt.braceL);
    while (!this.eat(tt.braceR)) {
      if (!first) {
        this.expect(tt.comma);
        if (this.afterTrailingComma(tt.braceR)) break;
      } else first = false;

      let node = this.startNode();
      node.imported = this.parseIdent(true);
      if (this.eatContextual("as")) {
        node.local = this.parseIdent();
      } else {
        this.checkUnreserved(node.imported);
        node.local = node.imported;
      }
      this.checkLValSimple(node.local, BIND_LEXICAL);
      nodes.push(this.finishNode(node, "ImportSpecifier"));
    }
    return nodes;
  }

  // Set `ExpressionStatement#directive` property for directive prologues.
  adaptDirectivePrologue(statements) {
    for (
      let i = 0;
      i < statements.length && this.isDirectiveCandidate(statements[i]);
      ++i
    ) {
      statements[i].directive = statements[i].expression.raw.slice(1, -1);
    }
  }
  isDirectiveCandidate(statement) {
    return (
      statement.type === "ExpressionStatement" &&
      statement.expression.type === "Literal" &&
      typeof statement.expression.value === "string" &&
      // Reject parenthesized strings.
      (this.input[statement.start] === '"' ||
        this.input[statement.start] === "'")
    );
  }

  initialContext() {
    return [types.b_stat];
  }

  braceIsBlock(prevType) {
    let parent = this.curContext();
    if (parent === types.f_expr || parent === types.f_stat) return true;
    if (
      prevType === tt.colon &&
      (parent === types.b_stat || parent === types.b_expr)
    )
      return !parent.isExpr;

    // The check for `tt.name && exprAllowed` detects whether we are
    // after a `yield` or `of` construct. See the `updateContext` for
    // `tt.name`.
    if (prevType === tt._return || (prevType === tt.name && this.exprAllowed))
      return lineBreak.test(this.input.slice(this.lastTokEnd, this.start));
    if (
      prevType === tt._else ||
      prevType === tt.semi ||
      prevType === tt.eof ||
      prevType === tt.parenR ||
      prevType === tt.arrow
    )
      return true;
    if (prevType === tt.braceL) return parent === types.b_stat;
    if (prevType === tt._var || prevType === tt._const || prevType === tt.name)
      return false;
    return !this.exprAllowed;
  }

  inGeneratorContext() {
    for (let i = this.context.length - 1; i >= 1; i--) {
      let context = this.context[i];
      if (context.token === "function") return context.generator;
    }
    return false;
  }

  updateContext(prevType) {
    let update,
      type = this.type;
    if (type.keyword && prevType === tt.dot) this.exprAllowed = false;
    else if ((update = type.updateContext)) update.call(this, prevType);
    else this.exprAllowed = type.beforeExpr;
  }

  // If we're in an ES6 environment, make parsers iterable
  [Symbol.iterator]() {
    return {
      next: () => {
        let token = this.getToken();
        return {
          done: token.type === tt.eof,
          value: token,
        };
      },
    };
  }

  static extend(...plugins) {
    let cls = this;
    for (let i = 0; i < plugins.length; i++) cls = plugins[i](cls);
    return cls;
  }

  static parse(input, options) {
    return new this(options, input).parse();
  }

  static parseExpressionAt(input, pos, options) {
    let parser = new this(options, input, pos);
    parser.nextToken();
    return parser.parseExpression();
  }

  static tokenizer(input, options) {
    return new this(options, input);
  }
}
