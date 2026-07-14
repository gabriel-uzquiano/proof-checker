/**
 * Parser for Propositional + Quantificational Logic
 *
 * Vocabulary (following PHIL 220g exactly):
 *
 *   PL sentence letters:  p, q, r, s, t  (with optional numeric subscripts)
 *   QL predicates:        P, Q, R, S, T  (uppercase, followed by terms)
 *   QL constants:         a, b, c, d, e  (lowercase, not in {p,q,r,s,t})
 *   QL variables:         x, y, z        (lowercase)
 *   Connectives:          ¬  ∧  ∨  →
 *   Quantifiers:          ∀  ∃
 *   Parentheses:          (  )
 *
 * PL Grammar (strict parentheses around binary connectives):
 *   formula ::= letter
 *             | ¬ formula
 *             | ( formula ∧ formula )
 *             | ( formula ∨ formula )
 *             | ( formula → formula )
 *
 * QL Grammar adds:
 *   formula ::= ... (all PL forms, with variables/constants in place of letters)
 *             | ∀x formula      (x is a variable)
 *             | ∃x formula
 *             | Px₁x₂…         (predicate applied to one or more terms)
 *
 * Atomic QL formulas: P, Q, R, S, T followed by a sequence of terms.
 *   A "term" is a constant (a,b,c,d,e) or a variable (x,y,z).
 *   E.g.:  Pa  Rab  Rxyz  Qxa
 *
 * Outer-parenthesis convention applies at top level.
 *
 * AST node types:
 *   { type: 'letter',  name: 'p', sub: null|'1' }          PL sentence letter
 *   { type: 'atom',    pred: 'P', args: ['a','x','b'] }     QL atomic formula
 *   { type: 'bot' }                                          ⊥
 *   { type: 'neg',   arg: node }
 *   { type: 'and',   left: node, right: node }
 *   { type: 'or',    left: node, right: node }
 *   { type: 'imp',   left: node, right: node }
 *   { type: 'forall', var: 'x', arg: node }
 *   { type: 'exists', var: 'x', arg: node }
 */

class ParseError extends Error {
  constructor(msg) { super(msg); this.name = 'ParseError'; }
}

// ── Normalise ASCII shorthands ────────────────────────────────────────────────
function normalise(s) {
  return s
    .replace(/<->/g, '↔')
    .replace(/<=>/g, '↔')
    .replace(/->/g,  '→')
    .replace(/=>/g,  '→')
    .split('/\\').join('∧')
    .split('\\/').join('∨')
    .replace(/~/g,   '¬')
    .replace(/-(?!>)/g, '¬')
    .replace(/&/g,   '∧')
    .replace(/\|/g,  '∨')
    .replace(/\\?forall\b/gi, '∀')
    .replace(/\\?exists\b/gi, '∃')
    .replace(/\\?all\b/gi,    '∀')
    .replace(/\\?ex\b/gi,     '∃')
    // Uppercase A/E before a variable (x,y,z): AxPx → ∀xPx, ExPx → ∃xPx
    .replace(/\bA(?=[xyz])/g, '∀')
    .replace(/\bE(?=[xyz])/g, '∃');
}

// ── Token types ───────────────────────────────────────────────────────────────
const T = {
  LETTER:    'LETTER',    // p, q, r, s, t  (PL sentence letter)
  PREDICATE: 'PREDICATE', // P, Q, R, S, T  (QL predicate — uppercase)
  TERM:      'TERM',      // a,b,c,d,e  (constant) or x,y,z (variable)
  NEG:    'NEG',
  AND:    'AND',
  OR:     'OR',
  IMP:    'IMP',
  BICOND: 'BICOND',
  FORALL: 'FORALL',       // ∀
  EXISTS: 'EXISTS',       // ∃
  LPAREN: 'LPAREN',
  RPAREN: 'RPAREN',
  EOF:    'EOF',
};

// Constants and variables of QL
const CONSTANTS = new Set(['a','b','c','d','e']);
const VARIABLES = new Set(['x','y','z']);
const PL_LETTERS = new Set(['p','q','r','s','t']);
const PREDICATES = new Set(['P','Q','R','S','T']);

function isTerm(ch) { return CONSTANTS.has(ch) || VARIABLES.has(ch); }

function tokenise(raw) {
  const s = normalise(raw.trim());
  const tokens = [];
  let i = 0;
  while (i < s.length) {
    const ch = s[i];
    if (ch === ' ' || ch === '\t' || ch === '\n') { i++; continue; }
    if (ch === '¬') { tokens.push({ type: T.NEG });    i++; continue; }
    if (ch === '∧') { tokens.push({ type: T.AND });    i++; continue; }
    if (ch === '∨') { tokens.push({ type: T.OR  });    i++; continue; }
    if (ch === '→') { tokens.push({ type: T.IMP });    i++; continue; }
    if (ch === '↔') { tokens.push({ type: T.BICOND }); i++; continue; }
    if (ch === '(') { tokens.push({ type: T.LPAREN }); i++; continue; }
    if (ch === ')') { tokens.push({ type: T.RPAREN }); i++; continue; }
    if (ch === '∀') { tokens.push({ type: T.FORALL }); i++; continue; }
    if (ch === '∃') { tokens.push({ type: T.EXISTS }); i++; continue; }

    // PL sentence letters: p, q, r, s, t with optional numeric subscript
    if (PL_LETTERS.has(ch)) {
      let sub = '';
      i++;
      while (i < s.length && /[0-9]/.test(s[i])) { sub += s[i]; i++; }
      tokens.push({ type: T.LETTER, name: ch, sub: sub || null });
      continue;
    }

    // QL predicates: P, Q, R, S, T (uppercase)
    if (PREDICATES.has(ch)) {
      tokens.push({ type: T.PREDICATE, name: ch });
      i++;
      continue;
    }

    // QL terms: constants a,b,c,d,e and variables x,y,z
    if (isTerm(ch)) {
      tokens.push({ type: T.TERM, name: ch });
      i++;
      continue;
    }

    // Subscript digits after terms (handled inline above); stray digits here
    if (/[0-9]/.test(ch)) {
      throw new ParseError(`Unexpected digit '${ch}' — subscripts are only allowed after sentence letters (p1, q2, …).`);
    }

    // Uppercase that is not a predicate
    if (/[A-Z]/.test(ch)) {
      throw new ParseError(
        `'${ch}' is not a predicate letter. Predicate letters are P, Q, R, S, T.`
      );
    }

    // Lowercase that is not a recognised symbol
    if (/[a-z]/.test(ch)) {
      let word = ch; i++;
      while (i < s.length && /[a-z0-9]/.test(s[i])) { word += s[i]; i++; }
      throw new ParseError(
        `'${word}' is not a recognised symbol. ` +
        `Sentence letters: p q r s t. Constants: a b c d e. Variables: x y z. Predicates: P Q R S T.`
      );
    }

    throw new ParseError(`Unexpected character '${ch}'.`);
  }
  tokens.push({ type: T.EOF });
  return tokens;
}

// ── Parser ────────────────────────────────────────────────────────────────────
class Parser {
  constructor(tokens) {
    this.tokens = tokens;
    this.pos    = 0;
  }

  peek()    { return this.tokens[this.pos]; }
  consume() { return this.tokens[this.pos++]; }
  at(type)  { return this.peek().type === type; }
  expect(type, hint) {
    if (!this.at(type)) {
      const got = this.peek().type === T.EOF ? 'end of input'
                : `'${tokenLabel(this.peek().type)}'`;
      throw new ParseError(hint || `Expected ${tokenLabel(type)}, got ${got}.`);
    }
    return this.consume();
  }

  parse() {
    if (this.at(T.EOF)) throw new ParseError('Empty input — enter a formula.');
    const node = this.parseFormula(/*topLevel=*/true);
    if (!this.at(T.EOF)) {
      const tok = this.peek();
      throw new ParseError(`Unexpected '${tokenLabel(tok.type)}' after formula — check your parentheses.`);
    }
    return node;
  }

  parseFormula(topLevel = false) {
    // ¬ φ
    if (this.at(T.NEG)) {
      this.consume();
      if (this.at(T.EOF)) throw new ParseError('¬ must be followed by a formula.');
      const arg = this.parseFormula();
      return { type: 'neg', arg };
    }

    // ∀x φ  or  ∃x φ
    if (this.at(T.FORALL) || this.at(T.EXISTS)) {
      const qtype = this.at(T.FORALL) ? 'forall' : 'exists';
      this.consume();
      // Expect a variable
      if (!this.at(T.TERM) || !VARIABLES.has(this.peek().name)) {
        const got = this.at(T.EOF) ? 'end of input' : `'${tokenLabel(this.peek().type)}'`;
        throw new ParseError(
          `The quantifier ${qtype === 'forall' ? '∀' : '∃'} must be followed by a variable (x, y, or z), but got ${got}.`
        );
      }
      const v = this.consume().name;
      if (this.at(T.EOF)) throw new ParseError(`Missing formula after ${qtype === 'forall' ? '∀' : '∃'}${v}.`);
      const arg = this.parseFormula();
      return { type: qtype, var: v, arg };
    }

    // ( φ ∧/∨/→ ψ )
    if (this.at(T.LPAREN)) {
      this.consume();
      if (this.at(T.RPAREN)) throw new ParseError('Empty parentheses — put a formula inside ( ).');
      const left = this.parseFormula();
      const conn = this.parseConnective();
      const right = this.parseFormula();
      if (this.at(T.AND) || this.at(T.OR) || this.at(T.IMP)) {
        throw new ParseError(
          `Each pair of parentheses encloses exactly one connective. ` +
          `Group it as, e.g., (p ∧ q) → r  or  p ∧ (q → r).`
        );
      }
      this.expect(T.RPAREN, `Missing closing ')' after the right subformula.`);
      return { type: conn, left, right };
    }

    // QL atomic formula: Predicate followed by one or more terms
    // e.g. Pa, Rab, Rxyz, Qxa
    if (this.at(T.PREDICATE)) {
      const pred = this.consume().name;
      const args = [];
      while (this.at(T.TERM)) {
        args.push(this.consume().name);
      }
      if (args.length === 0) {
        throw new ParseError(
          `Predicate '${pred}' must be followed by at least one term (a constant like a,b,c or a variable like x,y,z). E.g. ${pred}a or ${pred}xy.`
        );
      }
      return { type: 'atom', pred, args };
    }

    // PL sentence letter
    if (this.at(T.LETTER)) {
      const tok = this.consume();
      return { type: 'letter', name: tok.name, sub: tok.sub };
    }

    // Helpful errors
    if (this.at(T.AND) || this.at(T.OR) || this.at(T.IMP)) {
      throw new ParseError(`'${tokenLabel(this.peek().type)}' cannot start a formula — did you forget the left subformula or a '('?`);
    }
    if (this.at(T.RPAREN)) {
      throw new ParseError(`Unexpected ')' — check your parentheses.`);
    }
    if (this.at(T.BICOND)) {
      throw new ParseError(`'↔' is not a connective of this language. Use ¬, ∧, ∨, or →.`);
    }
    if (this.at(T.TERM)) {
      const t = this.peek().name;
      if (VARIABLES.has(t)) {
        throw new ParseError(`Variable '${t}' cannot start a formula by itself — use a predicate before it (e.g. P${t}) or a quantifier (e.g. ∀${t}P${t}).`);
      } else {
        throw new ParseError(`Constant '${t}' cannot start a formula by itself — use a predicate before it (e.g. P${t}).`);
      }
    }

    throw new ParseError(`Expected a formula, but got '${tokenLabel(this.peek().type)}'.`);
  }

  parseConnective() {
    if (this.at(T.AND)) { this.consume(); return 'and'; }
    if (this.at(T.OR))  { this.consume(); return 'or';  }
    if (this.at(T.IMP)) { this.consume(); return 'imp'; }
    if (this.at(T.BICOND)) throw new ParseError(`'↔' is not a connective of this language. Use ∧, ∨, or →.`);
    const got = this.at(T.EOF) ? 'end of input'
              : this.at(T.RPAREN) ? "')'"
              : `'${tokenLabel(this.peek().type)}'`;
    throw new ParseError(`Expected a connective (∧, ∨, or →) between the two subformulas, but got ${got}.`);
  }
}

function tokenLabel(type) {
  return {
    NEG:'¬', AND:'∧', OR:'∨', IMP:'→', BICOND:'↔',
    FORALL:'∀', EXISTS:'∃',
    LPAREN:'(', RPAREN:')',
    LETTER:'sentence letter', PREDICATE:'predicate', TERM:'term',
    EOF:'end of input'
  }[type] || type;
}

// ── Public API ────────────────────────────────────────────────────────────────

/**
 * Parse `input` as a PL or QL formula.
 * Tries bare form first; if that fails, wraps in parens (outer-paren convention).
 */
function parse(input) {
  const tokens = tokenise(input);
  const p = new Parser(tokens);
  return p.parse();
}

/**
 * Pretty-print an AST back to a Unicode string.
 * Omits outer parentheses at the top level (convention).
 */
function prettyPrint(node, topLevel = true) {
  if (!node) return '';
  switch (node.type) {
    case 'letter': return node.name + (node.sub || '');
    case 'atom':   return node.pred + node.args.join('');
    case 'bot':    return '⊥';
    case 'neg':    return '¬' + prettyAtom(node.arg);
    case 'and':    return wrap(`${prettyPrint(node.left, false)} ∧ ${prettyPrint(node.right, false)}`, topLevel);
    case 'or':     return wrap(`${prettyPrint(node.left, false)} ∨ ${prettyPrint(node.right, false)}`, topLevel);
    case 'imp':    return wrap(`${prettyPrint(node.left, false)} → ${prettyPrint(node.right, false)}`, topLevel);
    case 'forall': return `∀${node.var}${prettyQuantBody(node.arg)}`;
    case 'exists': return `∃${node.var}${prettyQuantBody(node.arg)}`;
    default: return '?';
  }
}

// Body of a quantifier: atom and letter don't need parens; everything else does.
function prettyQuantBody(node) {
  if (node.type === 'atom' || node.type === 'letter' || node.type === 'bot') {
    return prettyPrint(node, false);
  }
  if (node.type === 'neg' || node.type === 'forall' || node.type === 'exists') {
    return prettyPrint(node, false);  // these are self-delimiting
  }
  // binary connective needs parens
  return '(' + prettyPrint(node, true) + ')';
}

function prettyAtom(node) {
  if (node.type === 'letter' || node.type === 'atom' || node.type === 'bot' || node.type === 'neg') {
    return prettyPrint(node, false);
  }
  if (node.type === 'forall' || node.type === 'exists') {
    return prettyPrint(node, false);
  }
  // Binary connective under ¬: wrap in parens.
  return '(' + prettyPrint(node, true) + ')';
}

function wrap(s, topLevel) {
  return topLevel ? s : `(${s})`;
}

/**
 * Collect sentence letter names (e.g. ['p','q']) in an AST (PL use).
 */
function collectLetters(ast) {
  const letters = new Set();
  function walk(node) {
    if (!node) return;
    if (node.type === 'letter') { letters.add(node.name + (node.sub || '')); return; }
    if (node.type === 'neg')   { walk(node.arg); return; }
    if (node.type === 'forall' || node.type === 'exists') { walk(node.arg); return; }
    if (node.type === 'atom')  return;
    walk(node.left); walk(node.right);
  }
  walk(ast);
  return [...letters].sort();
}

/**
 * Collect all constant names occurring in an AST.
 */
function collectConstants(ast) {
  const consts = new Set();
  function walk(node) {
    if (!node) return;
    if (node.type === 'atom') { node.args.forEach(a => { if (CONSTANTS.has(a)) consts.add(a); }); return; }
    if (node.type === 'neg' || node.type === 'forall' || node.type === 'exists') { walk(node.arg); return; }
    if (node.type === 'letter' || node.type === 'bot') return;
    walk(node.left); walk(node.right);
  }
  walk(ast);
  return [...consts].sort();
}
