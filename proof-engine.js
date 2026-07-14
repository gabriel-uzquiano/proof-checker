/**
 * Proof Engine for Propositional + Quantificational Logic Natural Deduction.
 *
 * Propositional rules (PHIL 220):
 *   P       — Premise
 *   A       — Assumption (opens subproof)
 *   R       — Repetition             cite: [n]
 *   ∧I      — Conjunction Intro      cite: [m,n]
 *   ∧E      — Conjunction Elim       cite: [n]
 *   →E      — Conditional Elim (MP)  cite: [m,n]
 *   →I      — Conditional Intro      cite: [m–n]  (subproof)
 *   ∨I      — Disjunction Intro      cite: [n]
 *   ∨E      — Disjunction Elim       cite: [m,n,k]
 *   ¬E      — Negation Elim          cite: [m,n]
 *   ¬I      — Negation Intro         cite: [m–n]  (subproof)
 *   EFSQ    — Ex Falso               cite: [n]
 *   DN      — Double Negation        cite: [n]
 *
 * Quantifier rules (PHIL 220 Chapter 10):
 *   ∀E      — Universal Elim         cite: [n]
 *             From ∀xφ, derive φ(a/x) for any constant a.
 *   ∀I      — Universal Intro        cite: [n]
 *             From φ(a/x), derive ∀xφ, provided a is fresh:
 *             a must not occur in ∀xφ (i.e. in φ with x free) nor in any undischarged assumption.
 *   ∃I      — Existential Intro      cite: [n]
 *             From φ(a/x), derive ∃xφ for some constant a occurring in φ(a/x).
 *   ∃E      — Existential Elim       cite: [m,n]
 *             From ∃xφ (line m) and φ(a/x)→ψ (line n), derive ψ,
 *             provided a occurs neither in ψ nor in ∃xφ nor in any undischarged assumption.
 *
 * ⊥ aliases: _|_  bot  bottom  false  ⊥  \bot
 */

// ── Formula equality ──────────────────────────────────────────────────────────
function astEqual(a, b) {
  if (!a || !b) return false;
  if (a.type !== b.type) return false;
  switch (a.type) {
    case 'letter': return a.name === b.name && a.sub === b.sub;
    case 'atom':   return a.pred === b.pred && a.args.length === b.args.length
                       && a.args.every((v, i) => v === b.args[i]);
    case 'bot':    return true;
    case 'neg':    return astEqual(a.arg, b.arg);
    case 'and': case 'or': case 'imp':
      return astEqual(a.left, b.left) && astEqual(a.right, b.right);
    case 'forall': case 'exists':
      return a.var === b.var && astEqual(a.arg, b.arg);
    default: return false;
  }
}

function formulaStr(ast) {
  if (!ast) return '?';
  return prettyPrint(ast, true);
}

// ── Formula parsing helper ───────────────────────────────────────────────────
const BOT_ALIASES_RE = /\b(_\|_|bot|bottom|false|\\bot)\b/gi;
const FULL_BOT_RE    = /^(_\|_|bot|bottom|false|⊥|\\bot)$/i;

function parseFormula(raw) {
  const s = raw.trim();
  if (FULL_BOT_RE.test(s)) return { type: 'bot' };

  if (BOT_ALIASES_RE.test(s)) {
    BOT_ALIASES_RE.lastIndex = 0;
    const FAKE = 's9999';
    const patchedStr = s.replace(BOT_ALIASES_RE, FAKE);
    BOT_ALIASES_RE.lastIndex = 0;
    let ast;
    try { ast = parse(patchedStr); }
    catch(e) { try { ast = parse('(' + patchedStr + ')'); } catch(e2) { throw new Error('Cannot parse: ' + s); } }
    function patchBot(node) {
      if (!node) return node;
      if (node.type === 'letter' && node.name === 's' && node.sub === '9999') return { type: 'bot' };
      if (node.type === 'neg') return { type: 'neg', arg: patchBot(node.arg) };
      if (node.type === 'forall' || node.type === 'exists') return { ...node, arg: patchBot(node.arg) };
      if (['and','or','imp'].includes(node.type))
        return { ...node, left: patchBot(node.left), right: patchBot(node.right) };
      return node;
    }
    return patchBot(ast);
  }
  try { return parse(s); }
  catch(e) { return parse('(' + s + ')'); }
}

// ── Substitution helpers ──────────────────────────────────────────────────────

/**
 * Substitute constant `con` for all free occurrences of variable `vr` in `node`.
 * Returns a new AST (original unchanged).
 */
function substituteVar(node, vr, con) {
  if (!node) return node;
  switch (node.type) {
    case 'atom': {
      const newArgs = node.args.map(a => a === vr ? con : a);
      return { type: 'atom', pred: node.pred, args: newArgs };
    }
    case 'letter': case 'bot': return node;
    case 'neg': return { type: 'neg', arg: substituteVar(node.arg, vr, con) };
    case 'and': case 'or': case 'imp':
      return { ...node, left: substituteVar(node.left, vr, con), right: substituteVar(node.right, vr, con) };
    case 'forall': case 'exists':
      // If the quantifier binds vr, stop substituting (vr is bound inside)
      if (node.var === vr) return node;
      return { ...node, arg: substituteVar(node.arg, vr, con) };
    default: return node;
  }
}

/**
 * Substitute variable `vr` for all occurrences of constant `con` in `node`.
 * Used for ∀I / ∃I construction: given φ(a/x), recover φ by replacing a with x.
 */
function substituteCon(node, con, vr) {
  if (!node) return node;
  switch (node.type) {
    case 'atom': {
      const newArgs = node.args.map(a => a === con ? vr : a);
      return { type: 'atom', pred: node.pred, args: newArgs };
    }
    case 'letter': case 'bot': return node;
    case 'neg': return { type: 'neg', arg: substituteCon(node.arg, con, vr) };
    case 'and': case 'or': case 'imp':
      return { ...node, left: substituteCon(node.left, con, vr), right: substituteCon(node.right, con, vr) };
    case 'forall': case 'exists':
      // Don't substitute inside a quantifier that binds the target variable
      if (node.var === vr) return node;
      return { ...node, arg: substituteCon(node.arg, con, vr) };
    default: return node;
  }
}

/**
 * Collect all constants occurring anywhere in an AST.
 */
function constsInNode(node) {
  const s = new Set();
  function walk(n) {
    if (!n) return;
    if (n.type === 'atom') { n.args.forEach(a => { if (/^[abcde]$/.test(a)) s.add(a); }); return; }
    if (n.type === 'neg' || n.type === 'forall' || n.type === 'exists') { walk(n.arg); return; }
    if (n.type === 'letter' || n.type === 'bot') return;
    walk(n.left); walk(n.right);
  }
  walk(node);
  return s;
}

/**
 * Check whether constant `con` occurs anywhere in AST `node`.
 */
function constOccurs(node, con) {
  return constsInNode(node).has(con);
}

/**
 * Check whether variable `vr` occurs free in `node`.
 */
function varFree(node, vr) {
  if (!node) return false;
  switch (node.type) {
    case 'atom': return node.args.includes(vr);
    case 'letter': case 'bot': return false;
    case 'neg': return varFree(node.arg, vr);
    case 'and': case 'or': case 'imp':
      return varFree(node.left, vr) || varFree(node.right, vr);
    case 'forall': case 'exists':
      if (node.var === vr) return false;   // bound here
      return varFree(node.arg, vr);
    default: return false;
  }
}

// ── Rule name normalisation ───────────────────────────────────────────────────
function normaliseRule(raw) {
  // Key-building: normalise ASCII shorthands, uppercase, strip spaces
  const key = raw.trim()
    .replace(/\/\\/g, '∧').replace(/&/g, '∧')
    .replace(/\\\//g, '∨').replace(/\|(?!_)/g, '∨')
    .replace(/->/g, '→').replace(/=>/g, '→')
    .replace(/[~]/g, '¬')
    .replace(/\\?forall\b/gi, '∀')
    .replace(/\\?exists\b/gi, '∃')
    .replace(/\\?all\b/gi, '∀')
    .replace(/A\b/g, v => v) // don't mangle standalone A
    .toUpperCase()
    .replace(/\s+/g, '');

  const MAP = {
    'R': 'R', 'REP': 'R', 'REPETITION': 'R',
    '∧I': '∧I', 'AI': '∧I', 'ANDI': '∧I', 'CONJ': '∧I', 'CONJI': '∧I',
    '∧E': '∧E', 'AE': '∧E', 'ANDE': '∧E', 'CONJE': '∧E', 'SIMP': '∧E', 'S': '∧E',
    '→I': '→I', 'CI': '→I', 'CONDI': '→I', 'CD': '→I',
    '→E': '→E', 'CE': '→E', 'CONDE': '→E', 'MP': '→E',
    '∨I': '∨I', 'ORI': '∨I', 'DISJI': '∨I', 'ADD': '∨I',
    '∨E': '∨E', 'ORE': '∨E', 'DISJE': '∨E', 'MTP': '∨E',
    '¬I': '¬I', 'NEGI': '¬I', 'ID': '¬I', 'NI': '¬I',
    '¬E': '¬E', 'NEGE': '¬E', 'NE': '¬E',
    'EFSQ': 'EFSQ', 'EFQ': 'EFSQ', 'EXFALSO': 'EFSQ', 'EF': 'EFSQ',
    'DN': 'DN', 'DNE': 'DN', 'DNI': 'DN', 'DOUBLENEG': 'DN',
    'P': 'P', 'PR': 'P', 'PREM': 'P', 'PREMISE': 'P',
    'A': 'A', 'AS': 'A', 'ASS': 'A', 'ASSUMPTION': 'A', 'ASSUME': 'A',
    // Quantifier rules
    '∀E': '∀E', 'AE2': '∀E', 'UE': '∀E', 'FORALLE': '∀E', 'UI': '∀E',
    '∀I': '∀I', 'AI2': '∀I', 'UI2': '∀I', 'FORALLI': '∀I', 'UG': '∀I',
    '∃I': '∃I', 'EI': '∃I', 'EXISTSI': '∃I', 'EG': '∃I',
    '∃E': '∃E', 'EE': '∃E', 'EXISTSE': '∃E', 'ES': '∃E',
  };

  return MAP[key] || null;
}

// ── Parse a single proof line ─────────────────────────────────────────────────
function parseProofLine(rawLine, lineNo) {
  const indent = (rawLine.match(/^(\s*)/)[1] || '').replace(/\t/g, '  ').length;
  const text   = rawLine.trim();

  if (!text || text.startsWith('#')) {
    return { blank: true, indent, raw: rawLine, lineNo };
  }

  // Collapse spaced / unicode dashes between digits
  const normText = text.replace(/(\d+)\s*[\u2010-\u2015\-]\s*(\d+)/g, '$1-$2');
  const tokens = normText.split(/\s+/).filter(Boolean);

  const isCitFrag = (t) => /^[\d,\-]+$/.test(t);

  let citStart = tokens.length;
  while (citStart > 0 && isCitFrag(tokens[citStart - 1])) citStart--;

  if (citStart === 0) {
    return { error: 'No rule found', raw: rawLine, lineNo, indent };
  }

  const ruleRaw = tokens[citStart - 1];
  const rule    = normaliseRule(ruleRaw);

  const INT_RE   = /^\d+$/;
  const RANGE_RE = /^(\d+)-(\d+)$/;
  const citations = [];
  const ranges    = [];
  let citParseErr = null;

  const citeStr = tokens.slice(citStart).join(' ');
  const parts = citeStr.split(',').map(s => s.trim()).filter(s => s.length > 0);
  for (const part of parts) {
    const rm = part.match(RANGE_RE);
    if (rm) {
      ranges.push({ m: +rm[1], n: +rm[2], raw: part });
    } else if (INT_RE.test(part)) {
      citations.push(Number(part));
    } else {
      citParseErr = 'Cite line numbers separated by commas (e.g. ∧I 1, 2); use a dash for a subproof (e.g. →I 2-6).';
      break;
    }
  }
  for (const r of ranges) {
    if (r.m >= r.n) citParseErr = `Subproof range ${r.m}–${r.n} is invalid: the assumption line must come before the last line.`;
  }

  const formulaTokens = tokens.slice(0, citStart - 1);

  if (formulaTokens.length === 0) {
    return { error: 'No formula found', raw: rawLine, lineNo, indent };
  }

  const formulaRaw = formulaTokens.join(' ');

  let ast;
  try {
    ast = parseFormula(formulaRaw);
  } catch (e) {
    return { error: 'Cannot parse formula: ' + formulaRaw + (e.message ? ' — ' + e.message : ''), raw: rawLine, lineNo, indent };
  }

  if (!rule) {
    return { error: 'Unknown rule: ' + ruleRaw, raw: rawLine, lineNo, indent, formula: ast, citations, ranges };
  }

  if (citParseErr) {
    return { error: citParseErr, raw: rawLine, lineNo, indent, formula: ast, rule, citations, ranges };
  }

  return { formula: ast, rule, citations, ranges, indent, raw: rawLine, lineNo };
}

// ── Subproof structure ────────────────────────────────────────────────────────
function buildStructure(parsedLines) {
  const indentStack = [0];
  const lines = [];
  let proofLineNo = 0;

  parsedLines.forEach(pl => {
    if (pl.blank) return;

    const indent = pl.indent;

    while (indentStack.length > 1 && indentStack[indentStack.length - 1] > indent) {
      indentStack.pop();
    }

    if (indent > indentStack[indentStack.length - 1]) {
      indentStack.push(indent);
    }

    proofLineNo++;
    const depth = indentStack.length - 1;
    lines.push({ ...pl, depth, proofLineNo });
  });

  return lines;
}

// ── Availability check ────────────────────────────────────────────────────────
function isAvailable(targetIdx, citedIdx, lines, dischargedRanges) {
  const cited  = lines[citedIdx];
  const target = lines[targetIdx];

  if (!cited || !target) return false;
  if (cited.proofLineNo >= target.proofLineNo) return false;
  if (cited.depth > target.depth) return false;

  for (const [start, end] of dischargedRanges) {
    if (cited.proofLineNo >= start && cited.proofLineNo <= end) {
      return false;
    }
  }

  return true;
}

// ── Core validator ────────────────────────────────────────────────────────────
function validateProof(parsedLines, premises) {
  const lines           = buildStructure(parsedLines);
  const dischargedRanges = [];
  const results         = [];

  const byNo = {};
  lines.forEach((l, i) => { byNo[l.proofLineNo] = i; });

  function getLine(no) {
    const idx = byNo[no];
    return idx !== undefined ? lines[idx] : null;
  }

  function available(fromIdx, citedNo) {
    const citedIdx = byNo[citedNo];
    if (citedIdx === undefined) return false;
    return isAvailable(fromIdx, citedIdx, lines, dischargedRanges);
  }

  function checkCitations(fromIdx, nos, count) {
    if (count !== null && nos.length !== count)
      return `Expected ${count} citation(s), got ${nos.length}`;
    for (const no of nos) {
      if (!available(fromIdx, no))
        return `Line ${no} is not available here`;
    }
    return null;
  }

  /**
   * Collect all constants appearing in undischarged assumption lines
   * visible from the current proof index (fromIdx).
   */
  function undischargedAssumptionConsts(fromIdx) {
    const consts = new Set();
    for (let i = 0; i < fromIdx; i++) {
      const l = lines[i];
      if (l.rule !== 'A') continue;
      // Is this assumption currently undischarged (still open) from fromIdx?
      if (!isAvailable(fromIdx, i, lines, dischargedRanges)) continue;
      constsInNode(l.formula).forEach(c => consts.add(c));
    }
    return consts;
  }

  /**
   * Also collect constants in the premises (treated as always open).
   */
  function premiseConsts() {
    const consts = new Set();
    premises.forEach(p => constsInNode(p).forEach(c => consts.add(c)));
    return consts;
  }

  lines.forEach((line, idx) => {
    if (line.error) {
      results.push({ ...line, ok: false });
      return;
    }

    const { formula, rule, citations, ranges, depth, proofLineNo } = line;
    let ok = false;
    let errMsg = null;

    // Subproof ranges only valid for →I and ¬I
    if (ranges && ranges.length && rule !== '→I' && rule !== '¬I') {
      results.push({ ...line, ok: false, error: `${rule} does not take a subproof range (m–n). Cite separate line numbers instead.` });
      return;
    }

    const citCheck = (count) => checkCitations(idx, citations, count);

    switch (rule) {

      case 'P': {
        const e = citCheck(0);
        if (e) { errMsg = e; break; }
        if (depth !== 0) { errMsg = 'Premises must be at the top level'; break; }
        const match = premises.some(p => astEqual(p, formula));
        if (!match) errMsg = formulaStr(formula) + ' is not a listed premise';
        else ok = true;
        break;
      }

      case 'A': {
        const e = citCheck(0);
        if (e) { errMsg = e; break; }
        if (depth === 0) { errMsg = 'Assumptions must be inside a subproof (indent the line)'; break; }
        ok = true;
        break;
      }

      case 'R': {
        const e = citCheck(1);
        if (e) { errMsg = e; break; }
        const src = getLine(citations[0]);
        if (!src) { errMsg = `Line ${citations[0]} not found`; break; }
        if (!astEqual(src.formula, formula))
          errMsg = `Line ${citations[0]} has ${formulaStr(src.formula)}, not ${formulaStr(formula)}`;
        else ok = true;
        break;
      }

      case '∧I': {
        const e = citCheck(2);
        if (e) { errMsg = e; break; }
        if (formula.type !== 'and') { errMsg = 'Result must be a conjunction (φ∧ψ)'; break; }
        const l = getLine(citations[0]), r = getLine(citations[1]);
        if (!l || !r) { errMsg = 'Citation not found'; break; }
        if (astEqual(l.formula, formula.left) && astEqual(r.formula, formula.right)) ok = true;
        else if (astEqual(l.formula, formula.right) && astEqual(r.formula, formula.left)) ok = true;
        else errMsg = `Conjuncts don't match lines ${citations[0]} and ${citations[1]}`;
        break;
      }

      case '∧E': {
        const e = citCheck(1);
        if (e) { errMsg = e; break; }
        const src = getLine(citations[0]);
        if (!src) { errMsg = 'Citation not found'; break; }
        if (src.formula.type !== 'and') { errMsg = `Line ${citations[0]} is not a conjunction`; break; }
        if (astEqual(formula, src.formula.left) || astEqual(formula, src.formula.right)) ok = true;
        else errMsg = `${formulaStr(formula)} is not a conjunct of line ${citations[0]}`;
        break;
      }

      case '→E': {
        const e = citCheck(2);
        if (e) { errMsg = e; break; }
        const a = getLine(citations[0]), b = getLine(citations[1]);
        if (!a || !b) { errMsg = 'Citation not found'; break; }
        let condLine, antLine;
        if (a.formula.type === 'imp') { condLine = a; antLine = b; }
        else if (b.formula.type === 'imp') { condLine = b; antLine = a; }
        else { errMsg = 'One of the cited lines must be a conditional (φ→ψ)'; break; }
        if (!astEqual(condLine.formula.left, antLine.formula))
          errMsg = `Antecedent of line ${condLine.proofLineNo} doesn't match line ${antLine.proofLineNo}`;
        else if (!astEqual(condLine.formula.right, formula))
          errMsg = `Consequent of line ${condLine.proofLineNo} is ${formulaStr(condLine.formula.right)}, not ${formulaStr(formula)}`;
        else ok = true;
        break;
      }

      case '→I': {
        if (citations.length !== 0) { errMsg = `Use a dash for subproofs: write "→I ${citations[0]}–${citations[1] || citations[0]+1}", not "→I ${citations.join(' ')}".`; break; }
        if (!ranges || ranges.length !== 1) { errMsg = '→I requires a subproof range m–n (e.g. →I 2–3).'; break; }
        const r = ranges[0];
        if (formula.type !== 'imp') { errMsg = 'Result must be a conditional (φ→ψ)'; break; }
        const assumeLine = getLine(r.m);
        const lastLine   = getLine(r.n);
        if (!assumeLine || !lastLine) { errMsg = 'Citation not found'; break; }
        if (assumeLine.rule !== 'A') { errMsg = `Line ${r.m} must be an assumption (A)`; break; }
        if (assumeLine.depth !== lastLine.depth) { errMsg = 'Assumption and last line must be at the same depth'; break; }
        if (assumeLine.depth <= depth) { errMsg = 'Subproof must be at a deeper level than this line'; break; }
        if (!astEqual(assumeLine.formula, formula.left))
          errMsg = `Assumption (line ${r.m}) must match antecedent ${formulaStr(formula.left)}`;
        else if (!astEqual(lastLine.formula, formula.right))
          errMsg = `Last subproof line (${r.n}) must match consequent ${formulaStr(formula.right)}`;
        else {
          dischargedRanges.push([assumeLine.proofLineNo, lastLine.proofLineNo]);
          ok = true;
        }
        break;
      }

      case '∨I': {
        const e = citCheck(1);
        if (e) { errMsg = e; break; }
        if (formula.type !== 'or') { errMsg = 'Result must be a disjunction (φ∨ψ)'; break; }
        const src = getLine(citations[0]);
        if (!src) { errMsg = 'Citation not found'; break; }
        if (astEqual(src.formula, formula.left) || astEqual(src.formula, formula.right)) ok = true;
        else errMsg = `Line ${citations[0]} is not a disjunct of ${formulaStr(formula)}`;
        break;
      }

      case '∨E': {
        const e = citCheck(3);
        if (e) { errMsg = e; break; }
        const [n1, n2, n3] = citations;
        const l1 = getLine(n1), l2 = getLine(n2), l3 = getLine(n3);
        if (!l1 || !l2 || !l3) { errMsg = 'Citation not found'; break; }

        let disjLine, cond1Line, cond2Line;
        const candidates = [l1, l2, l3];
        for (let i = 0; i < 3; i++) {
          if (candidates[i].formula.type === 'or') {
            disjLine  = candidates[i];
            cond1Line = candidates[(i+1)%3];
            cond2Line = candidates[(i+2)%3];
            break;
          }
        }
        if (!disjLine) { errMsg = 'One cited line must be a disjunction (φ∨ψ)'; break; }
        if (cond1Line.formula.type !== 'imp' || cond2Line.formula.type !== 'imp')
          { errMsg = 'The other two cited lines must be conditionals (φ→χ and ψ→χ)'; break; }

        const phi = disjLine.formula.left;
        const psi = disjLine.formula.right;

        let matched = false;
        for (const [c1, c2] of [[cond1Line, cond2Line], [cond2Line, cond1Line]]) {
          if (astEqual(c1.formula.left, phi) && astEqual(c2.formula.left, psi)
              && astEqual(c1.formula.right, formula) && astEqual(c2.formula.right, formula)) {
            matched = true; break;
          }
        }
        if (!matched)
          errMsg = `Conditionals must be φ→${formulaStr(formula)} and ψ→${formulaStr(formula)}, where φ∨ψ is line ${disjLine.proofLineNo}`;
        else ok = true;
        break;
      }

      case '¬E': {
        const e = citCheck(2);
        if (e) { errMsg = e; break; }
        if (formula.type !== 'bot') { errMsg = 'Result of ¬E must be ⊥'; break; }
        const a = getLine(citations[0]), b = getLine(citations[1]);
        if (!a || !b) { errMsg = 'Citation not found'; break; }
        let phiLine;
        if (b.formula.type === 'neg' && astEqual(b.formula.arg, a.formula))
          phiLine = a;
        else if (a.formula.type === 'neg' && astEqual(a.formula.arg, b.formula))
          phiLine = b;
        else errMsg = `Lines ${citations[0]} and ${citations[1]} are not a formula and its negation`;
        if (phiLine) ok = true;
        break;
      }

      case '¬I': {
        if (citations.length !== 0) { errMsg = `Use a dash for subproofs: write "¬I ${citations[0]}–${citations[1] || citations[0]+1}", not "¬I ${citations.join(' ')}".`; break; }
        if (!ranges || ranges.length !== 1) { errMsg = '¬I requires a subproof range m–n (e.g. ¬I 3–4).'; break; }
        const r = ranges[0];
        if (formula.type !== 'neg') { errMsg = 'Result of ¬I must be a negation (¬φ)'; break; }
        const assumeLine = getLine(r.m);
        const botLine    = getLine(r.n);
        if (!assumeLine || !botLine) { errMsg = 'Citation not found'; break; }
        if (assumeLine.rule !== 'A') { errMsg = `Line ${r.m} must be an assumption (A)`; break; }
        if (botLine.formula.type !== 'bot') { errMsg = `Line ${r.n} must be ⊥`; break; }
        if (assumeLine.depth !== botLine.depth) { errMsg = 'Assumption and ⊥ must be at the same depth'; break; }
        if (assumeLine.depth <= depth) { errMsg = 'Subproof must be at a deeper level than this line'; break; }
        if (!astEqual(assumeLine.formula, formula.arg))
          errMsg = `Assumption (line ${r.m}) must match ${formulaStr(formula.arg)}`;
        else {
          dischargedRanges.push([assumeLine.proofLineNo, botLine.proofLineNo]);
          ok = true;
        }
        break;
      }

      case 'EFSQ': {
        const e = citCheck(1);
        if (e) { errMsg = e; break; }
        const src = getLine(citations[0]);
        if (!src) { errMsg = 'Citation not found'; break; }
        if (src.formula.type !== 'bot') errMsg = `Line ${citations[0]} must be ⊥`;
        else ok = true;
        break;
      }

      case 'DN': {
        const e = citCheck(1);
        if (e) { errMsg = e; break; }
        const src = getLine(citations[0]);
        if (!src) { errMsg = 'Citation not found'; break; }
        if (src.formula.type === 'neg' && src.formula.arg.type === 'neg'
            && astEqual(src.formula.arg.arg, formula)) { ok = true; break; }
        if (formula.type === 'neg' && formula.arg.type === 'neg'
            && astEqual(formula.arg.arg, src.formula)) { ok = true; break; }
        errMsg = `DN requires ¬¬φ→φ or φ→¬¬φ`;
        break;
      }

      // ── Quantifier rules ──────────────────────────────────────────────────

      case '∀E': {
        // From ∀xφ (cited line), derive φ(a/x) for some constant a.
        const e = citCheck(1);
        if (e) { errMsg = e; break; }
        const src = getLine(citations[0]);
        if (!src) { errMsg = 'Citation not found'; break; }
        if (src.formula.type !== 'forall') {
          errMsg = `Line ${citations[0]} is not a universally quantified formula (∀xφ)`;
          break;
        }
        // Try each constant: does substituting it into φ give the result?
        const vr = src.formula.var;
        const phi = src.formula.arg;
        // Also try substituting the bound variable with itself (i.e. the body unchanged — unusual but allowed)
        const candidates = ['a','b','c','d','e'];
        let matched = false;
        for (const con of candidates) {
          const instance = substituteVar(phi, vr, con);
          if (astEqual(instance, formula)) { matched = true; break; }
        }
        // Also allow keeping the variable (instantiating with itself is not standard, skip)
        if (!matched) {
          errMsg = `${formulaStr(formula)} is not an instance of ${formulaStr(src.formula)} — substitute a constant (a, b, c, d, or e) for ${vr}`;
        } else ok = true;
        break;
      }

      case '∀I': {
        // From φ(a/x) (cited line), derive ∀xφ.
        // Freshness: a must not occur in ∀xφ, nor in any undischarged assumption.
        const e = citCheck(1);
        if (e) { errMsg = e; break; }
        if (formula.type !== 'forall') {
          errMsg = 'Result of ∀I must be a universally quantified formula (∀xφ)';
          break;
        }
        const src = getLine(citations[0]);
        if (!src) { errMsg = 'Citation not found'; break; }

        const vr  = formula.var;
        const phi = formula.arg;   // φ — the body of the ∀ formula

        // Find a constant a such that: φ(a/x) matches the cited formula.
        // We try every constant that actually appears in the cited formula.
        const candidateConsts = [...constsInNode(src.formula)];
        if (candidateConsts.length === 0) {
          // The cited line has no constants — it might equal the body with x free,
          // which would mean using the variable as a pseudo-constant (not standard).
          errMsg = `∀I requires citing a line with a constant that can be generalised over`;
          break;
        }

        let witnessCon = null;
        for (const con of candidateConsts) {
          const candidate = substituteVar(phi, vr, con);
          if (astEqual(candidate, src.formula)) {
            witnessCon = con;
            break;
          }
        }

        if (!witnessCon) {
          errMsg = `Line ${citations[0]} (${formulaStr(src.formula)}) is not an instance of ${formulaStr(formula)} — no constant can be generalised to get ${formulaStr(formula)}`;
          break;
        }

        // Freshness check 1: a must not occur in ∀xφ (the result formula)
        if (constOccurs(formula, witnessCon)) {
          errMsg = `Constant '${witnessCon}' occurs in ${formulaStr(formula)}, so it cannot be the constant used for ∀I (it would remain free in the body)`;
          break;
        }

        // Freshness check 2: a must not occur in any undischarged assumption
        const assumpConsts = undischargedAssumptionConsts(idx);
        if (assumpConsts.has(witnessCon)) {
          errMsg = `Constant '${witnessCon}' occurs in an undischarged assumption, so ∀I is not applicable`;
          break;
        }
        ok = true;
        break;
      }

      case '∃I': {
        // From φ(a/x) (cited line), derive ∃xφ.
        const e = citCheck(1);
        if (e) { errMsg = e; break; }
        if (formula.type !== 'exists') {
          errMsg = 'Result of ∃I must be an existentially quantified formula (∃xφ)';
          break;
        }
        const src = getLine(citations[0]);
        if (!src) { errMsg = 'Citation not found'; break; }

        const vr  = formula.var;
        const phi = formula.arg;

        // Find a constant a in the cited line such that φ(a/x) = cited formula
        const candidateConsts = [...constsInNode(src.formula)];
        let matched = false;
        for (const con of candidateConsts) {
          const instance = substituteVar(phi, vr, con);
          if (astEqual(instance, src.formula)) { matched = true; break; }
        }

        if (!matched) {
          // Maybe the cited formula equals the body with x free (no constant involved)
          // That's not standard; give an informative error.
          errMsg = `Line ${citations[0]} (${formulaStr(src.formula)}) is not an instance of ${formulaStr(formula)} — no constant in that line substitutes for ${vr} to give ${formulaStr(phi)}`;
          break;
        }
        ok = true;
        break;
      }

      case '∃E': {
        // From ∃xφ (line m) and φ(a/x)→ψ (line n), derive ψ.
        // a must not occur in ψ, ∃xφ, or any undischarged assumption.
        const e = citCheck(2);
        if (e) { errMsg = e; break; }
        const lineA = getLine(citations[0]);
        const lineB = getLine(citations[1]);
        if (!lineA || !lineB) { errMsg = 'Citation not found'; break; }

        // Identify which is ∃xφ and which is φ(a/x)→ψ
        let existsLine, condLine;
        if (lineA.formula.type === 'exists' && lineB.formula.type === 'imp') {
          existsLine = lineA; condLine = lineB;
        } else if (lineB.formula.type === 'exists' && lineA.formula.type === 'imp') {
          existsLine = lineB; condLine = lineA;
        } else {
          errMsg = `∃E requires one cited line to be ∃xφ and the other to be φ(a/x)→ψ. ` +
                   `Line ${citations[0]} is a ${lineA.formula.type}, line ${citations[1]} is a ${lineB.formula.type}.`;
          break;
        }

        const vr  = existsLine.formula.var;
        const phi = existsLine.formula.arg;   // φ
        const ant = condLine.formula.left;    // φ(a/x) — antecedent of the conditional
        const con = condLine.formula.right;   // ψ — consequent, must equal result

        // ψ must equal the result formula
        if (!astEqual(con, formula)) {
          errMsg = `Consequent of line ${condLine.proofLineNo} is ${formulaStr(con)}, but the result here is ${formulaStr(formula)}`;
          break;
        }

        // Verify ant = φ(a/x) for some constant a
        const candidateConsts = [...constsInNode(ant)];
        let witnessCon = null;
        for (const c of candidateConsts) {
          const instance = substituteVar(phi, vr, c);
          if (astEqual(instance, ant)) { witnessCon = c; break; }
        }
        if (!witnessCon) {
          errMsg = `Antecedent of line ${condLine.proofLineNo} (${formulaStr(ant)}) is not an instance of ${formulaStr(existsLine.formula)} — no constant substitutes for ${vr} to give ${formulaStr(ant)}`;
          break;
        }

        // Freshness check 1: a must not occur in ψ (the result)
        if (constOccurs(formula, witnessCon)) {
          errMsg = `Constant '${witnessCon}' occurs in the result ${formulaStr(formula)}, so ∃E is not applicable`;
          break;
        }

        // Freshness check 2: a must not occur in ∃xφ
        if (constOccurs(existsLine.formula, witnessCon)) {
          errMsg = `Constant '${witnessCon}' occurs in ${formulaStr(existsLine.formula)}, so ∃E is not applicable`;
          break;
        }

        // Freshness check 3: a must not occur in any undischarged assumption
        const assumpConsts = undischargedAssumptionConsts(idx);
        if (assumpConsts.has(witnessCon)) {
          errMsg = `Constant '${witnessCon}' occurs in an undischarged assumption, so ∃E is not applicable`;
          break;
        }
        ok = true;
        break;
      }

      default:
        errMsg = `Unknown rule: ${rule}`;
    }

    results.push({ ...line, ok: ok && !errMsg, error: errMsg });
  });

  return results;
}

/**
 * Parse proof text and validate.
 * premises: string[] — raw formula strings from sequent input
 * Returns { lines: result[], complete: bool, premises, conclusion }
 */
function checkProof(proofText, premiseStrings, conclusionString) {
  const premises = [];
  for (const s of premiseStrings) {
    const t = s.trim();
    if (!t) continue;
    try { premises.push(parseFormula(t)); }
    catch (e) { return { lines: [], complete: false, error: `Cannot parse premise: ${t}` }; }
  }

  let conclusion = null;
  if (conclusionString && conclusionString.trim()) {
    try { conclusion = parseFormula(conclusionString.trim()); }
    catch (e) { return { lines: [], complete: false, error: `Cannot parse conclusion: ${conclusionString}` }; }
  }

  const rawLines   = proofText.split('\n');
  const parsedLines = rawLines.map((l, i) => parseProofLine(l, i + 1));
  const results    = validateProof(parsedLines, premises);

  const mainLines = results.filter(l => l.depth === 0 && !l.blank);
  const lastMain  = mainLines[mainLines.length - 1];
  const allOk     = results.every(l => l.ok);

  let complete = false;
  if (allOk && conclusion && lastMain) {
    complete = astEqual(lastMain.formula, conclusion);
  }

  return { lines: results, complete, premises, conclusion };
}
