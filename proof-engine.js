/**
 * Proof Engine for Propositional Logic Natural Deduction.
 *
 * Textbook rules (PHIL 220):
 *   R       — Repetition             cite: [n]         result: φ  (copy of line n)
 *   ∧I      — Conjunction Intro      cite: [m,n]       result: φ∧ψ
 *   ∧E      — Conjunction Elim       cite: [n]         result: φ or ψ  (either conjunct)
 *   →E      — Conditional Elim (MP)  cite: [m,n]       result: ψ  (from φ→ψ and φ)
 *   →I      — Conditional Intro      cite: [m–n]       result: φ→ψ  (subproof m–n: assume φ, derive ψ)
 *   ∨I      — Disjunction Intro      cite: [n]         result: φ∨ψ or ψ∨φ
 *   ∨E      — Disjunction Elim       cite: [m,n,k]     result: χ  (from φ∨ψ, φ→χ, ψ→χ)
 *   ¬E      — Negation Elim          cite: [m,n]       result: ⊥  (from φ and ¬φ)
 *   ¬I      — Negation Intro         cite: [m–n]       result: ¬φ (subproof m–n: assume φ, derive ⊥)
 *
 * Subproof rules (→I, ¬I) cite a subproof as a RANGE m–n (a dash between the
 * assumption line and the last line), e.g.  q→p   →I  2–3 .
 * A plain pair of line numbers (→I 2 3) is rejected with a corrective hint.
 *   EFSQ    — Ex Falso               cite: [n]         result: any φ  (from ⊥)
 *   DN      — Double Negation        cite: [n]         result: φ  (from ¬¬φ)
 *   P       — Premise                cite: []          result: listed premise
 *   A       — Assumption             cite: []          result: any φ  (opens subproof)
 *
 * Proof text format (one line per step):
 *   <formula>  <rule>  <citations>
 *
 * Subproofs: indentation level (number of leading spaces / tabs) determines depth.
 * A line at a deeper indent than the previous opens a subproof; returning to a
 * shallower indent closes it.
 *
 * Special formula: ⊥  (type as _|_ or bot or bottom or false or ⊥)
 */

// ── Formula equality ──────────────────────────────────────────────────────────
// Compare two AST nodes structurally
function astEqual(a, b) {
  if (!a || !b) return false;
  if (a.type !== b.type) return false;
  switch (a.type) {
    case 'letter': return a.name === b.name;
    case 'bot':    return true;
    case 'neg':    return astEqual(a.arg, b.arg);
    case 'and': case 'or': case 'imp':
      return astEqual(a.left, b.left) && astEqual(a.right, b.right);
    default: return false;
  }
}

function formulaStr(ast) {
  if (!ast) return '?';
  if (ast.type === 'bot') return '⊥';
  return prettyPrint(ast, true);
}

// ── Formula parsing helper ───────────────────────────────────────────────────
// Replace bot aliases inside a formula string with the ⊥ token the parser can
// handle, then parse. Returns an AST node.
const BOT_ALIASES_RE = /\b(_\|_|bot|bottom|false|\\bot)\b/gi;
const FULL_BOT_RE    = /^(_\|_|bot|bottom|false|⊥|\\bot)$/i;

function parseFormula(raw) {
  const s = raw.trim();
  // Pure bot
  if (FULL_BOT_RE.test(s)) return { type: 'bot' };
  // Bot inside a larger formula — substitute with a temporary placeholder
  // that the parser CAN handle: we extend parse() by pre-substituting _|_ → ⊥
  // Since the parser doesn't handle ⊥ at all, we need a different strategy:
  // walk the formula string and replace _|_ with a sentinel letter, parse,
  // then patch the AST.
  const BOT_SENTINEL = 's'; // We'll treat this letter as bot in post-processing
  // Only substitute when bot alias appears in the string
  if (BOT_ALIASES_RE.test(s)) {
    BOT_ALIASES_RE.lastIndex = 0;
    const patched = s.replace(BOT_ALIASES_RE, '__BOT__');
    // We'll parse by replacing __BOT__ with a unique fake letter and fix after
    // Actually simpler: recursively build AST by splitting on connectives.
    // Easiest: use a tag that looks like a valid letter token to the parser.
    // The parser allows p,q,r,s,t with optional numeric subscripts.
    // Let's pre-process: replace bot alias with 's9999' (unlikely to clash) and
    // post-process the AST.
    const FAKE = 's9999';
    const patchedStr = s.replace(BOT_ALIASES_RE, FAKE);
    BOT_ALIASES_RE.lastIndex = 0;
    let ast;
    try { ast = parse(patchedStr); }
    catch(e) { try { ast = parse('(' + patchedStr + ')'); } catch(e2) { throw new Error('Cannot parse: ' + s); } }
    // Replace all letter nodes with name 's' and sub '9999' with bot
    function patchBot(node) {
      if (!node) return node;
      if (node.type === 'letter' && node.name === 's' && node.sub === '9999') return { type: 'bot' };
      if (node.type === 'neg') return { type: 'neg', arg: patchBot(node.arg) };
      if (node.type === 'and' || node.type === 'or' || node.type === 'imp')
        return { ...node, left: patchBot(node.left), right: patchBot(node.right) };
      return node;
    }
    return patchBot(ast);
  }
  // Normal parse with unofficial-form fallback
  try { return parse(s); }
  catch(e) { return parse('(' + s + ')'); }
}

// ── Rule name normalisation ───────────────────────────────────────────────────
function normaliseRule(raw) {
  const s = raw.trim()
    .replace(/\/\\/g, '∧').replace(/\\/g, '∧')
    .replace(/&/g,    '∧')
    .replace(/\\\//g, '∨').replace(/\|/g, '∨')
    .replace(/->/g,   '→').replace(/=>/g, '→')
    .replace(/[~\-](?=I|E)/g, '¬')
    .replace(/^~/,    '¬')
    .toUpperCase()
    // After upper-casing, restore unicode that got mangled
    .replace(/∧/g, '∧').replace(/∨/g, '∨').replace(/→/g, '→').replace(/¬/g, '¬');

  // Map common aliases
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
  };

  // Normalise the raw string before lookup
  const key = raw.trim()
    .replace(/\/\\/g, '∧').replace(/&/g, '∧')
    .replace(/\\\//g, '∨').replace(/\|(?!_)/g, '∨')
    .replace(/->/g, '→').replace(/=>/g, '→')
    .replace(/[~]/g, '¬')
    .toUpperCase()
    .replace(/\s+/g, '');

  return MAP[key] || MAP[s] || null;
}

// ── Parse a single proof line ─────────────────────────────────────────────────
// Returns { formula, rule, citations, indent, raw, lineNo }
// formula is an AST node (or null for blank lines)
function parseProofLine(rawLine, lineNo) {
  // Measure indentation (spaces + tabs, tab = 2 spaces)
  const indent = (rawLine.match(/^(\s*)/)[1] || '').replace(/\t/g, '  ').length;
  const text   = rawLine.trim();

  if (!text || text.startsWith('#')) {
    return { blank: true, indent, raw: rawLine, lineNo };
  }

  // Line format:  <formula>  <rule>  <citations>
  // The formula may contain spaces (e.g. "(p ∧ q)"), so we tokenize from the
  // right. Citation material is made of digits, commas, and dashes only
  // (e.g. "1, 2, 3" or "2-6"). The rule is the single token immediately
  // before the citation material; the formula is everything before the rule.
  //
  // Citation syntax (required):
  //   • separate line numbers with commas  →  ∧I 1, 2     ∨E 1, 4, 7
  //   • cite a subproof with a dash range  →  →I 2-6      ¬I 2-3
  // A space-separated list such as "∧I 1 2" is rejected with a hint.

  // Collapse spaced / unicode dashes between digits into a single "m-n" token
  // so a range like "2 – 3" or "2—3" stays together after whitespace splitting.
  const normText = text.replace(/(\d+)\s*[\u2010-\u2015\-]\s*(\d+)/g, '$1-$2');
  const tokens = normText.split(/\s+/).filter(Boolean);

  // A citation fragment is digits, commas, and dashes only (no letters/symbols).
  const isCitFrag = (t) => /^[\d,\-]+$/.test(t);

  // Find where citations start (trailing fragments).
  let citStart = tokens.length;
  while (citStart > 0 && isCitFrag(tokens[citStart - 1])) citStart--;

  // The token just before the citations is the rule.
  if (citStart === 0) {
    return { error: 'No rule found', raw: rawLine, lineNo, indent };
  }

  const ruleRaw = tokens[citStart - 1];
  const rule    = normaliseRule(ruleRaw);

  // Parse the citation material into line numbers + subproof ranges.
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
  // Validate any range: m must be strictly less than n
  for (const r of ranges) {
    if (r.m >= r.n) citParseErr = `Subproof range ${r.m}–${r.n} is invalid: the assumption line must come before the last line.`;
  }

  const formulaTokens = tokens.slice(0, citStart - 1);

  if (formulaTokens.length === 0) {
    return { error: 'No formula found', raw: rawLine, lineNo, indent };
  }

  const formulaRaw = formulaTokens.join(' ');

  // Parse the formula — uses parseFormula which handles ⊥ aliases and unofficial forms
  let ast;
  try {
    ast = parseFormula(formulaRaw);
  } catch (e) {
    return { error: 'Cannot parse formula: ' + formulaRaw, raw: rawLine, lineNo, indent };
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
/**
 * Given an array of parsed lines, build a stack-based subproof structure.
 * Returns lines annotated with:
 *   line.depth    — nesting depth (0 = main proof)
 *   line.subproofOpen  — true if this line opens a new subproof (assumption)
 *   line.subproofClose — depth levels closed after this line
 *
 * Also returns a flat array of { lineNo, depth, formula, rule, citations, error }
 */
function buildStructure(parsedLines) {
  // Assign depth from indentation
  // We use a stack of indent levels
  const indentStack = [0];
  const lines = [];
  let proofLineNo = 0;

  parsedLines.forEach(pl => {
    if (pl.blank) return;

    const indent = pl.indent;

    // Pop stack while top indent > current (closing subproofs)
    while (indentStack.length > 1 && indentStack[indentStack.length - 1] > indent) {
      indentStack.pop();
    }

    // If current indent > top, push (opening subproof)
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
/**
 * A line at index i is "available" from line at index j if:
 *   - lines[j].depth <= lines[i].depth (not inside a closed subproof relative to i)
 *   - lines[j] has not been discharged before i
 *
 * A subproof from line s to line e (depth d+1) is discharged at the →I or ¬I
 * line that cites it. After that point, individual lines within the subproof
 * are no longer available.
 *
 * We track discharged ranges: set of [start, end] pairs (by proofLineNo).
 */
function isAvailable(targetIdx, citedIdx, lines, dischargedRanges) {
  const cited  = lines[citedIdx];
  const target = lines[targetIdx];

  if (!cited || !target) return false;

  // Can't cite a future line
  if (cited.proofLineNo >= target.proofLineNo) return false;

  // Cited line must be at same depth or shallower — unless it's inside a
  // subproof that's still open (depth > target.depth means it's in a deeper
  // subproof that has NOT yet been discharged = still open)
  if (cited.depth > target.depth) return false;

  // Check if cited line has been discharged
  for (const [start, end] of dischargedRanges) {
    if (cited.proofLineNo >= start && cited.proofLineNo <= end) {
      // It's inside a discharged subproof — only allowed if this is the →I/¬I line itself
      return false;
    }
  }

  return true;
}

// ── Core validator ────────────────────────────────────────────────────────────
/**
 * Validate an array of parsed proof lines against a set of premises.
 * premises: AST[] — the sequent's premise list
 * Returns: results[], one per non-blank line, with { ok, error, proofLineNo, depth, formula, rule, citations }
 */
function validateProof(parsedLines, premises) {
  const lines          = buildStructure(parsedLines);
  const dischargedRanges = []; // [startProofLineNo, endProofLineNo]
  const results        = [];

  // Index lines by proofLineNo for fast lookup
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

  lines.forEach((line, idx) => {
    if (line.error) {
      results.push({ ...line, ok: false });
      return;
    }

    const { formula, rule, citations, ranges, depth, proofLineNo } = line;
    let ok = false;
    let errMsg = null;

    // Subproof ranges (m–n) are ONLY valid for →I and ¬I. Any other rule
    // that receives a dash range is a mistake.
    if (ranges && ranges.length && rule !== '→I' && rule !== '¬I') {
      results.push({ ...line, ok: false, error: `${rule} does not take a subproof range (m–n). Cite separate line numbers instead.` });
      return;
    }

    const citCheck = (count) => checkCitations(idx, citations, count);

    switch (rule) {

      case 'P': {
        // Must be an actual premise, depth 0, no citations
        const e = citCheck(0);
        if (e) { errMsg = e; break; }
        if (depth !== 0) { errMsg = 'Premises must be at the top level'; break; }
        // Check formula matches one of the premises
        const match = premises.some(p => astEqual(p, formula));
        if (!match) errMsg = formulaStr(formula) + ' is not a listed premise';
        else ok = true;
        break;
      }

      case 'A': {
        // Assumption — opens a subproof; no citations
        const e = citCheck(0);
        if (e) { errMsg = e; break; }
        if (depth === 0) { errMsg = 'Assumptions must be inside a subproof (indent the line)'; break; }
        // The previous line at depth-1 or this is the first line at this depth
        // Any formula is valid as an assumption
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
        // MP: need φ→ψ and φ, derive ψ. Citations can be in either order.
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
        // Subproof: cite range [m–n] where m is assumption (φ) and n is last line (ψ)
        // Result must be φ→ψ. A dash range is REQUIRED (not two bare line numbers).
        if (citations.length !== 0) { errMsg = `Use a dash for subproofs: write “→I ${citations[0]}–${citations[1] || citations[0]+1}”, not “→I ${citations.join(' ')}”.`; break; }
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
          // Discharge the subproof lines between assumeLine and lastLine
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
        // Cite: [d, c1, c2] where d is φ∨ψ, c1 is φ→χ, c2 is ψ→χ (any order among c1,c2)
        const e = citCheck(3);
        if (e) { errMsg = e; break; }
        const [n1, n2, n3] = citations;
        const l1 = getLine(n1), l2 = getLine(n2), l3 = getLine(n3);
        if (!l1 || !l2 || !l3) { errMsg = 'Citation not found'; break; }

        // Find the disjunction among the three cited lines
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

        // cond1 should be φ→χ or ψ→χ; match accordingly
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
        // Cite: [m, n] — one is φ, other is ¬φ; result is ⊥
        const e = citCheck(2);
        if (e) { errMsg = e; break; }
        if (formula.type !== 'bot') { errMsg = 'Result of ¬E must be ⊥'; break; }
        const a = getLine(citations[0]), b = getLine(citations[1]);
        if (!a || !b) { errMsg = 'Citation not found'; break; }
        // Find which is φ and which is ¬φ
        let phiLine, negLine;
        if (b.formula.type === 'neg' && astEqual(b.formula.arg, a.formula))
          { phiLine = a; negLine = b; }
        else if (a.formula.type === 'neg' && astEqual(a.formula.arg, b.formula))
          { phiLine = b; negLine = a; }
        else errMsg = `Lines ${citations[0]} and ${citations[1]} are not a formula and its negation`;
        if (phiLine) ok = true;
        break;
      }

      case '¬I': {
        // Subproof ending in ⊥: cite range [m–n] where m is assumption (φ), n is ⊥
        // Result: ¬φ. A dash range is REQUIRED (not two bare line numbers).
        if (citations.length !== 0) { errMsg = `Use a dash for subproofs: write “¬I ${citations[0]}–${citations[1] || citations[0]+1}”, not “¬I ${citations.join(' ')}”.`; break; }
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
        // From ⊥, derive anything
        const e = citCheck(1);
        if (e) { errMsg = e; break; }
        const src = getLine(citations[0]);
        if (!src) { errMsg = 'Citation not found'; break; }
        if (src.formula.type !== 'bot') errMsg = `Line ${citations[0]} must be ⊥`;
        else ok = true;
        break;
      }

      case 'DN': {
        // From ¬¬φ derive φ, or from φ derive ¬¬φ
        const e = citCheck(1);
        if (e) { errMsg = e; break; }
        const src = getLine(citations[0]);
        if (!src) { errMsg = 'Citation not found'; break; }
        // ¬¬φ → φ
        if (src.formula.type === 'neg' && src.formula.arg.type === 'neg'
            && astEqual(src.formula.arg.arg, formula)) { ok = true; break; }
        // φ → ¬¬φ
        if (formula.type === 'neg' && formula.arg.type === 'neg'
            && astEqual(formula.arg.arg, src.formula)) { ok = true; break; }
        errMsg = `DN requires ¬¬φ→φ or φ→¬¬φ`;
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
 * Parse proof text into raw line objects, then validate.
 * premises: string[] — raw formula strings from sequent input
 * Returns { lines: result[], complete: bool, error: string|null }
 */
function checkProof(proofText, premiseStrings, conclusionString) {
  // Parse premises
  const premises = [];
  for (const s of premiseStrings) {
    const t = s.trim();
    if (!t) continue;
    try { premises.push(parseFormula(t)); }
    catch (e) { return { lines: [], complete: false, error: `Cannot parse premise: ${t}` }; }
  }

  // Parse conclusion
  let conclusion = null;
  if (conclusionString && conclusionString.trim()) {
    try { conclusion = parseFormula(conclusionString.trim()); }
    catch (e) { return { lines: [], complete: false, error: `Cannot parse conclusion: ${conclusionString}` }; }
  }

  // Parse proof lines
  const rawLines = proofText.split('\n');
  const parsedLines = rawLines.map((l, i) => parseProofLine(l, i + 1));

  // Validate
  const results = validateProof(parsedLines, premises);

  // Check completeness: last non-blank line at depth 0 must match conclusion
  const mainLines = results.filter(l => l.depth === 0 && !l.blank);
  const lastMain  = mainLines[mainLines.length - 1];
  const allOk     = results.every(l => l.ok);

  let complete = false;
  if (allOk && conclusion && lastMain) {
    complete = astEqual(lastMain.formula, conclusion);
  }

  return { lines: results, complete, premises, conclusion };
}
