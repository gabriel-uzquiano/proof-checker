/**
 * App logic for the Propositional Logic Proof Checker.
 */

// ── DOM refs ──────────────────────────────────────────────────────────────────
const premisesInput    = document.getElementById('premises-input');
const conclusionInput  = document.getElementById('conclusion-input');
const proofTextarea    = document.getElementById('proof-textarea');
const outputPanel      = document.getElementById('output-panel');
const sequentDisplay   = document.getElementById('sequent-display');
const completionBanner = document.getElementById('completion-banner');
const premisesStatus   = document.getElementById('premises-status');
const conclusionStatus = document.getElementById('conclusion-status');
const copyLinkBtn      = document.getElementById('copy-link-btn');

// ── Helpers ───────────────────────────────────────────────────────────────────
function escHtml(s) {
  return String(s)
    .replace(/&/g,'&amp;')
    .replace(/</g,'&lt;')
    .replace(/>/g,'&gt;')
    .replace(/"/g,'&quot;');
}

function formulaDisplay(ast) {
  if (!ast) return '';
  if (ast.type === 'bot') return '⊥';
  return prettyPrint(ast, true);
}

// ── Symbol insertion ──────────────────────────────────────────────────────────
// The Proof-card toolbar always inserts into the proof textarea.
function insertSym(sym) {
  insertInto(proofTextarea, sym);
}

function insertInto(el, sym) {
  const start = el.selectionStart;
  const end   = el.selectionEnd;
  el.value = el.value.slice(0, start) + sym + el.value.slice(end);
  el.selectionStart = el.selectionEnd = start + sym.length;
  el.focus();
  el.dispatchEvent(new Event('input'));
}

// ── Tab key: insert spaces in textarea ───────────────────────────────────────
proofTextarea.addEventListener('keydown', (e) => {
  if (e.key === 'Tab') {
    e.preventDefault();
    const start = proofTextarea.selectionStart;
    const end   = proofTextarea.selectionEnd;
    // If selection spans multiple lines, indent each line
    if (start !== end && proofTextarea.value.slice(start, end).includes('\n')) {
      const lines = proofTextarea.value.split('\n');
      let charCount = 0;
      let startLine = 0, endLine = 0;
      for (let i = 0; i < lines.length; i++) {
        if (charCount <= start) startLine = i;
        if (charCount < end)    endLine = i;
        charCount += lines[i].length + 1;
      }
      const indent = e.shiftKey ? '' : '  ';
      const newLines = lines.map((ln, i) => {
        if (i < startLine || i > endLine) return ln;
        if (e.shiftKey) return ln.startsWith('  ') ? ln.slice(2) : ln;
        return indent + ln;
      });
      proofTextarea.value = newLines.join('\n');
      proofTextarea.dispatchEvent(new Event('input'));
    } else {
      // Insert 2-space indent at cursor
      const spaces = e.shiftKey ? '' : '  ';
      proofTextarea.value = proofTextarea.value.slice(0, start) + spaces + proofTextarea.value.slice(end);
      proofTextarea.selectionStart = proofTextarea.selectionEnd = start + spaces.length;
      proofTextarea.dispatchEvent(new Event('input'));
    }
  }
});

// ── Sequent display (pretty-printed to match the textbook) ─────────────────────
function tryParseFormula(s) {
  if (!s.trim()) return null;
  try { return parseFormula(s); }
  catch (e) { return { error: e.message || String(e) }; }
}

function prettyOrRaw(s) {
  const ast = tryParseFormula(s);
  if (!ast) return s;
  if (ast.error) return s;
  return formulaDisplay(ast);
}

function updateSequentDisplay() {
  const premStrs = premisesInput.value.split(',').map(s => s.trim()).filter(Boolean);
  const concStr  = conclusionInput.value.trim();
  if (!premStrs.length && !concStr) {
    sequentDisplay.textContent = '';
    return;
  }
  const premPretty = premStrs.map(prettyOrRaw).join(', ');
  const concPretty = concStr ? prettyOrRaw(concStr) : '?';
  sequentDisplay.textContent = (premPretty || '—') + '  ⊢  ' + concPretty;
}

// ── Live parse feedback for the sequent inputs ────────────────────────────────
function setFieldStatus(input, statusEl, ok, msg) {
  input.classList.toggle('valid', ok && msg);
  input.classList.toggle('invalid', !ok && msg !== '');
  statusEl.textContent = msg;
  statusEl.classList.toggle('ok', ok && msg);
  statusEl.classList.toggle('err', !ok && msg);
}

function updateParseStatus() {
  // Premises: parse each comma-separated formula
  const premStrs = premisesInput.value.split(',').map(s => s.trim()).filter(Boolean);
  if (!premStrs.length) {
    setFieldStatus(premisesInput, premisesStatus, true, '');
  } else {
    const parsed = premStrs.map(tryParseFormula);
    const firstErr = parsed.find(p => p && p.error);
    if (firstErr) {
      setFieldStatus(premisesInput, premisesStatus, false, '✗ ' + firstErr.error);
    } else {
      setFieldStatus(premisesInput, premisesStatus, true, '✓ ' + parsed.map(formulaDisplay).join(',  '));
    }
  }
  // Conclusion
  const concStr = conclusionInput.value.trim();
  if (!concStr) {
    setFieldStatus(conclusionInput, conclusionStatus, true, '');
  } else {
    const ast = tryParseFormula(concStr);
    if (ast && ast.error) setFieldStatus(conclusionInput, conclusionStatus, false, '✗ ' + ast.error);
    else setFieldStatus(conclusionInput, conclusionStatus, true, '✓ ' + formulaDisplay(ast));
  }
}

// ── Main live checking ────────────────────────────────────────────────────────
function run() {
  updateSequentDisplay();
  updateParseStatus();

  const proofText = proofTextarea.value;
  const premStrs  = premisesInput.value.split(',').map(s => s.trim()).filter(Boolean);
  const concStr   = conclusionInput.value.trim();

  if (!proofText.trim()) {
    outputPanel.innerHTML = '<div class="output-empty">Enter a proof above to check it.</div>';
    completionBanner.hidden = true;
    return;
  }

  const { lines, complete, error } = checkProof(proofText, premStrs, concStr);

  if (error) {
    outputPanel.innerHTML = `<div class="output-error">⚠ ${escHtml(error)}</div>`;
    completionBanner.hidden = true;
    return;
  }

  // Render Fitch-style output
  outputPanel.innerHTML = renderFitch(lines);

  // Completion banner
  completionBanner.hidden = !complete;
}

// ── Fitch-style renderer ──────────────────────────────────────────────────────
// Builds a proper Fitch column with:
//   • Vertical scope bars (│) for each nesting level
//   • Horizontal bar below each assumption (─── scope header)
//   • Green bg + ✓ for ok lines, red-tinted bg + ✗ + error message for errors
function renderFitch(lines) {
  if (!lines.length) return '<div class="output-empty">Enter a proof above to check it.</div>';

  // We need to track open subproofs to draw scope lines and assumption separators.
  // A subproof "opens" at an A line (depth d), and "closes" when depth drops back.
  // We draw a horizontal bar after each A line.

  const maxDepth = lines.reduce((m, l) => Math.max(m, l.depth), 0);

  let html = '<div class="fitch-proof">';

  lines.forEach((line, idx) => {
    const { ok, depth, proofLineNo, rule, citations, ranges, formula, error } = line;
    const cls     = ok ? 'fitch-line ok' : 'fitch-line err';
    const icon    = ok ? '✓' : '✗';
    const iconCls = ok ? 'fitch-icon ok' : 'fitch-icon err';

    // Scope bar rendering: for each depth level 0..maxDepth,
    // draw a │ if that depth is currently active (open subproof),
    // or a space if not.
    // For a line at depth d, depths 1..d are active.
    // Depth 0 = main proof (no bar). Depths 1..line.depth have a bar.
    let barsHtml = '';
    for (let d = 1; d <= maxDepth; d++) {
      if (d <= depth) {
        barsHtml += `<span class="fitch-bar-seg fitch-bar-active"></span>`;
      } else {
        barsHtml += `<span class="fitch-bar-seg fitch-bar-empty"></span>`;
      }
    }

    // Formula
    const formulaHtml = escHtml(formulaDisplay(formula));

    // Justification — render subproof ranges as “m–n", plain citations as a list
    let citeStr = '';
    if (ranges && ranges.length) {
      citeStr = ranges.map(r => `${r.m}–${r.n}`).join(', ');
    } else if (citations && citations.length) {
      citeStr = citations.join(', ');
    }
    const justHtml = rule
      ? escHtml(rule) + (citeStr ? `<span class="fitch-cite"> ${escHtml(citeStr)}</span>` : '')
      : '';

    const tooltip = (!ok && error) ? ` title="${escHtml(error)}"` : '';

    html += `
      <div class="${cls}"${tooltip} style="--cur-depth:${depth}">
        <span class="fitch-lineno">${proofLineNo}</span>
        <span class="fitch-bars">${barsHtml}</span>
        <span class="fitch-formula">${formulaHtml}</span>
        <span class="fitch-just">${justHtml}</span>
        <span class="${iconCls}">${icon}</span>
        ${!ok && error ? `<div class="fitch-errmsg">${escHtml(error)}</div>` : ''}
      </div>`;

    // Horizontal separator after the final premise (textbook draws a line
    // under the premises). Trigger on the last consecutive P line at depth 0.
    if (rule === 'P' && depth === 0) {
      const next = lines[idx + 1];
      if (!next || !(next.rule === 'P' && next.depth === 0)) {
        html += `<div class="fitch-premise-sep"></div>`;
      }
    }

    // Horizontal separator after assumptions
    if (rule === 'A') {
      html += `<div class="fitch-assume-sep" style="--bar-depth: ${depth}"></div>`;
    }
  });

  html += '</div>';
  return html;
}

// ── Examples ──────────────────────────────────────────────────────────────────
// Two banks: (1) RULE_ILLUSTRATIONS — one minimal example per rule, labelled by
// rule name; (2) PROOF_EXAMPLES — worked sequents from the textbook (§5.1–5.12),
// labelled by the sequent itself.
const RULE_ILLUSTRATIONS = [
  { label: 'Repetition', premises: 'p', conclusion: 'p',
    proof:
`p   P
p   R  1` },
  { label: '∧I', premises: 'p, q', conclusion: 'p∧q',
    proof:
`p    P
q    P
p∧q  ∧I  1, 2` },
  { label: '∧E', premises: 'p∧q', conclusion: 'p',
    proof:
`p∧q  P
p    ∧E  1` },
  { label: '→I', premises: 'p', conclusion: 'q→p',
    proof:
`p    P
  q  A
  p  R  1
q→p  →I  2–3` },
  { label: '→E', premises: 'p→q, p', conclusion: 'q',
    proof:
`p→q  P
p    P
q    →E  1, 2` },
  { label: '∨I', premises: 'p', conclusion: 'p∨q',
    proof:
`p    P
p∨q  ∨I  1` },
  { label: '∨E', premises: 'p∨q, p→r, q→r', conclusion: 'r',
    proof:
`p∨q  P
p→r  P
q→r  P
r    ∨E  1, 2, 3` },
  { label: '¬I', premises: 'p, ¬p', conclusion: '¬q',
    proof:
`p    P
¬p   P
  q  A
  ⊥  ¬E  1, 2
¬q   ¬I  3–4` },
  { label: '¬E', premises: 'p, ¬p', conclusion: '⊥',
    proof:
`p    P
¬p   P
⊥    ¬E  1, 2` },
  { label: 'EFSQ', premises: 'p, ¬p', conclusion: 'q',
    proof:
`p    P
¬p   P
⊥    ¬E  1, 2
q    EFSQ  3` },
  { label: 'DN', premises: '¬¬p', conclusion: 'p',
    proof:
`¬¬p  P
p    DN  1` },
];

const PROOF_EXAMPLES = [
  {
    label: 'Repetition',
    premises: 'p',
    conclusion: 'p',
    proof:
`p   P
p   R  1`,
  },
  {
    label: '∧I',
    premises: 'p, q, r',
    conclusion: 'p∧(r∧q)',
    proof:
`p       P
q       P
r       P
r∧q     ∧I  3, 2
p∧(r∧q) ∧I  1, 4`,
  },
  {
    label: '∧E',
    premises: 'p∧(r∧q)',
    conclusion: 'r',
    proof:
`p∧(r∧q)  P
r∧q      ∧E  1
r        ∧E  2`,
  },
  {
    label: '→E',
    premises: 'p, p→(q∧r), q→(s∧t)',
    conclusion: 'r∧t',
    proof:
`p        P
p→(q∧r)  P
q→(s∧t)  P
q∧r      →E  2, 1
q        ∧E  4
s∧t      →E  3, 5
t        ∧E  6
r        ∧E  4
r∧t      ∧I  8, 7`,
  },
  {
    label: '→I ⊢ p→(r∧q)',
    premises: 'p→(q∧r)',
    conclusion: 'p→(r∧q)',
    proof:
`p→(q∧r)  P
  p      A
  q∧r    →E  1, 2
  r      ∧E  3
  q      ∧E  3
  r∧q    ∧I  4, 5
p→(r∧q)  →I  2–6`,
  },
  {
    label: '→I ⊢ p→q',
    premises: 'p∧q',
    conclusion: 'p→q',
    proof:
`p∧q  P
  p  A
  q  ∧E  1
p→q  →I  2–3`,
  },
  {
    label: '∨E',
    premises: '(p∧q)∨(q∧p)',
    conclusion: 'p',
    proof:
`(p∧q)∨(q∧p)  P
  p∧q  A
  p    ∧E  2
(p∧q)→p      →I  2–3
  q∧p  A
  p    ∧E  5
(q∧p)→p      →I  5–6
p            ∨E  1, 4, 7`,
  },
  {
    label: '¬I ⊢ ¬¬p',
    premises: 'p',
    conclusion: '¬¬p',
    proof:
`p   P
  ¬p  A
  ⊥   ¬E  1, 2
¬¬p   ¬I  2–3`,
  },
  {
    label: '¬I ⊢ ¬p',
    premises: 'p→q, ¬q',
    conclusion: '¬p',
    proof:
`p→q  P
¬q   P
  p  A
  q  →E  1, 3
  ⊥  ¬E  4, 2
¬p   ¬I  3–5`,
  },
  {
    label: 'DS',
    premises: 'p∨q, ¬p',
    conclusion: 'q',
    proof:
`p∨q  P
¬p   P
  p   A
  ⊥   ¬E  3, 2
  q   EFSQ  4
p→q  →I  3–5
  q   A
  q   R  7
q→q  →I  7–8
q    ∨E  1, 6, 9`,
  },
  {
    label: 'EFSQ',
    premises: '¬p',
    conclusion: 'p→q',
    proof:
`¬p  P
  p  A
  ⊥  ¬E  2, 1
  q  EFSQ  3
p→q  →I  2–4`,
  },
  {
    label: 'DN',
    premises: '',
    conclusion: 'p∨¬p',
    proof:
`  ¬(p∨¬p)  A
    p      A
    p∨¬p   ∨I  2
    ⊥      ¬E  3, 1
  ¬p       ¬I  2–4
  p∨¬p     ∨I  5
  ⊥        ¬E  6, 1
¬¬(p∨¬p)   ¬I  1–7
p∨¬p       DN  8`,
  },
];

function loadExample(ex) {
  if (!ex) return;
  premisesInput.value   = ex.premises;
  conclusionInput.value = ex.conclusion;
  proofTextarea.value   = ex.proof;
  run();
}

function sequentLabel(ex) {
  return ex.premises ? ex.premises + ' ⊢ ' + ex.conclusion : '⊢ ' + ex.conclusion;
}

function buildExampleButtons() {
  const rulesHost  = document.getElementById('rules-row');
  const proofsHost = document.getElementById('proofs-row');
  if (rulesHost) {
    RULE_ILLUSTRATIONS.forEach((ex) => {
      const btn = document.createElement('button');
      btn.className = 'example-btn';
      btn.textContent = ex.label;
      btn.onclick = () => loadExample(ex);
      rulesHost.appendChild(btn);
    });
  }
  if (proofsHost) {
    PROOF_EXAMPLES.forEach((ex) => {
      const btn = document.createElement('button');
      btn.className = 'example-btn example-btn--proof';
      btn.textContent = sequentLabel(ex);
      btn.onclick = () => loadExample(ex);
      proofsHost.appendChild(btn);
    });
  }
}

// ── Event listeners ───────────────────────────────────────────────────────────
proofTextarea.addEventListener('input', run);
premisesInput.addEventListener('input', run);
conclusionInput.addEventListener('input', run);

// ── Theme toggle ──────────────────────────────────────────────────────────────
document.querySelector('[data-theme-toggle]').addEventListener('click', () => {
  const html = document.documentElement;
  html.setAttribute('data-theme', html.getAttribute('data-theme') === 'dark' ? 'light' : 'dark');
});

// ── Help panel ────────────────────────────────────────────────────────────────
function toggleHelp(e) {
  e.preventDefault();
  const panel = document.getElementById('help-panel');
  panel.hidden = !panel.hidden;
}

// ── Share / load a proof via the URL hash ─────────────────────────────────────
// Encode the sequent + proof in the page hash so a link reloads the exact proof.
function shareProof() {
  const params = new URLSearchParams();
  if (premisesInput.value)   params.set('p', premisesInput.value);
  if (conclusionInput.value) params.set('c', conclusionInput.value);
  if (proofTextarea.value)   params.set('pr', proofTextarea.value);
  const url = location.origin + location.pathname + '#' + params.toString();
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(url).then(
      () => flashShare('Copied!'),
      () => flashShare('Link ready — see address bar')
    );
  } else {
    flashShare('Link ready');
  }
  history.replaceState(null, '', url);
}

function flashShare(msg) {
  if (!copyLinkBtn) return;
  const original = copyLinkBtn.textContent;
  copyLinkBtn.textContent = msg;
  copyLinkBtn.classList.add('shared');
  setTimeout(() => {
    copyLinkBtn.textContent = original;
    copyLinkBtn.classList.remove('shared');
  }, 1800);
}

function loadFromHash() {
  if (!location.hash || location.hash.length < 2) return false;
  const params = new URLSearchParams(location.hash.slice(1));
  if (!params.has('p') && !params.has('c') && !params.has('pr')) return false;
  premisesInput.value   = params.get('p') || '';
  conclusionInput.value = params.get('c') || '';
  proofTextarea.value   = params.get('pr') || '';
  return true;
}

if (copyLinkBtn) copyLinkBtn.addEventListener('click', shareProof);

// ── Init ──────────────────────────────────────────────────────────────────────
// Keep the focused input's caret when a symbol button is clicked (prevent the
// button from stealing focus), so insertion lands in the field the user was editing.
document.querySelectorAll('.sym-btn').forEach((b) => {
  b.addEventListener('mousedown', (e) => e.preventDefault());
});
buildExampleButtons();
loadFromHash();
run();
