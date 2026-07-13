# Propositional Proof Checker — self-hosted copy

These files let you host the proof checker on its own GitHub Pages site so it
can be embedded in `<iframe>`s from your bookdown book.

The published copy at `https://prop-proof-checker.pplx.app/` works fine for
plain links, but it sends `X-Frame-Options: DENY` and
`content-security-policy: frame-ancestors 'none'`, so it **cannot be framed**.
Self-hosting removes that restriction. This mirrors how you already host the
model checker at `https://gabriel-uzquiano.github.io/model-checker/`.

## Setup (separate repo, mirroring your model-checker repo)

1. Create a new GitHub repository named `proof-checker` (under your account).
2. Copy these files to the **root** of that repo:
   ```
   index.html   style.css   app.js   parser.js   proof-engine.js   .nojekyll
   ```
3. In the repo, enable **Settings → Pages → Source: main branch / root**.
4. The checker goes live at:
   ```
   https://gabriel-uzquiano.github.io/proof-checker/
   ```

The asset paths in `index.html` are relative and the share-link origin is
dynamic, so no code changes are needed.

## .nojekyll

The `.nojekyll` file disables Jekyll processing on GitHub Pages. Keep it at
the repo root (included here). It prevents Jekyll from skipping files that
start with `_`.

## Point the helper at your hosted copy

In `R/proof_checker.R`, change `PC_BASE` to your hosted URL (keep the trailing
slash):

```r
PC_BASE <- "https://gabriel-uzquiano.github.io/proof-checker/"
```

Do this only after the repo is live, otherwise links 404. With it set,
`pc_link()` links resolve here and `pc_iframe()` / `pc_embed()` frames work.

## Using it inline

````markdown
`r pc_embed(proofs[["andI-worked"]], solution = TRUE)`
````

`pc_embed()` renders an inline `<iframe>` in HTML output and falls back to a
plain link in PDF output.
