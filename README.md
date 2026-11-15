### The Matrix Cookbook, using Lean's mathlib

This repository aims to provide the lemmas in [The Matrix Cookbook](https://www.math.uwaterloo.ca/~hwolkowi/matrixcookbook.pdf) (November 15, 2012) as proofs in the Lean theorem prover.

Ideally, every proof in this repository should be a reference to a single lemma in [Mathlib](https://github.com/leanprover-community/mathlib4/), the maths library for lean.

The progress bar below shows the state of this repository; green represents lemmas which are proven, yellow lemmas which are stated, red lemmas which are ready to be stated, and dark red for entire missing sections.
Clicking on the progress bar will take you to a version that links to each lemma.

[![](https://eric-wieser.github.io/lean-matrix-cookbook/progress_bar.svg)](https://eric-wieser.github.io/lean-matrix-cookbook/progress_bar.svg)

### Website

The chapters are also rendered as a [literate website](https://eric-wieser.github.io/lean-matrix-cookbook/) with [Verso](https://github.com/leanprover/verso), showing each cookbook equation alongside its Lean statement and proof.
CI publishes it to GitHub Pages on every push to `master`, next to the progress bar.
To build it locally:

```
lake build :literateHtml
```

The site is written to `.lake/build/literate-html/`. `literate.toml` controls which chapters are included; currently only chapter 1 (`MatrixCookbook/1Basic.lean`) is published.
Prose and equations live in the Lean files themselves, as Verso-syntax module comments (`/-! -/`) and docstrings (`set_option doc.verso true`), with LaTeX written as ``$`...` `` (inline) or ``$$`...` `` (display).
Text quoted from the cookbook is written as a blockquote (`> ...`); everything else is commentary on the formalization.
Styling, including the two-column layout on wide screens, is in `site/cookbook.css`.
`site/cookbook.js` flags theorems that are unproved (the proof uses `sorry`), and cookbook equations that are not yet stated (equation `(n)` has no `eq_n` theorem), matching the progress bar's statuses. Verso does not notice changes to that file, so delete `.lake/build/literate-html` before rebuilding after editing it.

Verso and Mathlib must be on matching Lean versions, so bump the `verso` tag in `lakefile.toml` alongside Mathlib.
