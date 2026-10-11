# A Note on Distance-Preserving Graph Sparsification

Greg Bodwin. Information Processing Letters (2022).
Source: https://arxiv.org/abs/2001.07741v3 (7 May 2021).
Site: https://paperlab-distance-sparsification.greg-bodwin.chatgpt.site

Selected on 11 October 2026 after checking all nine existing Sites, accessible
GitHub repositories, the full main tree, and all repository branches. No prior
Site or Lean project for this paper was found.

## Certified milestone

Commit `d5dcafc28b31457b3e80a9cb6c58dde4ec37172f` passed compilation,
the declaration-wide axiom audit (78 declarations), and separate official
Lean kernel replay:
https://github.com/gbodwin/paper-formalizations/actions/runs/38143822607

This milestone proves the main amplification lemma, the graph neighborhood
lemma, and an actual +2 slack construction with explicit integer cost bounds.
It also proves a finite weighted-expectation witness lemma and an actual graph
counterexample to a printed equality. The complete +2 theorem is the next
checkpoint. This is not yet a certification of all five graph applications.
See `PROOF_COVERAGE.md` for statement-level scope and `CORRECTIONS.md` for repairs.

## Reproduce

Use the root repository's pinned Lean 4.34.0 and mathlib revision.

```sh
lake build SlackSparsification
lake env lean 'A Note on Distance-Preserving Graph Sparsification/verification/Audit.lean'
for file in 'A Note on Distance-Preserving Graph Sparsification/SlackSparsification/'*.lean; do
  module="SlackSparsification.$(basename "$file" .lean)"
  lake env leanchecker -v "$module"
done
```

The audit permits only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof holes, new axioms, or `native_decide` certificates.
The supplied finite witnesses use ordinary kernel-checked proofs.
The repository-wide module index, axiom audit and kernel script include this library.

The local container denies the Lean runtime's per-process executable lookup.
Unmodified GitHub Actions provides the compiler and checker; no kernel or
runtime patch is used. Checkpoint commits are preserved even when a new draft
fails; always use the exact certified commit above for a verified release.

## Source and reading edition

`source/extremallog.tex` and `source/extremallog.bbl` preserve arXiv v3.
`source/corrected-reading.tex` applies the explicitly marked C1 repair.
The Site retains the full paper, mathematical notation, references and original
retraction notice, with editorial notes beside the relevant statements.
The author already retracted the earlier all-pairs +4 claim in v3; this is not
presented as a new finding.
