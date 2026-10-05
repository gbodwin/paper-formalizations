# Bodwin paper formalizations

Lean 4 formalizations accompanying papers by Greg Bodwin and collaborators.

This is an initial, partial formalization. The only paper currently represented
is Bodwin–Patel (2019), *A Trivial Yet Optimal Solution to Vertex Fault Tolerant
Spanners*: [arXiv:1812.05778v2](https://arxiv.org/abs/1812.05778v2).
The main spanner-size theorem has not been formalized.

## Current coverage

| Paper statement | Lean declaration | Coverage |
| --- | --- | --- |
| Definition 3: vertex blocking set | `BodwinPapers.VFTSpanners.IsBlockingSet` | Definition |
| Lemma 4: sampled graph and edge deletion | `BodwinPapers.VFTSpanners.prunedGraph` | Construction |
| Lemma 4: deletion eliminates short cycles | `BodwinPapers.VFTSpanners.prunedGraph_no_short_cycle` | Proof of deterministic step |
| Equivalent cycle-length inequality | `BodwinPapers.VFTSpanners.prunedGraph_cycle_length_gt` | Proof of deterministic step |
| Lemma 3: greedy output admits a small blocking set | — | Planned |
| Lemma 4: exact fixed-size edge and blocker survival counts | `sum_sampled_edges`, `sum_sampled_blockers` | Complete finite counts |
| Lemma 4: expectation lower bound and a dense high-girth sample | `sum_retained_edges_bound`, `exists_dense_high_girth_sample` | Exact finite binomial bound, for `3 ≤ r ≤ n` |
| Lemma 4: specialize `r = ceil(n/(2f))` and derive asymptotic bounds | — | Planned |
| Theorem 1 and Corollary 2 | — | Planned |

See [the statement map](docs/statement-map.md) for the exact scope and
[verification](docs/verification.md) for the checked version and results.

## Build

Install Lean using the [official setup guide](https://lean-lang.org/install/),
then run these commands from this directory:

```sh
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
```

The `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin Lean and all
resolved dependencies. Lean is pinned to 4.34.0, with the matching mathlib
release pinned by commit. Upgrading these pins requires rebuilding the project.

GitHub Actions builds the default library, checks that its module index is
complete, and audits all declarations under `BodwinPapers`. The axiom allowlist
is Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; proof holes
and additional axioms cause the audit to fail. A green build checks the encoded
statements; the source-to-statement correspondence still needs mathematical
review.

## Adding another paper

Use `BodwinPapers/<PaperName>/` for proofs and update the root module imports.
Add a versioned paper link and a row-by-row statement map. Mark complete proofs,
partial results, and planned work accurately. Cite the paper authors separately
from the formalization contributors. Only completed proofs belong in the build;
record remaining statements in documentation rather than proof placeholders.

## License and attribution

The proposed license for the new formalization code is MIT (see `LICENSE`).
Paper copyrights and dependency licenses remain with their respective authors.
This repository links to papers rather than redistributing their PDFs or LaTeX.
