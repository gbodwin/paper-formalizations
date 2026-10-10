# Greedy Algorithms for Shortcut Sets and Hopsets

**Status: source review and proof repairs in progress. No Lean theorem from this paper has yet been verified.**

Source: [arXiv:2511.20111v2](https://arxiv.org/abs/2511.20111v2), posted 26 April 2026.

The [source map](verification/source-scope.md) distinguishes the paper's original results from cited background and records the planned proof obligations. The [independent review](verification/independent-source-diagnostics.json) confirms two incorrect intermediate proof assertions, with exact finite examples. Neither is a counterexample to a main theorem.

- Section 2.2: the potential and its averaging denominator count different sets of pairs. An exact correction to the explanation of the cited BRR algorithm is recorded, but has not yet been formalized in Lean.
- Lemma 5.7's proof: a normalized-shortest valid path need not have normalized-shortest subpaths, even under the longest-shortest qualifier. The cubic potential-drop conclusion and the main theorem remain unresolved by this diagnostic.

Reproduce the finite diagnostics (Python 3 standard library only):

```sh
cd 'Greedy Algorithms for Shortcut Sets and Hopsets/verification'
python check_source_examples.py
python chain_potential_model.py
```

These executable checks support the source audit; they are not Lean kernel proofs. In particular, the example that refutes the hereditary-optimality step still satisfies the paper's cubic drop inequality in the tested instances.

No companion website has yet been published for this paper.
