# Greedy Algorithms for Shortcut Sets and Hopsets

**Status: preliminary arithmetic and a generic greedy framework are verified locally; no graph-level main theorem is complete.**

Source: [arXiv:2511.20111v2](https://arxiv.org/abs/2511.20111v2), posted 26 April 2026.

The [source map](verification/source-scope.md) distinguishes the paper's original results from cited background and records the planned proof obligations. The [independent review](verification/independent-source-diagnostics.json) confirms two incorrect intermediate proof assertions, with exact finite examples. Neither is a counterexample to a main theorem.

- Section 2.2: the potential and its averaging denominator count different sets of pairs. An exact correction to the explanation of the cited BRR algorithm is recorded; only its rounding/counting arithmetic is formalized so far.
- Lemma 5.7's proof: a normalized-shortest valid path need not have normalized-shortest subpaths, even under the longest-shortest qualifier. The cubic potential-drop conclusion and the main theorem remain unresolved by this diagnostic.

Reproduce the finite diagnostics (Python 3 standard library only):

```sh
cd 'Greedy Algorithms for Shortcut Sets and Hopsets/verification'
python check_source_examples.py
python chain_potential_model.py
```

These executable checks support the source audit; they are not Lean kernel proofs. In particular, the example that refutes the hereditary-optimality step still satisfies the paper's cubic drop inequality in the tested instances.

No companion website has yet been published for this paper.

## Initial Lean coverage

- `RecapArithmetic`: exact end offsets, old/new distance-index inequalities, rectangle cardinality and the conditional insertion-count bound for the corrected explanation of the cited BRR rule.
- `FinitePotential`: a monotone natural potential with relative progress halves in an exact integer block, obeys a dyadic bound, and eventually vanishes.
- `FiniteGreedy`: an actual finite minimum-new-potential insertion run, its maximum-drop property, termination, stability after zero potential, and output-cardinality bounds under an explicit relative-progress interface.

These are preliminary components with explicit graph-specific interface obligations. The graph-level potential-progress inequality, actual greedy algorithms, the three main theorems and the chain-proof repair remain incomplete.

On 10 October 2026 all three modules and the root import compiled under Lean 4.34.0; all 80 defining-module declarations passed the standard-axiom audit, and all three modules passed sequential kernel replay. See the [local verification record](verification/local-result.json). Full exact-commit repository CI is tracked separately; a local pass is not a claim that an unfinished CI run has passed.
