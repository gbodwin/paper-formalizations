# Greedy Algorithms for Shortcut Sets and Hopsets

**Status: the unweighted directed-graph greedy algorithm is formalized and locally checked for termination, legal shortcuts, reachability preservation, and final hopbound. The main size theorems remain incomplete.**

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

- `DirectedPaths`: native directed walks, consistent shortest paths, true minimum hop distance, and preservation of original reachability under closure-edge insertion. The tiebreaking construction imports an already-proved local library theorem.
- `GraphGreedy`: Algorithm 1 instantiated on its actual unweighted graph potential. Strict progress, termination, reachability preservation, final hopbound, the elementary quadratic size bound, and the cubic initial-potential bound are proved. The sharper relative-progress bound remains an explicit obligation.
- `ShortcutWalk`: replaces an actual path segment by an added directed edge. For an active demand of length greater than β≥4, constructs exactly (⌊β/4⌋+1)² distinct legal edges, each of which reduces that demand to at most β hops.

- `FiniteCharging`: rigorous finite double counting of individual demand repairs, and the exact integer relative-progress denominator.
- `WarmupUnweighted`: the warm-up size bound for the actual unweighted greedy output, with no graph-progress premise left open. For β≥4 its size is at most `(Nat.log 2 (n^3) + 1) * (n^2 / (β/4 + 1)^2 + 1)`, with natural-number divisions.

The stronger DAG potential-progress inequality, weighted hopset model, the three main size theorems, Algorithm 2, and the chain-proof repair remain incomplete.

The previous three-module checkpoint, [6ec5346](https://github.com/gbodwin/paper-formalizations/commit/6ec5346f9ac563208f19642addf6767e09a1aab8), passed [full repository CI](https://github.com/gbodwin/paper-formalizations/actions/runs/38056710539), including all-declaration audit and independent kernel replay. The newer graph checkpoint's local results are recorded separately in [the verification record](verification/local-result.json); local checks do not assert that a pending exact-commit CI run has passed.
