# Remaining applications: source and partial-proof reconciliation

## Preserved implementation inventory

Read-only targeted fetch located `distance-sparsification-checkpoints` at `b7a01e2ebe0582fb5417af1bdafecdb0d27a4052`. Its partial implementations were not in the accepted +6 worktree. That branch is unchanged. Six files are recovered with exact upstream SHA256/size provenance in `recovered-source-manifest.json`:

| Partial module | Existing content | This checkpoint |
| --- | --- | --- |
| DirectedBasics | Actual directed-walk costs and infimum distances; triangle, reversal, optimal-path split | Recovered and strictly validated; remove unused instance binders and deprecated lemma spelling |
| DirectedTrees | Internally constructed in/out shortest-path trees, at most n arcs each | Recovered and strictly validated; remove one unused instance binder |
| DirectedExact | Actual half-demand construction and integer edge budget | Recovered byte-identically and strictly validated |
| DirectedComplete | Square-root rounding and complete amplification, empty/unreachable cases | Recovered and strictly validated; `letI` style repair only |
| ReachabilityBasics | Actual directed reachability; ordinary `SourcewiseBound` hypothesis; deduplicated indexed application and small-demand case | Recovered byte-identically; not compiled or accepted by this checkpoint |
| ReachabilityParameters | Floor parameter and conditional large-demand arithmetic | Recovered byte-identically; not compiled or accepted by this checkpoint |

The tie-breaking module `LinearDistancePreservers.ConsistentTiebreaking` is an unchanged required support dependency, byte-identical to the preserved branch. It is compiled/replayed only to validate this paper's directed proof; no other paper is developed or edited. All other accepted source/evidence is unchanged. No canceled external workspace is accessed.

The most advanced remaining obligation is the directed exact-distance endpoint: the preserved draft already contains the full construction, unlike reachability's still-conditional interface. This checkpoint validates that chain and adds `SlackSparsification.Directed.exists_exact_input_preserver`, explicitly restricting the output to actual ordered input arcs. It also proves that finite distance is equivalent to actual directed reachability. Aggregate imports remain at the reviewed +6 checkpoint; the new directed endpoint is imported directly by its separate verification entry point. The unvalidated reachability partials are not silently added to aggregate validation.

## Exact original statements and implemented scope

The preserved `source/extremallog.tex` (arXiv 2001.07741v3) states:

- Theorems 3–4: an n-node directed weighted graph and p demand pairs admit complete/slack distance preservers of O(n sqrt(p)) edges. The slack proof retains short paths and in/out trees rooted at a hitting set; amplification gives the complete result.
- Theorem 5.1: directed reachability preservation with O((np)^(2/3)+n) edges.
- Theorem 5.2: for P contained in S×V, the printed text says **distance** preserver with O(sqrt(nps)+n) edges.

The source-restricted citation is Abboud–Bodwin, *Reachability Preservers: New Extremal Bounds and Approximation Algorithms*. Its [Theorem 1, page 2](https://arxiv.org/pdf/1710.11250v3) states **reachability** preservation with O(n+sqrt(n|P||S|)) edges. The abstract states the same bound; the source separately discusses distance-preserver bounds. This confirms the already recorded C6 citation/type correction. The paper's Theorem 5.1 reduction needs only reachability. No counterexample to the stronger printed distance theorem is established here, and no false-theorem claim is made. The prior C1 triangle-inequality proof repair likewise must not be relabeled as a false final theorem.

`SourcewiseBound K A C` precisely supplies reachability for arbitrary source-restricted demand subsets at a uniform constant C. It is an ordinary hypothesis, not an axiom and not yet constructed. There is no completed reachability slack/complete module in the recovered branch. The remaining reachability work includes that actual reduction and either a proved sourcewise premise or an explicitly bounded conditional result; this checkpoint does not erase the premise or add runtime work.

The validated directed model uses a finite vertex type, an ambient undirected simple graph K for walks, and an independent relation A orienting allowed arcs. This represents arbitrary loopless directed adjacency, for example with K complete. Weights are **nonnegative real numbers**, including zero; no symmetry is imposed on arc weights or A. Distances are infima of actual directed walk costs in extended nonnegative reals, with infinity for unreachable pairs. The new wrapper returns a finite subset of `{(u,v) | K.Adj u v ∧ A u v}` and preserves exact distance on all demands, with explicit edge bound

```text
(14*n / (1 - (1/2 : ℝ)^(1/2 : ℝ))) * (p : ℝ)^(1/2 : ℝ).
```

The original text's word “weighted” does not state a sign convention in this theorem paragraph. This checkpoint explicitly certifies the nonnegative-weight model; it does not silently claim a signed-weight, negative-cycle, parallel-edge or self-loop normalization theorem. Empty vertex types, empty demand sets, unreachable demands, and zero weights are included in the proved model. No shortest paths, tree-existence oracle, successful sample, or preserver constructor is assumed by the complete endpoint. The result is mathematical existence, not an executable polynomial-time algorithm. Runtime, optional extensions, websites, and whole-paper completion remain outside this checkpoint.
