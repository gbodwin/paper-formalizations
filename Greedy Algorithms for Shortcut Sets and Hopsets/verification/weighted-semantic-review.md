# Weighted greedy semantic review

Reviewed commit: `ab4679bfa4283119c80b4dd2a67cea536300fc56` on `greedy-shortcuts-verification-20261010`.

## Verdict

No new semantic defect found within the explicitly stated finite directed, nonnegative-real-weight scope. The actual weighted greedy correctness and rounded logarithmic Section 2.1 warm-up claim are supported by the reviewed definitions and proof structure. This does not certify the three incomplete main theorems or the undirected setting.

## Main checks

- **Heavy parallel edges:** `WeightedHopDistance.lean:114-138` changes original weights only on explicitly inserted ordered pairs. `149-211` expands closure edges into original walks and proves exact distance preservation. Collapsing the newly inserted cheaper parallel edge and its dominated original representative is semantically sound for shortest costs and minimum hop counts.
- **Walks versus paths:** `WeightedPaths.lean:92-102` quantifies shortestness over all native allowed walks; `147-152` proves minimum-hop shortest walks are simple even with zero-cost cycles. Native walks ignore self-loop steps, which are immaterial to this nonnegative, hop-minimal objective. Unreachable zero sentinels in `WeightedHopDistance.lean:32-52` are protected by reachability and candidate restrictions.
- **Perturbation:** `WeightedPerturbation.lean:23-40,97-129` builds one actual positive edge weighting for all endpoint pairs. Original cost precedes hop count; injective edge coding breaks remaining ties. `WeightedPaths.lean:154-172` extends uniqueness from simple paths to walks. This proves the covered version of Lemma 4.2 by deterministic finite perturbation rather than the source's random construction (`source/tex/content/greg.tex:328-346`).
- **Actual greedy rule:** `GraphGreedy.lean:18` uses contribution d for d > beta, not excess above beta. `WeightedGreedy.lean:13-88` instantiates the genuine empty-start finite greedy run. `FiniteGreedy.lean:25-60,86-149` proves optimal next-potential selection, maximum drop, fresh insertions, termination, and stationary output after zero potential. It matches Algorithm 1 (`source/tex/content/intro.tex:140-152`).
- **Quantitative warm-up:** `ShortcutWalk.lean:68-109` counts exactly (floor(beta/4)+1)^2 legal repair candidates. `WeightedShortcut.lean:28-78` proves the replacement remains weighted-shortest. `WarmupWeighted.lean:17-90` and `FiniteCharging.lean:13-52` discharge actual demand charging and graph progress, then use the true greedy choice and finite dyadic decay. `WarmupWeighted.lean:94-109` proves the explicit bound `(Nat.log 2 (n^3) + 1) * (16*n^2 / beta^2 + 1)` for every integer beta >= 1, including small targets. This is a valid exact-rounded variation on Section 2.1's first/last-third proof (`source/tex/content/greg.tex:15-50`), with no remaining quantitative graph-progress hypothesis.
- **Bounded horizon:** `FiniteHorizon.lean:43-66` retains both the pre-budget progress condition and k*D <= M explicitly; it does not assume the open main graph estimate.

All Lean paths above are relative to `Greedy Algorithms for Shortcut Sets and Hopsets/GreedyShortcuts/`.

## Keep the stated boundaries

1. The source merely says weighted; the proved domain is nonnegative real weights. No broader negative-edge or negative-cycle interpretation is established.
2. Directed ordered-pair insertions do not constitute the undirected greedy algorithm even on a symmetric input. Symmetric insertion and edge-budget translation remain necessary.
3. The stronger DAG, existentially optimal weighted, and chain size results remain incomplete. Noncomputable finite choice establishes a mathematical run, not a runtime bound. The rounded bound is not itself a formal asymptotic Big-O theorem.
4. The two documented source diagnostics were treated as known and are not new findings.

## Verification boundary

Read committed blobs at the exact checkpoint rather than concurrently edited working files. All 20 source hashes match the committed local verification manifest. Compilation, the reported 384-declaration axiom audit, and sequential kernel replay were not rerun, as requested. Exact-commit CI was not checked here and remains separate. Uncommitted `WeightedExpansion` and `WeightedSavings` were excluded. No proof code was modified.


## Follow-up: Lemma 4.3 displayed proof

Source: [printed page 10 / PDF page 12](https://arxiv.org/pdf/2511.20111v2#page=12), `source/tex/content/greg.tex:372-400`.

**Classification:** the displayed equations are false literally, but this is a locally repairable collection of sign, graph-label, and incidence-indexing errors. The intended unique-path argument proves the same lemma after correction. This does not expose a further unresolved conceptual gap comparable to the two known source diagnostics.

### Exact source expressions

First telescoping display (`greg.tex:385`):

```tex
\sum \limits_{(s, t) \in A'} \hopdist_{G \cup H'}(s, t)  = \phi' - \sum \limits_{i=1}^{|H'|} \sum \limits_{(s, t) \in A'} \left(\hopdist_{G \cup H'_i}(s, t) - \hopdist_{G \cup H'_{i-1}}(s, t)\right).
```

The next display's first two lines (`greg.tex:391-392`):

```tex
\sum \limits_{(s, t) \in A'} \hopdist_{G \cup H'}(s, t) &\ge \phi' - \sum \limits_{i=1}^{|H'|} \sum \limits_{(s, t) \in A'} \left( \hopdist_{G'}(u_i, v_i) - 1\right)\\
&= \phi' - \sum \limits_{i=1}^{|H'|} \sum \limits_{(s, t) \in A'} \left(\hopdist_{G \cup \{(u_i, v_i)\}}(s, t) - \hopdist_{G}(s, t)\right)\\
```

### Precise correction

Let h=|H'|, H'_0=emptyset, H'_i={e_1,...,e_i} subset H', and keep A' fixed at its initial value. Write d_i(q)=hopdist_(G' union H'_i)(q), d_e(q)=hopdist_(G' union {e})(q), and ell_i=hopdist_G'(u_i,v_i). Let I_i(q) be 1 precisely when u_i occurs before v_i on the unique base shortest path pi'(q), and 0 otherwise. In the undirected version use whichever endpoint order occurs along that path.

The corrected chain is:

```text
sum_(q in A') d_h(q)
  = phi' - sum_i sum_(q in A') [d_(i-1)(q) - d_i(q)]
 >= phi' - sum_i sum_(q in A') I_i(q) * (ell_i - 1)
  = phi' - sum_i sum_(q in A') [d_0(q) - d_(e_i)(q)]
 >= phi' - sum_i Delta'(e_i)
 >= phi' - h * max_e Delta'(e).
```

Accordingly:

- Reverse the decrement in both displayed differences (`385`, `392`).
- Change the base graph from G to G' throughout these displays and the subsequent average (`385`, `391-392`, `396-398`).
- Change H'_i subset H to H'_i subset H' (`381`).
- Insert the forward-path incidence indicator in the edge-length sum (`391`). Merely having both endpoints on a directed path is insufficient if they appear in reverse order.
- The prose at `387` mentions only currently active pairs, but the telescoping displays use the initial A'. The marginal raw-hop inequality must be applied to every pair in that fixed A', including those that later become inactive. The same expansion argument proves it for all such pairs.
- Keep the inequality at `393`: singleton raw-hop savings are at most the thresholded potential drop, not always equal to it. If a pair falls to at most beta hops, its entire old contribution disappears.

Why the repair works: expand an augmented shortest path into the unique original shortest path. Every used new edge spans a forward contiguous interval. Replacing the new edge by that interval yields an old-state shortest walk with at most ell_i-1 additional hops. Thus each marginal raw-hop saving is at most I_i(q)*(ell_i-1), which equals its empty-state singleton saving. This does not depend on whether q remains active. The final averaging requires nonempty A', supplied by an unfinished greedy round.

### Tiny witnesses showing these are real literal errors

1. Unit directed path a->b->c, beta=1, H'={(a,c)}: phi'=2 and final sum=1. The printed telescoping right side is 2-(1-2)=3; the corrected value is 1.
2. Two disjoint unit directed paths a->b->c and x->y->z, beta=1, e=(a,c): A'={(a,c),(x,z)}. The unqualified edge-length sum is 1+1=2; true singleton savings total 1+0=1. Therefore fixing signs and graph primes alone does not fix the subsequent equality.
3. Unit directed cycle a->b->c->d->a, demand (a,d), e=(c,a): both endpoints lie on the unique demand path, in reverse order. The edge's base length minus one is 1, but its singleton saving for this demand is zero. This shows why forward incidence is needed in the directed model.

These observations expand the existing source-scope note, rather than add a new main-theorem counterexample. The uncommitted expansion/savings draft was briefly inspected: `WeightedSavings.multi_edge_savings` states the required aggregate inequality directly and avoids the faulty displays. No compilation, audit, or kernel replay was performed for that draft by this reviewer.


## Six-module extension: finite directed Theorem 1.7 analogue

This later review covers the six local source hashes listed below, rather than extending the contents of commit ab4679bf retrospectively. No publication-blocking semantic defect was found. `WeightedBenchmark.directed_near_existential` proves the actual greedy output's size at most m, exact distances, and target hopbound with explicit finite parameters. This supersedes the earlier checkpoint's directed NNReal Theorem 1.7 gap; full original-paper scope remains partial.

- **Universal and least benchmark (`WeightedBenchmark:31-56`):** all finite W with card W <= card V in the current universe, all directed relations, all NNReal weights, and all inputs with at most m ordered edges are quantified. The actual V is included. Comparison hopsets are existentially quantified and legal, with card <= h. The empty-hopset bound at B=card V proves existence; Nat.find specification and minimality prove the benchmark is genuinely least. No input graph or path selection is hidden in the benchmark.
- **Actual output with no assumed progress (`WeightedBenchmark:61-88,101-114`):** the result refers to the reviewed WeightedGreedy.output. Perturbation, unique-path comparison progress, weight transfer, benchmark comparison existence, and the rounded stopping budget are all discharged before the final theorem.
- **First-m-round budget (`WeightedBenchmark:58-97`, `FiniteHorizon:43-66`):** K=Nat.log 2(n^3)+1, h=floor(m/(2K)), D=2h. The proof establishes KD<=m and invokes progress only before m inserted edges. Ordered-edge union cardinality is at most original cardinality plus inserted cardinality, hence comparison graphs have at most 2m edges even when an inserted edge overlaps an original heavier edge.
- **Small cases (`WeightedBenchmark:74-114`):** h=0 is handled separately by proving initial potential zero, not dividing by zero; this includes m=0. K>=1 handles n=0,1. The target max 1(2*exopt) handles exopt=0 and meets the greedy definition's positive-target requirement.
- **Savings (`WeightedExpansion:28-80`, `WeightedSavings:13-75`, `WeightedProgress:50-94`):** exact walk expansion makes every used hopedge a contiguous interval of the unique base shortest path. A simple augmented minimum-hop path uses each dart at most once, so summing singleton savings bounds aggregate saving. Thresholded contribution drops then dominate raw-hop savings. The proof bypasses the incorrect Lemma 4.3 displays.
- **Transfer (`WeightedTransfer:12-86`, `WeightedStateProgress:14-76`):** closure weights are recomputed correctly for each weighting and current graph. A common expansion preserves both costs, establishing original augmented hopdistance <= perturbed augmented hopdistance, with equality at the empty state. Therefore the original candidate drop dominates the perturbed drop. Current-state candidate/potential identities are explicitly proved.

Remaining boundaries: directed ordered-edge counting, NNReal weights, noncomputable mathematical run, and exact base-two integer-logarithm/floor parameters. Undirected translation, real-log asymptotic conversion, broader weight domains, strong DAG and chain results remain outside this claim.

Reviewed source SHA256 values:

```text
ef3c0a7058c7e3bcf1b1f26fda74bb16efccf3e5d8040ef3ec7428f534197efa  WeightedExpansion.lean
5cbb5f2536c267a72042a962f18cd64c48358f720031cdcc9a2a9818a1e7b746  WeightedSavings.lean
245be75bf3847e2cc2b2c2e97f502bcde7326a48ccc2e8b0e6391833876ab68c  WeightedProgress.lean
6630e41d139ac814bc4ee0bfb7b30f99f461375b0d4c71c7fd0e1f308bd1864f  WeightedTransfer.lean
8beb073e7ed7ea7550c620308834f03695fdd10ea4da817481b48f83a6d59aeb  WeightedStateProgress.lean
eb623196b86045a26d0c0b2eb3c0366b8c05484f7620f89bdde72acf35b45a66  WeightedBenchmark.lean
```

All six hashes were rechecked unchanged after reading. The parent reports a passed 26-module local gate with 435 audited declarations and six new replays; this reviewer did not rerun those checks. Exact new-commit CI remains separate. Detailed structured review: `weighted-benchmark-semantic-review-six-modules.json`.
