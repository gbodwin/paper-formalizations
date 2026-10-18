# Theorem 34, fixed stretch 2: one focused candidate and its obstruction

Research base: **`682c8809fbf4a92b2f86be08916b0d81b0b1bd2e`**. Accepted mathematical source stays **`78cb40c7837db049d645d73696f2e0b724ce8a3b`**. The parent reports independent acceptance of handwritten Lemmas A–D and all 11 bindings in the previous research checkpoint. That is mathematical/source/hash review, **not Lean execution or formalization**. Those notes, proofs, diagnostics and all earlier evidence remain unchanged.

**Outcome:** this pass tests a different graph: complete bipartite heavy demands on terminals, connected through shared short and long hubs. It proves a complete parameter classification for that family. Cheap fault connectivity and forced heavy output can coexist, but yield only the weaker n/f scale in the forcing regime; the other regimes admit constant-ratio spanners. A general incident-cost screen also shows that bounded weight aspect ratio cannot deliver the requested uniform-in-f stretch-2 target. These are handwritten results awaiting review, not a repair or a counterexample to the original existential theorem.

No compiler, Lean kernel checker, accepted-source edit, cache retrieval, extraction, cache advice, CI, site publication or completed-runtime development occurred. In particular this pass does **not** search replacement certificates on the obstructed near-extremal blowup family.

## 1. Exact unresolved target

Keep the definitions in the accepted [previous research report](../light-eft-theorem34-research-20261018/REPORT.md). Let `D_q(G)` be the genuine minimum weight of a q-fault component preserver, with every fault set a subset of **the full input edge set**. Let `ell_q(H|G)=w(H)/D_q(G)`.

For fixed stretch **2**, the research target remains:

`for every fixed real c≥2, exists alpha(c)>0, for every integer f≥1,`
`there are unbounded orders n and inputs G such that every f-EFT 2-spanner H satisfies`
`ell_floor(cf)(H|G) ≥ alpha(c) lambda(floor(n/sqrt(cf)),3)`.

The coefficient is independent of f and n. Fix c,f before growing n; the order threshold may depend on them. The explicit floor is the same research bookkeeping as in the accepted notes, not an approved source-theorem amendment. The full Theorem 34 has not been narrowed to stretch 2; this is its requested first unresolved test.

For integer M≥2, the balanced unit-weight complete bipartite graph has weighted girth >3 and lightness `floor(M²/4)/(M−1)≥M/4`. Thus

`lambda(M,3) ≥ M/4`.                                      (1)

The original paper's [Theorem 17](https://arxiv.org/html/2502.10890v2#S3.SS1), at its fixed parameters k=1 and epsilon=1/2, gives the matching O(M) scale. The obstructions below use only the elementary lower bound (1), not that upper theorem or any unproved girth conjecture. The original [Theorem 34](https://arxiv.org/html/2502.10890v2#S4.SS2) remains the source target; its already reviewed certificate defect is not relabeled as new.

## 2. A preliminary weight screen

**Lemma E (aspect-ratio obstruction, proved here).** For a finite positive-weight connected simple n-vertex graph, n≥2, set `A=w_max/w_min`. Accepted Lemma A implies

`ell_q(G|G) ≤ A max(1,(n−1)/(q+1))`.                       (2)

Proof: put `r_v=min(q+1,deg_G(v))`. The incident-cost bound gives `D_q(G)≥(w_min/2) sum_v r_v`, whereas `w(G)≤(w_max/2) sum_v deg_G(v)`. For each degree d≤n−1,

`d ≤ max(1,(n−1)/(q+1)) min(q+1,d)`.

Sum this inequality and divide the positive denominator. The full input G is always an eligible f-EFT 2-spanner, so (2) is an upper bound available to the existentially cheapest output, irrespective of f.

Write r=cf, q=floor(r), M=floor(n/sqrt(r)). For n≥max(q+2,2sqrt(r)), (1) gives `lambda(M,3)≥n/(8sqrt(r))`. If all eligible outputs were to satisfy the target with coefficient alpha, applying it to H=G and using (2) would require

`A ≥ alpha(q+1)/(8sqrt(r)) ≥ alpha sqrt(r)/8`.              (3)

Consequently no family with aspect ratio bounded independently of f can witness the intended uniform coefficient, whatever its combinatorial structure. This is a restriction on candidate inputs, **not** on all positive-weight graphs. It motivates allowing arbitrarily tiny cheap-edge weights in the next candidate.

## 3. Different construction: shared short and long hubs

Fix integers f≥1, q≥2f, t≥q+2. There are disjoint terminal sets A,B with |A|=|B|=t and a hub set Z of size `s=q+1`. Total order is `n=2t+s`. Include:

- every A–B edge, called heavy, of weight 1;
- every terminal–hub edge;
- no other edges.

Choose `h∈{0,...,s}` short hubs. Their incident edges have a common weight `0<a≤1/4`, allowed to depend arbitrarily on f and t. All other `L=s−h` long hubs have incident weight `b=3/2`. In particular the weight aspect ratio need not stay bounded: a may tend to zero as fast as desired. Let Q be **all terminal–hub edges**, and let G also contain the heavy edges. This is a new weighted graph, not the previously obstructed blowup.

Put

`S = h a + L`,       `T = h a + (3/2)L`.

### Actual fault connectivity and genuine denominator bounds

**Lemma F.** Q is a q-fault connectivity preserver of G, and

`t S ≤ D_q(G) ≤ w(Q)=2t T`.                                (4)

For a cut containing x of the 2t terminals and y of the s hubs, the Q cut size is

`x(s−y)+(2t−x)y`.

Every nontrivial cut has size at least s=q+1. If y=0 or y=s this is immediate; if 0<y<s, minimization over x gives at least `2t min(y,s−y)≥2t≥s`. Accepted Lemma A therefore proves the exact q-fault preserver property. Equivalently Q remains connected after **every** q input-edge faults, including faults outside Q; G is a supergraph.

Each terminal has degree t+s in G and needs at least s incident edges in any certificate. Its s cheapest incident edges consist of h short edges and L heavy edges, since t≥s and `a<1<b`. Their cost is exactly S. The 2t terminal contributions alone give `D_q(G)≥tS` by accepted Lemma A; hub contributions can only increase this lower bound. Q need not be optimal. Both sides of (4) refer to the actual denominator, not a supplied substitute.

## 4. Complete classification of this candidate

**Lemma G (three regimes, proved here for all parameters above).**

| Short-hub count | Rigorous behavior | Consequence |
|---|---|---|
| `2h≤f` | Every heavy edge is indispensable to every f-EFT 2-spanner | Denominator cost leaves only an O(t/q) available ratio |
| `f/2<h≤f` | Q plus representative heavy edges is an f-EFT 2-spanner | Competitive ratio at most 5 |
| `h≥f+1` | Q alone preserves all fault-deleted distances exactly up to f faults | Competitive ratio at most 3 |

These cases cover every integer h, including h=0. All paths below are actual graph paths with their full weights; no projected/path-restricted distance is identified with global distance.

### Regime 1: heavy output is forced, but the denominator is costly

For a heavy edge uv, delete every short-hub edge incident to u or v. These are 2h distinct actual input edges, at most f, and uv survives. In G−uv−F, neither endpoint has a surviving short edge. A two-edge alternative through a long hub costs 3; two heavy edges cannot join opposite heavy-bipartition sides. Every longer alternative starts and ends with weight at least 1 and has a positive middle segment, hence costs >2. More explicitly its length is at least `min(3,2+a)>2`. Thus G−F distance is 1 through uv and every f-EFT 2-spanner must contain uv. This works for all t² heavy edges, with a separate valid fault set for each.

Combining the forced weight with the **upper** denominator bound in (4) proves a genuine, but weaker, lower bound:

`ell_q(H|G) ≥ t/(2T)` for every eligible H.                (5)

It does not prove the requested scaling. The eligible choice H=G and the **lower** denominator bound give

`ell_q(G|G) ≤ t/S + 2T/S ≤ 4t/[3(q+1)] + 3`.              (6)

Indeed `T≤(3/2)S`; and `h≤f/2≤q/4` yields `S≥L≥3(q+1)/4`. Thus the best output cannot have more than O(n/q) ratio in this regime, uniformly in the arbitrarily small a. With c fixed, this loses the required square-root-f factor.

### Regime 2: too many short attachments for the fault budget

Choose arbitrary `A_0⊆A`, `B_0⊆B`, each of size f+1. Let H contain Q and every heavy edge incident to A_0 or B_0. It has at most `2t(f+1)` heavy edges.

Fix any F⊆E(G), |F|≤f, and a surviving input edge. Terminal–hub edges are retained in H and need no detour. A surviving heavy edge already in H also needs none. For an omitted heavy edge uv, consider surviving short-hub attachments at its endpoints:

- If both endpoints have one, choose such hubs i,j. If i=j there is a 2a path. Otherwise there are 2t−2 possible intermediate terminals z for the 4a walk `u–i–z–j–v`. Their two middle edges are disjoint across z, and 2t−2>f, so one survives. Its length is `4a≤1`.
- Both endpoints cannot lose all h attachments, because that would cost 2h>f faults.
- If u has none but v retains a hub j, use one of the f+1 vertices z∈B_0. Since uv is omitted, v∉B_0. The paths `u–z–j` have disjoint pairs of edges; f faults cannot destroy all f+1. Appending surviving `j–v` gives length `1+2a≤3/2≤2`. The other orientation uses A_0 identically.

Every surviving input edge therefore has an H−F replacement of length at most twice its weight. Expanding a shortest G−F path proves the all-pairs guarantee. Q is a subgraph of H and remains connected under q faults, so these instances have finite distances; the edge-to-path argument would also preserve unreachable-pair semantics.

Using (4), `S≥L=q+1−h≥q+1−f≥f+1`, and `T≤(3/2)S`,

`ell_q(H|G) ≤ [2tT+2t(f+1)]/(tS) ≤ 5`.                 (7)

The argument uses arbitrary input faults, not only faults at the selected endpoints.

### Regime 3: short hubs alone make heavy edges redundant

For every heavy uv there are h>f edge-disjoint two-edge short-hub paths of length `2a≤1/2`. At least one survives any f faults. Every other surviving input edge is already in Q. Thus every input edge has a Q−F replacement no longer than itself; since Q⊆G, **all** distances agree after every such F. In particular Q is an f-EFT 2-spanner, with

`ell_q(Q|G) ≤ 2T/S ≤ 3`.                                (8)

### Uniform-in-f implication, with order thresholds handled correctly

Set c=2, q=2f and `M=floor((2t+q+1)/sqrt(q))`. For **every** choice of h and a, including choices varying with t, (6)–(8) supply an eligible H with

`ell_q(H|G) ≤ max(5, 3+4t/[3(q+1)])`.

Since `lambda(M,3)≥M/4`, fixing f and then letting t→∞ gives the uniform-in-h,a bound

`limsup_t [min_H ell_q(H|G) / lambda(M,3)] ≤ 8sqrt(q)/[3(q+1)]`.

The right side tends to zero as f grows. For any proposed positive coefficient alpha(2), first choose a sufficiently large **fixed** f, then all sufficiently large t fail that coefficient. The bound is uniform over h_t and a_t, so no unbounded subsequence of this family rescues it. A parameter-dependent onset does not change this conclusion. This rules out this entire defined shared-hub candidate class for the intended reduction; it does not rule out other positive-weight graphs or refute the existential theorem.

## 5. Exact remaining test

The pass has not produced a stretch-2 witness with the required scaling. The next concrete test is to replace the **common** cheap-neighbor pool with a different incidence geometry, while avoiding the following two simultaneous failures:

1. Too few cheap attachments leave roughly q expensive edges per terminal by accepted Lemma A, raising the denominator to the n f scale.
2. Many globally shared cheap attachments give the 2a/4a or one-heavy-plus-2a alternatives above, allowing a sparse spanner.

For a next candidate pursuing **individual-edge forcing**, explicitly provide its full vertex set (including all helpers), actual q-fault preserver Q satisfying Lemma A's cut criterion, and a family E_h of genuinely forced edges. One precise sufficient forcing obligation is, for each e=uv∈E_h, an actual `F_e⊆E(G)\{e}`, `|F_e|≤f`, with

`dist_(G−e−F_e)(u,v) > 2 w(e)`.

Its cost obligation remains the original one:

`sum_(e∈E_h) w(e) / w(Q) ≥ alpha(c) lambda(floor(n/sqrt(cf)),3)`.

These are unresolved obligations for that proof strategy, not necessary conditions on every possible repair or assumptions promoted to a theorem. Every other heavy edge must remain present when checking the forcing path condition; checking Q−F_e alone is insufficient. The total n must count helper vertices, and (3) must be respected. No new incidence geometry satisfying these requirements is proved or conjectured here as established. The full theorem and the stretch-2 test remain open; no narrower completion scope is adopted.

## 6. Finite support, preservation and disposition

[experiments.py](experiments.py) uses exact integer/Fraction arithmetic and shortest paths on explicit graphs; it has no network, solver, subprocess or proof-kernel interface. [Results](experiment-results.json) and [raw log](experiments-01.log) preserve its first passing run:

- 20 cases: f=1,q=2,t=4 and f=2,q=4,t=6, every h, with a=1/4 and a=1/[4(f+1)²].
- 110 cut-cardinality pairs covering all cuts of the two complete bipartite certificates by symmetry.
- 176 explicit heavy-edge forcing fault sets in the low-h regime.
- 1,278 all-pairs distance/fault-set checks in the middle/high regimes. For f=1 these cover all input fault sets of size at most one. For f=2 they cover the empty set, all singleton faults and 32 deterministic sampled two-edge faults per case; **they are not exhaustive** for f=2. Sample scope is retained in every result row.

Finite experiments support but do not prove the arbitrary-parameter statements. Lemmas E–G are handwritten proofs awaiting independent review; they are not Lean-certified. The failed candidate is preserved with both its forcing argument and the cheap competing outputs, not discarded or claimed as a repair.

[Preservation and source bindings](preservation.json), [commands](commands.txt) and [manifest](manifest.json) record the accepted starting evidence, exact source context, unchanged tracked files and idle/free-lock checks. The previous A–D checkpoint remains intact; no new search or certificate replacement was made on its obstructed input family. One initial metadata lookup used the absent filename `ExactExtremal.lean`; no Lean invocation or source edit resulted, and no theorem claim depends on that lookup. No failed mathematical experiment was overwritten.

This coherent pass stops here. Publication is research-only with `[skip ci]` and exact remote verification. All previous theorem status, accepted proof/audit results, disabled preparation, denied-cache state, completed runtime work and websites remain unchanged. The worker pauses for independent review with no compiler/checker process and the universal lock free.
