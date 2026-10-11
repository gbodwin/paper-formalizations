# Corrections and formal proof obligations

These notes refer to arXiv:2001.07741v3. They do not claim the final pairwise
bounds are false. The original source is preserved separately.

## C1: Theorem 12 routing starts with an inequality

In the first line of the medium-pair calculation, replace
`dist_H(s,t) = dist_H(s,x) + dist_H(x,x') + dist_H(x',t)` by `≤`, justified by
the triangle inequality. Placement on a shortest path in G does not imply
additivity in H. The following upper-bound argument still works.

`CorrectionExample.lean` certifies a witness: H is the cycle
0–1–2–3–4–5–6–0; G additionally has edge 1–4. Vertex 1 lies on a G-shortest
0–4 path, but H-distance 0–4 is 3 while H-distance 0–1 plus 1–4 is 4.
Set x=1 and x'=t=4 to witness the displayed three-segment issue.
The corrected TeX and Site apply the inequality directly.

## C2: Joint coverage and cost

Expected coverage and expected cost require a simultaneous existential
argument. For finite weighted outcomes with 0≤X≤p, Y≥0, EX≥βp, EY≤C,
β,p,C>0, `exists_joint_sample` proves a witness X≥βp/2 and Y≤2C/β.
It maximizes a combined score; no independence assumption is needed.
The +2 implementation instead proves a deterministic greedy hitting lemma.

## C3: Overlap and integer thresholds

Added prefixes/suffixes can overlap. If their union covers every missing edge,
route exactly. Otherwise select attachments in source-to-target order.
A fractional length threshold can be below one; rounding it up naively may add
an uncontrolled O(p) cost. For +2 use d=ceil(p^(1/3)) and m=floor(n/d²),
and take neighborhoods at all missing-edge source endpoints. A long path has
at least m+1 such indices, so the cost proof works even when m=0.
The corresponding +4/+6 prefix/suffix construction remains a proof obligation.

## C4: Reachability and infinity

The paper verbally defines the intended reachability condition correctly.
A literal substitution k=∞ in an extended-distance additive inequality makes
the inequality true even for an empty graph. `IsReachabilityPreserver` is
therefore a separate predicate, as intended by the paper.

## C5: Boundary and accounting conventions

Use ≤ threshold for the base case and > threshold for recursion; empty demand
sets need no edges. The main cost series is geometric. Weighted path arguments
need shortest-path existence (for example nonnegative weights on finite graphs).
For Bernoulli sampling with mean μ=nρ, E|R|²=μ²+μ(1−ρ), not simply μ².
The extra term must be bounded, or replaced by a deterministic construction.

## C6: Theorem 5.2 names the wrong type of preserver

Replace “distance preserver” by “reachability preserver” in part 2 of Theorem 5.
The cited Abboud–Bodwin source states a reachability bound, both in its abstract
and Theorem 1 (page 2 of the PDF): https://arxiv.org/pdf/1710.11250v3
The proof of Theorem 5.1 needs only reachability, so this restores the correct
external premise without changing that reduction. This is a source-comparison
correction, not a Lean proof that the stronger distance statement is false.
The Site and corrected TeX apply it directly.

## Existing retraction

The v3 source already withdraws the earlier +4 all-pairs O(n^(7/5)) claim.
That notice remains visible. It is not a new result of this verification.
