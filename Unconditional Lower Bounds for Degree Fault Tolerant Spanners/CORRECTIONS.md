# Corrections and proof clarifications

Source edition: [arXiv:2607.07576v1](https://arxiv.org/abs/2607.07576v1), 8 July 2026.
Original PDF SHA256: `cbf9a322032cd3c672b663ef8547e74a76435ce6df81ab0c3ad77e70d66f8699`.

This record does not modify the original published PDF. The new website edition
will identify its corrected statements explicitly. The formalization remains
under development until its complete verification record says otherwise.

## 8 October 2026: the dimension-one boundary case

**Affected claims:** Section 2.1 and Lemma 6 (printed page 4, PDF page 5);
Lemma 16 (printed page 10, PDF page 11).

The incidence construction is stated for `k >= 1`, but the claimed size requires
`k >= 2`. When `k=1`, every displayed slope vector is `(1)`. For every `x,t`,

`{x + lambda*(1) : lambda in F_p} = F_p`.

Consequently the collection of distinct subset-lines has one element. The
specified incidence graph is the star `K_{p,1}`. It has `p+1` vertices and `p`
edges, rather than `2p` vertices and `p^2` edges. For example, `p=2` gives three
vertices and two edges, rather than four vertices and four edges. The later
blowup density calculation inherits this boundary-case error.

**Correction:** impose `k >= 2` on this incidence-size argument and its blowup
calculation, and handle `k=1` in Theorem 5 separately with the complete graph.

**Why the main result survives:** a stretch-one spanner of an unweighted
complete graph cannot omit an edge, already for the empty fault set. Therefore
this witness has exactly `N choose 2 = N(N-1)/2` compulsory edges for every
fault budget `f`. For `N>=2`, this is at least `N^2/4`. The factor
`f^(1-1/k)` equals one at `k=1`, so this is precisely the required lower-bound
order, including budgets larger than the number of vertices.

The source audit independently checked the error and repair. The Lean
implementation now compiles the complete-graph rigidity and exact count, the
quadratic arithmetic inequality, and the corrected `k>=2` incidence counts.
The remaining full-paper verification gates are tracked separately.

## Clarifications used in the formal proof

These are proof-convention clarifications, not additional failures of the main result.

- Lemma 9 is stated for a point-rooted alternating closed walk with different
  point endpoints across every line occurrence. Its cycle applications satisfy
  this condition. This avoids ambiguity about reversal across the closing seam
  of a line-rooted walk. Repeated slope occurrences are grouped explicitly before
  applying independence of distinct moment-curve vectors.
- The failure-set cutoff is expressed as `2*(lineLength+1) <= k`, preserving the
  real inequality and its implicit floor, including odd `k`.
- The matching assertion includes the protected edge. At the reference point,
  no failed edge is incident, because that point lies on the reference line and
  on no distinct parallel line.
- Disconnected replacement endpoints are represented by infinite distance.
- After cloud projection, every remaining edge avoids the entire base matching,
  including the protected base edge. Loop erasure of the projected open walk
  gives the simple path used in the short-cycle contradiction.
- The direct construction family has `N=2*f*p^k` and exactly `f^2*p^(k+1)` edges.
  The final theorem states its quantifiers explicitly. No unrestricted all-pairs
  `(N,f)` lower bound with `f` arbitrarily larger than `N` is asserted for `k>1`.
