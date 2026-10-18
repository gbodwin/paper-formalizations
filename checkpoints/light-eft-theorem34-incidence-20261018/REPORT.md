# Fixed stretch 2: projective incidence, full-graph forcing and its cost

Research base: **`ea8e75d23ee891664949f185cd9081bec90b7f85`**. Accepted Lean source remains **`78cb40c7837db049d645d73696f2e0b724ce8a3b`**. The parent reports independent acceptance of handwritten Lemmas E–G, including their three regimes and candidate-family obstruction. This records mathematical/source/hash review, **not Lean execution**. Those notes and their exact sampled/exhaustive experiment labels remain unchanged.

**Outcome:** a different incidence geometry gives actual cheap fault-connectivity certificates and explicit one-edge forcing faults against the full graph. Its heavy-weight regime proves a genuine lower family of order n/f for stretch 2, but not the requested n/sqrt(f) scale. Its small-weight regime admits a much cheaper stretch-2 spanner despite only one common helper per terminal pair. The resulting obstruction covers this defined incidence family, **not the original existential theorem**. No repair or narrower completion scope is claimed.

The mathematical screening [PRECHECK.md](PRECHECK.md) was written before the first graph experiment. Its exact hash is stored in the experiment output. It supplies the certificate algorithm, full cost including helpers, and full-graph forcing argument in advance. No compiler, accepted-source edit, cache retrieval, extraction, cache advice, CI, site or unrelated-paper work occurred. Neither the common-hub family nor the obstructed near-extremal blowup family is reused.

## 1. Target and definitions retained

For q≥0, `D_q(G)` is the genuine minimum weight of a q-fault component preserver, tested against **all** `F⊆E(G)`, |F|≤q. Competitive lightness is `ell_q(H|G)=w(H)/D_q(G)`. The fixed-stretch-2 target remains

`∀ fixed real c≥2, ∃ alpha(c)>0, ∀ integers f≥1, ∃ unbounded orders n and G,`
`∀ f-EFT 2-spanners H⊆G: ell_floor(cf)(H|G) ≥ alpha(c) lambda(floor(n/sqrt(cf)),3)`.

The coefficient is independent of f and n; fix c,f before growing n. The order threshold may depend on c,f. Floors are the already explicit research bookkeeping, not a source-theorem amendment. This subproblem does not replace the full stretch range of Theorem 34.

Accepted Lemma A gives the exact truncated-cut criterion and incident-cost lower bound. Accepted Lemma E–G's notes also prove the elementary comparison `lambda(M,3)≥M/4` for M≥2 using the balanced unit complete bipartite graph. Only this lower comparison is needed to obstruct the candidate below; no conjectured extremal estimate is assumed.

## 2. A genuinely different geometry, with all helpers counted

Fix f≥1, c≥2 and q=floor(cf)≥2f. Choose any prime p≥q. Let P be the one-dimensional subspaces of F_p³ and L the projective lines, represented dually by nonzero linear forms modulo scalar multiples. A point x is incident to a line z if x·z=0. The point and line vertex types are disjoint even if their representative triples agree.

There are `m=p²+p+1` points and m lines. Each point has p+1 incident lines and each line p+1 points. Distinct points have exactly one common line; distinct lines meet in exactly one point. For example, the count of lines through x is `(p²−1)/(p−1)=p+1`, obtained from its two-dimensional orthogonal space. Two independent equations have a one-dimensional common kernel, giving the unique intersections. These elementary finite-field facts define the geometry, rather than assuming an unconstructed design oracle.

Let K be its incidence graph. Split the point vertices into balanced sets A,B and add every A–B edge of weight 1, called heavy. Every incidence edge has weight `a∈(0,1]`; there are no other edges. The full graph is G.

The order is **n=2m**, including all m line helpers. Write `h=|A||B|=floor(m²/4)` for the number of heavy edges. The incidence edge count is m(p+1), and

`w(K)=a m(p+1)`,       `w(G)=a m(p+1)+h`.

No helper is adjacent to all terminals: it sees only p+1 of m points. Every terminal pair has common-neighbor overlap exactly one, in contrast to a global common hub pool. For each fixed c,f, primes p≥q are unbounded, so n grows without bound with the fault budget fixed.

## 3. Actual certificate and full denominator cost

**Lemma H (incidence cut certificate and cost; handwritten proof).** There is an explicitly constructed q-fault preserver C⊆K⊆G with

`a m(q+1) ≤ D_q(G) ≤ w(C) ≤ a(q+1)(2m−1)`.             (H1)

First fix two distinct points u,v and their unique common line l. One incidence path is u–l–v. Pair the other p lines through u bijectively with the other p lines through v. If the paired lines meet at z, they give the four-edge path u–line–z–line–v. The p+1 paths are edge-disjoint: their endpoint line sets are disjoint apart from l, their intermediate points are distinct and not u or v, and the two vertex types prevent accidental identifications. This gives p+1 edge-disjoint point-to-point paths of length at most four.

Every cut separating two points therefore has at least p+1 incidence edges. If all points lie on the same shore, the other nonempty shore contains a line and all p+1 of its incident edges cross. Hence every nontrivial K cut has at least p+1≥q+1 edges. This proves actual q-fault connectivity, not merely a cloud-level assertion.

Construct C by **q+1 residual-forest rounds**: take the lexicographically selected maximal forest of the residual incidence graph, retain its edges and remove them before the next round. For any cut, if fewer than q+1 crossing edges have been retained, some original crossing edge remains. Its endpoints lie in a residual connected component spanned by the next maximal forest, so that forest retains another crossing edge. After q+1 rounds each C cut has at least q+1 edges. Accepted Lemma A makes C a q-fault preserver of the full G. Each forest has at most n−1 edges, proving the cost upper bound in (H1). The finite cut argument is stated explicitly; no novelty or formalization claim is made for this standard certificate operation.

For the lower bound, every vertex has at least p+1≥q+1 input incidence edges of minimum weight a. Every q-fault certificate needs degree at least q+1 there. Summing the accepted incident-cost bound over **all 2m vertices, including helpers**, gives `D_q(G)≥a m(q+1)`.

Thus the actual optimum is within a factor less than two of the stated cost upper bound. C need not itself be optimal. In particular the denominator cost is of order a q n, not the larger cost a p n of the entire incidence graph. We will use C for connectivity cost and K for a short-path spanner; their roles are not interchangeable.

## 4. Full-graph forcing, with every other heavy edge present

**Lemma I (exact one-fault alternative distance; handwritten proof).** Suppose `1/2<a≤1`. For each heavy e=uv with u∈A,v∈B, let l_uv be the unique common line and set

`F_e={u–l_uv}`.

This is one actual input incidence fault, excludes e and has size ≤f. In the **full graph** G−e−F_e,

`dist(u,v)=1+2a>2`,                                      (I1)

whereas `dist_(G−F_e)(u,v)=1` through e. Consequently every f-EFT 2-spanner contains all h heavy edges.

To prove (I1), classify a path by its heavy-edge count. With no heavy edge, the sole two-incidence route was destroyed, so at least four incidence edges cost `4a≥1+2a`. With one heavy edge, an alternative to e must contain at least two incidences, costing `1+2a`. Two heavy edges alone cannot join the opposite A/B sides; if incidences occur, they add positive even length and cannot improve the bound. Three or more heavy edges cost at least 3≥1+2a. Incidence segments between point vertices always have even length, because heavy edges have only point endpoints.

The lower bound is attained by the retained heavy u–v', where v' is another B point, followed by the two incidences on the line through v',v. That path cannot use the failed u-incidence. Thus the correct alternative distance is **1+2a**, not the incidence-only value 4a. All other heavy edges remain available throughout this calculation.

Using the genuine cost upper bound in (H1), every eligible H therefore satisfies

`ell_q(H|G) ≥ h/[a(q+1)(2m−1)]`.                        (I2)

For example, since a≤1 and h≥m(m−1)/4, this is at least `(m−1)/[8(q+1)] = (n−2)/[16(q+1)]`. This is a rigorous weaker n/f lower family for fixed c, not the requested n/sqrt(f) conclusion. Notice that K is a fault-free 2-spanner even here (the common-line route has length 2a≤2), but the specified single fault makes each heavy edge necessary. The forcing is genuinely fault-sensitive.

## 5. Why the candidate still cannot meet the uniform target

**Lemma J (complete weight-range screen for this family; handwritten proof).** Allow a to vary arbitrarily with f and p within (0,1]. Neither reducing overlap to one nor shrinking a repairs the target.

### Small weights: 0<a≤1/2

For each heavy pair the p+1 edge-disjoint incidence paths in Lemma H survive any f input faults in at least one path, because p≥q≥2f. A surviving path has cost at most `4a≤2`. Every other surviving input edge is already in K. The edge replacement argument therefore makes K an f-EFT 2-spanner of the **full G**, giving

`min_H ell_q(H|G) ≤ w(K)/D_q(G) ≤ (p+1)/(q+1)`.         (J1)

All relevant fault-deleted graphs are connected: C is q-resilient and f≤q. Thus no unreachable distance is coerced to a finite value. At the exact boundary a=1/2, the four-edge path has length **2**, which is an allowed replacement; strict forcing requires >2.

Set r=cf and `M=floor(2m/sqrt(r))`. For each fixed c,f, `lambda(M,3)≥M/4` grows on the order of m, whereas (J1) grows only on the order of p. The ratio to the target tends to zero as p→∞. Making incidence edges arbitrarily smaller cancels from the numerator/denominator bound; it does not restore the missing scale.

### Larger weights: 1/2<a≤1

The heavy edges are forced, but the available eligible choice H=G and the denominator **lower** bound in (H1) give

`min_H ell_q(H|G) ≤ (p+1)/(q+1) + h/[a m(q+1)]`
`                    ≤ (p+1)/(q+1) + m/[2(q+1)]`.        (J2)

Together with (I2), this pins down the asymptotic scale to n/(q+1) for each fixed fault budget. It does not supply n/sqrt(q). In this weight range the aspect ratio is at most two, consistent with accepted Lemma E; the new contribution is an actual incidence construction, explicit forcing and a matching denominator cost, not a newly alleged source error.

### Uniform coefficient and parameter-dependent onsets

Fix c=2, q=2f. From (J1), (J2) and `lambda(M,3)≥M/4`, for arbitrary choices a=a_p,

`limsup_(prime p→∞) [min_H ell_q(H|G)/lambda(M,3)] ≤ sqrt(q)/(q+1)`.

The small-weight subsequence has limit zero. In the other subsequence, divide (J2) by M/4 and use `m=p²+p+1` and `M~2m/sqrt(q)` to obtain the displayed bound. It is uniform over a_p in its allowed ranges.

Given any proposed alpha(2)>0, choose a sufficiently large **fixed** f, then let p grow through primes. Eventually every graph of this family fails that coefficient. Since this occurs beyond a parameter-dependent onset, no forbidden all-n/f diagonal or saturation argument is being used. This proves failure of this defined candidate family, **not** failure of the original theorem, which can choose other graphs. The projective-incidence construction is not a return to the common-hub or old blowup family.

## 6. Precise unresolved next test

The remaining difficulty is now visible in a geometry with pairwise helper overlap exactly one: robust four-edge alternatives survive even after the unique two-edge path is killed. Merely lowering codegree or cheap-edge weight does not address them.

For a next **individual-edge-forcing** candidate, a concrete sufficient test is:

1. Count every terminal and helper in n; construct a cheap backbone K with weight a per edge and actual q-fault-preserver C, verifying accepted Lemma A's cut criterion. Residual forests may give `w(C)≤a(q+1)(n−1)` if the required cuts are present.
2. Use an actual family E_h of heavy edges, retaining every other heavy edge when testing one e. Exhibit `F_e⊆E(G)\{e}`, |F_e|≤f, and prove `dist_(G−e−F_e)(u,v)>2w(e)`.
3. Verify the exact target budget `sum_(e∈E_h)w(e)/w(C) ≥ alpha(c) lambda(floor(n/sqrt(cf)),3)` with coefficient independent of f.

For instance, the tempting budget a=O(1/sqrt(q)) with a dense heavy family is useful only if step 2 survives. It requires eliminating all cheap routes of roughly O(sqrt(q)) hops, **and mixed routes through other heavy edges**, within f faults. The present incidence geometry fails already at four hops. This is an unresolved finite construction test, not an assumed oracle, a claim such a geometry exists, or a necessary restriction on every possible proof strategy. Aggregate rather than individual-edge forcing remains logically available. No new candidate meeting these requirements is proved here.

The full fixed-stretch-2 target and Theorem 34 remain open. The n/f construction is recorded as a useful partial result, not adopted as a replacement theorem or completion scope.

## 7. Finite evidence and preservation

[experiments.py](experiments.py) uses exact modular arithmetic, rational weights and explicit shortest paths. It has no solver, network, subprocess, compiler or proof-kernel interface. [Raw log](experiments-01.log) and [results](experiment-results.json) retain the first passing run. The pre-experiment file's SHA256 is bound in the results and checked again when sealing.

- Four incidence/certificate geometries, with `(p,q)=(2,2),(3,2),(5,4),(7,2)`. The corresponding total vertex counts, **including helpers**, are 14,26,62,114. The actual C edge counts are 21,52,186,297; the full K edge counts are 21,52,186,456. The last case is geometry/cost-only, not a distance experiment.
- 2,160 unordered point-pair families checked for the stated p+1 simple edge-disjoint incidence paths.
- For the 14-vertex certificate, every **16,382 nontrivial vertex subset** was tested as a cut (both complementary shores are counted). Larger cases were not exhaustively cut-enumerated; maximal-forest and path-disjointness checks are labeled separately.
- Fifteen weighted cases, for p=2,3,5, with weights `a=1/[4(f+1)²],1/4,1/2,3/4,1` and corresponding f=1,1,2.
- 588 **weighted edge/fault witnesses** checked the exact full-graph alternative distance 1+2a in the forcing range, with all other heavy edges retained.
- 882 targeted nonforcing edge/fault checks below or at the boundary; these are specified one-fault tests, **not exhaustive tests of all f=2 faults**.
- 102 weighted graph/fault instances checked all-pairs stretch in the small p=2 case: three low-weight cases, each with the empty set and every one-edge input fault (34 sets per weighted graph). No such exhaustive all-pairs claim is made for p=3,5 or7.

Finite checks support, but do not prove, the arbitrary-parameter handwritten arguments H–J. They are not Lean acceptance. No failed experiment was overwritten. The mathematically unsuccessful candidate and both sides of its weight-range screen remain fully preserved.

[Source/preservation bindings](preservation.json), [commands](commands.txt) and [manifest](manifest.json) record the accepted starting checkpoint, precheck hash, exact new artifacts and idle/free-lock status. All old notes, sampled-versus-exhaustive labels, theorem status, proof/audit evidence, disabled runtime preparation, completed modules and sites remain untouched. Denied cache retrieval was not retried. Publication uses `[skip ci]` with exact remote verification; the worker then pauses for independent review with no compiler/checker process and the common lock free.
