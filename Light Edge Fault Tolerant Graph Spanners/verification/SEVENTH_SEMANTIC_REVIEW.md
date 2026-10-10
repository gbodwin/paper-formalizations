# Actual Section 4.1 lower-family semantic and source review

Result: **PASS for the seven frozen component modules and their explicit lower-family scope.** This is not a whole-paper final audit or a certification of a literal every-n, epsilon-independent reading of Theorem 10.

Reviewed 10 October 2026. The review was read-only with respect to proof sources; no compiler or kernel checker was run. The reviewer independently checked all seven source hashes against `seventh-source-hashes.json`, inspected their actual definitions and proofs, and revisited the relevant prior foundations. The pinned PDF and text match `sources/SHA256.json`. Printed pp. 4 and 20 were also rendered and visually inspected.

Separate gate evidence: the coordinating task reports the 36-module/root/index build and exhaustive allowed-axiom audit PASS for 369 declarations; the inspected aggregate log confirms the audit count and gate completion. The coordinator has reported exact-source kernel replay PASS for SubdivisionForcing, CycleRotatedPotential and CoreGraphWeight. Replay of the other four modules is pending at the time of this report. These are separate gates, not checks performed by this reviewer.

## 1. Exact proved scope

Let M=m+3, f be a positive natural number, q a natural number with q≤2f−1, and t a real number with t≥1. For every m satisfying 2 ceil(t)≤m+2, the actual input is the f-colored parallel subdivision of the native M-cycle plus the direct core-cycle edges. Its weights are 1 on subdivision edges and W=(m+2)/ceil(t) on core edges. Its actual vertex count is

n=M+Mf=M(f+1).

There exists a genuine minimum-weight q-fault connectivity preserver Q. Every actual f-EFT t-spanner H of this input has competitive lightness at least n/(16 f² t). Q has strictly positive total weight. The input itself is an eligible spanner at the original real t, and for every fixed f,t the admissible family has unbounded order. For positive integer stretch k the corresponding bound is n/(8 f² k), on the domain 2k≤m+2.

The more general intermediate result gives W/(2f) whenever W≥2 and tW<2(m+2). Neither the general nor specialized theorem takes a numerator lower bound, denominator upper bound, forcing conclusion, optimality oracle, or target competitive inequality as a hypothesis.

## 2. Graph, faults, walks and all eligible outputs

`Vertex` is the sum of native core vertices and genuine unordered base edges paired with Fin f. Thus every branch is attached to exactly the two endpoints of its base edge, there are no phantom branches, and the construction is a finite undirected simple graph. M≥3 avoids cycle degeneracies. `coreWeight` assigns W precisely to the actual core graph's edges; the disjoint endpoint types prove every actual subdivision edge has weight 1. Under the finite-domain condition W≥2, all graph weights are strictly positive.

`IsEFTSpanner` requires H≤G and actual walk replacement after every permitted fault set. Walk weights sum the weights of actual traversed unordered edges. The already supplied `eftSpanner_iff_distance` identifies this formulation with the literal all-pairs weighted-distance inequality for these positive weights and t≥1, including disconnected pairs. Fault sets range over all finite unordered pairs, slightly more broadly than the source's subsets of E(G). Intersecting any such set with E(G) has no greater cardinality and leaves both G and every H≤G unchanged after deletion, so this does not strengthen the source's mathematical requirement in this setting.

For a candidate core edge {u,v}, `endpointFaults` consists of the f actual edges from u to that base edge's f branch vertices. Its proved cardinality is at most f, which is sufficient; it never contains the core edge. In `cutPotential`, the affected branch vertices have potential φ(v), so all surviving edges of these branches have zero jump. Every other branch gets the midpoint of its endpoints' potentials. The proved base jump bound of 2 therefore gives jump at most 1 on every surviving subdivision edge. Surviving direct core edges have jump at most 2≤W. Both orientations and all sum-type cases are checked.

`cyclePotential m r a = 2*((a-r).val)` rotates each desired cut to the native cycle's closing edge. Deleting {r,r−1} removes precisely the modular discontinuity. The previously reviewed path containment then proves the off-cut Lipschitz bound, while the endpoint gap is exactly 2(m+2). `core_edge_forced` applies actual walk telescoping to any replacement walk returned by the spanner property. Its strict gap contradicts omission of the edge. `cycle_core_retained` covers both orientations of every native cycle adjacency. H is arbitrary; no algorithmic origin or extra structural condition restricts eligible outputs.

## 3. Numerator, denominator and enumeration

`CoreGraphWeight` identifies the core graph with the actual injective image of the base cycle. It therefore counts M core edges once each and proves total core weight MW. Subgraph monotonicity with nonnegative weights gives totalWeight(H)≥MW.

The prior unit graph is a genuine (2f−1)-fault connectivity preserver, not an assertion that all branch vertices survive connected. Its proof transports every surviving input edge and then every input walk, including components containing fault-isolated branch vertices. Fault-budget monotonicity makes it eligible for every q≤2f−1. Its actual unit-edge weight is at most 2Mf. Only this proved upper budget is needed; the batch does not claim a new exact unit-edge-count theorem.

`IsMinimumFTPreserver` minimizes the actual finite edge-weight sum over every eligible preserver. `exists_minimum_preserver` proves attainment using the nonempty finite set of simple subgraphs, with G itself as a witness. Thus totalWeight(Q)≤2Mf is obtained by comparing the genuine optimum to the concrete unit certificate. Minimum-preserver weight is choice-independent.

`cycle_preserver_weight_pos` uses the empty fault set and the distinct adjacent core vertices 0 and 1. A valid preserver must connect them, hence cannot be empty. Every edge has weight at least 1, so its total weight is positive. All divisions in the competitive bound consequently use a real positive denominator, including q=0.

The private `canonicalWeight` only chooses a common Fintype enumeration for the same finite edge sum. `totalWeight_canonical` proves equality using subsingleton equality of Fintype structures. Similarly, the cardinality normalization goes through Nat.card and proves equality for every supplied enumeration. No weight rescaling, graph replacement, limit convention, or new denominator is hidden in this normalization.

## 4. Real stretch, nonvacuity and unboundedness

`stretch_mono` proves the correct direction: a t-spanner is an s-spanner for s≥t when weights are nonnegative. The real result applies the integer result at k=ceil(t), using t≤ceil(t)≤2t for t≥1. It loses only the stated factor two. `cycle_real_input_self_spanner` separately proves nonvacuity at t itself, rather than merely at ceil(t).

The exact cardinality theorem yields n=M(f+1), and the comparison to n has explicit uniform constants 8 and 16. `cycle_family_unbounded` supplies m=N+2k for every requested order threshold N; the real version applies this to ceil(t). This establishes an unbounded sequence of actual graphs for every fixed permitted parameter tuple. It does not assert existence at every integer n, nor dispense with the displayed parameter-dependent finite-domain restriction.

## 5. Exact source domains and formulation qualifications

Source: Bodwin, Dinitz, Koranteng and Wang, *Light Edge Fault Tolerant Graph Spanners*, [arXiv:2502.10890v2](https://arxiv.org/abs/2502.10890v2), 25 April 2025. Page numbers below are printed page numbers, with the unnumbered title page excluded.

- **Definition 1, p. 1:** introduces stretch with “let k ≥ 1”; it does not restrict k to integers. Theorem 2 on the same page explicitly does say “positive integer,” so integer stretch should not be silently imposed on Definition 1 or Theorem 9. Fault tolerance remains an integer counting parameter in the actual construction, where j ranges over [f].
- **Theorem 9, pp. 3 and 19:** begins “For any f, k ≥ 1, there is a family of n-node weighted graphs G” and displays ℓ_f(H|G)≥Ω(n/(f²k)). The p. 19 introduction says the result rules out sublinear (2f−1)-competitive lightness “for small f,k.” The theorem is a family statement, unlike the explicitly all-n wording of Theorem 10.
- **Proof of Theorem 9, p. 20:** constructs m+mf vertices and unit subdivision edges, with direct edges of weight (2m−2)/k−ϵ. It gives a (2f−1)-fault unit-edge certificate of weight 2mf and ends with ℓ_(2f−1)(H|G)≥Ω(n/(f²k)). Thus the proof supplies the stronger competition budget despite the theorem display using f. The formal construction implements this stronger scope and hence also covers q=f, since f≤2f−1 for positive integer f.
- The source's claimed complementary distance 2m−2 uses the direct edges being at least as expensive as their two-unit-edge alternatives. The reviewed proof makes that finite-range condition explicit as W≥2 and uses a strict gap. Choosing W=(M−1)/k, or the rounded real version, is a valid constant-factor choice within the source's weight family and preserves its lower-family order of growth. It avoids an implicit small-slack/sufficiently-large-cycle assumption.
- **Theorem 10, p. 4:** the exact opening is “For all positive integers f, k, n and all ε > 0:”. Its lower bullet says there are n-node graphs for the stretch (1+ε)(2k−1), and the exact displayed coefficient is `poly(f,k)`, with no ε argument: ℓ_(2f−1)(H|G)≥poly(f,k)·n. There is no explicit sufficiently-large-n clause in this statement.
- **Global convention, p. 2, footnote 1:** the paper says O_x notation hides factors depending on x, which are constant when x is constant. This is an explicit parameter-dependence convention for subscripted O notation. I found no global convention declaring all stretch parameters integral, suppressing ε in Theorem 10's `poly(f,k)`, defining that lower-bound `poly` coefficient precisely, or automatically replacing every all-n lower-bound assertion by a fixed-parameter sufficiently-large-n statement.

Substituting t=(1+ε)(2k−1) into the reviewed theorem gives the explicit lower coefficient

1 / [16 f² (1+ε)(2k−1)],

on the admissible unbounded family. For each fixed f,k,ε this is a positive constant times n and supplies the competition-threshold lower-family conclusion. Uniformity over unrestricted ε is a different assertion: this proof retains ε dependence and a finite-domain threshold depending on t. These observations warrant an explicit formulation qualification; they do not alone prove that some different construction could not establish a stronger uniform theorem.

Likewise, the previously checked high-f saturation fact (q≥n−2 forces every preserver to equal G) does not refute this fixed-parameter asymptotic family. The constructed family is outside that saturation range, and a parameter-dependent large-n threshold can avoid high-f diagonals. A saturation example contradicts only a specifically quantified finite-uniform claim whose demanded ratio actually exceeds 1. No such additional theorem-level contradiction is asserted here.

**Source conclusion:** the batch proves the mathematical lower-family content of Theorem 9 for arbitrary real stretch and its stronger q≤2f−1 version. It also supplies the lower-family ingredient underlying the intended fixed-parameter threshold interpretation of Theorem 10. It does not certify Theorem 10's literal every-n, ε-independent wording. That distinction is correctly disclosed by the current README and checkpoint, and is not a blocker to this component PASS.

## 6. Limits and frozen sources

No semantic blocker was found in this batch. This review does not cover the main upper bounds, Theorem 34, polynomial runtime, unreviewed drafts, exact-commit CI, or a fresh whole-paper skeptical audit. Those remain separate obligations.

All seven actual sources under `repo/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/` matched the frozen review manifest:

- SubdivisionForcing: `d4667ce3fdd15b947796a73645d34a53a5347da28e57fdd278a363e9258c6b19`
- CycleRotatedPotential: `34fb0d9e615e47e3610276e633c67984b3186fd226636c310c089434573681d6`
- CoreGraphWeight: `b7519d37e6a4301d1459fa6a019efdfb7ceffbd220987507e5bdbcc35e56b6e9`
- CycleCoreRetention: `51c48366b129d2e5d3940de15f4a05212097cc34144cbd982c595778ac601291`
- CycleCompetitiveLower: `dc7d3204245e89d5e673bbbf551df220ba2e4063486578a912da484a8fcc3bcd`
- CycleLowerFamily: `40f85d0d88213ecf16968f1f53be57a15490dc2447a45b40310afcd79e0c3db8`
- RealStretchLowerFamily: `b2ba82f1f22151a17865fd9e05e7cdd1c8f97c05dd28ac5bef91c373a76dec5b`

Pinned source PDF SHA-256: `8552afdf89b6a44ed642154379dfd3556bc6471cedb90c518733991123489b55`.
