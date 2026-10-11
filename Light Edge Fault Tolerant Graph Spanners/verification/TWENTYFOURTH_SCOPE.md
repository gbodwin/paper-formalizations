# Native Eulerian single-Steiner reduction: frozen 125-module packet

13 new proof modules, 112 prior production proof files unchanged. This packet
extends fully green commit 5277f0eafb5937064345c8b8645add37e88c45d8.
The exact source hashes are in twentyfourth-source-hashes.json and the production
verification/TWENTYFOURTH_ENTIRE_SOURCE_HASHES.json (root plus all 125 modules).

## Actual conclusion and scope

`exists_native_steiner_reduction` starts with an arbitrary finite native
`Graph (Option V) E`, every actual integer-valued degree even (loops count twice),
and actual 2*k-edge-fault connectivity for any supplied relation P on terminal
vertices V. Membership of all required terminals in the graph is part of the
connectivity premise. k is any natural number, including zero. V may be empty;
center degree zero and center loops are handled without invoking a positive-degree
split. Other isolated vertices, unused ambient edge IDs, loops and parallel
original edge identities are allowed.

It constructs a finite edge type F and actual graph H, a finite trace of literal
distinct-ID center splits from G to H, zero nonloop center incidence in H, all
original vertices retained in H, even degrees, and all required connections.
The actual center-free graph centerCore H has exactly the original terminal
vertex domain and retains those native fault connections and even degrees.
No abstract splitting primitive, packing existence, final cut lower bound, or
preselected admissible pair is an assumption of this final theorem.

A fresh split edge has ID none and every surviving old ID becomes some e.
The two deleted identities are distinct; their other endpoints need not be.
Equal endpoints create a loop. No original parallel identities are collapsed.
Center loops never affect cuts or nonloop incidence, and are deleted in the final
centerCore domain reduction. The trace guarantees literal valid split operations,
not a theorem that every arbitrary trace preserves connectivity.

## Proof chain to audit

1. Integral incident mass is modular and nonnegative. For a symmetric
   skew-supermodular deficit covered by that mass, tight sets sharing a positive
   identity have tight union: difference uncrossing loses twice the intersection.
2. Finite maximization constructs the largest tight set through a fixed identity.
   Symmetry prevents it from containing all identities. A partner outside it is
   chosen; if no such tight set exists, any different identity works. Even slack
   makes every non-tight dangerous set impossible. Both quantifiers are genuine
   finite choices; neither maximum nor partner is supplied.
3. A pair-separation requirement is 2*k or zero. Its union-max inequality and
   symmetry imply skew-supermodularity. Native core cuts are symmetric,
   submodular and posimodular, proved by per-original-edge endpoint cases. Their
   difference with the requirement gives the actual deficit. Original cut bounds
   imply coverage, and actual cut parity implies even slack.
4. Native center cuts are exactly core cuts plus original incident mass. The
   split graph's exact center-free cut loss is two iff both other endpoints are
   inside, zero otherwise. This preserves all required native fault connections,
   not just an abstract cut surrogate. Complement symmetry handles cuts
   containing the center.
5. A proved native handshake identity establishes equivalence of even degrees
   and even cuts, with each loop counted twice. A nonempty center incidence set
   therefore has cardinality at least two. Each constructed split reduces its
   cardinality by exactly two while preserving even degrees.
6. Strong induction on that actual cardinality constructs complete center
   elimination over successively extended finite edge-ID types. The explicit
   trace records the constructed steps. Exact core-cut equality then proves
   the actual terminal-domain reduction.

Canonical CenterInc Fintype enumeration is fixed explicitly; one local
Subsingleton.elim transports the subtype sum enumeration. This is ordinary
finite-enumeration invariance, not an identification of distinct edge IDs.

## Primary-source relationship

Chekuri–Shepherd, Approximate integer decompositions for undirected network design
problems, SIAM J. Discrete Math., printed pp.168–170: Theorem2.1 supplies general
Mader splitting; the paragraph immediately after it restricts their use to
Eulerian graphs. Theorem3.1 first removes singleton islands by splitting and
expands solutions back through the split. Cached primary PDF/text are in sources/
forest_packing_sidma.{pdf,txt}. The new packet proves the uniform-threshold
Eulerian case sufficient to preserve the specified original 2*k pairs. It does
not claim the general non-Eulerian theorem or simultaneous unequal thresholds.

Bernáth–Király–Végh, EGRES TR2011-10, pp.2–4 and6–7:
https://egres.elte.hu/tr/egres-11-10.pdf . This supplies the deficit/coverage and
dangerous-set viewpoint and symmetric skew-supermodular context. Our direct
finite even-slack proof uses neither their general Mader theorem nor a loopless
degree-specification assumption; it is a proved specialized argument.

## Explicit remaining obligations

No edge-disjoint forest is lifted through the trace yet. Original-edge path
expansion, acyclicity/pruning after expansion, simultaneous disjointness and the
multi-island contraction/packing induction remain open. General Eulerian forest
packing/congestion, weighted/fractional dependencies, EFT main upper bounds,
Theorem34's defective certificate repair and runtime are not completed here.
The previously proved finite native Theorem22 iff remains unchanged.
No new source error is asserted; the original statement is retained.

## Gate distinctions

All13 draft and production sources strictly compile. The125 root/index,
all972 declaring-module allowed-axiom checks and all13 independent official
kernel replays passed. Exact receipts are in verification/twentyfourth-local-gates.json. Reciprocal exact-source review is pending under the
two-worker cap; no child may be spawned. Exact-commit full CI and any full-paper
skeptical audit are separate future gates. Current public remote and private Site
remain the fully green112 baseline and v28 with all16 boxed-L markers.
