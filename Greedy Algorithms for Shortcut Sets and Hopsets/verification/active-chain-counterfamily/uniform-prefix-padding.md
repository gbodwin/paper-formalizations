# Source-multiplicity padding: bounded skeptical review

Date: 2026-10-10. Source-only mathematical review. No compiler, finite test execution, Git change, or publication was performed. This is an ordinary proof review, not a Lean theorem.

## Result

The uniform prefix-padding argument is correct under its stated hypotheses. Its exact distance and raw-drop identities extend from inherited states to **every legal padded state**, by projecting away fresh-endpoint edges. Consequently the entire positive-drop greedy choice relation and its phase lengths are preserved at a **fixed stopping threshold D >= 2**. This does not identify independently chosen tie-breaks or independently recomputed thresholds.

There is a precise additional obstruction to a source-multiplicity repair. Padding the existing guard-collision family gives, for arbitrarily large parameters, an **active instance with an equal-size maximum packing at the canonical radius**, in which:

- m^2 failed prefix/suffix pairs still return the same last-bad-chain guard;
- that guard supplies q = 3m actual off-path chains, each of cardinality r;
- among their qr vertices, at most 3m+1 can ever have any positive source-row saving, at any legal state or for any insertion.

Thus neither collision incidences nor all vertices in the supplied off-path chains can be counted as distinct useful source charges. The already-known cubic-saving edge in that family survives unchanged. This is **not a counterexample to universal cubic progress or to the desired O(n I / L^2) phase bound**. Both remain open here.

## 1. Model and sources checked

The source is arXiv:2511.20111v2, Section 5, particularly the source-dependent validity definition and Lemma 5.7 proof. The review also checked:

- the exact original source-multiplicity/phase question;
- the uniform-prefix-padding derivation and the included diagnostic script/results;
- `near-maximum-obstruction.md`;
- `cubic-rectangle.md`;
- `guard-collisions.md`;
- the source interfaces in `DirectedPaths.lean`, `ChainDistance.lean`, `PackedChainOutput.lean`, `ChainGuardSeparation.lean`, and `ChainGuardCone.lean`.

The endpoint-floor and excess-potential identities are already present in `ChainEndpointFloor.lean` and `ChainExcessPotential.lean`; they are not claimed as new results of this review. The known additive-window and quadratic-derived bounds are not reproved or strengthened here.

Throughout, earliest entries are fixed by original reachability. The selected objective remains the sum of all actual important distances. The stopping test remains the maximum of those distances. No rebased minimum-path optimality is assumed.

## 2. Exact all-state projection lemma

Let the old graph have a disjoint nonempty chain cover C_1,...,C_I, covering all old vertices V, and contain consecutive forward chain edges. Form the padded graph exactly as in the proposed proof: extend each chain to r vertices by a fresh prefix, and give every fresh vertex a base edge to every old vertex. Let F denote the fresh vertices and A = |F|. Let J be **any** legal shortcut state of the padded graph. Define

    pi(J) = J intersect (V x V).

This is a legal old state, because original reachability between old vertices is unchanged.

### Old-source paths

No old vertex reaches a fresh vertex, even after legal insertions. Therefore every path from an old source stays in V, and the edges available there are exactly the old base edges together with pi(J). Enlarging a chain by an unreachable prefix does not change any old source's earliest entry on that chain. Labels of old vertices are unchanged. Hence the sets of old-source valid paths, their chain counts, all old important pairs, and all their normalized distances agree exactly with the old instance at pi(J).

### Fresh-source rows

A fresh source p on C_i reaches only later fresh vertices of C_i, together with every old vertex. It reaches no fresh vertex of another chain. Thus its own-chain important target is p, at distance 1; its important target on C_j for j != i is the first old vertex of C_j, at distance 2. The base contains the direct edge realizing the latter distance. The two distinct endpoint labels give a lower bound of 2 for every possible route, even after arbitrary legal insertions. There are exactly I demands in this row, so its row potential is permanently 2I-1.

Consequently, for every legal J,

    phi_plus(J) = phi_old(pi(J)) + A(2I-1).

The same argument identifies old source-row potentials individually, not merely their total.

### Arbitrary insertion batches

For any legal set E of new candidate edges, projection commutes with union, so

    phi_plus(J) - phi_plus(J union E)
      = phi_old(pi(J)) - phi_old(pi(J) union pi(E)).

Thus the preservation concerns every batch marginal as well as every one-edge marginal. A fresh-endpoint edge has zero marginal. An old edge has exactly its old marginal. This is an exact quotient of the potential landscape, not an inference from the thirteen finite examples.

The largest one-edge drop is preserved whenever that maximum is defined. For degenerate instances with no old candidate edges, interpret the best drop as the maximum over {0} together with the candidate drops. Active states below automatically have a nonempty candidate set, so this convention does not affect greedy execution.

### Fixed-threshold active greedy histories

For a fixed D >= 2, all fresh-source demands already satisfy the stopping condition. Therefore padded and projected states are stopped simultaneously. If they are active, an old important demand has distance greater than D. Its direct legal repair attains cost at most 2 and therefore gives a strictly positive raw-potential drop. A maximum-drop choice cannot have a fresh endpoint.

Since all old marginals agree, the sets of positive maximizing old edges agree. Induction transports any active greedy history, including its exact number of insertions until the fixed threshold is met. Arbitrary already-present fresh edges are immaterial. A particular independent tie-breaking implementation need not choose the same member of this common maximizing set.

This also transports a phase stopped at L/2 when L/2 >= 2 and the same numerical threshold is used on both instances. It does **not** compare runs whose thresholds have been independently recomputed from their different vertex counts. The factor n I in the proposed phase budget also grows under padding; history preservation alone supplies no lower bound contradicting that budget.

## 3. Preprocessing, maximum packing, and radius

### Within-chain preprocessing replacement

Replacing an added forward edge inside one chain by its consecutive chain segment preserves source validity: all inserted steps remain in the same chain label. It introduces no additional chain label, and no new first entry of a different chain. The resulting walk cannot repeat a vertex because all its edges are forward in the same DAG. Therefore the replacement preserves the normalized cost.

This argument applies in the presence of any fixed legal shortcut state, before and after an additional candidate insertion. Hence further legal within-chain preprocessing changes neither normalized distances nor candidate marginals. It need not preserve the literal set of path edge sequences in general: it can add new representations of the same-cost routes. In the two-vertex old cores used here, the old forward pair is already present, so further chain preprocessing adds no new old-to-old pair and the old path sets themselves remain unchanged.

The stated finite four-hop witness can consequently be used for the enlarged chains. Its cited edge-count bound is a combinatorial bound, not a machine-runtime statement. The fresh-to-old edges are part of the newly constructed original graph, which may be dense; they are not being hidden inside that preprocessing bound.

### Maximum packing

The supplied enlarged chains partition N = I r vertices into I disjoint r-vertex chains. Every disjoint family of r-vertex chains has at most floor(N/r) = I members. Thus this supplied packing is maximum, including against chains that mix old and fresh vertices in other ways.

This proves the existence of the stated maximum packing. It does not force an unrelated choice operator to select this family. Likewise, matching the canonical radius below does not identify the particular packing selected by `defaultOutput`.

### Exact canonical radius

For old chain size at most two, choose r to be the least integer at least 3 with I <= r^2. Then N = I r <= r^3. If r > 3, minimality implies I > (r-1)^2, so

    N > r(r-1)^2 > (r-1)^3.

The least integer at least 3 with N <= r^3 is therefore exactly r, as required by the actual `PackedChainOutput.radius` definition. For r = 3 the lower bound of 3 settles minimality directly.

### Rounded activity in the tree application

The hereditary-route obstruction and its old minimizers survive padding. Fresh rows have maximum at most 2, so they do not produce new qualifying near-maximum pairs in the stated beta L > 2 regime.

However, the inequality L^3 > N by itself does not imply L > radius(N): an integer L can equal the rounded radius. To assert activity for that rounded stopping rule, use an explicit additional sufficiently-large-k condition.

For the tree family, fix h >= 4 and T = 2^(h+1)-1. Since M <= 2 T k and L >= h k, it suffices to choose k also satisfying

    h^2 k > 8 T,     h k >= 4.

Then sqrt(M) < h k/2 and

    r = max(3, ceil(sqrt(M))) < h k <= L.

Such k can be chosen alongside every existing condition in the hereditary obstruction. This preserves its quantified consequence while making the rounded-activity assertion explicit. No claim of universal cubic progress follows.

## 4. A canonical-active off-path source-capacity obstruction

There is an especially direct application to the already-proved guard-collision family.

For m >= 3, its fully covered, unpadded core has

    M = 6m+1 chains,     n_core = 6m+2 vertices,     L = 3m+1.

Every chain is a singleton except C = (z,b). Its maximum-pair path is

    P = s,a_1,...,a_(3m),

and the guard path is

    Q = s,w_1,...,w_(3m-1),z.

All m^2 pairs with sources a_i, 1 <= i <= m, and targets a_j, 2m+1 <= j <= 3m, have the same unique cost-3 rebased minimum through b, the same unique last edge disallowed for s, and the same resulting guard z. These are the existing symbolic conclusions, not new finite-test assumptions.

Apply uniform prefix padding with r least at least 3 such that M <= r^2. The resulting N = M r instance has the supplied maximum packing and exact canonical radius r by Section 3. Moreover, for m >= 3,

    M = 6m+1 <= (3m)^2,     r <= 3m < 3m+1 = L.

Thus this is active at the **rounded** stopping threshold, with no asymptotic rounding qualification. All old distances, paths, important pairs, and guard collisions remain unchanged by Section 2.

Let W consist of the q = 3m chains absent from P and occurring on Q: the 3m-1 singleton w-chains and C. After padding, their union contains q r vertices. Among those vertices, only the 3m+1 old vertices can ever have a positive source-row marginal. Every other vertex is fresh and has a permanently saturated row. This holds at every legal padded state, for every one-edge insertion and even every insertion batch.

More generally, if every old chain has at most b vertices, the union of any q enlarged chains contains at most b q sources capable of any positive marginal, although it contains q r vertices. For every proposed positive constant c, choose r > b/c. Then a lower bound asserting c q r distinct useful source vertices solely from those q chains is false.

In the collision family, r tends to infinity with m. Its actual guard-path source-capacity ratio is at most

    (3m+1)/(3m r),

which tends to zero. This applies to genuine off-path chains supplied by an actual inaccessible guard, not merely to an arbitrary collection of irrelevant chains. It also occurs with maximum packing and the canonical radius while the literal stopping test is false.

The conclusion is deliberately limited. The old w-source rows can still support many distinct targets and large savings. In particular the known insertion

    (w_m,w_(2m))

retains its old raw-potential drop of at least m^2(m-1), asymptotic to L^3/27. The padded instance is therefore not a cubic-progress counterexample. What it rules out is replacing a proved count of off-path chains by that count times their common length as though those were automatically useful independent source rows.

## 5. Exact unresolved boundary and diagnostic scope

A complete source-multiplicity repair still needs to construct, for one common insertion, sufficiently many distinct actual important pairs with actual positive savings. In particular it must control all three of:

1. Which supplied vertices have unsaturated rows and retain substantial old distances after rebasing.
2. How many of those distinct pairs are supported by the **same** candidate insertion.
3. How to count colliding guard paths or recursive charges without duplicate use of the same source/target pair, while preserving the necessary distance scale.

Neither chain cardinality, maximum packing, nor canonical-radius alignment supplies item 1. The collision example independently prevents treating guard incidences as distinct guards. A phase proof could avoid a one-step cubic assertion, but still needs an amortized argument for the literal raw-potential maximizer; the exact padding projection does not provide that missing argument. No multiplicative cone shrinkage or rebased optimality has been introduced here.

The diagnostic script checks thirteen finite instances: the asymmetric hereditary example and twelve fixed-seed small DAGs. It recomputes old distances, new-row minima, the potential offset, old and fresh candidate marginals, and an inherited nonempty state where such a missing old candidate exists. I inspected this scope but did not rerun it. Those tests do not establish arbitrary-state projection, packing optimality, the radius identity, or the asymptotic source-capacity obstruction; those conclusions rest on the proofs above.

**Final status:** padding and its scoped consequence pass this bounded mathematical review. The all-state/batch projection lemma and canonical-active source-capacity obstruction are rigorous ordinary deductions suitable for a later formalization if desired. Universal cubic progress and the O(n I / L^2) phase assertion remain unresolved.
