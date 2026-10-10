# Section 4.1 foundation semantic review

Result: **PASS for the eight frozen component modules, not for a main lower-bound theorem.**

Reviewed on 10 October 2026. This was an independent, bounded source/semantic review. No compiler or kernel replay was run, and no proof source was modified. Build, axiom-audit, kernel-replay and exact-commit CI results are separate gates owned by the coordinating task.

Parent-provided gate update: both independent four-module kernel replay groups passed on all eight frozen sources; the last group completed at 20:05:15 UTC. This is reported evidence from the coordinating task, not a replay performed by this reviewer.

## Source and scope

Source: Bodwin, Dinitz, Koranteng and Wang, *Light Edge Fault Tolerant Graph Spanners*, arXiv:2502.10890v2, Section 4.1, printed pp. 19–20, especially the cloud-subdivided cycle construction and connectivity-certificate paragraph on p. 20. The supplied PDF SHA-256 is `8552afdf89b6a44ed642154379dfd3556bc6471cedb90c518733991123489b55`, matching the supplied source manifest. The supplied text and the relevant definitions in `Basic`, `LightSpanners.Basic`, `LightSpanners.Weight`, and native Mathlib cycle/bridge APIs were inspected.

The formal cycle has N = m+3 vertices. Thus N is always at least three, excluding the two-vertex simple-graph degeneracy. Its branches are indexed by a genuine unordered base edge and a color in Fin f. Relabeling each cycle edge {i,i+1} by i identifies these branches with the source's v_(i,j); there are no phantom branches for nonedges or duplicate oriented copies. Choosing the added core graph D to be the native cycle gives the source's unweighted graph structure. Heavy-edge weights and their full forcing construction are not defined by this batch.

## Findings

1. **Finite fault pigeonhole and localization:** Different colors have disjoint actual edge sets. The counting proof bounds the disjoint union of F intersected with those edge sets by F itself, so faults that are nonedges, or added core edges, do not invalidate it. F.card < 2 * card I ensures a color with at most one failed actual edge, including the empty-color boundary correctly. The subsequent localization uses the sum-type endpoint distinction and branch identity to isolate one bad base edge; when the intersection is empty it selects an arbitrary genuine base edge, using the explicit nonempty-edge premise.

2. **Actual base-walk lifting:** Connectedness and absence of bridges are substantive stated premises of the general theorem. Deleting the localized base edge leaves a preconnected graph. Each remaining base adjacency is replaced by its two surviving subdivision edges of the chosen color, and induction transports actual walks. There is no assumed fault-tolerant host, packing theorem, or assumed conclusion.

3. **Full preserver semantics:** `IsFTConnectivityPreserver` explicitly requires subgraph inclusion and all-pairs reachability equivalence for every permitted finite fault set. `unit_graph_isFTPreserver` replaces surviving unit edges by themselves and each surviving extra core edge by a lifted core walk, then transports every input walk. The converse is actual subgraph monotonicity after faults. A branch with both incident edges failed is isolated in both graphs, since D adds only core-to-core edges; neither the definition nor proof assumes the whole post-fault graph is connected. This also handles reflexive reachability and other disconnected pairs.

4. **Native cycle specialization:** The specialized theorem establishes a nonempty genuine edge set and proves absence of bridges from the actual degree-two native cycle, using Mathlib's finite-cycle edge-deletion reachability result. Native cycle preconnectedness supplies the other premise. With f>0, the natural-number budget 2*f-1 is strictly below 2*f. The result covers arbitrary D, and hence the intended D equal to the base cycle.

5. **Vertex and weight accounting:** Degree sum yields exactly N native base edges. The vertex type therefore has exactly N+N*f vertices. The explicit dart encoding covers every unit edge, giving the proved upper bound 2*|E(C)|*card I, hence 2*N*f on the cycle. Unit-weight summation is over actual graph edges and assumes weight one only there. The formal result is an upper budget, not an exact subdivision-edge-count equality; the README and checkpoint describe it accurately. This upper budget suffices for the intended certificate comparison once the remaining assembly exists.

6. **Cut-cycle containment:** The statement concerns the actual cycle after deletion of {0,N-1} and actual `pathGraph N`. Its proof removes precisely the modular wraparound possibility and handles both orientations and the impossible loop case. The theorem proves containment; the docstring's informal description of the remaining edges is mathematically consistent, but equality itself is not the checked theorem.

7. **Potential telescoping and forcing:** The potential bound is proved by actual walk induction. Forcing uses a specified finite fault set of size at most f, an original edge that survives that set, and a strict potential gap. Its Lipschitz premise is imposed on the actual input graph after those faults and deletion of the candidate edge. If the output omitted the edge, its returned replacement walk embeds in precisely that graph, contradicting the gap. No replacement-distance lower bound or retained-edge conclusion is an input. Nonnegative weights or stretch at least one are not needed for this conditional real-valued lemma itself. Constructing a suitable potential, checking it on all remaining heavy edges, and imposing the eventual weight/parameter conditions remain genuine obligations.

## Scope claims

The inspected README and `verification/CHECKPOINT.md` accurately call this partial foundation work, separate local build/audit from still-pending review/replay gates, and leave the heavy-edge potential, rotations and genuine optimal-denominator ratio assembly open. No joined Theorem 9 or 10 lower bound is claimed. The source's displayed Theorem 9 uses f-competition while its p. 20 proof establishes the stronger (2f-1)-competition assertion; this batch establishes the latter certificate only and does not conceal that distinction. Uncompiled draft modules were excluded from review and from this PASS.

No semantic or source-correspondence blocker was found within the declared frozen scope. This report does not certify the unreviewed drafts, global main theorems, runtime, exact-commit CI, or a completed whole-paper formalization.

## Frozen SHA-256 values

All eight actual source files under `repo/Light Edge Fault Tolerant Graph Spanners/LightEFTSpanners/` were hashed during this review and matched both `review/sixth-source-hashes.json` and `verification/SIXTH_SOURCE_HASHES.json`:

- PotentialForcing: `65dc60706b5b2d4d6901f64ebd448cc3b8cc194d26ecd699013cd77fc45ad4fe`
- DisjointCycleFaults: `c0a84a6ceea2903462dbefa951c84bbf79ee42a6c305f6ee6ad64181ee8efbf7`
- ParallelSubdivision: `979027328eaeb4448148156612caa4c34469df3d7734361109b0214ae3b7b9c8`
- SubdivisionCleanColor: `64d92c234fa997bb5dc13e0a3341625fd1362ddd6316e5739853f2abb631700b`
- SubdivisionPreserver: `9f340f8e34da589bb1982dd634c2a5052d44246e1f958905429c2f0be2a81a14`
- CycleCertificate: `8a28b4a56a57e4107e0262878a4f7da561009af1deaf0e4ef5d226592cb61e9c`
- SubdivisionWeight: `30ba749f9efe08ad2f8c9181789901910a8aae352fb49a8cb5d8abf76a641125`
- CycleLinearization: `7fe935f1f82118bbcd74d7aefe0fcd108d50020084905fc0a3ad37d30350665c`
