# Internal SCC connector and unconditional finite directed reachability

Tested source: `b2f6cbd033c8aa87597f09d11aa7f3655f1e245d`. Additive branch `checkpoint/scc-internal-20261016`, CI skipped. This checkpoint discharges the internal-connector and bidirectional-sourcewise premises within the existing finite directed graph model. It awaits independent review; no whole-paper completion is claimed.

## Prior review recorded

The user reports acceptance of SCC source `b3ea492e33df053dd186d0fe1d7c7499909c2fb0` and evidence `11690f560db73f1f05ef121d5687a1e088168482`, verifying all 77 manifest entries, 41 chunks, 214 roots, the 18797-constant closure, six source-bound locked receipts and preservation of prior work. That accepted checkpoint retained the C=4 internal-connector premise. This records independent source/log/hash reconciliation, not fresh execution or CI. The reviewer was idle before work resumed. All prior proofs and evidence remain unchanged.

## Internal construction

`componentVertices` is the actual vertex subtype of an SCC. `component_induced_reachable` uses the accepted `support_same_component` theorem to restrict an original allowed path to the induced ambient graph on that subtype. The restriction is justified for every support vertex. `allowed_map_iff` transfers allowedness through graph-homomorphism walk maps.

`exists_component_connector` chooses the component representative as root and applies the existing `exists_root_preserver` to the induced graph with zero weights. Original induced reachability makes each root distance finite; preserved finite distance gives actual allowed walks in both directions. Concatenation then connects any two vertices within the component. The construction filters the resulting arcs to actual induced adjacency and maps them back to original vertex pairs. The mapped connector is a subset of original input arcs, and its cardinality is at most twice this component's size.

`component_fiber_card_sum` proves the exact identity

`sum_c Fintype.card(componentVertices K A c) = Fintype.card V`.

It uses the equivalence between the sigma type of quotient fibers and the original vertex type. This includes empty V. `exists_internal_connector` unions the component connectors; finite-union cardinality and the fiber identity give at most `2*n` arcs in total. It does not charge `2*n` separately for every component. The result connects every same-SCC pair using only actual input arcs.

## Discharged premises and endpoint

`sourcewise_bound_uniform` supplies the constructed connector to the previously proved quotient, representative-arc lifting and budget theorem. It proves `SourcewiseBound K A 4` for arbitrary orientations A, with no SCC, DAG, connector or sourcewise-existence premise.

`bidirectional_sourcewise_uniform` instantiates that theorem for both A and `fun u v => A v u`, with the same uniform constant 4.

`exists_reachability_preserver` applies the accepted HalfCover and amplification construction. For every finite V, ambient simple graph K, arbitrary directed allowed relation A, and finite ordered-pair demand set P, it produces F such that:

- `F ⊆ inputArcs K A`;
- `|F| ≤ 8*n + 25*n^(2/3)/(1-(1/2)^(2/3))*p^(2/3)`;
- each demanded pair is reachable using F if and only if it was reachable using A.

There is no sourcewise, acyclicity, internal-connector, supplied-path, hitting-set or preserver premise in this final statement. Empty vertex/source/demand sets, same-SCC demands, coincident endpoints and unreachable demands are included by the existing constructions and the finite fiber argument.

The formal domain remains finite oriented input arcs supported by an ambient simple graph. This is a reachability existence theorem, not a weighted-distance theorem or a runtime/algorithmic-complexity claim. The earlier distance/reachability citation mismatch is not changed into a claim about a stronger distance theorem. No website or whole-paper completion claim is made.

## Validation and raw evidence

Official Lean 4.34.0 and accepted pinned dependencies were reused incrementally. No clean dependency rebuild, default Lake build, dependency update, CI execution or parallel worker was used. Exact toolchain executable, source and local object hashes are in `evidence/source-toolchain-object-hashes.json`. Dependency search paths include the accepted local build and original candidate fallback, as in prior incremental checks.

Final compilation used `-j1 -DautoImplicit=false -DwarningAsError=true` and emitted zero warnings. Official `leanchecker -v SlackSparsification.SCCInternal` replayed the new module individually. The strict recursive audit passed: 223 actual-owner project roots, nine declarations owned by the new module, 18871 recursively visited constants and 14 opaque bodies. Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms. Types and bodies are traversed; unsafe/partial declarations and other axioms are rejected.

Four locked invocations are preserved: one failed compilation, one successful compilation, one individual replay and one audit. The failed attempt exposed a Fintype-instance mismatch between the set-subtype and predicate-subtype cardinalities in the fiber sum. The repair uses an explicit cardinality equivalence for each fiber before applying the sigma-fiber equivalence. This is a proof repair, not a mathematical assumption or a paper counterexample. The entire raw diagnostic and submitted source remain in that attempt's UUID directory.

Every invocation used the universal exclusive lock and unique source-bound receipt. `execution-reconciliation.json` verifies all four source hashes, UUID uniqueness, one lock inode, non-overlap and child reaping. Full commands/options, submitted-source snapshots, lock ownership, child PIDs, and UTC/monotonic times are retained. Entry point: `python checkpoints/scc-internal-20261016/run.py SCCInternal [replay|audit]`.

The original recursive TSV is preserved alongside ordered row-aligned chunks. [audit-export/manifest.json](audit-export/manifest.json) gives each chunk's bytes/hash and the whole-file reconstruction hash. Concatenate chunk bytes in manifest order without extra headers or separators. The complete evidence manifest covers reports, logs, receipts, snapshots, inventories and chunks.

Terminal checks show no Lean/Lake/checker process and a free common lock, approximately 23 GiB disk free and a 16 GiB memory limit. Paused for independent review of this unconditional reachability checkpoint. No general mathematical construction premise remains in the endpoint; independent review and any later coordinated clean CI are still pending.
