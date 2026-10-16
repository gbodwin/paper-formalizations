# SCC quotient and lifting; internal-tree construction remains

Tested source: `b3ea492e33df053dd186d0fe1d7c7499909c2fb0`. Additive branch `checkpoint/scc-quotient-20261016`; CI skipped. This is the next quotient-and-lifting checkpoint for independent review. **The general sourcewise theorem is not yet proved.**

## Prior review recorded

The user reports independent acceptance of the DAG sourcewise endpoint with C=2 at source `42748534aa8b774dfdf759734b6255a96ab589a4`, evidence `0461e19daea0d4914e7cb7b102f9b5a5f443212d`: all 89 manifest entries, 40 chunks, 187 roots, the 18655-constant closure, nine source-bound locked receipts and preservation of prior work verified. DAG acyclicity remains explicit. This was incremental source/log/hash reconciliation, not CI or fresh execution. The reviewer was idle. No existing proof or evidence file was modified.

## Proved SCC infrastructure

`componentSetoid` defines equivalence by actual mutual allowed reachability; `Component` is its finite quotient. Reflexivity uses nil walks, and transitivity uses concatenation. `component_eq_iff` identifies equality of classes with mutual reachability. `component_card_le` proves the number of classes is at most n, using surjectivity of the quotient map.

The quotient ambient simple graph is complete, independently of the directed relation. `componentArc` requires distinct classes and an original crossing arc witnessed by endpoints, class equalities, ambient adjacency and allowedness. Thus there are no quotient self-loops and no invented directed arcs.

`project_reachable` projects actual walks inductively. When consecutive vertices have the same class, it skips that step; otherwise it inserts a witnessed quotient arc. `component_arc_lift` and `lift_component_walk` lift through original within-class paths. The nil case covers demands whose original endpoints share a class. `component_reachable_iff` proves equivalence of original and quotient reachability.

`component_reachable_antisymm` derives antisymmetry of quotient reachability from the defining equivalence. `component_acyclic` then proves the accepted explicit acyclicity predicate on actual quotient input arcs: the first edge of any nonnil closed walk would connect two distinct classes reachable in both directions.

`support_same_component` proves every vertex of an allowed path between equivalent endpoints stays in that SCC. It splits the original path at the vertex and closes the return direction through the original endpoint equivalence. No assertion equating restricted and global distances is used.

`component_demand_images` maps sources and demands as finite images. It proves both cardinalities do not increase and all quotient demand sources lie in the quotient source image. Coincident classes and repeated images are deduplicated.

## Original representatives and sparse lifting

`component_arc_representatives` selects one original crossing arc for each selected quotient arc. The resulting finite image is an actual original input-arc subset and has cardinality at most the selected quotient arc count.

`lift_selected_component_walk` lifts selected quotient walks through those representatives and a supplied internal connector I. It explicitly handles the original demand endpoints and the nil quotient walk. `lift_component_preserver` unions the representatives and I, proves original input-arc support, preserves reachability equivalently, and bounds the arc count by `|I|+|Q|`.

These sparse-lifting lemmas retain the explicit ordinary premise that I connects every pair within an SCC. They do not assert that sparse internal trees have already been constructed.

## C=4 budget: proved conditionally, not an unconditional theorem

`sourcewise_bound_of_internal_connector` proves `SourcewiseBound K A 4` provided an actual input-arc connector I has `|I| ≤ 2*n` and connects every same-class pair. It applies the accepted C=2 DAG theorem to the proved acyclic quotient, uses deduplicated source/demand images, selects original arc representatives, and lifts them.

The budget is verified in Lean: quotient cardinality monotonicity gives at most `2*sqrt(n*p*s)+2*n` selected quotient arcs; adding at most `2*n` internal arcs gives at most `2*sqrt(n*p*s)+4*n`, hence `4*(sqrt(n*p*s)+n)`. The coefficient 4 is therefore a proved consequence of the explicit connector premise, not a claim that the premise is discharged.

The arguments quantify over arbitrary orientations and allow empty vertex, source and demand sets. No artificial vertex or nonempty-type hypothesis was added. The remaining uniform theorem and its reverse-orientation instantiation require constructing I.

## Exact remaining obligation

Construct, for every original directed input, an actual arc set I of cardinality at most 2*n connecting all pairs within each SCC. The planned proof builds in/out trees within each component, proves original-arc support, and sums component-size budgets without duplicate vertices. `support_same_component` now supplies path containment needed to restrict to a component subtype. The existing root-tree theorem must be applied on that subtype or otherwise charged componentwise: using a global 2*n budget separately for each SCC would be invalid.

After this construction, instantiate `sourcewise_bound_of_internal_connector` for an arbitrary orientation, then independently for its reversal, and feed the resulting bidirectional bound into the accepted HalfCover endpoint. No such final general theorem is claimed by this checkpoint. No genuine false paper statement or counterexample was established; no site or whole-paper completion claim is made.

## Validation and preservation

Official Lean 4.34.0 and accepted pinned dependencies were reused incrementally. No dependency update, default Lake build, CI execution or parallel worker was used. Exact source/toolchain/local-object hashes and dependency paths are retained; paths include the accepted local build and original candidate fallback, as in prior incremental checks.

The final module compiles with `-j1 -DautoImplicit=false -DwarningAsError=true` and zero warnings. Official `leanchecker -v SlackSparsification.SCCQuotient` replays it individually. The strict recursive audit passes: 214 actual-owner project roots, 27 declarations owned by the new module, 18797 recursively visited constants and 14 opaque bodies. Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms. Types and bodies are traversed, with unsafe/partial declarations and other axioms rejected. Passing this audit does not discharge the internal-connector hypothesis.

Six invocations are preserved: two failed compilations, two successful compilations (one quotient stage, one final lifting/budget stage), one replay and one audit. Failure 1 was a quotient Fintype-cardinality instance mismatch and a missing induction-hypothesis argument. Failure 2 was applying implicit `card_attach` as an explicit function. Raw diagnostics and source snapshots remain in UUID directories; semantic label logs are convenience copies only.

All six invocations used the universal exclusive lock and unique source-bound receipts. `execution-reconciliation.json` verifies source snapshot hashes, UUID uniqueness, one lock inode, non-overlap and reaped children. Exact commands/options, PIDs, lock ownership and UTC/monotonic times are retained. Entry point: `python checkpoints/scc-quotient-20261016/run.py SCCQuotient [replay|audit]`.

The raw recursive TSV is preserved alongside row-aligned ordered chunks. [audit-export/manifest.json](audit-export/manifest.json) contains chunk sizes/hashes and the complete reconstruction hash. Concatenate listed bytes without extra separators; only the first chunk contains the header. The complete evidence manifest covers the reports, logs, snapshots, receipts, inventories and chunks.

Terminal checks show no Lean/Lake/checker process and a free common lock, approximately 23 GiB free disk and a 16 GiB memory limit. Paused for independent review at this meaningful quotient/lifting result, with all prior proofs and partials preserved.
