# Minimal-preserver and same-vertex collision foundations

Tested source: `895844eb7f4596a4ab5938cc8ac6d0f2a341bb0f`. Additive branch `checkpoint/sourcewise-minimal-20261016`; CI skipped. This is the next foundational checkpoint for independent review, **not** a discharge of `BidirectionalSourcewiseBound`.

## Prior review recorded

The user reports independent acceptance of HalfCover source `6231f1d25ebcf9753e92156ca6fa8dc31582d606` and evidence `a12bcc14266a97efeb9c62006bb414d8f59b7a5f`: both chunk exports closed the old evidence gap, all 112 manifest entries, closures, five source-bound locked receipts and preservation of prior evidence verified. This was incremental source/log/hash review, not CI or fresh execution. The reviewer was idle before this worker resumed. All prior mathematical sources and evidence remain unchanged.

## New mathematics

`exists_minimal_reachability` constructs a cardinality-minimal preserver among subsets of actual input arcs. It applies to arbitrary orientations and finite graphs, without a DAG, sourcewise theorem, nonempty-vertex or nonempty-demand assumption. Its minimization is a proved finite-witness construction, not a new premise.

`minimal_arc_required` proves every retained arc has a demand in P which was originally reachable and requires that arc on every allowed walk of the selected preserver. `Requires` explicitly includes reachability, avoiding vacuous requirements for unreachable demands. Deleting an arc and minimality produce the witness.

`minimal_empty_of_no_reachable` proves the minimal witness is empty if all listed demands are unreachable, including empty P. `zero_sources_empty_demands` proves a source-constrained demand set is empty when the source set has cardinality zero.

`path_incoming_unique` proves a simple path cannot contain distinct incoming arcs with the same head. `path_no_incoming_start` rules out an arc entering the starting vertex of a simple path.

`required_same_demand_same_vertex` identifies required incoming arcs of one fixed demand when their heads coincide. `required_same_source_same_vertex` proves the analogous result for two different targets sharing a source: splice a prefix of the first path with a suffix of the second; the required second arc must lie in the prefix because the simple suffix cannot enter its start. Incoming uniqueness on the first simple path identifies the arcs. These results need no acyclicity assumption.

`collision_same_vertex` combines those two facts: for a fixed demand and a fixed other source, collisions at the same vertex have the same ordered pair of incoming arcs. This explicitly handles the case that must be separated before the distinct-vertex DAG splice argument.

`light_arcs_card` bounds the arcs entering vertices of indegree at most d by `n*d`, using finite incoming-arc unions. This bound holds even for d=0; the remaining heavy-edge argument must choose d≥1 before division.

All the new graph theorems are uniform in the orientation A (or selected finite arc relation F), so they can be instantiated on the reverse orientation. This does not yet supply a uniform sourcewise size bound for either orientation.

## Remaining construction

Still unproved: distinct-vertex required-edge collision uniqueness in a DAG; injective charging of competing incoming edges to sources; heavy-arc counting and optimization with d≥1; SCC contraction, linear-cost internal in/out trees, quotient-source and demand deduplication, and lifting chosen quotient arcs to original input arcs. Consequently the final reachability endpoint retains the explicit bidirectional sourcewise premise. No conditional result is relabeled unconditional.

The completed same-vertex argument is a proof detail made explicit, not a counterexample or a correction to the paper's theorem. No genuinely false paper statement was established in this checkpoint. No runtime, website, or whole-paper completion claim is made.

## Validation

Official Lean 4.34.0 and accepted pinned dependencies were reused incrementally; no clean dependency rebuild or CI run was performed. Exact toolchain executable, source and local object hashes are retained in `evidence/source-toolchain-object-hashes.json`. Dependency paths in the execution receipts include the previously validated local build and original candidate fallback. No pins changed.

Final module compilation passed `-j1 -DautoImplicit=false -DwarningAsError=true` with zero warnings. Official `leanchecker -v SlackSparsification.SourcewiseMinimal` replayed the new module individually. The strict recursive audit passed: 160 actual-owner project roots, 14 declarations owned by the new module, 18533 recursive constants and 14 opaque bodies. Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms. The audit rejects unsafe/partial constants and traverses types and bodies; it does not certify unproved construction obligations.

Seven locked invocations are preserved: three failed compilations, two successful compilations (one intermediate source, one final source), one individual replay and one audit. Failures concern unused/omitted section instances, redundant simplification, dependent equality rewriting, and a deprecated conditional-rewrite name. Consequential kernel errors and `sorry` diagnostics from failed elaborations are retained; the successful strict source contains no sorry. No failure is discarded or overwritten in the UUID records.

Every invocation used the common exclusive lock and source-bound UUID receipt, with original submitted source snapshots, command/options, source SHA256, lock ownership, child PID, timestamps and reaping state. `execution-reconciliation.json` verifies all seven source hashes, unique IDs, one lock inode, non-overlap and reaped children. Exact invocation entry point: `python checkpoints/sourcewise-minimal-20261016/run.py SourcewiseMinimal [replay|audit]`.

The raw recursive TSV is preserved and also exported in ordered, row-aligned chunks under [audit-export/manifest.json](audit-export/manifest.json), with individual hashes and a complete reconstruction hash. Concatenate chunk bytes in manifest order, without inserting headers or separators. The complete evidence manifest hashes logs, receipts, snapshots, inventories and chunks.

Terminal checks found no Lean/Lake/checker process and a free common lock, with approximately 23 GiB free disk and 16 GiB memory limit. Paused at this meaningful foundational result for independent review. No parallel workers or automatic CI were started; no existing source or evidence was removed.
