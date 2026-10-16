# Uniform DAG sourcewise bound; general SCC reduction remains

Tested source: `42748534aa8b774dfdf759734b6255a96ab589a4`. Additive branch `checkpoint/sourcewise-collision-20261016`, CI skipped. This is a meaningful DAG endpoint for independent review. **The general sourcewise theorem is not yet proved.**

## Prior independent review

The user reports acceptance of foundational source `895844eb7f4596a4ab5938cc8ac6d0f2a341bb0f`, evidence `896b55442474eb21433eb4b0f226b052db70f537`, all 80 manifest entries, 40 chunks, 160 roots, the 18533-constant closure, seven source-bound locked receipts and preservation of prior work. This is recorded as incremental source/log/hash reconciliation, not CI or fresh execution. The reviewer was idle. All existing mathematical files and evidence are preserved unchanged.

## Acyclicity and collision proof

`SelectedAcyclic K F` explicitly means every allowed closed walk on F is nil. `selected_acyclic_path` derives simplicity of every allowed walk by applying this property to its closed subwalks. Acyclicity is an ordinary graph hypothesis, not an axiom or an assumed collision theorem.

`ordered_walk_split` orders two vertices on the actual fixed-demand walk, constructing prefix, middle and suffix walks. `incoming_in_middle` locates a required incoming edge at the later split vertex in the middle segment: simplicity excludes the prefix and the suffix.

`collision_ordered_impossible` splices the other source's prefix, that middle segment and the second target's suffix. It explicitly proves that each avoids the competing required edge. The middle avoids it by incoming uniqueness; the prefix avoids it because acyclicity makes prefix-plus-middle simple; the suffix avoids it because a simple path cannot enter its start. The concatenation contradicts requirement of the competing edge.

`required_collision_unique` combines this distinct-vertex contradiction with the accepted same-vertex proof. It gives equality of both ordered incoming edges for collisions sharing a fixed demand and other source. The same-vertex case is not silently discarded.

## Injection, counting and optimization

`competing_arcs_card` chooses a requiring demand for each competing edge and labels it by that demand's source. Collision uniqueness proves injectivity, hence at most |S| competitors. Existence of requiring demands is supplied by the earlier minimal-preserver construction when this lemma is used in the endpoint.

`required_heavy_mul_le` constructs disjoint incoming-edge fibers, omitting the fixed required edge from each. Each heavy vertex contributes at least d competitors. Distinct required heads prevent double counting, giving h*d ≤ |S|. `required_heavy_card_le` uses d≥1 to divide safely.

`acyclic_required_total_bound` covers heavy arcs by the union of their requiring-demand fibers, using union inequalities even when several demands require one arc. Together with the accepted light bound, it proves `|F| ≤ n*d + |P|*|S|/d` for d≥1.

`exists_sourcewise_dag_integer` constructs a minimal input-arc preserver internally and discharges the requirement-label and minimality premises before applying that bound. Its only graph restriction is acyclicity of actual input arcs.

`sourcewise_dag_parameter` chooses `d = ceil(sqrt(n*p*s)/n)+1` for n>0. It proves d≥1 and the uniform bound `n*d+p*s/d ≤ 2*(sqrt(n*p*s)+n)`, including p*s=0 without dividing by it.

`sourcewise_bound_of_acyclic` proves `SourcewiseBound K A 2` for every acyclic orientation A. The empty-vertex case is separate. Zero sources/demands are allowed. `selected_acyclic_reverse` proves reversal preserves the explicit condition, so `bidirectional_sourcewise_of_acyclic` supplies both orientations with the same constant 2.

`reachability_complete_acyclic` applies the accepted HalfCover and amplification endpoint, with actual input-arc support and reachability equivalence on demands. Its bound is

`4*n + 13*n^(2/3)/(1-(1/2)^(2/3))*p^(2/3)`.

This DAG theorem has no sourcewise-construction premise. It **does** retain the explicit acyclicity restriction. It is not the general-graph theorem or whole-paper completion.

## Remaining SCC work

SCC contraction, linear-cost internal in/out trees, quotient-demand/source deduplication and lifting chosen quotient arcs to original input-arc representatives are not implemented here. The general endpoint still retains its bidirectional sourcewise premise. The next proof must transfer the DAG construction to the SCC quotient, account for the internal-tree union, and prove original reachability and arc support after lifting. See [SCC-NEXT.md](SCC-NEXT.md) for proposed contracts, all explicitly unproved.

No false paper statement or counterexample was established. The explicit same-vertex split and segment-avoidance reasoning fill proof details; they do not change the asserted sourcewise bound.

## Strict sequential validation

Official Lean 4.34.0 and accepted pinned dependencies were reused incrementally. No clean dependency rebuild, default Lake build, CI run, parallel worker or site change occurred. Exact source/toolchain/object hashes and dependency search paths are retained. The search path includes the accepted local build and original candidate fallback, as in the prior incremental checks.

The final module compiles with `-j1 -DautoImplicit=false -DwarningAsError=true`, with zero warnings. Official `leanchecker -v SlackSparsification.SourcewiseCollision` replays this module individually. The strict recursive audit passes: 187 actual-owner roots, 27 declarations owned by the new module, 18655 recursively visited constants and 14 opaque bodies. Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms. Types and bodies are traversed; unsafe/partial declarations and other axioms are rejected.

Nine invocations are preserved: three failed compilations, four successful compilations at additive stages, one individual replay and one audit. Failures were an unused-instance lint plus an incorrectly applied support-membership lemma; ambiguous `disjoint_left`; and insufficient numerical normalization in the final DAG endpoint. All raw diagnostics and source snapshots remain in the UUID directories. Semantic label logs are convenience copies, not the authoritative failed-attempt records.

All nine used the universal exclusive lock and source-bound execution receipts. `execution-reconciliation.json` verifies unique UUIDs, one lock inode, nonoverlapping monotonic intervals, reaped children and every submitted-source snapshot hash. Commands/options, PIDs and UTC/monotonic times are retained. Entry point: `python checkpoints/sourcewise-collision-20261016/run.py SourcewiseCollision [replay|audit]`.

The raw recursive TSV and ordered row-aligned chunks are retained. [audit-export/manifest.json](audit-export/manifest.json) records each chunk's bytes/hash and the complete reconstruction hash. Concatenate the listed chunk bytes without additional separators or headers. The evidence manifest covers logs, receipts, snapshots, inventories and chunks.

Terminal checks show no compiler/checker/Lake process and a free common lock, approximately 23 GiB free disk and 16 GiB memory limit. Paused at this DAG result for independent review before the SCC reduction.
