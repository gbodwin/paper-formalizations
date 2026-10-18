# Light EFT package-stage attempt: four-stage execution passed

**All four bounded stages and the final receipt/preservation gate passed. Independent result review is pending.** Exactly one authorized entry call used implementation **`2d75404bfd140d0e8ecb13d3c2554b853b9a1640`**, with one fresh post-planning coordinator callback explicitly authorizing reuse of released lock **33:3258**. There was no automatic retry, source promotion, broad build, retrieval or CI execution. This is incremental staged-theorem evidence, not clean dependency provenance or whole-paper completion.

## Exact tested artifact

The compiled module is **`LightEFTSuppliedForestStage.SuppliedForestGoodEvent`**. The public theorem remains **`LightEFTSpanners.SampledGreedy.voting_good_event_of_supplied_forests`**. The exact staged file belongs to implementation `2d75404b`; its unchanged 4,988-byte payload originates at preparation commit `40029953e9e53525f0f1f431d6d56333b05183a3`. The wrapper's `source_commit` field records that payload origin. Frozen imported project source remains `78cb40c7837db049d645d73696f2e0b724ce8a3b`. Publication HEAD was separately `9c80a0e9f8662bf7908b3063cdbb25e38cc39d35`; it did not replace the tested implementation in plans, environments or receipts.

| Artifact | Bytes | SHA256 |
| --- | ---: | --- |
| Submitted theorem source | 4,988 | `6356a3b369813a155e824e471b0f7a48d29a66fb117db41eca767ed3300febee` |
| New target `.olean` | 185,576 | `b5e18c2425b50a2b7008f2a5f9ab928f22daae1d530293d373691a0a378cbc18` |
| Recursive audit TSV | 10,483,642 | `a3bf42e240b49ddfd17a6566f5b51b546c465de25a4441a3a701c168298e4260` |

The exact source snapshots are in each applicable stage's evidence. [Produced-object bindings](produced-object-bindings.json) map the untouched work-root object to its byte-identical archived copy under `produced-objects/`; that copy is evidence, not an accepted-project object. The original source's draft comment was preserved byte-for-byte; this report records its successful execution without editing or promoting the source.

Official pinned Lean **4.34.0** and the accepted local dependency/object inventory were reused. [Exact argv, environments, tool/source/pin bindings](commands-and-source-tool-bindings.json) and [entry command](commands.txt) are preserved. Compile/resolve/audit used the reviewed direct Lean command with `-j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true`; replay used only `leanchecker -v LightEFTSuppliedForestStage.SuppliedForestGoodEvent`. No default Lake build or imported-module recompilation was requested.

## Four individual stage results

| Stage | Attempt UUID | Child PID | Exit |
| --- | --- | ---: | ---: |
| Compile | `fe15e2888e8a4670afa16bf08ac58422` | 6689 | 0 |
| Exact resolution | `96f216431d344ada804de42aa93d97c2` | 6723 | 0 |
| Singleton kernel replay | `ee728129ca2946fe9fd399b23ab977bb` | 6749 | 0 |
| Focused owner/axiom audit | `b7ccceb1695845c3958380496e471443` | 6771 | 0 |

All four logs have **zero actual Lean warnings/errors**. Mimalloc option text such as `max_warnings` is allocator configuration, not a Lean warning. Raw logs are unedited. The [resolution result](resolution.json) selects exactly the new target object. The replay log contains exactly the reviewed singleton replay diagnostic.

The audit inventories **one actual-owner theorem root**, the named public theorem owned by the isolated physical module. Its exact reachable closure contains **22,362 constants**, **14 opaque bodies**, no unsafe/partial finding, and only **`propext`, `Classical.choice`, `Quot.sound`** as axioms. There are zero strict findings. Traversal covers constant types, definition/theorem/opaque values, inductive family/constructor links, constructor parents and recursor family/constructor/rule-RHS links as implemented in the unchanged audit traversal. It does not claim an audit of unrelated or unreachable declarations.

[Audit reconciliation](audit-reconciliation.json) independently checks the serialized graph is exactly reachable from the one root; this Python evidence check is not another Lean audit. [Raw audit files](audit-raw/) and [53 ordered recursive-export chunks](../light-eft-supplied-forest-package-20261018/production-evidence/exports/recursive-dependencies.tsv/manifest.json) are preserved. Concatenate listed part bytes without added separators to reconstruct the exact TSV/hash above.

## Ownership, resources and preservation

[Execution reconciliation](execution-reconciliation.json), [controller result](controller-result.json), [fresh coordination](coordination.json), and the four original [receipts/logs/samples](../light-eft-supplied-forest-package-20261018/production-evidence/) record the complete execution. The four UUIDs and child PIDs are distinct; their owned intervals strictly do not overlap. All used the same explicitly reused device/inode **33:3258**, directory identity **[33,1]**, ownership epoch `7d164441f8ac44d9b9c316cdd79869f3`, linked to the prior released epoch. Fresh coordination preceded acquisition by **0.097191291 seconds**. No inode creation, replacement, truncation or other-lock adoption occurred.

The unchanged kernel readbacks were AS **12 GiB**, CPU **60 seconds**, CORE **0**, and FSIZE **16 MiB** for ordinary stages / **64 MiB** for audit. The wall deadline remained **90 seconds per stage**, with all existing admission, visible/host floor, RSS and anonymous-growth checks. Runtime-wall-to-confirmation was 44.166 / 44.482 / 44.759 / 45.432 seconds respectively, including approximately 40.5–41.5 seconds of preexec preservation/handshake waiting. Per-stage samples, admission values and sampled versus `wait4` RSS metrics are retained; sampled peaks are intermittent, not continuous measurements or kernel heap caps. Visible accounting retains `PARTIAL_VISIBLE_ANCESTORS; unseen limits UNKNOWN`.

All four source-bound receipts confirm inherited lock identity, kernel limit verification, waitid/wait4 status agreement, child reaping, no remaining descendants and between-stage preservation. The final gate records `preservation_failed=false` and `preserved=true`. The lease released only after kernel ECHILD. Terminal inspection found **no active compiler/checker**, and verified the same common inode free. The released lock, work root and generated artifacts remain in place.

The canonical journal has **69,628 rows**, including the same **11,426 newly observed local signature bindings**. Initial and final excluded-metadata exports each have **62,420 rows** and identical SHA256 `1c3fc58cf35713fed67a78a70fa7dcb79c530995da154abc2061b017e8dd493c`. [Export summary](export-summary.json) links all ordered manifests, including 101 input-journal chunks and 87 chunks for each metadata journal. [Runtime bindings](runtime-bindings.json) seal all 365 runtime/claim files. [Prior failure preservation](prior-failure-preservation.json) verifies the earlier failed attempt's 215 outer entries and ten runtime files unchanged.

Signature bindings remain **newly observed local evidence**. This run verifies their recorded bindings within the bounded execution; it establishes neither historical preservation before observation nor authenticated dependency provenance. No clean dependency rebuild or aggregate replay occurred.

## Fixture publication correction and remaining scope

The original 225-entry preparation manifest listed **67 synthetic `.olean` files that were absent from the Git tree at `9c80a0e9`** because recursive `git add` honored ignore rules. That historical omission is not described as a complete publication retroactively. This outcome commit explicitly force-adds those exact paths after verifying each against the original manifest: payload **`synthetic object, not Lean`**, **26 bytes**, SHA256 **`caaf4b95f8809f37ea163cb7825e5bf370f673aa16a5adf8a3fb42865029afc0`**. [Correction record](fixture-publication-correction.json) enumerates all 67. No fixture was rerun and no inventory pass was added for publication. These bytes are synthetic fixture data, not compiled Lean objects or runtime inputs.

The verified theorem remains conditional on finite graphs with `Q ≤ G`, the supplied acyclic subforest family of Q, eligible-host lower bound, congestion at most two, positive f/h/k/eps, stated weight positivity/nonnegativity, and `AccurateTrace` for the supplied fixed tape. It proves the EFT-spanner and weight/competitive-lightness conclusions for that input, including the zero-seed-weight consequence. It does not construct the required forest family, establish a sampling law or minimum-seed theorem, or prove an algorithmic runtime bound.

All publication additions are sealed and explicitly staged, including ignored fixture and generated-object evidence. Published with `[skip ci]` on the existing `light-eft-spanners-checkpoints` branch. Independent result review remains pending. No source was promoted; the worker stops here with no compiler/checker running.
