# Reachability contracts: conditional checkpoint for independent review

Tested source commit: `960f95c7ddf766b6ee463c6930bacf938edabdae`. Sole worker; no CI triggered. This checkpoint does **not** prove the full directed reachability result.

## Accepted directed CI correction

The user reports independent acceptance of source `58116f153e48e57a055767cabfd1bc89f622214d`: artifact `12017312820`, 937681 bytes, SHA256 `f35757c6595b065379778bf796a0c77d73b354c15e40676c82457c663e1f44b3`; all 195 manifest entries and 60 UUID receipts reconciled, including lock, PIDs, non-overlap and reaped children; the 119-root audit is byte-identical. This records source/log/hash reconciliation, not a fresh proof execution. The fresh sequencing gap is closed; historical missing-timing qualification remains.

Actual warnings are 13: ConsistentTiebreaking 8, Hitting 2, PlusFourParameters 2, Amplification 1, ParameterBounds 0. One Amplification hint contains `warning:`. The future gate and read-only reconciliation count anchored source-location diagnostic headers. Retained logs yield 13; no accepted proof was rerun merely to correct this. Raw artifact metadata and old logs remain unchanged. The old directed checkpoint hash manifest describes its original commit; the new evidence manifest covers corrected documents separately.

## Proven here

- Repaired preserved ReachabilityBasics (addition monotonicity theorem and unused-instance lint) and ReachabilityParameters (targeted associativity rewrite). Original recovered partials remain in the earlier recovery evidence; failed source snapshots are retained here.
- `sourcewise_input`: a supplied sourcewise witness can be filtered to actual input arcs without increasing cardinality, preserving reachability in both logical directions.
- `targetwise_indexed`: apply the reversed-arc sourcewise premise and swap the witness back. Image cardinality handles repeated demands.
- `reachability_via_hubs`: forward and reverse sourcewise witnesses jointly route through selected hubs, with cost at most `2*C*(sqrt(n*p*|R|)+n)`, actual input-arc support, and reachability equivalence. Union bounds remain valid for overlapping arcs and coincident endpoints.
- `reachability_complete_of_constructors`: the existing finite amplification theorem now yields an input-supported complete reachability preserver, conditional on sourcewise and half-cover constructors. Cost is `2*C*n + B/(1-(1/2)^(2/3))*p^(2/3)`.

No global/path-restricted distance identification is used. Reachability is existence of an allowed walk; unreachable demands are implication premises, and input-subset monotonicity rules out newly reachable pairs. No nonempty-vertex hypothesis is imposed. Nil walks cover coincident endpoints.

## Exact remaining obligations

`SourcewiseBound K A C` quantifies over every source set R and demand subset P with first endpoints in R. It must produce allowed arcs of cardinality at most `C*(sqrt(n*|P|*|R|)+n)` preserving each originally reachable demand. It remains an ordinary hypothesis, not an axiom or a constructed theorem. For the hub reduction, `BidirectionalSourcewiseBound` requires this for both A and `fun u v => A v u` with the same nonnegative C. An A-only bound does not justify the reverse orientation.

The [cited Abboud–Bodwin paper](https://arxiv.org/abs/1710.11250) states the sourcewise **reachability** bound. The preserved citation mismatch with the main paper's stronger distance wording remains; this checkpoint does not settle that stronger claim.

The second outstanding constructor is `ReachabilityHalfCover K A B threshold`: for every larger demand set Q, produce actual input arcs F and residual R contained in Q, with residual cardinality at most half Q and cost at most `B*|Q|^(2/3)`, routing Q minus R. Amplification itself is now discharged. The half-cover must still be built from short paths, long-path hitting and the two oriented sourcewise witnesses. The hub lemma assumes selected hubs and the two half-path reachabilities explicitly; it does not select them.

The repaired parameter lemmas establish the numerical large-demand budget with `B=(1+6*C)*n^(2/3)` when `n ≤ p²`. The small constructor applies when `p² ≤ n`. The complete wrapper requires `threshold² ≤ n`. A future complete construction must choose the threshold and connect the long-path selection to these numerical regimes. Merely supplying the numerical inequality or assuming the half-cover is not the full result. No new constant C is proved uniform over all graphs here.

## Validation and evidence

Official Lean 4.34.0 and existing pinned dependencies were reused. Exact executable, source and object hashes are retained. The dependency search path in every receipt includes the previously validated local build and original candidate fallback; this is incremental validation, not a fresh clean dependency rebuild or CI run.

Commands were `python checkpoints/reachability-contracts-20261016/run.py MODULE [replay|audit]`. Every actual compiler/checker was awaited through `scripts/SequentialLean.py`. Compilation used `-j1 -DautoImplicit=false -DwarningAsError=true`; replay used official `leanchecker -v` with one module each. Full absolute argv and paths are in the UUID receipts.

All three final modules compile with zero warnings and pass individual kernel replay. Recursive audit passes: 137 actual-owner project roots, 18 selected declarations from the three reachability modules, 18132 recursively visited constants, 14 opaque bodies, only `propext`, `Classical.choice`, `Quot.sound`. The audit traverses types and bodies and rejects unsafe/partial dependencies and other axioms; explicit theorem hypotheses remain mathematical premises regardless of axiom-audit success.

There are 14 locked attempts: eight successes (four compilations, including one intermediate Contracts version, three individual replays, one audit) and six failures. Failures comprise the original Basics draft, original Parameters draft, three Contracts elaboration/lint/syntax attempts, and the initial replay with missing official Lean on PATH. PATH was corrected without changing the toolchain. All raw logs, UUID receipts and content-addressed submitted sources remain. Source snapshots can repeat across replay attempts. `execution-reconciliation.json` checks all 14 UUID receipts, one lock inode, reaped children and nonoverlapping intervals, including failures. No raw diagnostic was overwritten; semantic label logs are convenience copies only.

`source-object-hashes.json`, `local-toolchain-objects.json`, `actual-owner-inventory.tsv`, `recursive-dependencies.tsv`, `import-closure-loaded.txt`, and all UUID attempt records support independent review. Terminal observation found no compiler/checker/Lake process and a free common lock, approximately 23 GiB disk free, 16 GiB memory limit and four-CPU quota. Paused for independent review; no website, certified branch, accepted conditional source, or automatic CI changes.
