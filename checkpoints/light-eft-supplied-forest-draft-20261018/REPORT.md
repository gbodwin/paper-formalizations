# Supplied-forest good-event adapter: staged proof and execution proposal

**Preparation only: no Lean invocation, lock recreation or source promotion.** The independently accepted planning checkpoint is aafb18253721ed2af3403a8904da61cd13357b95; its acceptance is recorded from the user's review, not new execution. Frozen mathematical source remains 78cb40c7837db049d645d73696f2e0b724ce8a3b.

## Exact draft

[SuppliedForestGoodEvent.lean](staged/LightEFTSpanners/SuppliedForestGoodEvent.lean) defines the proposed theorem LightEFTSpanners.SampledGreedy.voting_good_event_of_supplied_forests. Its SHA256 is 6356a3b369813a155e824e471b0f7a48d29a66fb117db41eca767ed3300febee. This file is staged under the checkpoint, outside the accepted source/import graph. It has a complete proof draft with no sorry/admit or new premise axiom, but has not been parsed, elaborated, compiled, audited or kernel checked.

Inputs are Q<=G; the specified F : Fin(q+1)->SimpleGraph V; forest/subset certificates; direct eligible-host count at least 2*f+h; original-edge forest congestion at most two; the existing nonnegative/positive weight and positive f,h,k,eps hypotheses; and the same tape accurate on its actual reached states. **There is no additional 2*f+h<=q+1 inequality and no q-preserver/minimum-seed assumption.**

For t=(1+eps)(2k-1), the output H using exactly F and tape, and B=1+64*f*Lambda(n,t+1)/h, the statement retains:

- IsEFTSpanner G H w t f;
- W(H)<=B*W(Q);
- W(Q)=0 implies W(H)=0;
- competitiveLightness H Q w<=B.

The proof draft transfers global forest congestion through ForestComponentPacking.forest_component_congestion and restricts to eligible hosts. VotingOutput.output_isEFTSpanner supplies correctness; VotingOutputWeight.voting_output_weight_bound supplies the raw inequality. In the zero branch, nonnegative output weight and the raw upper bound first give W(H)=0. Only after retaining that fact does the ratio proof use the zero-denominator convention.

The probability join is **not solved**. ComputableForestProbability.polynomial_actual_output_failure_probability separately requires the actual q-fault connectivity-preserver certificate, represented seed equality, the reversed candidate-order identity and every indexed host draw correspondence to List.ofFn of the assignment. It also needs the existing assignment law, rational-input interpretation and hgood projection. This deterministic adapter neither constructs those inputs nor proves a sampler, packing algorithm, seed approximation or polynomial runtime.

## Proposed bounded validation

[execution-proposal.json](execution-proposal.json) gives exact official executable paths/hashes, staged source hashes, a proposed fresh output root, the environment (with an explicitly unbound reviewed-commit slot) and four sequential commands:

1. Compile only LightEFTSpanners.SuppliedForestGoodEvent into a fresh private object root.
2. Run the accepted official resolver for exactly that module and require exactly its new object with no shadow/prefix expansion.
3. Run leanchecker -v LightEFTSpanners.SuppliedForestGoodEvent once.
4. Execute the uncompiled [focused audit helper](staged/SuppliedForestGoodEventAudit.lean), importing only the new module. Inventory all its actual-owner declarations, require the named theorem, and traverse recursive types plus definition/theorem/opaque values and inductive/recursor links. Reject unsafe/partial declarations and axioms beyond propext, Classical.choice, Quot.sound.

Imported accepted objects are reused without rebuilding or replaying other modules. The LightEFT portion of that import closure has 196 modules; [accepted-imports.json](accepted-imports.json) verifies their object hashes against the prior accepted audit inventory. Other transitive library bindings still require fresh pre-exec verification against that preserved inventory. This is a proposed incremental check, not a clean/authenticated rebuild or full-graph audit.

Reviewed limit values are retained: -j1 -s65536 -M5120 -DautoImplicit=false -DwarningAsError=true; AS 12 GiB, CPU 60 seconds and wall 90 seconds per stage, core zero, per-file 16 MiB ordinary /64 MiB audit. Admission requires >2 GiB disk, >=3 GiB host availability, >=3 GiB visible headroom for compile/resolve and >=4 GiB for replay/audit. Runtime sampling at 100 ms retains the 1 GiB host/visible floor, 6 GiB observed RSS stop, 3 GiB per-visible-cgroup anonymous-growth stop and 16 MiB decision-log cap. These are bounded visible measurements, not continuous RSS proof or knowledge of hidden ancestor limits. Audit output cap is 320 MiB; ordered row-aligned chunks and reconstruction hashes must accompany complete raw exports.

The four stages require fresh admission, source-bound UUID receipts, exact object/tool/search-path bindings and inherited-lock/limit/PID-start handshake checks before each exec. Stop on the first failure; preserve diagnostics and objects; do not retry or promote source automatically. No default Lake build, aggregate replay, version probe, CI, retrieval, extraction or cache advice is proposed. The new scope/ownership wrapper is not implemented or authorized here; unchanged historical entry points must not be run as substitutes.

## Environment and ownership

[environment.json](environment.json) records the current observations. There is no visible separate ordinary worker or compiler/checker. Disk free is approximately 4.68 GiB; visible memory limit 16 GiB, headroom approximately 15.38 GiB and host MemAvailable approximately 16.69 GiB. These are preparation observations, not execution admission.

The historical lock pathname is absent. PID1 began after the prior audit; its prior supervisor/child PIDs are absent. The current cgroup namespace text happens to match the old receipt, but process/mount/lock continuity is not established. Some FD/namespace observations are permission denied and remain qualified. No historical inode is asserted free or reused.

[OWNERSHIP.md](OWNERSHIP.md) proposes coordinated exclusion, future atomic O_EXCL/no-follow creation, nonblocking flock, fresh identity binding, FD/path and inherited-description checks, whole-batch ownership and kernel-ECHILD-gated release. It explicitly preserves old receipts and requires a reviewed new epoch/wrapper rather than weakening old 33:3849 assertions.

All 486 accepted source hashes, pins, prior objects and evidence are preserved. One preparation tool-template syntax error occurred before any nested tool or shell ran; its diagnostic is retained in preparation-failures.log. No Lean failure/success result or warning count is asserted. Publish only this additive checkpoint on light-eft-spanners-checkpoints with [skip ci], verify the exact remote commit, then pause for independent review.
