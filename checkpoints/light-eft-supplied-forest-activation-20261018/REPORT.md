# Light EFT activation-order delta

This additive preparation checkpoint addresses only the activation order identified during independent review of **`283f4de446d4f082429098e33ecb050c4aab310b`**. That review accepted the inventory correction and exact newly observed signature supplement. It did not authorize production. The earlier 95.613-second measurement covers the complete validation script; its builder-only duration is not known. No additional real inventory pass, resource probe, Lean/checker invocation, lock creation or real production attempt occurred here.

## New activation contract

`execute_production(reviewed_commit, coordination)` now requires **a coordinator callable**, not a preissued document. It completes the existing read-only input and complete-plan construction first, records planning completion, and then calls that explicitly supplied coordinator **once**. The returned document must have been issued at or after planning completion. A returned preissued document is rejected; the wrapper never rewrites its timestamp, obtains a replacement after failure, or retries activation.

The existing `ReviewedAuthority` checks the returned document against the reviewed implementation, current owner/boot/namespace/directory facts and the unchanged **less-than-60-second** deadline. The exact prepared wrapper bindings must still match. The idle check and fresh-work-root absence check run before mutations. Then `authority.check_live()` repeats the current-facts/deadline check **immediately before the first evidence-directory/claim/work write**. Lease entry retains its existing independent freshness check before any lock I/O.

A future caller must therefore supply the explicit coordinator callback and obtain genuinely fresh coordination after planning. Supplying an old document directly is disabled; wrapping an old document in a callback does not evade the issued-after-planning check. This is an API preparation change, not an automatic activation path or new authorization.

Only the copied `driver.py` changed among the **21** base helper/data files. The other **20** files are byte-identical, including `authority.py`, `lease.py`, `scope.py`, resource/supervision helpers and the three inventory data files. In the driver, only `execute_production` and the activation-description text differ. `make_production_plan` and `_run_batch` have identical ASTs. The same exact bound plans, roots, dependencies and inputs flow into the batch; no replanning occurs after the callback. Under-lease Context construction, canonical input journaling, full input/preservation checks and child pre-execution checks remain unchanged. [Scope reconciliation](scope-reconciliation.json) and [base bindings](base-bindings.json) document these comparisons.

The signature supplement remains byte-identical with SHA256 `887fbf98a695a0b5992aa172cd098fc237bd6572d2a52491531c769bc73da964`, and retains its newly-observed-local qualification. Its referenced real signatures were **not** reread in this delta. The accepted inventory checkpoint's 917 sealed entries and manifest parts were rehashed unchanged as evidence preservation only; this is not another inventory execution.

## Synthetic validation

**12 tests passed, exit 0**, in one Python-only attempt. [Exact command](commands.txt), [raw diagnostics](diagnostics/activation-tests-attempt-1.log), [results and event records](test-evidence/c053e0fe75474bfc8b85c6abb43848e2/result.json), and all Python source snapshots are retained.

The fixture substitutes a synthetic planner, fake commit/bindings and ownership facts, and a virtual monotonic clock. It advances planning by **96 virtual seconds** without sleeping. Fresh-flow claim/directory writes and lease/batch calls are intercepted in memory; there is no real claim, work root or lock. The original production entry's ordering logic is exercised only with these synthetic substitutions, not with actual production inputs or authority.

The fixtures verify:

- Long planning finishes before the one coordinator callback; fresh coordination succeeds through the virtual forwarding path with the identical prepared plans/bindings.
- A preissued document returned after planning creates no claim, evidence directory, work root or lock.
- Documents that expire in the provider, during wrapper binding review, or during the idle check create none of those artifacts. No timestamp is changed or callback retried.
- An ownership incarnation change after initial authority construction is caught before mutations.
- Missing prepared wrapper bindings and planning failure create no artifacts; planning failure does not request coordination.
- A document argument and missing/extra activation flags remain disabled.
- The existing deadline accepts 60 seconds minus one nanosecond and rejects exactly 60 seconds.
- The real lease entry rejects stale synthetic authority before reaching any lock I/O.

Real planner/classifier functions, process launch, lock I/O and resource APIs are replaced by fail-fast guards during these tests. Stale-path event records show no mutation intercept reached, and their physical synthetic claim/work/evidence paths remain absent. The positive path's recorded mutations are explicitly virtual, not production receipts. Expected stale rejections are test assertions; no failed real activation or Lean diagnostic was produced.

## Disposition

All accepted inventory evidence and historical partials remain unchanged in the prior checkpoint. This delta has its own source snapshots, logs and complete hash manifest. No theorem acceptance, fresh kernel replay, mathematical source change or CI result is claimed. Published on the existing `light-eft-spanners-checkpoints` branch with `[skip ci]`; the sole worker pauses for independent review. Production still requires review of this exact implementation and separately authorized fresh coordination.
