# Sequential full and focused validation

Source-only scheduling redesign for independent review. No compiler, admission,
push or CI was started. Fast is off. Mathematical sources remain exactly the
source-reviewed4f06895e checkpoint; all36 proofs are unelaborated. The accepted
kernel baseline remainsc1aaa0a0 and its failed/accepted evidence is preserved.
This revision does not change any proof, audit, handoff or child resource limit.

The original Lean workflow retains every accepted full check, including all567
global kernel replays, the complete declaration audit and all24 staged children.
The unexecuted642ae01a inline batch and external preparation are removed from
that job. Its120-minute limit remains. Paid and decoder evidence uploads are
added immediately after those gates; the existing bridge and final uploads stay.

After full success, a separate reusable workflow runs on a fresh GitHub-hosted
runner. The local `./.github/workflows/light-eft-fair-bit-focused.yml` reference
selects the same immutable caller commit. Only `workflow_call` is exposed: no
additional push, PR, manual or workflow-run trigger can launch duplicate work.
The existing push/PR/manual trigger and checkpoint-branch exclusion are retained.
The caller's repository-wide single-compiler concurrency reservation remains held
through full, focused and aggregation. `needs: check` serializes their jobs. The
callee does not acquire a competing nested concurrency lock or use a matrix.

The focused job checks out the exact source input, independently runs the pinned
ordinary lean-action setup, builds the same three explicit external inputs,
then performs the unchanged module-index check before any producer snapshot.
It runs paid9, decoder4, bridge4 and batch12 strictly sequentially, all in this
one check job. No objects, producer receipts, leases or filesystem identities
come from the full job. No download-artifact step exists. Ordinary/cache inputs
are newly observed, not asserted to have authenticated clean-build provenance.
All17 producer children are reconstructed and authenticated by the existing
same-run machinery before the batch. Full retained-context equality and the
growing owned output root are unchanged. Evidence uploads immediately follow
each of the four gates and a final upload preserves complete available evidence.

Both CI policies preserve every old identity check and additionally require the
exact caller workflow name/ref/SHA, role/source, check job and actual defining
job workflow repository/path/ref/SHA. The caller is alwaysLean/lean.yml; the job
path is lean.yml for full and light-eft-fair-bit-focused.yml for focused.
`job.workflow_*` supplies actual callee identity; `github.workflow_*` is the
caller context. Missing properties fail closed. A ref spelling of the exact
current event ref or exact commit is accepted only with matching actual SHA.
Both workflow byte strings and scheduling runtime helpers are exact Git-bound
spec inputs. The batch also explicitly rejects the full role. Complete identity
is present in every producer/batch receipt, so full-job receipts cannot stand in
for focused producer receipts. Existing boot, namespace, inode and lease checks
continue to enforce same-machine physical continuity.

Each successful job emits its exact commit only after all verification steps and
immediate uploads have passed. The final always-run `Full and focused exact-commit
acceptance` job requires both dependency results to be success and both outputs
to match the current event SHA. Missing, skipped, cancelled, failed or mismatched
jobs reject. A later final-upload failure also makes its job result fail despite
an earlier commit marker. The aggregation artifact records rejection as well as
success. There is no continue-on-error, optional full check or focused-only
acceptance route. Repository branch-protection settings are not changed or
claimed: the combined check/run and both complete artifacts are required for our
acceptance procedure, followed by independent terminal review.

The accepted run39507492456 job118919963785 measured6534seconds, leaving666seconds
inside its120-minute job. Reused focused setup/index measured279seconds; paid,
decoder and bridge measured597/540/353seconds, totaling1490. Thus the reused
focused subtotal is1769seconds (29m29s), without the53m20s global replay or other
full checks. PLAN.json conservatively allocates600seconds setup and3000seconds
producers, each above twice observation, plus900seconds unmeasured external
preparation,1800seconds unmeasured batch and600seconds evidence/status. The
115-minute planning envelope leaves5minutes inside the unchanged120-minute
focused limit. These are forecasts rather than new deadlines or a worst-case
proof; prespawn/wall maxima can sum beyond the job limit. New-module elaboration,
additional external build/cache work, scanning, uploads and runner variance
remain unmeasured. Timeout remains a failure. No automatic retry or resource
relaxation follows. This is sufficient scheduling evidence to review, not a
claim of execution qualification or kernel acceptance.

The12 original blocked batch models remain; seven added scheduling models exercise
both strengthened policies, all trigger/role combinations, actual workflow-field
failures, status/commit conjunction and the actual aggregation/marker entrypoints.
The offline checker verifies exact full
check preservation, order, concurrency, trigger graph, unique artifact names,
binding cascades, unchanged mathematical/runtime sources and original resources.
They do not launch a native child, acquire a lease or verify Lean. The original
642ae01a check_implementation.py/refresh_spec.py are preserved historical tools;
the scheduling check_schedule.py/refresh_bindings.py supersede them for this
revision and must be used to avoid restoring the obsolete inline workflow.

Primary GitHub documentation for this reviewed design:

- [Same-commit relative reusable workflows](https://docs.github.com/en/actions/how-tos/reuse-automations/reuse-workflows).
- [Caller context, dependency and concurrency semantics](https://docs.github.com/en/actions/reference/workflows-and-actions/reusing-workflow-configurations).
- [Actual job workflow identity](https://docs.github.com/en/actions/reference/workflows-and-actions/contexts).

Next is sequential independent review of the exact commit, byte bindings,
scheduling budget and status aggregation before publication/execution. The local
namespace/headroom remains unqualified and is not retried. Shared-stream
refinement, joint state/cost composition, arithmetic bit costs, bank/caller
handoff, aggregate costs and the whole paper remain open.
