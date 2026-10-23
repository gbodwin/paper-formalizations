# Single-call semantic binding reuse: unintegrated SOURCE proposal

Base `b7d1de222d954f269fef5d06c62e8ad67ee2cbea`. This checkpoint preserves the exact baseline and proposes changing ONLY `scope.Context.verify`. The live engine, diagnostic harness, manifests, workflows, proof sources and all production entries remain unchanged. No proposed function, model, diagnostic, compiler, Lean/Lake/checker/audit, push or CI ran in this unit. Independent sequential source review is pending. Fast remains off.

## Evidence and scope

The owning coordinator independently verified the official b7d1de22/run39878096937 artifact, including successful exit, owned reaping, ECHILD and released CI lease. Its compact evidence is `libfile_52692915372c81919b16886d608084fc`, SHA256 `98da61930fd351e29ed650e11a584d38fa857daf9e5dc811f91c5e8ddf45217b`. The measured 1,024-module controlled case confirms repeated reads. Exact raw phase values were not supplied in this delegation and are not invented here. One supported consumer materialization attempt returned no workspace path and the unmodified helper failed with `download failed`; there was no repeat or bypass. These measurement statements are attributed to the coordinator, not a new author measurement.

The separately owned operator reservation was released at `2026-10-23T00:44:58.225918+00:00` after fresh terminal/empty queues, exact process-command/boot/path identity and kernel flock-owner checks. The old transport session was unavailable after environment recovery; the owned process handled its release marker and produced the release receipt. Its kernel flock disappeared. The remaining process entry was a zombie, not an active lock owner; no PID was killed or reused. `OPERATOR-RELEASE.json` preserves the receipt.

This is a source-level redundancy proposal, not proof of full-job savings. Neither the measured controlled case nor the earlier 256-module package-selection benchmark supplies complete inherited production roots, all semantic sidecars, large receipt states or full-job costs. The local noninitial namespace remains barred. No full qualification retry is justified by this checkpoint.

## Proposed change

For the existing initialized-inventory branch, create a LOCAL `CIIdentityGuard` seal from the input authority, excluded metadata, generated/resolved protected inputs and the two journals, using the original inventory's complete files/directories. The constructor performs the original metadata/membership/parent checks before any reuse. Call the unchanged `CIInventory.scan()` once: it still enumerates the entire input tree and invokes the original `regular`/`bind` content checks for every semantic file, as well as all classifier, orphan-family, runtime-file, membership and original-snapshot comparisons.

Freshly hash every `self.inputs` entry OUTSIDE that returned semantic map. The original full row equality of every scanned semantic entry against `self.inputs` remains mandatory. These are two independent expected authorities: the inventory's original snapshot and the context's input binding map. A semantic row missing from, or differing in, either authority rejects. No hash is trusted merely because a path appears in a set.

All original generated/resolution checks, input-journal binding, member comparison, semantic/input equality, excluded-journal binding and `effective` computation remain. `effective` retains every root/shadow/prefix/package/leaf/target check and its independent dependency/target content reads. No partial result or acceptance is reused there. Only the redundant semantic portion of `unchanged(self.inputs)` is satisfied by the ONE fresh semantic binding pass already required by `scan`.

After `effective`, recheck the held lease and invoke the seal's unchanged `verify()`. This freshly revisits exact tree membership, file identity including ctime/mode/ownership/link count, directory identity and real parents, comparing against the entry snapshot. Persistent membership, identity, link, directory or parent drift must reject before return, even after the content-binding pass. The seal is an additional final metadata guard; it does not replace the parent's existing preexec/runtime/post-child checks. It stores no content-result cache outside this invocation, opens no long-lived descriptors and never changes the lease lifecycle.

When `inventory_policy is None`, all original content/tree/effective checks and their order remain. No seal or reuse is introduced in that branch. The inventory branch requires an already established original inventory; the existing production factories scan before constructing their contexts. A missing/uninitialized authority now fails explicitly before reuse. The three singleton admission contexts still invoke the same base verification plus their unchanged empty-output, absent-resolution and singleton-selection checks; no replay/module/command selector changes.

## Check-retention argument

Let S be the exact semantic map returned by this invocation's original `scan`, and I the context input map. On supported immutable input/configuration state, `scan` succeeds only after freshly checking each S path with the same `regular`/`bind` implementation used by `unchanged`, and comparing the entire observed inventory with its original authority. The retained `all(I.get(k) == v for k,v in S.items())` checks the complete row (path, bytes, digest and identity) for every semantic entry. Thus each I entry in S has the identical content/identity evidence its separate `unchanged` read supplied. Every I entry outside S still goes through `unchanged`. New/resolved/journal/effective checks remain independently fresh. This covers ALL original input bindings and every original acceptance predicate, not only expected project dependencies.

The existing immutable/no-writer premise includes the input trees, authority maps and configuration for the entire call. Under that premise, the new entry/final seal succeeds for every valid original call, and the single fresh semantic pass plus complete row equality yields the original accept/reject outcome. Invalid bindings/classification/membership remain fail-closed; where several violations coexist, the first diagnostic may differ because scanning occurs earlier. No guarantee is made about identical exception precedence, arbitrary concurrent/transient writers, historical inode continuity, or an uninitialized/custom inventory object outside the supported constructors. The final seal catches persistent ordinary drift; it is not a proof that no transient writer existed.

The added metadata traversals consume time and memory. Removing one full content-binding pass may or may not improve elapsed time on the actual runner. No runtime/peak/full-job budget result is claimed. Existing guard exceptions still propagate; no failure is caught and accepted, and no caller can receive success without the final seal completing.

| Original obligation | Proposed fresh evidence |
| --- | --- |
| Every semantic I binding | Original full `scan` content binding + original-inventory equality + retained S/I full-row equality |
| Every nonsemantic I binding | Original `unchanged` on I minus S |
| New objects/resolution/journals | Original independent `unchanged`/`bind` calls |
| Classification, sidecar/runtime families, full tree | Entire original `CIInventory.scan` and member comparison |
| Root/package/shadow/prefix/leaf/target/dependencies | Entire original `effective` call, including its content reads |
| File/parent/directory/membership stability | Original `CIIdentityGuard` entry snapshot AND final `verify` |
| Lease, source/argv/identity, namespace/resources, cleanup | Original surrounding guards unchanged; an extra final lease check |
| Declarations, axioms, collision coverage, kernel checks | No source or policy change whatsoever |

## Review and later validation boundary

`MODELS.json` contains TEXT-ONLY adversarial requirements, not executed fixtures. Source review must first check exact transformation, row coverage, excluded/extra inputs, supported constructor assumptions, final-seal independence and unchanged ordinary/admission paths. No production integration or diagnostic publication is authorized by this proposal.

If subsequently approved, load baseline/proposed scope bytes as isolated diagnostic modules without replacing production. Compare complete ordered selections and valid/invalid outcomes on immutable cases, with separate controlled drift cases. Retain every content/classification/leaf check and every source/resource/lifecycle guard. Use the existing bounded representative context and original inherited-lease authority, with fresh trees/state per version. Profile the new seal snapshots explicitly so metadata cost is not hidden in residual time. Repeat calls must each redo scan/content binding and final seal; there must be no cross-call cache. The original <=1-MiB result/64-KiB progress, one child, 90-second whole wall/CPU60/AS12GiB/RSS6GiB/file16MiB and five-minute diagnostic job remain. No extra jobs/children, splitting, timer reset or work moved outside supervision.

Only after independent exact diagnostic/source review and measured attribution could a separately approved production integration replace the one target file and refresh the existing five-spec acyclic engine/source binding cascade and finite assertions. That integration is not performed here. Full relevant kernel verification, declaration/axiom/collision audits, same-job focused checks, independent review, 567 fresh serial checker processes and 120/120/5-minute exact-commit qualification remain mandatory before acceptance. All 36 bodies and the whole paper remain unqualified/open.
