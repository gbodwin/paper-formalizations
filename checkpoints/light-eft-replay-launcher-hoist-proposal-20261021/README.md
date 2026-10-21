# Replay launcher proposal: source review only

This additive checkpoint proposes one production-file change, provided as
`PROPOSED.patch` (zero-context unified diff; inspect against the bound base and
use `git apply --unidiff-zero --check` when reviewing). It is deliberately not applied. `scripts/KernelCheck.sh`, all
workflows, five gate specifications, proof sources, audit code, resource guards
and exact-commit acceptance remain byte-identical to d031f60c681650e48b409115adaffd240ec6493a.
There is no new native execution authority. The previous one-shot qualification
is consumed, and no compiler, push, dispatch or physical CI retry was started.
Fast remains off.

The old script invokes `lake env leanchecker -v MODULE` 567 times. The proposed
script runs the complete loop under one `lake env`, using the already running
Bash executable. Each target still launches the official checker separately,
in the same order, with the same `-v` argument and inherited resource settings.
No check result, object, imported environment, kernel replay or declaration
audit is cached or reused. Shell command lookup is refreshed for each target;
`command leanchecker` prevents an exported shell function replacing the binary.
Nonempty shell startup hooks fail closed before the additional shell.

The five libraries contribute 13, 48, 59, 18 and 429 modules. `MODULES.json`
binds every current source and all 567 ordered, distinct, prefix-free targets.
The existing glob selection and quoting are retained. A nonzero checker exit
still stops the loop immediately. No aggregate prefix or multi-module checker
call replaces the singleton calls.

## Source argument and limits

Pinned Lean v4.34.0 maps to upstream commit
293d5d0c0c3f3dded4688b3ccd6a33939ac5102b. Its
[Lake environment handler](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/lake/Lake/CLI/Main.lean#L1158)
loads the workspace and computes the augmented environment before spawning a
command. The proposed change removes 566 repetitions of that setup.
[Workspace environment construction](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/lake/Lake/Config/Workspace.lean#L417)
still supplies the same library, executable and dynamic-library paths under an
unchanged configuration, ordinary build tree and parent environment.

The [official checker](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/LeanChecker.lean)
continues to search its object roots and call `replayFromImports` for every
selected singleton. All 567 such searches, imports and replays remain. Its
multi-target interface creates tasks for all selected modules, which would
change ownership and memory behavior; this proposal does not use it. Primary
source bytes were fetched at the exact commit, Git blob hashes verified, and
matched to the current local distribution. Copies are in the review artifact.

Equivalence is conditional on fixed configuration, toolchain, search roots,
ordinary outputs and relevant environment during global replay. It is not a
claim of identical behavior under arbitrary mid-run Lake configuration edits,
transient setup failures, startup hooks, or filesystem races. The added shell's
effective tool/search-path identity needs independent review and eventual
authorized native qualification. Model tests do not establish that identity.

Both existing 120-minute jobs, the 5-minute aggregation, all native 90-second
caps, every admission/sample/lifecycle check, full and focused verification,
same-job producer authority and exact-commit aggregation are unchanged. No job
is added to reset a deadline. The proposal does not move or remove any existing
check, retry a timeout or reuse cross-job objects.

## Evidence and unresolved benefit

Run 39618998763 attempt 1 remains cancelled: paid, decoder, bridge and canonical
gates passed, global replay was cancelled, focused skipped and aggregation
failed. Its 453 replay-start diagnostics establish neither 453 completions nor
all 567 completions. Exact cancellation cause remains unverified.

The full job spent 3,951 seconds before global replay. The 452 observed gaps
between start diagnostics average approximately 7.202 seconds. Linear cadence
extrapolation gives approximately 134.03 minutes overall. This is an estimate,
not a bound or an attribution of cost to Lake. Closing that estimate through
launcher hoisting alone would require about 1.49 seconds saved per removed
setup. There is no native measurement showing that saving. This patch may be
insufficient, especially because checker object-root discovery and replay
costs are unchanged. It must not be described as qualifying the job budget.

The parent's independent bridge review verified 515/515 payloads and child
launch-to-kernel-terminal times of 7.253, 10.020, 10.631 and 69.207 seconds.
Four preflights totaled 169.853 seconds; post-terminal receipt work totaled
90.561 seconds. Those are concrete separate overhead targets. Source inspection
shows full inventory checks in both `before_child` and `prepare_child`, a
separate preexec identity/critical-hash pass, and post-child verification.
These are distinct observations around source snapshots and preparation.
This checkpoint removes none of them or their hash reads. The timing totals
do not isolate traversal, hashing, durable writes or export work; deleting a
pass would not be an evidenced equivalent optimization. Child terminal time
must not be confused with later receipt completion.

Twelve offline tests exercise fake launcher/checker execution, all 567 exact
targets, arguments and relevant environment, first/middle/last failures,
startup-hook rejection, quoting and source preservation. `verify_source.py`
checks patch reconstruction, every module carrier and all existing gate
binding rows. Neither invokes Lean or Lake. Runtime performance and native
environment equivalence remain unverified. Parent sequential independent
source review is still required.

## Next step and paper scope

Review this exact proposal and preserved terminal evidence first. If it is
accepted for implementation, apply only the proposed script delta, bind the
script and revised controls through the existing exact-source machinery,
refresh the finite specification cascade, and independently review that exact
integration commit before requesting any new bounded native measurement or
physical attempt. The existing allowance does not authorize either.

All 36 new proof bodies remain unelaborated. The accepted kernel/CI baseline
remains c1aaa0a00c0c943cec4b2753a937023e9884db04. Shared-stream refinement, joint
state/cost composition, arithmetic bit costs, bank/caller handoff, aggregate
costs and whole-paper acceptance remain open.
