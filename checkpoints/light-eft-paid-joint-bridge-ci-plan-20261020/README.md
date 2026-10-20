# Source-only exact-commit CI verification plan

Planning checkpoint only. No runtime adapter is installed, no live workflow or
existing CI specification is changed, and no push, compiler, supervisor or CI
launch is authorized by these files. The proposed production diff must not be
published by itself: the finite adapter and its noncompiler regressions described
in IMPLEMENTATION-CONTRACT.md still require implementation and independent review.

The twelve-declaration bridge source at cc147275808c734c93154bd397ca7e0d018dc5dd
is unchanged. Its source design and Git tree binding passed independent review;
it remains uncompiled. The failed local preflight is preserved in Library
libfile_834e3138191c819195cbf027d19ade7d and its original local directory. No local
admission retry, namespace manipulation, cache eviction or guard relaxation is
part of recovery. No user action or access/approval failure is established.

The proposed gate runs in the existing ordinary exact-commit Lean workflow,
after the paid focused gate and the accepted joint-decoder gate have succeeded.
It uses the same accepted child runner, accounting, leases, receipt verifiers,
collision reader, full owner audit and ordinary checker. There is no new local,
manual-dispatch, cross-run artifact-download or alternate compiler route.

The changed target imports exactly 80 project modules: 77 ordinary-CI build
modules and three same-run staged modules. The staged modules are both paid
modules from the early focused gate and JointAssignmentLaw from the later decoder
gate. The planned search path uses their ORIGINAL physical object roots and seals
all actually emitted companions. It never rebuilds those accepted stages merely
to prepare bridge inputs, copies a transport manifest into production, or treats
a prior-run artifact as current-run provenance.

PLAN.json contains the exact source closure and origin map, 27 explicit external
boundary imports, complete transitive-object discovery policy, pins and tool
hashes, unchanged resource contract, sequential stage plan and acceptance rules.
HANDOFF-CONTRACT.md specifies complete prior receipt/index/lease/input continuity.
The proposed Lean audit and resolver helpers are unelaborated source drafts. The
collision reader and recursive traversal are retained; only the finite target,
twelve required roots and reachable interface assertions change.

PROPOSED-WORKFLOW.yml and REQUIRED-PRODUCTION-DELTA.patch are review artifacts,
not active workflow files. The delta inserts the bridge gate after the decoder,
an immediate bridge-only evidence upload before later checks, and the bridge
root in the existing final upload. Every existing check, concurrency group,
permission and 120-minute job limit remains. It refreshes only workflow byte rows
in the THREE existing paid/decoder/corollary specs, plus the corollary spec's
binding to the changed decoder spec. SPEC-BINDING-UPDATES.json records exact
proposed values. Final adapter source/spec binding will require another refresh
against the eventual exact candidate; it cannot use this plan as an admission.

The last accepted run took about 102 minutes. The new four-stage gate adds work
under the unchanged 120-minute whole-job deadline. Success within that deadline
is not assumed. The immediate bridge upload preserves its completed evidence
before later corollary/global replay work; any later timeout is still a failed
ordinary CI attempt requiring diagnosis, never permission to skip checks.

After independent plan review, implement the finite adapter, required negative
regressions and source bindings; review the exact implementation before one
coordinated publication/run. Kernel acceptance and all mathematical/runtime
obligations remain open. No whole-paper completion is claimed.
