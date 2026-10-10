# UNVERIFIED integration gates

Candidate: 251 component modules plus the import-only DirectedFlowCutGap root.
Source snapshot: 2026-10-10T11:19:02.476639+00:00.
Lean: 4.34.0. Mathlib: 5ed2965256430c3649e86755f9576b54eca72435.
Allowed axioms: propext, Classical.choice and Quot.sound.

No compiler, axiom, kernel or execution result is asserted for this snapshot.
The historical 174-component verification at fc11ede6 does not transfer to
the 58 added components or certify this aggregate. The 193-component
parent is a separate integration candidate, not a new verified baseline here.

## Reproduction

Run from a clean checkout of the candidate commit:

```sh
python3 scripts/CheckDirectedFlowCutGapSnapshot.py
lake exe cache get
lake build
bash scripts/CheckModuleIndex.sh
bash scripts/StrictDirectedFlowCutGap.sh
lake env lean scripts/AxiomAudit.lean
lake env lean -DautoImplicit=false -DwarningAsError=true "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/BinaryCoverEntrySmoke.lean"
lake env lean -DautoImplicit=false -DwarningAsError=true "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/WeightedCombinedSmoke.lean"
(
  set -euo pipefail
  runtime_log="$(mktemp)"
  trap 'rm -f "$runtime_log"' EXIT
  lake env lean -DautoImplicit=false -DwarningAsError=true "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/RuntimeGraphCombinedSmoke.lean" 2>&1 | tee "$runtime_log"
  python3 scripts/CheckRuntimeGraphCharges.py "$runtime_log"
)
bash scripts/KernelCheck.sh
```

The workflow also retains strict compilation of the five repaired graph-bound
components already in the parent. The full-repository axiom driver audits all
owned declarations by defining module, including generated/private declarations.
The kernel driver visits every paper's component sources and explicitly replays
the DirectedFlowCutGap root. The paper-local KernelReplay.lean lists all 251
components and that root; it is an alternative replay driver, not extra evidence.
The paper-local AxiomAudit.lean likewise provides a reproducible focused audit.

## Execution scope and remaining gates

The retained public regressions check their existing binary-cover and weighted
selection/packing examples. The RuntimeGraphCombinedSmoke driver adds the
existing eight #eval bodies for the six finite-data routines and binary graph
code required by the 193-component candidate. Its assertions and case sets are
preserved exactly. The previous local attempt timed out; execution of this
driver remains PENDING and no pass is inferred. All test bytes are pinned in
the manifest. Graph-operation and dispatch-charge fields are printed by this
driver. CheckRuntimeGraphCharges.py requires exactly one of each graph marker:
at most 27 retained events, 27 stopping scans and positive graph operations;
five positive dispatch charges; and nine guesses, 243 stopping scans and
positive guess-family operations. CI runs this parser only after successful
Lean execution. Missing, duplicate, malformed or invalid markers fail the step.
The parser adds no Lean cases and does not establish an execution pass itself.

These tests do not cover every newly added execution body. Dedicated source-
specific runtime regressions for the new 251-component graph-execution bodies,
weighted-runtime/tape bodies and packing-assembly additions are not integrated
in this candidate and are NOT COVERED.
In particular, the added confidence consequence is proof-only; it does not add
an executable regression or discharge the graph-provider contract.

Promotion requires all exact-commit CI gates, the missing source-specific
execution regressions, and independent exact-source semantic reconciliation.
The whole-paper probability/runtime result, unconditional provider construction,
and companion website are not established by this integration. No native
compiler, allocator or hardware correctness claim is made.

The manifest binds source bytes and public verification drivers. It is a
snapshot description, not a compilation receipt. Later source repairs require
a new snapshot and must not be silently adopted under these hashes.
