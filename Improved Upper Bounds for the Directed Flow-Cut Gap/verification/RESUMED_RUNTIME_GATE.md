# Resumed exact193 runtime gate

This branch preserves all 193 proof components and their import-only root from
6b8a1e24b087378384898f44108c21345a2a089b byte-for-byte. It adds the recovered
eight-body runtime gate absent from that earlier successful CI run.

The original smoke source is SHA-256
5f4b7ab9795c66743f698323bd2c27f72439a2ede27308fb78c14bc646b3b97f.
The single-main driver is freshly prepared, not a recovered old driver or
verification receipt. Its current version includes the explicitly documented
elaboration repairs below. Undoing those edits and replacing its eight named
IO Unit headers with the original #eval headers reproduces the original
source exactly; main and ordered START/DONE markers are appended.

CI first checks the exact proof-source and runtime-driver hashes, then runs its
normal build, strict repaired-module compilation, exhaustive owned-declaration
axiom audit, existing execution regressions, this eight-body runtime gate with
explicit printed-charge checks, and project-component kernel replay.

This commit does not assert a CI result before that run finishes. The verified
174-component partial baseline remains fc11ede6. The larger 251-component
working integration and 105 preserved drafts are separate, unverified work.
Full-paper completion, weighted provider construction, full algorithm/runtime
joins, and the companion reading site remain open.

## Harness elaboration repair

Fresh CI 38052341343 passed the full repository build, repaired graph-module
strict checks, exhaustive 12,650-declaration flow-cut axiom audit, and existing
binary-cover/weighted regressions. The recovered runtime harness itself failed
before executing because of three equality-inference errors and decimal-field
notation. No runtime PASS or kernel-replay result is inferred from that run.

The next harness version has five explicitly reversible text edits, recorded
in runtime-elaboration-repairs.json: tuple equality is expressed as its two
component equalities; two Nat.bits literals are parenthesized and typed; and
the two raw-state tuple observers have explicit return types. Every original
fixture, branch, compared field, and charge assertion is retained. The archived
original remains byte-for-byte preserved. The checker reverses these edits
before checking the original #eval-body bytes. New CI is required.

## Nested equality elaboration budget

The second run, CI 38053497682 at ae27eb10, again passed the library and existing
gates but exposed one remaining numeric field-notation site and two tuple
instance-synthesis failures. An Init-only local probe reproduced the latter:
the nested tuple's constructive DecidableEq exceeds Lean's default instance
size limit of128. The same tuple and list equality probes pass with the limit
set to10000. This version adds that elaboration-only option and parenthesizes
the final Nat.bits literal. All seven reversible harness edits are recorded.
No runtime execution result is inferred from the two failed elaborations.

## Boundaries retained after source review

The graph charge model still uses the named array callback (table[i],7).
The six full-copy bit/list routine certificates are separate; this is not yet
a theorem substituting those routines throughout the graph implementation.
The guess result constructs a finite family with a suitable member for each
feasible comparator, not a selected exact optimum. The weighted pathwise bound
retains its reached-state oracle premises; complete weighted provider, sampling
and outer runtime joins remain open. Nothing here is a full-paper bit-runtime
claim or native compiler/allocation verification.

## Separate recovered 251-source diagnostic

This branch adds the exact 58 recovered draft components to the inherited 193 sources. All 251 component bytes retain their recovered hashes; this is an unverified aggregate. Its workflow reuses the repaired eight-body driver and strict marker parser while adding strict checks for every new component. The eight bodies do not exercise the 58 new graph, tape, sampling, and packing bodies. Those source-specific execution and semantic gates remain open even if this diagnostic CI succeeds.
