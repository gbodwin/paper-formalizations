# NEW final-dispatch reconstruction: strict 9/9

This additive reconstruction was written from exact published Flow 722 at
commit ea1dfba989c89eb8ceed693cdad42ba8d96584f5. It is not recovered historical
source. Earlier unpublished source, objects and verification receipts were not
recovered and confer no evidence on this reconstruction.

## Current validation

All nine new production modules passed fresh strict Lean compilation on
2026-10-14, completing at 01:21:32 UTC. Each process used the recovered official
Lean 4.34.0, -j1, autoImplicit=false, warningAsError=true, one compiler thread,
exclusive shared compiler locking and bounded execution. Current source/object,
import, compiler, environment, successful receipt and log bindings are in
static-check.json and strict-build/state.json; current-validation.json summarizes
the exact status. Production Lean source is frozen.

All failed attempts retain their original source snapshots, logs and receipts.
Repairs affect proof elaboration/normalization and linter cleanup only. Every
original theorem statement and the literal program remain unchanged apart from
whitespace; strict-proof-repairs.patch records the source differences.

Official new-module kernel replay, four physical degenerate fixtures, exhaustive
new-declaration type/body closure audit, envelope gates and exact-commit CI remain
separate pending gates. No positive physical whole-program coverage is claimed.
This strict compilation result is not a release-ready or paper-completion claim.
Published 722 tracked sources and gates remain unchanged.

## Program and scope

The literal 13,320-label program receives already represented original cost,
matrix and demand roots in a/b/c. It generates vertex labels and the actual
context, executes dispatch, retains infeasible/zero outputs, or computes the
optional minimum and actual original-root grid family on one append-only heap.
Saved registers restore a/b/c; d returns the result.

Output.covers represents precisely the ordered state projection of the richer
high-level Result records, not every record field. Its target is
BinaryFractionalGuesses.solveInput. The nonrecursive inputBound uses
GridFamilyEnvelope.instructionBound and separately pays the redundant minimum
scan. Initial representations, demand encoding, a dense cursor and initial H/B
remain premises. Full source parsing/store construction and all remaining paper
obligations are outside this result.

Module order: FinalDispatchProgram, FinalDispatchCallLift, FinalDispatchCalls,
FinalDispatchPrefix, FinalDispatchOutput, FinalDispatchPositive, FinalDispatchTail,
FinalDispatchTrace, ActualFinalDispatch.

Controllers match small relative labels pc.val-13264. Child ranges are 0..10759,
10760..12899,12900..12943 and 12944..13263. Entry 13318; terminal 13319. The advertised
composition overhead 32 is conservative.

## Preserved preceding versions

The source-only snapshot backed up on flow-unverified-recovery-20261014 at
commit af3faa05575cd74401fc7776608ad7bfeedf8f04 remains explicitly unverified.
The later relational-spacing repair and its old hashes remain recorded in
relational-spacing-repair.json. Earlier uncompiled README/static manifests and
runner-status files are retained under preceding-unverified-snapshots.
Those earlier records describe their own historical source versions, while
current-validation.json and the current strict receipts describe this version.
