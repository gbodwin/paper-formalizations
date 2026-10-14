# NEW unverified final-dispatch reconstruction

This additive draft was written on 2026-10-14 from the exact published Flow722
source at ea1dfba989c89eb8ceed693cdad42ba8d96584f5. It is not recovered historical
source. No previous source/object/compilation/audit receipt applies to it.

## Status

- Nine new Lean modules, totaling a literal 13,320-label program and its proof drafts.
- Source inspection and the accompanying static checker only; Lean has NOT been run.
- No new compiled objects, strict compile pass, kernel replay, declaration-closure
  audit, physical execution fixture, exact-commit CI or publication gate is claimed.
- In particular there is no positive physical whole-program execution fixture.
- Published722 tracked source and gates remain unchanged.

## Scope

The program receives already represented original cost/matrix/demand roots in
a/b/c, generates vertex labels, builds the actual dispatch context, preserves
infeasible and zero results, and on the positive branch executes an optional
minimum scan and the actual original-root grid family on the same append-only
heap. Saved registers restore the original a/b/c roots and return the result in d.

Output.covers represents the ordered state projection of the high-level Result
records, not every record field. Its target is BinaryFractionalGuesses.solveInput.
The inputBound uses GridFamilyEnvelope.instructionBound and separately pays the
redundant minimum scan. Initial representations, demand encoding, the dense
cursor and initial H/B remain premises. Full source parsing/store construction
and the paper's remaining whole-program obligations are not resolved here.

## Modules in build order

1. FinalDispatchProgram
2. FinalDispatchCallLift
3. FinalDispatchCalls
4. FinalDispatchPrefix
5. FinalDispatchOutput
6. FinalDispatchPositive
7. FinalDispatchTail
8. FinalDispatchTrace
9. ActualFinalDispatch

The controller matches small relative labels (pc.val-13264), preserving child
ranges 0..10759, 10760..12899, 12900..12943 and 12944..13263. Entry is13318;
terminal is13319. Exact new controller overhead: prefix6 instructions plus two
child returns yields8 beyond row+dispatchSteps; positive tail adds6 instructions
plus two child returns, and continuation adds4. Total advertised overhead32 is
conservative.

Compilation is reserved for an explicitly assigned bounded, single-thread slot
under /workspace/shared/formalization-compiler.lock after exact722 dependencies
and objects are restored. Future compile results must be new receipts for these
exact source hashes, not inherited historical evidence.
