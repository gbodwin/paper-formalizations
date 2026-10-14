# Final dispatcher envelope: new reconstruction draft

Created 2026-10-14 from the hash-verified published Flow722 source tree and the
new final-dispatch reconstruction. This is new additive work. It is not the
unavailable pre-replacement draft, and no lost proof objects are inferred.

## Intended result

A fixed `Polynomial Nat` majorizes `FinalDispatch.inputBound`. Its exact physical
polynomial is `completeBound 13320 N N (instructionPolynomial.eval N)` and is to
bound the very same `FinalDispatch.solve_bit` run at
`N = ds.length + n + LambdaRowProgram.rowBits costs.toList + H + B + 1`.
Represented original cost, adjacency, and demand roots; demand encoding; the
dense cursor; initial empty stack; and the initial `Bounded H B` premise are
retained. The output covers branch represents only the ordered state projection
specified by `FinalDispatch.Output`, not the entire high-level result records.

## Files

- `DirectedFlowCutGap/FinalDispatchEnvelope.lean`: occurrence-sum, field, label,
  and matrix bounds; fixed instruction/physical polynomial; exact input-bound
  connection and same-run theorem.
- `verification/FinalDispatchEnvelopeFullRootValidation.lean`: indexed imported
  module declarations with final owner lookup and deduplication, allowed-axiom
  checks, new-module unsafe checks, and fourteen full type/body dependency
  closures with cached edges and independent root traversals.
- `verification/FinalDispatchEnvelopeSmoke.lean`: numerical-expression checks
  only, including empty input, self demands, repeated demands, padded zero and
  half fractions, mixed costs, and sparse/dense matrices. This does not run a
  physical machine or substantiate a physical heap fixture.

## Validation state

Pending. No Lean invocation, compilation, audit run, or regression run has yet
been performed for these files. Strict `warningAsError` replay is required after
the published dependency objects and new dispatcher modules are available.
Published source files have not been edited by this reconstruction.
