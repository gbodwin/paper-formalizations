# Charged packed Boolean heap constructor

Production modules: `DirectedFlowCutGap/PackedBooleanConstructor.lean` and
`DirectedFlowCutGap/PackedBooleanRead.lean`. They depend on the verified
`BooleanTableRead` six-instruction read and its existing immutable-reference
store and binary arithmetic, without editing any shared dependency.

## Executed construction

`construct xs` recursively handles the tail, starting with the literal heap
`[.nil]`, binary next address `[true]`, and binary root `[]`.
Each input bit performs the existing full-copy `appendCell` for its flag,
`increment true` for the new pair address, another full-copy `appendCell`
for the pair of old next and old root, and a second `increment true` for
the next free address. Neither natural decoding nor `Nat.bits`, a natural
counter, or heap length produces an executable address.

The seed charge is 5. Every cons adds both literal append charges, both
literal increment charges, and 12 units of fixed list/record overhead.
These are conservative syntactic-operation annotations, not native Lean
wall-clock measurements. `prepend_exec` exposes actual `AppendCellExec`
derivations and the exact cursor/charge equations.

## Proved contracts

- Exactly `2*m+1` actual heap cells; next decodes to this heap length and
  root decodes to `2*m`.
- The erased actual heap satisfies `BoolList` for exactly the input list.
- Every `i ≤ m` has `IndexSpine heap (2*i) i` in this same heap, using the
  already-allocated suffix pairs. No separate unary-index list is built.
- Root/next/reference widths are bounded by `2*m+1` (linear, not logarithmic).
- Each cons adds at most `160*(m+1)^2` operations; whole construction costs
  at most `128*(m+1)^3`.
- Given an incoming binary encoding of a valid `i : Fin m`, with width at
  most `2*m+1`, `prepareRead` uses actual `add false index index` to produce
  pointer `2*i`. The actual add charge and 12 units of record overhead are
  included: full preparation is at most `128*(m+1)^3+32*(m+1)+12`.
- The actual initial reader state has both record and width bound `2*m+2`.
  `prepareRead_spec` discharges the representation/boundedness premises.
  `read_constructed_high` and `read_constructed_bit` apply the unchanged
  fixed read, retaining the valid-index premise and emitting the selected
  bit in exactly `3*i+3` successful instructions. The latter adds full
  preparation to the existing charged terminal-complete read bound.

## Explicit boundaries

Acquisition and encoding of the incoming Boolean list, the incoming binary
index word, and external source bits are not charged here. The input index
has an explicit value and width premise; no free natural-to-binary conversion
is used. The preparation program's ghost natural charge arithmetic is not
part of calculating address words. These routines are concrete closed
Boolean/list bodies, but their constructor is not compiled into the fixed
reference instruction language in this component. General compiler
correctness, whole-graph/controller substitution, graph traversal, and the
paper's final runtime theorem remain outside this bounded result. The old
abstract callback charge 7 is not a physical bit-runtime claim.

## Validation

`prepare_validation.py` changes only the import line in each production
source for a dependency-minimal local gate. The complete declarations and
proofs remain unchanged. It uses the previously verified, literal
proof-preserving `BooleanTableReadJoined` extraction; see the dependency
packet's manifest and README for the precise extracted dependencies.
This is not a full production import-graph rebuild or full-project CI.
All compiler and independent kernel-replay calls use the shared nonblocking
flock and short timeouts. Diagnostic logs are retained.

## Final validation result

Strict constructor compilation, strict read compilation, six literal `rfl`
smoke examples, the theorem axiom audit, and independent `leanchecker` replay
of both modules all passed. Only standard `propext`, `Classical.choice`, and
`Quot.sound` occur; `prepend_exec` is axiom-free. The final gate exited 0.
See `completion-receipt.json`, `validation-manifest.json`, and
`final-tail-1.log` for exact scope, hashes, and evidence.
