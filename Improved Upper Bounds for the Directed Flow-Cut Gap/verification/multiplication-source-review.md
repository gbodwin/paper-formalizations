# Reciprocal component review: literal multiplication and source-input join

2026-10-11 18:12 UTC. COMPONENT PASS. Read-only review by the active Greedy owner;
no helper or compiler used. Both full files (548 lines) and the immediate
addition, control-label relocation, stack-extension, reader, arithmetic and
terminal-accounting contracts were inspected. Exact source SHA256s were
recomputed before review and again when saving this receipt:

- BinaryMultiplicationProgramDraft.lean: f7752afeac646cede606fe9d70b58fc1a8bf64c8326b54eab0928f6d00388227
- InputMultiplicationProgramDraft.lean: d22fbaf13dbc32c7fe46b53414174e93ea36886ddc5aa93b7b727bdfe42e4c9e

## Concrete recursive arithmetic

The 96-slot table contains actual branch/field/call/return/move/make operations.
Its old addition halt at63 is replaced by a literal return. The relocation
agreement is required only at old non-halt slots, and the proved successful
addition run reaches63 before that new return. The added multiplication caller
stack is retained by the checked stack-extension lemma, rather than supplied
as an unproved call contract.

The four-instruction prefix saves the first operand's tail, the unchanged
second operand root and the current flag root in an actual frame. Recursion
returns the exact padded suffix product and restores those saved registers.
Two real allocations prepend a false bit. For a false input bit, branch and
return finish this shifted product; for a true bit, real moves pass the retained
second operand and shifted product to the addition entry, then the result is
returned to the original multiplication caller. Append-only heap extension
preserves the old flag and both operand representations. There is no host-side
multiplication instruction hidden in the table: BinaryArithmetic.mul occurs
in the specification and proof-side counts.

The empty first operand takes three successful instructions and allocates a
new nil cell. False/true recursive steps respectively add8 and additionSteps+13
successful instructions; their allocation recurrences are exactly the displayed
cells function. These account for the call/return frames and both shift cells.
The output equals the full padded BinaryArithmetic.mul word, not merely its
numeric value. The separate arithmetic theorem identifies its value as the
product. Empty operands and stored zero padding are covered by the same proof.
The quadratic successful-step/allocation bounds use the retained output-length
bound and actual addition bounds; no favorable canonical-width premise occurs.

## One actual source-input execution

The 116-slot join embeds multiplication below96 and places two actual ten-slot
self-delimiting readers at offsets96 and106. It starts at105 from an empty heap,
empty stack and zero represented registers. Reader halts104/114 are replaced
by real moves; the first result is retained in register a while the second reader
runs. The second move passes the literal roots to multiplication entry94, which
creates its own caller and eventually reaches the sole final halt95.

The two reader runs consume exactly encode(xs) then encode(ys), with the exact
request-event concatenation and the original supplied suffix remaining. Both
padded operands and the padded product coexist in the same append-only heap.
The final heap length is 3*(|xs|+|ys|)+4+cells(xs,ys), and the next-address invariant
is derived from that heap, not supplied by an external constructor. The primitive
accepts represented inputs; the source wrapper discharges those premises through
the actual readers, while retaining the explicit well-formed source encoding.

Both lower results are obtained from these same literal natural runs through
polynomial_simulation, and terminal_accounting charges the actual final attempt.
The wrapper uses initial bounds H=1,B=0, derives at most160*(totalLength+1)^2
successful instructions, and bounds completeBound116 by the stated
6,000,000,000*(totalLength+1)^6. The constant comfortably covers the displayed
sixth-degree and fourth-degree terms. No intermediate halt is silently paid as
the final halt or substituted for the concrete continuation.

## Evidence and limits

No mathematical or semantic blocker found at the exact hashes. Local strict
compilation, safety audit, fixtures, official kernel replays, remote byte binding
and full exact CI are separate gates owned by the author. This receipt is a
component source review, not an end-to-end paper audit or a new runtime model.
The charged interpreter scope, explicit source encoding, and open whole graph,
budget-expression and fuel construction/composition obligations remain intact.
