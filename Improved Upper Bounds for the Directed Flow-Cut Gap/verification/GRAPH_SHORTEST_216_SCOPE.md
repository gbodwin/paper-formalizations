# Actual graph shortest-path recovery: 216-source runtime candidate

This checkpoint extends the separately verified 172-source runtime closure by
44 sources (3,610 lines). The other, overlapping 351-source aggregate remains
its own verified checkpoint; these counts must not be added. The repository's
historical 193-source root and every inherited proof body are unchanged.

## Constructed execution

`GraphRecoveryController.graph_bit` in `ActualGraphShortest.lean` executes a
literal 1,344-slot lower-machine program from an explicit represented graph,
vertex enumeration, rational vertex-cost row, source and target. It:

1. constructs the synchronous bounded-round minimizer using the previously
   verified 720-slot discovery program;
2. branches on that same computed optional result;
3. allocates the actual support-search context from the returned record;
4. runs a forward-updating support search and retains the first predecessor;
5. projects the recovered edge tails while sharing their original padded words;
6. materializes the outgoing source-zero cost list and performs canonical binary
   rational accumulation; and
7. returns the literal old `BinaryFractionalWalkOracle.shortest` optional
   candidate, including its exact recovered edge list and stored cost fields.

The proof connects the same heap, caller frames, allocations and execution all
the way through. It supplies a polynomial instruction bound from the input
vertex count and stored word widths, and charges the final halted attempt on
that same lower run. No recovered path, materialized cost list, computed cost
or minimizing output is provided as an input premise.

The 20-source instruction trace, eight-source semantic/size refinement,
seven-source costed-recovery composition, and nine-source shortest controller
have separate immutable source manifests and review receipts. The local safety
audit checks all 3,164 declarations in these 44 defining modules and the full
transitive type/body closures of eight endpoint theorems. It rejects unsafe
constants and axioms other than `propext`, `Classical.choice`, and `Quot.sound`.

Twenty-six actual-interpreter fixtures check singleton and absent outputs,
missing support or adjacency, forward chains, first-predecessor behavior,
padded vertex words, source-zero costs and zero-cost cycles. They compare exact
outputs, step and cell totals, retained heap/source/caller state, terminal PC
and terminal-inclusive operation accounting.

## Boundary

The graph/matrix/row/label representations, valid finite enumeration, initial
heap/bit-width bounds and positive stored denominators remain explicit. This
checkpoint does not yet construct raw graph input, traverse the complete demand
collection, compose adaptive packing updates/masks/fuel, or establish the whole
paper's physical runtime. The existing whole-paper formalization is partial.

## Evidence status

Each source has a strict local elaboration receipt. The exact new component
has a passed local declaration/closure audit and fixtures. All 44 official kernel
replays pass. All four source reviews pass. The full local reference audit passes 15,544
declarations. A separate preservation review is required before publication;
its source-bound receipt records that independent check.
The full 216-source clean build, inherited execution gates, exhaustive reference
closure audit and exact manifest replay are required on the published commit;
local evidence alone is not a terminal full-CI claim. The older durable draft
backup remains unchanged under `flow-recovery-drafts/20261012-support-recovery`.
