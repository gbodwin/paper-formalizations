# Reciprocal component review: source-built row table and same-heap read

2026-10-11 18:21 UTC. COMPONENT PASS at the exact SHA256s below. The active
Greedy owner read both full sources (522 lines), the used reader/relocation
contracts, and the existing indexed-reader and fractional-field interfaces.
No child, compiler, source modification or whole-paper audit was involved.

- SourceRowTableProgramDraft.lean: dd0601f7f6f8913862b202f27c2bbeb8d6926d30b1220abad7772addc78a39aa
- SourceRowReadProgramDraft.lean: b910fd95c5eeb3be2d3ee4a457e6d3d46860a72e4d8699c0eff86653f2558f03

## Literal table construction

The 32-slot table requests an actual row flag. False constructs the terminal
nil; true invokes the actual self-delimited word reader twice, moves the returned
roots into registers a and b, and makes a real recursive row call. Its saved
caller restores both roots before the two final pair allocations prepend the
record and table spine. Thus records appear in the source order even though
tail storage is completed first. Every padded numerator and denominator word
is represented exactly, rather than reduced to its numeric value.

The relocated word reader reaches its old halt24, now a literal return to the
row caller. Its own top-level frame and the row caller's extra saved stack are
both included. The row recurrence counts22 fixed successful instructions per
record plus6 per stored field bit, and4 for the empty terminator; the external
top call adds one. Allocations count the real row flag, both word-reader heaps,
the two record/spine pairs, and the final flag/nil pair, yielding precisely
3*storedBits+7*rowCount+2. Append-only extension preserves already read field
roots and the recursively constructed tail. Empty tables and empty padded words
are covered directly; malformed-source behavior is not part of the contract.

## Source index and actual selected record

The 68-slot composition starts from an empty heap/stack at the actual table top
call. Table halt31 becomes a move retaining its root in register b and entering
the source-word reader at41. That reader preserves b; its halt40 becomes a move
of the index word root into a followed by entry67 of the relocated 26-slot
indexed reader. The latter constructs its actual unary index and traverses the
same represented table. Its halt is at66. The intermediate terminal slots are
continuations, and only the final halt is terminally charged.

The whole execution requests exactly the row encoding followed by the index-word
encoding. The original supplied suffix remains untouched afterward. The output
registers represent the selected literal pair of padded words. The final heap
size is tableCells+3*indexWordLength+value(indexWord)+3; this includes the decoded
word and the actual unary-index allocations. The index restriction
value(indexWord)<rowCount is explicit and is used to obtain the linear
successful-instruction bound in storedBits+rowCount+indexWordLength+1. No
externally supplied heap, table, unary cursor or metadata word remains in this
source-to-read theorem.

The final fractional-row adapter uses fields_length and fields_get for the
actual BinaryFractionalRows.Row and Fin index. It substitutes the exact stored
numerator/denominator bits, including padding, in the same run theorem. It does
not derive denominator validity from arbitrary field bits, or silently replace
a source-supplied binary index by an unrepresented host index. The numerical
index equality remains an explicit specification premise.

## Charged semantics and scope

The same high run is refined into the actual bit interpreter, with initial
bounds H=1,B=0, the exact event stream, and one paid terminal attempt. The row
constructor's10,000,000 cubic stored-size bound and the whole read's100,000,000
cubic bound cover the displayed control/heap/address terms. The latter uses
at most40 times the stored-size expression in successful instructions; the
index validity premise is essential for that step. Input acquisition is now in
the literal program for these representations, without a host table constructor.

No blocker found at these hashes. Full production CI, safety audit, fixtures,
module replay and remote publication binding remain separate gates. No fixed-7
read charge is adopted, and this review does not substitute the program through
the whole graph callback, packing/budget/fuel computation or physical runtime
claim. The explicit encoded-source and valid-index boundary must remain visible.
