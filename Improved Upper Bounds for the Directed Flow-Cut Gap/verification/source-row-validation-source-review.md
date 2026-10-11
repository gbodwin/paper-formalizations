# Source-row denominator validation: bounded source review

Verdict: PASS for the two exact sources and the explicit domain below.
Reviewed on 11 October 2026 by the concurrently active minor-free-spanners
owner. No child worker or compiler was used for this review.

## Exact sources

- BinaryZeroProgramDraft.lean, 146 lines, SHA256
  023227d73c8367f5852bd72b71c95c41dd2193b4b3ba43452e3c75c4c5a73ec4.
- SourceRowValidationProgramDraft.lean, 193 lines, SHA256
  70a59d030dfb9386c02a65fed3bb7214cffeee00ddc0353ad084c9036e30636e.

The source hashes were recomputed after reading both full files. The existing
isZero/isZero_spec definitions, source-row execution and instruction bound,
and lower terminal-attempt semantics were also inspected at their actual
interfaces. Production byte binding and full CI are separate gates.

## Concrete instruction and representation checks

1. The nine-slot zero program follows the real pair/flag representation.
   Nil allocates true; a false bit takes four actual transitions to its tail;
   a true bit takes five transitions and returns false immediately. The
   result is allocated at the original dense heap's next index. The saved
   caller is restored, with only its designated r3 result changed. The old
   heap and complete unused source are retained. The proof handles empty and
   padded-zero words and never assumes the zero-test answer as a premise.

2. The 79-slot table relocates the actual 68-slot row reader and nine-slot
   zero program. Its row halt at66 becomes the move saving the numerator in
   r2. Slot77 moves the actual denominator pointer to r0 and transfers to the
   zero wrapper at75. The relocated zero continuation at76 restores the
   numerator to r0, then reaches the one final halt at78. The nonhalt slot
   equalities justify the literal run transport; no intermediate halt is
   charged or treated as an executed instruction in this composition.

3. The composed run starts with empty heap/stack and the literal encoded rows,
   encoded binary index, and arbitrary trailing suffix. It consumes exactly
   the encoding request events, returns exactly that suffix, preserves both
   selected padded field representations, and appends the zero flag tied to
   the actual stored denominator. The exact heap count is the row-cell count
   plus3*index-word-length+index-value+4; dense next equals that heap length.
   The same final state supplies all these facts, including its empty stack.

4. The output flag is true exactly for a zero denominator. The companion
   accepted_iff theorem proves that false is equivalent to positive natural
   denominator value. This gives a returned rejection flag; it does not
   claim a separate control-flow rejection path or validation of every row.

## Same-run lower cost

The actual high run is transferred through the established polynomial
simulation to one lower Run with the same requested events, retained fields,
flag and suffix. The halt is proved from the same final state and its single
terminal attempt is explicitly included in the charge bound.

The selected denominator length is bounded by the total field-bit length.
Together with the existing row-reader bound and the real zero-loop bound,
this proves at most48*z successful instructions for
z=total-field-bits+row-count+index-word-length+1. The stated
200000000*z^3 bound follows from the explicit completeBound79,1,0 and does not
assume a semantic zero-test cost or omit pointer/lookup/terminal charges.

## Preserved scope

The source must have the stated valid encoding, and the binary index must be
in range. This proves neither malformed-stream validation nor out-of-range
handling. It validates the selected denominator and preserves the selected
fields, not every denominator or the entire graph input. The component does
not establish graph-algorithm execution or the paper's final runtime theorem.

The owner reports strict compilation, the88-declaration/type-body audit,
eight actual lower-interpreter fixtures and both official replays passed.
Those gates were not rerun by this source reviewer. No semantic changes are
required; publication and exact-commit full CI remain separate.
