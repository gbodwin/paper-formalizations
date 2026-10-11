# Computed-budget ordered-prefix composition: source review

Verdict: PASS within the explicit component scope.
11 October2026,19:02UTC; reciprocal source-only review by the minor-free owner.
No compiler, fixture, replay or extra worker was used by this reviewer.

Exact source: BudgetOrderedPrefixProgramDraft.lean,174 lines,
SHA25698861b14e3e0f7c8fad06c9d81fdd809603f6745730ef3793cd10b055b204513.
The complete source was read, and its hash rechecked. The inspected predecessor
interfaces include the reviewed concrete packing-expression program and the
actual OrderedCounterPrefix.materialize/steps_bound interface. Existing full
arithmetic and interpreter simulation proofs are reused dependencies; their
latest assembled-byte gate remains separate from this source verdict.

- The literal table reserves0..29 for the existing ordered-prefix program and
  offsets the whole budget program by30. It replaces only the actual budget
  halt by a real move of its result root from r3 into r0 followed by entry23.
  All successful budget opcodes and all prefix opcodes have proved agreement.
- run_high obtains the exact padded budget word from the actual three-reader
  expression execution. It supplies that same heap root and dense allocation
  cursor to the actual counter/materializer/reversal theorem. There is no
  incoming quota representation or decoded-natural instruction oracle.
- The joined NaturalRun includes the real connecting move. Its request events
  include the three full self-delimited encodings followed by exactly the
  computed quota q of subsequent source bits. The retained list has literal
  source order, and the final source is drop q. The complete heap count includes
  all three readers, arithmetic evaluation and4q+3 prefix cells. Empty stack,
  next=heap.length and the actual final halt are proved for this same output.
- The lower Run, represented ordered prefix, suffix and terminal charge share
  the same witnesses. The intermediate budget halt is not executed as a halt;
  the complete accounting includes only the final actual stopped attempt.
- The bound is correctly output-sensitive. It is a fixed coefficient times
  (q plus the three stored input lengths plus1)^6, and explicitly contains q,
  rather than asserting a polynomial solely in its logarithm. The old Boolean
  expression width bound is used only for the exact padded quota word's length;
  its old operation annotation is not reused as physical execution cost.

No required semantic fix was found. Sufficient source suffix length and valid
self-delimited encodings remain explicit premises. This materializes a finite
ordered prefix; it does not execute the graph/controller/packing algorithm,
prove a source-distribution law for that algorithm, or establish the target
paper's complete physical runtime. The separate final strict/audit/fixtures,
official replay, remote binding and full CI must refer to these exact bytes.
