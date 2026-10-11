# Concrete expression instruction compilation: exact-source semantic review

Verdict: PASS within the explicit component scope.
Reviewer: minor-free-spanners owner, reciprocal source-only review on
11 October2026,18:49UTC. No child, compilation or kernel replay was run by
the reviewer. This is not an independent whole-paper runtime audit.

## Exact source binding

The four sources were read in full. Their SHA256 hashes and line counts match
verification/expression-frozen-sources.json:

- ConcreteExpressionProgramDraft.lean,519 lines:
  ae949a9782e72cd376cbf59c294e9e4f57740d989ce03dd4597c1967bf922ae7
- ConcreteExpressionBoundsDraft.lean,111 lines:
  b06224abc253a2c5f28ab027b2be3cb652beb7551ad899077ef88223edbd3f3c
- InputExpressionProgramDraft.lean,217 lines:
  87291fb62d53b8b330b856546ed285cc5488eadcdebae3d221373369a09cf2a3
- PackingBudgetProgramDraft.lean,47 lines:
  32e47adafdbc0f49fe632387b546c57d36f013d99ff7edfda7767a6b7e51f4f9

Relevant previously proved interfaces inspected: saved-stack run preservation,
terminal attempt/result/accounting semantics, and the literal
EncodedPackingBitBudget.body/run_value polynomial. The existing arithmetic,
label relocation and high-to-low simulation theorems are reused dependencies,
not newly independently reverified here. Final exact assembled build, audit,
fixtures, official replays, remote byte binding and full CI are separate gates.

## Substantive findings

1. The output program is a literal finite instruction table depending only on
   static syntax. Arithmetic slots occupy0..95; expression code starts at96,
   followed by a real top-level call and final halt. The closed agreement and
   slot lemmas discharge the local lookup conditions. The helper Agree premise
   is not exposed as an evaluator-correctness assumption in evaluate_high,
   evaluate_bit, evaluate_from_source or compute_budget.
2. Saved-register handling is sound. The left child returns into r3; the right
   child begins with the original a,b,c inputs and the saved left root in r3.
   Its caller frame returns the right root into r2 and restores the left root.
   Only then are the arithmetic a/b arguments overwritten. Every outer return
   restores the original caller registers except its chosen destination. This
   includes input2, repeated syntax and nested right subtrees.
3. Literals allocate actual nil/flag/pair cells. Input nodes may share the
   existing input root; no old expression-copy charge is reused. Binary nodes
   call the real relocated addition/multiplication bodies, and their return
   instructions pop actual caller frames. The recursive proof explicitly joins
   all instruction runs. runSteps includes each syntax occurrence, node call,
   move and return, while runCells accounts for the actual appended heap.
4. The closed high-level endpoint proves the exact padded Boolean word, original
   represented inputs, append-only heap extension, source retention, empty
   stack, actual final halt and next=heap.length simultaneously. Its lower
   endpoint transfers that same run through polynomial_simulation and applies
   terminal_accounting to its actual stopped output. The terminal charge is
   included; it is not paired with an unrelated output witness.
5. The width coefficient is linear in the stored input length. The instruction
   and allocation coefficient is quadratic and depends only on static syntax;
   multiplication's asymmetric2*left+right+1 width is accounted for. The final
   sixth-power bound follows the actual completeBound, with H/B resources and
   all successful instructions plus final attempt covered. No constant in the
   fixed packing specialization depends on the three input words or suffix.
6. The three-reader composition starts with genuinely empty heap/stack. It copies
   the real self-delimited readers into disjoint label ranges and replaces their
   three old halts with actual register moves. Exact request events consume
   precisely the three encodings, retaining the arbitrary suffix. Prior input
   roots remain valid through append-only allocation. The composed heap length
   and total instruction count include all readers, moves and the expression.
7. PackingBudgetProgram substitutes the literal checked budget expression and
   proves both equality with its full padded output word and the exact displayed
   natural polynomial. Its Run, retained input representations, exact suffix,
   halt and terminal-inclusive bound share the same charge/out witnesses.

## Limits and required fixes

No semantic fix is required for these four exact sources. The valid
self-delimited three-word encoding remains an explicit input domain; there is
no arbitrary raw-input parser/validation theorem. The result computes a fixed
arithmetic budget in the specified binary-reference model. It does not execute
the graph/controller/packing algorithm, splice that algorithm's fuel or output
prefix, establish the old abstract read charge7, or prove the paper's claimed
full physical runtime. Existing aggregate paper scope and remaining proof gaps
must remain explicit. Final compilation/replay/CI must still use these exact
hashes; a source change needs a new binding or review as appropriate.
