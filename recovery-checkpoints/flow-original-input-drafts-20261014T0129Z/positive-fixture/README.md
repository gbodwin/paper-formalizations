# Positive whole-dispatcher fixture draft — UNRUN

Prepared 2026-10-14. This is a NEW test harness, not recovered historical
source. No Lean, lake, compiler, interpreter, kernel replay or runtime process
was launched while preparing it. Only source reads, file writes and the Python
static checker were used. There is no positive physical result yet.

## Fixture

- Vertices: 0, 1, 2.
- Directed edges: 0→1 and 1→2; no other edges.
- Demand: (0,2), exactly once.
- Original costs: [0/1, 1/1, 0/1], using canonical zero/one fields.
- Source bits: [true,false,true].
- Original input store: 56 cells from the literal constructor, checked at run time.
- Entry: 13318; successful final halt location: 13319.

This is minimal in vertex count for this dispatcher: with at most two vertices,
a distinct-endpoint demand has a path only if there is a direct edge (the
infeasible branch), while a self-demand is also infeasible. If there is no such
path, dispatch yields a zero cut. The chain's sole internal vertex has positive
cost, and its zero-cost endpoints remain present under keptAdjacency, so the
path survives the zero-cost mask. The program must take its positive route.

The source-derived grid size is 2·1 + 2·size(3) + 3 = 9. Each cover uses the fixed
3·3² = 27 inner stop tests, totaling 243 across the family. These are semantic
loop counts, NOT physical instruction counts or wall-clock estimates.

The earlier GridFamilyInputSmoke positive cases call the grid entry directly
on one vertex, including no-demand/self-demand inputs. They do not establish a
positive execution of the whole dispatcher. The existing OriginalDispatchSmoke
positive case establishes a suitable branch-shape precedent, but its endpoint
fractions use zero denominators and cannot be copied as valid Fraction input.
This draft uses denominator one throughout.

## Files

1. FinalDispatchPositiveFixtureSupport.lean: input packing, branch preflight,
   raw-field decoders and observation-side solveInput comparison helpers.
2. FinalDispatchPositivePhysicalSmoke.lean: literal BitState 13320 execution.
3. FinalDispatchPositiveNaturalDiagnostic.lean: separate tickNatural diagnostic.
4. static_check.py and draft-manifest.json: source-only checks and hash inventory.

None is a production module. Production source files were not edited.

## Physical acceptance conditions

The executable requires one explicit positive maximum-attempt count. There is
no default large run. The cap includes successful instructions AND the final
paid terminal attempt. Exhausting it emits INCOMPLETE_PHYSICAL and a nonzero
exit; a stopped failure at another program location cannot be accepted.

Execution calls ImmutableReferenceTerminal.attempt FinalDispatch.program on
the actual BitState. Every successful result comes from that call. No child
result, branch witness, dispatch context, generated vertex list, grid fuel,
minimum, shifted row or output state is installed in the initial heap.

The check requires:

- Observed original dispatch entry 12898, positive continuation 13306, minimum
  entry 13262, grid call 13309, actual grid entry 10758 and output wrapper 13311.
- Final location 13319, empty stack, unchanged source and zero I/O events.
- attempts = successful instructions + 1.
- Exact terminal attempt cost controlCost 13320 = 13336.
- Total charged operations = sum of the actual successful attempt charges +
  the single actual terminal charge. A separate terminal replay is an
  observation and is deliberately not charged a second time.
- Original a/b/c pointer bits and their decoded cost/matrix/demand content;
  preservation of the original physical and erased heap prefix; dense cursor.
- Positive output tag nil, then nine correctly decoded states in exact order.
- Bit-for-bit equality of weights, best row, bestCost, total, loads, event masks,
  bottleneck labels and event fractions against states from the real high-level
  BinaryFractionalGuesses.solveInput. It compares the stored state projection,
  not Result.operations/stopTests or other non-stored Result metadata.
- Instruction and total physical-operation envelope checks against
  FinalDispatch.inputBound and ImmutableReferenceTerminal.completeBound.

The successful-instruction count is discovered by actual execution and printed.
It is not hardcoded. The only numeric expected values are properties of the
fixture/model (56 initial cells, 9 grid entries and 13336 halt charge).

## Heap retention and progress

Both execution loops use a direct tail recursive call with one current state,
scalar counts and Boolean visit observations. Progress is printed and flushed
after each 1000 attempts, before the tail call. There is no recursive chunk
return that holds an old state and combines its totals after the next run.
The caller retains only the small original input for later preservation checks.
The source pattern is tail-recursive; compiler/runtime behavior is still UNRUN.

This does not remove production costs. The physical interpreter performs
sequential bit-address lookup and literal full-store copying on allocation.
Those helper bodies have their own recursion and the growing heap itself is
unavoidable. Every grid state is retained by the production algorithm. Memory,
stack usage and runtime can be substantial even for this smallest fixture.
The high-level oracle and output decode are additional post-run work. Their
phases are announced, but are not part of the physical charge.

## Future bounded verification, not performed

Use the already assigned single-thread compiler/runtime slot and lock at
/workspace/shared/formalization-compiler.lock. Recheck that all nine actual
final-dispatch modules and the exact722 dependencies have current strict
receipts before compiling the test. The snapshot hashes in draft-manifest.json
identify source inspected while drafting, not successful imports or objects.

Compile support first into an isolated test object directory. Add that directory
to LEAN_PATH alongside the existing single flattened DirectedFlowCutGap project
object overlay and its external dependencies. Do not combine two partial
DirectedFlowCutGap overlays. Compile each test under -j1,
-DautoImplicit=false and -DwarningAsError=true, keeping the exact command,
source/import hashes, log, exit status, duration and resource caps in new receipts.
No existing production runner allowlist is changed by this draft.

Only then assign explicit wall-time, memory/stack and attempt caps for a runtime.
An optional natural diagnostic can first expose instruction/heap growth and
route observations, but it must be labelled NATURAL_DIAGNOSTIC_MATCH_ONLY and
NEVER promoted to physical evidence. A finite cap/timeout is incomplete evidence,
not a pass, a proof failure or a reason to replace the actual interpreter.
A physical run can print PASS_PHYSICAL only after its whole check succeeds.

There is no measured successful-instruction count, final heap size, total paid
cost, wall-clock duration, peak RSS, compilation result or physical pass for
this draft. No affordable completion time is promised. Even a later fixture
pass is one test of already represented roots; it is not source parsing,
a proof of all-input execution, a fresh kernel/axiom audit, exact-commit CI,
native allocator correctness or whole-paper completion.

## Source references

Exact722 base:
/workspace/shared/flow-published722-recovered-20261014T0012Z/Improved Upper Bounds for the Directed Flow-Cut Gap

Inspected new dispatcher:
/workspace/shared/flow-final-dispatch-reconstruction-20261014/DirectedFlowCutGap

Relevant source: OriginalDispatchSpec.lean, BinaryFractionalDispatch.lean,
BinaryFractionalGuesses.lean, ImmutableReferenceSimulation.lean,
ImmutableReferenceTerminal.lean, PackedWordPairTable.lean,
GridFamilyInputSmoke.lean, OriginalDispatchSmoke.lean and the nine new
FinalDispatch modules. Exact hashes are recorded in the manifest.
