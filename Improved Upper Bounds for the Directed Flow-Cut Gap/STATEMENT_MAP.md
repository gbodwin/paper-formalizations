# Source-to-Lean status map

Pinned source: Bodwin–Samborska, arXiv:2604.03412v3 (9 July 2026).
This is a partial checkpoint. The main vertex and edge rounding bounds,
randomized output guarantees, and attained optimum and corollary interfaces
are proved. Both pipelines execute from original graph bitstrings with a
polynomial random-read bound. The physical fractional prefix and packed
integer controller have separate deterministic polynomials. The composed
vertex, edge and adaptive charge counters also have polynomial bounds in the
original input dimensions. The original-input solvers also have counted parsing,
and the adaptive solver can reuse a single charged threshold-demand computation.
The physical source entry counts serialization, binary dispatch fuel, validation and terminal decoding. The edge solver also measures flat price and weight matrix assembly, line adjacency, fractional row projection, gadget cut projection, and final output conversion. `PaidDirectEdgeWire.wire_line_polynomial` bounds the additional scalar line preparation on every literal edge source and tape, and `edgeWithLineControl_value` preserves the entire earlier paid result. `wire_boundary_polynomial` also includes the additional indexed price decode and final cut or witness projection. `FramedSolverRecords.edge` and `FramedSolverRecords.vertex` retain the earlier paid result while carrying the modeled framing record count through success or rejection. `OriginalSourceFraming.readBinary_checked` proves a bit-model bound for framing, including malformed and truncated inputs. `PhysicalSourceInputJoin` reads the three retained tables and invokes the original typed validators. `PhysicalSourceInputJoin.vertex_arrays` and `edge_arrays` bound the modeled typed input array work, including rows assembled before rejection. `FramedVertexStorage.array_polynomial` joins those vertex arrays to the fractional cache and the returned plan arrays. `BinaryLineLabels.prepare_control_polynomial` bounds nested line tabulation and its indexed reads. `FramedDirectEdgeWire.recorded_polynomial` bounds the combined recorded work on successful edge executions. The complete bit-time composition still needs a width-sensitive refinement of the remaining structural word operations.

`PaidFramedVertexWire.wire_polynomial` and `PaidDirectEdgeWire.wire_polynomial` extend the recorded-work bounds to every original source and literal tape. A failed round keeps its incurred charge, and later rows and samples execute only after the preceding one succeeds. The returned results, unread suffix, and old phase charges agree pointwise with the earlier entries.

The hard integer cutoff now calls a terminating packed interpreter without evaluating an initial fuel formula. `PaidTotalRawGraphExecution.complete_trace` bounds a complete reference trace using a tape extension inside the termination proof. The executable receives the original tape. `GuardedFuelFreeRounding.meets_old_entry` preserves the returned option and proves that recorded work stays within the earlier bound for every positive-level packed input.

The [packed cut-mask copy](verification/PACKED_MASK_ASSEMBLY_20261120.md) certifies the hard branch’s output word length, measured typed mask construction and each allocated address width. Its recorded allowance, returned mask and unread tape agree with the earlier implementation.

The [cached controller storage proof](verification/PACKED_CACHE_STORAGE_20261120.md) follows the initial cache fold and the executed packed prefix through halt or tape exhaustion. It bounds modeled persistent-array allocations, copy instructions, address widths and the operands of completed cache reads and appends.

The [measured mask readback](verification/PACKED_MASK_READBACK_20261120.md) uses binary index arithmetic and charges the cached reads of the actual final cut mask. Lean proves polynomial metadata work for every literal tape in the active regime and preserves the earlier result and recorded work.
[Physical amplified solvers](verification/PHYSICAL_AMPLIFIED_SOLVERS_20261119.md)
[Composed charge bounds](verification/PHYSICAL_AMPLIFIED_COST_20261119.md)
[Original input phases](verification/ORIGINAL_INPUT_PHASES_20261119.md)
[Physical source framing and edge composition](verification/PHYSICAL_SOURCE_FRAMING_20261120.md)
The [packed scalar execution](verification/PACKED_SCALAR_EXECUTION_20261120.md) includes the control instructions, initial cache and guarded charge accumulation. The same packed run supplies the measured mask reader. Lean bounds their combined work and links the cache and terminal mask allocations in one binary reservation trace for every literal tape in the active regime.

The [binary vertex fractional source proof](verification/BINARY_VERTEX_SOURCE_DISPATCH_20261120.md) joins the original physical parser, exact cached execution and counted terminal readback. Its separate cache layout follows the actual completed literal execution and bounds the binary reservations.

[Recorded work for every source and tape](verification/PAID_SOURCE_SOLVERS_20261120.md)
[Terminating packed rounding without numerical fuel](verification/FUEL_FREE_PACKED_ROUNDING_20261120.md)

| Source item | Verified scope at this checkpoint | Still required |
| --- | --- | --- |
| Theorems 1–2 | Main all-cost vertex and edge bounds, actual randomized guarantees, attained sum-flow duality, physical fractional dispatch and packed rounding on one literal tape. The original-input solvers preserve the verified output and unread suffix. | Complete deterministic bit-time bound for the outer composition |
| Theorems 3–5 | Actual finite unit-cost, uniform-weight, edge/vertex and self-reduction network | Complete algorithmic realization and runtime |
| Corollaries 6–8 | The executable paired vertex and edge solvers achieve the minimum of both Corollary 6 factors. Attained normalized sparsest/concurrent-flow optima and weak-decomposition PMFs establish the mathematical corollaries. `SelectedWeakCutLaw.verified` identifies the normalized law of the original-input sampler with the minimum of both loss bounds | Complete structural bit time and the unrestricted near-linear exact-weight decomposition horizon |
| Lemma 9 | Actual all-regime randomized law, uniform ε expected-size and n^(-κ) high-probability size bounds. `PhysicalEpochInputProgram.physical_epoch_input` produces exact original-label order and grid assignments from the stored mask and literal fair tape. | Deterministic bit complexity of the full controller |
| Theorem 10 | Cited background only | Not claimed formalized |
| Lemma 11 | Actual indexed-path level crossing, including infinite distances | Complete |
| Lemma 12 | Every selected demand is internally cut. The loop preserves processed-demand correctness. The packed controller computes the midpoint cut, updates masks and mass, and refreshes the cache on the same heap. Its input, guarded execution and cut readback have explicit cost bounds. The total positive-level entry uses its termination proof and runs without constructing fuel. | Complete outer deterministic bit-time bound |
| Lemma 13 | Actual restart sequence, analysis-epoch splitting, whole-trace bounds, outer recursion and explicit global parameters | Complete finite mathematical component |
| Lemma 14 | Actual uniform-level law, unconditional stopped-prefix expectation and full-epoch truncation bound | Complete finite component |
| Lemma 15 | Actual capped-ceiling horizon, active-state tail, unconditional outer cost and global parameter specialization | Complete finite mathematical component |
| Lemma 16 | Exact finite-law pushforward, supported active-prefix coupling, actual joint-event tail and graph-pair union bound | Complete finite probability component |
| Lemma 17 | Constructed charging and actual-cap application to adaptive states; numerical global-cap denominator comparison | Complete finite mathematical component |
| Lemma 18 | Actual maximal endpoint-safe family, common residual paths and stable-gate bound used on actual adaptive states | Complete repaired finite component |
| Lemma 19 | Explicit finite indexed base-path bound, including floor and constant slack | Complete finite component; see correction log for fixed-λ bookkeeping |
| Lemma 20 | Actual balanced median shortcuts, edge/mediator counts and two-edge paths | Complete finite component |
| Lemma 21 | Concrete occurrence charging with multiplicity≤2 | Complete finite component |
| Lemmas22–25 | Actual charge set, both alternatives, constructed canonical fan, exact level-value bridge | Complete finite stable-state components |
| Lemma 26 | Corrected scan, first-crossing graph extraction and maximal-family application | Complete finite stable-state component |
| Lemma 27 | Actual maximal family, proved comparison candidate and exact stable-gate mass comparison | Complete finite stable-state component |
| Theorem 28 | Actual repaired finite chain/port reduction:6n vertices,2W mass,2αW pullback | Constructive runtime |
| Theorem 29 | Actual repaired finite reduction: 4n² vertices,3W weight,6αC cost, zero cases | Runtime; exact gap notation requires the stated bounded-instance interpretation |
| Theorems30–31 | Actual dyadic edge-to-vertex and split-vertex constructions, path and cost bridges, and bounded-oracle forms. The original edge solver measures line assembly, row and cut transport, and dyadic gadget assembly. | Complete constructive bit time |
| Theorem 32 | Actual endpoint-safe self-reduction and uniform vertex n^(1/3+ε) composition | Runtime |
| Theorem 33 | `ExactFlowCutGap.vertex_law` and `ExactFlowCutGap.edge_law` give the finite probability laws at the paper's least integer factors on `Fin n` at the original total. The vertex family has a near-linear horizon. The edge family has a quadratic horizon in general and near-linear horizons under the positive-weight floor, the small-mass condition, the outgoing light weight budget, or with bounded or sufficiently large total weight. The packed edge sampler realizes the smaller calibrated headline bound from literal bits. | The unrestricted near-linear uniform edge horizon and complete structural bit time remain open. |

The current scoped gate is [the constructive workflow](../.github/workflows/flow-constructive-rounding.yml).
The adaptive edge-family extension has a [separate exact-commit gate](../.github/workflows/flow-adaptive-family.yml) and a [proof scope record](verification/ADAPTIVE_EDGE_FAMILY_20261119.md).
The charged vertex modes and original-width envelope have a [full-library gate](../.github/workflows/flow-library-verification.yml) and a [proof scope record](verification/CHARGED_VERTEX_20261119.md).
The fixed sampled-cut state update has a [proof scope record](verification/ROUND_STATE_UPDATE_20261119.md). The [physical fair-tape epoch](verification/PHYSICAL_EPOCH_SCAN_20261119.md) draws, scans and refreshes one represented epoch, with explicit instruction and heap bounds. The [physical adaptive controller](verification/PHYSICAL_ADAPTIVE_CONTROLLER_20261119.md) proves stabilization and repeated fair-tape epochs from a represented cache. The [original-graph controller](verification/ORIGINAL_GRAPH_CONTROLLER_20261119.md) builds that cache from adjacency and threshold words and links the resulting literal-tape cut to the established law. The [raw controller](verification/RAW_GRAPH_CONTROLLER_20261119.md) computes the restart ratio and budgets and returns the actual cut under the finite fair-tape law.
The [binary vertex preparation](verification/BINARY_VERTEX_PREPARATION_20261119.md) measures the scalar work on the observed cover rows and proves the literal-tape law, validity, and a source-length envelope for the returned counters. The integer cutoff gate and edge and adaptive transformations have separate cost scopes.
The [binary edge preparation](verification/BINARY_EDGE_PREPARATION_20261119.md) composes the literal input with binary gadget weights, prices and row rounding, and bounds the returned counters. Its exact output and tape agree with the earlier edge solver.
The [binary adaptive family](verification/BINARY_ADAPTIVE_FAMILY_20261119.md) joins exact parameter computation and normalized adaptive prices to the binary edge solver. The calibrated entry has the literal-tape law, original-weight frequency and confidence guarantees, and a polynomial for the returned operation counts.
The [binary source and terminal reader](verification/BINARY_SOURCE_READBACK_20261119.md) frame the dispatcher input, evaluate its instruction bound on binary words, and pay for validation and conversion of each reached terminal row or witness.
The [paired multicut solvers](verification/PAIRED_MULTICUT_20261119.md) run both modes on the same literal fair source, choose the cheaper cut at the original prices, and prove the Corollary 6 minimum bound with the original confidence.
The [amplifier and controller boundary](verification/BINARY_ROUND_BOUNDARY_20261119.md) charges the exact trial computation, shares the decoded prices, and verifies the hard controller’s packed input words and mask copy. The same checkpoint gives a near-linear exact-weight family when the original weights already satisfy the positive-weight floor.
The [dyadic gadget assembly](verification/BINARY_GADGET_LAYOUT_20261119.md) charges the actual arc collection, retained-label selection, adjacency matrix and price tests while preserving the exact reference layout.
The [line projections and exact-weight family](verification/BINARY_EDGE_PROJECTIONS_20261120.md) verify the charged line matrix and each edge boundary, and give a near-linear exact-weight horizon when the total of the tiny weights is sufficiently small.
The [weight-budget proof](verification/WEAK_DECOMPOSITION_WEIGHT_BUDGET_20261120.md) proves monotonicity in the exact total, gives two more edge horizons at the original factor, and measures the original edge and weak-cut wire matrices.
The [direct binary edge entry](verification/DIRECT_BINARY_EDGE_WIRE_20261120.md) computes the cover plan from the original edge wire and passes it to the same physical rounding and selection. Lean proves identical results and unread tape for every input and both modes.
The [exact marginal law](verification/WEAK_DECOMPOSITION_EXACT_MARGINALS_20261119.md) uses finite convex separation to obtain loss α from the original all-cost factor in both models, with validity on the whole support.
The manifest `verification/component-verification.json` records an earlier
component checkpoint.
Independent reviews record semantic scope and boundary cases. No desired
main bound, optimizer, graph-path correspondence or favorable random outcome
is introduced as a custom axiom.

The current 90-component checkpoint adds exact retained integer control,
concrete integer distances and midpoint cuts, exact joint finite epoch sampling,
and natural-parameter all-regime bounds/cost thresholds. The final adaptive
retained-output law, complete operation/bit bounds, rational transformations
and initial fractional solver are still open algorithmic obligations.

The 100-component checkpoint proves the actual single-pass retained state and
output laws, computed demand-mask/tape bridge and event counts. It also adds
counted residual/encoded candidate implementations with the explicit scope
limits in README.md. Nonterminal execution, stronger retained-edge/factory
costs, fair bits, weighted transformations and the constructive initial solver
remain separate full-paper gates.

The 112-component checkpoint adds concrete retained-edge early-stop flow,
constructed candidate enumerations/dictionaries, the actual nonterminal sampled
execution test, a factor-three rational covering recurrence with a certified
column oracle, and generic adaptive bounded-fair-bit error transfer. Full graph
bit lowering, weighted execution, concrete covering oracle/guesses and total
operation/bit complexity remain explicit unfinished algorithmic obligations.

The 130-component checkpoint adds the actual positive-cost graph-cover oracle
and output encoding, computed clone/shortcut inputs and pullbacks, concrete
integer distance/input charges, and the lazy literal-bit realization of the
actual retained controller. The latter includes ideal-law identity, default
support validity, event-error and all-branch bit-call bounds plus a substantive
nonterminal execution. Full runtime/arithmetic, the remaining reductions,
original-input LP dispatch/guesses and the concrete weak-LDD family remain open.

The 153-component checkpoint adds concrete zero-aware vertex-LP dispatch and
objective guesses, exact raw-rational graph-oracle/state/output refinement,
actual weighted preparation/uniform/heavy inputs and cut pullbacks, and shared
binary primitives plus whole-monad bounded-bit decoding. Component operation
and width bounds do not complete the controller/storage/address simulation.
The executable edge path, full outer composition and generic exact-W transfer
remain open; this checkpoint is not a full-paper release.

The 162-component checkpoint adds actual Boolean-list word/rejection and binary
rational primitives, complete retained controller and sampled-result refinement,
and concrete natural epoch/dyadic-root construction. Their local instruction
and word bounds do not complete the actual binary/storage/address join, the
edge-resource solver, weighted outer algorithm or generic exact-W transfer.
This remains a partial-paper checkpoint.

The subsequently verified 174-component checkpoint adds binary covering recurrence/width/charge components,
explicit sampler/signed-arithmetic/storage components and a retained-count
analytic lemma. These additions do not finish full algorithmic runtime or
Theorem 33's efficient exact-W construction. The exact-commit aggregate gates and combined binary-cover execution test
passed at fc11ede6; the full paper remains unfinished.

The 191-source integration branch adds seventeen unverified working components
for clean compiler feedback. It closes no additional paper statement until
compilation, execution and independent semantic gates are reconciled.

The pending 193-component candidate repairs the earlier integration and adds
literal common-denominator integer masses and binary prefix selection. The
actual approximate-packing trace has a proved pathwise 3-alpha marginal bound
under its stated reached-state oracle contract. It does not supply that oracle,
the adaptive success law, binary mass construction or final exact-W algorithm.
No additional whole-paper result is declared complete by this integration.
