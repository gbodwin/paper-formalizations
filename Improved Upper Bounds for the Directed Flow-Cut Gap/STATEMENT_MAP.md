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
The complete source-to-cut bit-time bound remains open.
[Physical amplified solvers](verification/PHYSICAL_AMPLIFIED_SOLVERS_20261119.md)
[Composed charge bounds](verification/PHYSICAL_AMPLIFIED_COST_20261119.md)
[Original input phases](verification/ORIGINAL_INPUT_PHASES_20261119.md)

| Source item | Verified scope at this checkpoint | Still required |
| --- | --- | --- |
| Theorems 1–2 | Main all-cost vertex and edge bounds, actual randomized guarantees, attained sum-flow duality, physical fractional dispatch and packed rounding on one literal tape. The original-input solvers preserve the verified output and unread suffix. | Complete deterministic bit-time bound for the outer composition |
| Theorems 3–5 | Actual finite unit-cost, uniform-weight, edge/vertex and self-reduction network | Complete algorithmic realization and runtime |
| Corollaries 6–8 | Attained normalized sparsest/concurrent-flow optima, actual weak-decomposition PMF and both main factors | Polynomial LP computation, complete algorithmic realization and efficiency |
| Lemma 9 | Actual all-regime randomized law, uniform ε expected-size and n^(-κ) high-probability size bounds. `PhysicalEpochInputProgram.physical_epoch_input` produces exact original-label order and grid assignments from the stored mask and literal fair tape. | Deterministic bit complexity of the full controller |
| Theorem 10 | Cited background only | Not claimed formalized |
| Lemma 11 | Actual indexed-path level crossing, including infinite distances | Complete |
| Lemma 12 | Every selected demand is internally cut. The loop preserves processed-demand correctness. The packed controller computes the midpoint cut, updates masks and mass, and refreshes the cache on the same heap. Its input, guarded execution and cut readback have explicit cost bounds. | Complete outer deterministic bit-time bound |
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
| Theorems30–31 | Actual dyadic edge-to-vertex and split-vertex constructions, all path/cut/count/weight/cost bridges and bounded-oracle forms | Constructive runtime |
| Theorem 32 | Actual endpoint-safe self-reduction and uniform vertex n^(1/3+ε) composition | Runtime |
| Theorem 33 | Finite family and PMF for both models. `PhysicalEdgeFamily.calibrated_physical` executes the adaptive edge-cut calls and transfers the literal fair-bit, confidence and original-weight frequency bounds. `AdaptiveWidthEnvelope.family_polynomial_reads` bounds the calibrated family in the original stored width. The exact-weight edge law also has a quadratic-horizon variant. | Complete deterministic bit-time for the adaptive composition. Near-linear horizon at the exact original-weight rounding factor. |

The current scoped gate is [the constructive workflow](../.github/workflows/flow-constructive-rounding.yml).
The adaptive edge-family extension has a [separate exact-commit gate](../.github/workflows/flow-adaptive-family.yml) and a [proof scope record](verification/ADAPTIVE_EDGE_FAMILY_20261119.md).
The charged vertex modes and original-width envelope have a [full-library gate](../.github/workflows/flow-library-verification.yml) and a [proof scope record](verification/CHARGED_VERTEX_20261119.md).
The fixed sampled-cut state update has a [proof scope record](verification/ROUND_STATE_UPDATE_20261119.md). The [physical fair-tape epoch](verification/PHYSICAL_EPOCH_SCAN_20261119.md) draws, scans and refreshes one represented epoch, with explicit instruction and heap bounds. The [physical adaptive controller](verification/PHYSICAL_ADAPTIVE_CONTROLLER_20261119.md) proves stabilization and repeated fair-tape epochs from a represented cache. The [original-graph controller](verification/ORIGINAL_GRAPH_CONTROLLER_20261119.md) builds that cache from adjacency and threshold words and links the resulting literal-tape cut to the established law. The [raw controller](verification/RAW_GRAPH_CONTROLLER_20261119.md) computes the restart ratio and budgets and returns the actual cut under the finite fair-tape law.
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
