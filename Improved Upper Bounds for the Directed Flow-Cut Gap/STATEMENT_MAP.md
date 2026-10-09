# Source-to-Lean status map

Pinned source: Bodwin–Samborska, arXiv:2604.03412v3 (9 July 2026).
This is a partial checkpoint. The main vertex/edge rounding bounds and actual randomized output guarantees
and attained optimum/corollary interfaces are proved; constructive runtime remains open. A checked component is not
counted as an entire source theorem when other claims remain.

| Source item | Verified scope at this checkpoint | Still required |
| --- | --- | --- |
| Theorems 1–2 | Both main all-cost vertex and edge rounding bounds, uniform constants, actual randomized core guarantees and attained sum-flow duality | Constructive runtime and encoding |
| Theorems 3–5 | Actual finite unit-cost, uniform-weight, edge/vertex and self-reduction network | Complete algorithmic realization and runtime |
| Corollaries 6–8 | Attained normalized sparsest/concurrent-flow optima, actual weak-decomposition PMF and both main factors | Polynomial LP computation, complete algorithmic realization and efficiency |
| Lemma 9 | Actual all-regime randomized law, uniform ε expected-size and n^(-κ) high-probability size bounds | Constructive runtime |
| Theorem 10 | Cited background only | Not claimed formalized |
| Lemma 11 | Actual indexed-path level crossing, including infinite distances | Complete |
| Lemma 12 | Every selected demand internally cut; actual loop traces preserve processed-demand correctness | Complete finite component |
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
| Theorem 33 | Corrected actual finite sampling family/PMF for both models, linear-in-n edge horizon via tiny-edge preprocessing, arbitrary Δ>0 normalization and explicit modified-weight oracle contract | Complete algorithmic runtime and bit complexity |

The aggregate imports every checked component. The exact source hashes and
allowed-axiom/kernel results are in `verification/component-verification.json`.
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
