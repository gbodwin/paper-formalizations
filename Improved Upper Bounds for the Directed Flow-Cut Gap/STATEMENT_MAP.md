# Source-to-Lean status map

Pinned source: Bodwin–Samborska, arXiv:2604.03412v3 (9 July 2026).
This is a partial checkpoint. The headline bounds, complete randomized
algorithm and its runtime are not yet proved. A checked component is not
counted as an entire source theorem when other claims remain.

| Source item | Verified scope at this checkpoint | Still required |
| --- | --- | --- |
| Theorems 1–2 | Genuine model, graph flow duality and many supporting components | Main uniform all-size approximation bounds and algorithm |
| Theorems 3–5 | Repaired finite unit-cost component of Theorem 29 | Full self-reduction and edge/vertex/uniform network |
| Corollaries 6–8 | Generic vertex rounding-to-finite-family bridge | Main factors, sparsest-cut bridge, edge version, efficiency |
| Lemma 9 | None of its final bound asserted | Full algorithm, size, probability and runtime |
| Theorem 10 | Cited background only | Not claimed formalized |
| Lemma 11 | Actual indexed-path level crossing, including infinite distances | Complete |
| Lemma 12 | Every selected feasible demand is internally cut for every level in[0,1] | Full algorithm loop/termination invariant |
| Lemma 13 | Actual candidate minima, first-ready restart sequence, whole-trace geometric/log bounds | Analysis-epoch splitting and probabilistic loop assembly |
| Lemma 14 | Real uniform-level and full frozen-prefix expected new cost/cardinality | Instantiate stopped truncation on the adaptive process |
| Lemma 15 | Supporting mass and survival inequalities | Round horizon and stopping argument |
| Lemma 16 | Actual uniform permutation/product-level law, exponential graph survival, joint stopped wrappers | Verify wrapper coupling for the complete adaptive process |
| Lemma 17 | Constructed long/short charging and exact stable current-mass graph-value bound | Apply to the adaptive process with global parameters |
| Lemma 18 | Actual maximal indexed endpoint-safe family, common residual paths, stable-gate mass lower bound | Adaptive schedule application |
| Lemma 19 | Explicit finite indexed base-path bound, including floor and constant slack | Complete finite component; see correction log for fixed-λ bookkeeping |
| Lemma 20 | Actual balanced median shortcuts, edge/mediator counts and two-edge paths | Complete finite component |
| Lemma 21 | Concrete occurrence charging with multiplicity≤2 | Complete finite component |
| Lemmas22–25 | Actual charge set, both alternatives, constructed canonical fan, exact level-value bridge | Complete finite stable-state components |
| Lemma 26 | Corrected scan, first-crossing graph extraction and maximal-family application | Complete finite stable-state component |
| Lemma 27 | Actual maximal family, proved comparison candidate and exact stable-gate mass comparison | Complete finite stable-state component |
| Theorem 28 | Actual repaired finite chain/port reduction:6n vertices,2W mass,2αW pullback | Runtime and final gap/asymptotic notation |
| Theorem 29 | Actual repaired finite reduction: 4n² vertices,3W weight,6αC cost, zero cases | Runtime; exact gap notation requires the stated bounded-instance interpretation |
| Theorems30–31 | Not asserted | Edge-weighted model and genuine transformation/count/cost proofs |
| Theorem 32 | Actual endpoint-safe finite self-reduction and real-power specialization | Final uniform asymptotic composition and runtime |
| Theorem 33 | Corrected finite vertex family for arbitrary nonnegative weights from explicit rounding oracle | Edge version, preprocessing, bounded family size and runtime |

The aggregate imports every checked component. The exact source hashes and
allowed-axiom/kernel results are in `verification/component-verification.json`.
Independent reviews record semantic scope and boundary cases. No desired
main bound, optimizer, graph-path correspondence or favorable random outcome
is introduced as a custom axiom.
