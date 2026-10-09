# Source-to-Lean status map

Pinned source: Bodwin–Samborska, arXiv:2604.03412v3 (9 July 2026).
This is a partial checkpoint. The headline bounds, complete randomized
algorithm and its runtime are not yet proved. A checked component is not
counted as an entire source theorem when other claims remain.

| Source item | Verified scope at this checkpoint | Still required |
| --- | --- | --- |
| Theorems 1–2 | Genuine model, graph flow duality and many supporting components | Main uniform all-size approximation bounds and algorithm |
| Theorems 3–5 | Repaired finite unit-cost component of Theorem29 | Full self-reduction and edge/vertex/uniform network |
| Corollaries 6–8 | Generic vertex rounding-to-finite-family bridge | Main factors, sparsest-cut bridge, edge version, efficiency |
| Lemma9 | None of its final bound asserted | Full algorithm, size, probability and runtime |
| Theorem10 | Cited background only | Not claimed formalized |
| Lemma11 | Actual indexed-path level crossing, including infinite distances | Complete |
| Lemma12 | Every selected feasible demand is internally cut for every level in[0,1] | Full algorithm loop/termination invariant |
| Lemma13 | Actual mass monotonicity and exact geometric/log restart accounting | Constructed repaired schedule satisfying the shrinkage premises |
| Lemma14 | Real uniform-level expected new cost/cardinality | Random prefix law and adaptive epoch coupling |
| Lemma15 | Supporting mass and survival inequalities | Round horizon and stopping argument |
| Lemma16 | Proved Maclaurin/subset-product exponential inequality; genuine one-round hazard | Uniform permutation/independent-level coupling and stopped joint event |
| Lemma17 | Base counting and shortcut ingredients | Long/short charging and graph-value lower bound |
| Lemma18 | Endpoint-aware genuine carrier prefix and common residual subpaths | Maximal indexed family, mass lower bound and schedule application |
| Lemma19 | Explicit finite indexed base-path bound, including floor and constant slack | Complete finite component; see correction log for fixed-λ bookkeeping |
| Lemma20 | Actual balanced median shortcuts, edge/mediator counts and two-edge paths | Complete finite component |
| Lemma21 | Concrete endpoint-occurrence multiplicity≤2 | Instantiate on the full charging procedure |
| Lemmas22–25 | Counting, label, reachability and level-value foundations | Charging alternatives and canonical-sequence proof |
| Lemma26 | Corrected numerical scan and actual first-crossing graph extraction | Global witness-system application |
| Lemma27 | Attained capped optimizer and proposed comparison-candidate interface | Maximal-family assembly and its exact mass comparison |
| Theorem28 | Not asserted | Actual chain expansion and uniform-weight reduction |
| Theorem29 | Actual repaired finite reduction: 4n² vertices,3W weight,6αC cost, zero cases | Runtime; exact gap notation requires the stated bounded-instance interpretation |
| Theorems30–31 | Not asserted | Edge-weighted model and genuine transformation/count/cost proofs |
| Theorem32 | Constant correction documented | Full finite self-reduction and uniform asymptotic bridge |
| Theorem33 | Corrected finite vertex family for arbitrary nonnegative weights from explicit rounding oracle | Edge version, preprocessing, bounded family size and runtime |

The aggregate imports every checked component. The exact source hashes and
allowed-axiom/kernel results are in `verification/component-verification.json`.
Independent reviews record semantic scope and boundary cases. No desired
main bound, optimizer, graph-path correspondence or favorable random outcome
is introduced as a custom axiom.
