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
