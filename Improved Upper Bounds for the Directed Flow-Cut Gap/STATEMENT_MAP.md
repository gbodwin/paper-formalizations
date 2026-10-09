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
| Lemma 9 | Actual bounded adaptive output and expected-size theorem under explicit parameter inequalities | Uniform parameter specialization, final size/probability bound and runtime |
| Theorem 10 | Cited background only | Not claimed formalized |
| Lemma 11 | Actual indexed-path level crossing, including infinite distances | Complete |
| Lemma 12 | Every selected demand internally cut; actual loop traces preserve processed-demand correctness | Complete finite component |
| Lemma 13 | Actual first-ready restart sequence, analysis-epoch splitting, whole-trace cap/log bounds and finite outer recursion | Final uniform parameter specialization |
| Lemma 14 | Actual uniform-level law, unconditional stopped-prefix expectation and full-epoch truncation bound | Complete finite component |
| Lemma 15 | Actual capped-ceiling horizon, active-state tail and outer expected cost under explicit inequalities | Uniform global parameter specialization |
| Lemma 16 | Exact finite-law pushforward, supported active-prefix coupling, actual joint-event tail and graph-pair union bound | Complete finite probability component |
| Lemma 17 | Constructed charging and actual-cap application to adaptive states; numerical global-cap denominator comparison | Complete finite component; final global parameter choice separate |
| Lemma 18 | Actual maximal endpoint-safe family, common residual paths and stable-gate bound used on actual adaptive states | Complete repaired finite component |
| Lemma 19 | Explicit finite indexed base-path bound, including floor and constant slack | Complete finite component; see correction log for fixed-λ bookkeeping |
| Lemma 20 | Actual balanced median shortcuts, edge/mediator counts and two-edge paths | Complete finite component |
| Lemma 21 | Concrete occurrence charging with multiplicity≤2 | Complete finite component |
| Lemmas22–25 | Actual charge set, both alternatives, constructed canonical fan, exact level-value bridge | Complete finite stable-state components |
| Lemma 26 | Corrected scan, first-crossing graph extraction and maximal-family application | Complete finite stable-state component |
| Lemma 27 | Actual maximal family, proved comparison candidate and exact stable-gate mass comparison | Complete finite stable-state component |
| Theorem 28 | Actual repaired finite chain/port reduction:6n vertices,2W mass,2αW pullback | Runtime and final gap/asymptotic notation |
| Theorem 29 | Actual repaired finite reduction: 4n² vertices,3W weight,6αC cost, zero cases | Runtime; exact gap notation requires the stated bounded-instance interpretation |
| Theorems30–31 | Actual edge-weighted path/cut/distance foundation, including edge-preserving erasure | Genuine transformation/count/cost proofs |
| Theorem 32 | Actual endpoint-safe finite self-reduction and real-power specialization | Final uniform asymptotic composition and runtime |
| Theorem 33 | Corrected finite vertex family for arbitrary nonnegative weights from explicit rounding oracle | Edge version, preprocessing, bounded family size and runtime |

The aggregate imports every checked component. The exact source hashes and
allowed-axiom/kernel results are in `verification/component-verification.json`.
Independent reviews record semantic scope and boundary cases. No desired
main bound, optimizer, graph-path correspondence or favorable random outcome
is introduced as a custom axiom.
