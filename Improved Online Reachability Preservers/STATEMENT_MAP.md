# Statement map

Greg Bodwin and Tuong Le, *Improved Online Reachability Preservers*.
The reference is [arXiv:2410.20471v1](https://arxiv.org/abs/2410.20471v1), dated
October 27, 2024. The [versioned PDF](https://arxiv.org/pdf/2410.20471v1) and
[unversioned PDF](https://arxiv.org/pdf/2410.20471) have SHA-256
`9a32d8314cf4f0ab9e00e62577fde0928a58839696aae836c2d40fb1800a1abb`.
The [SODA 2025 record](https://doi.org/10.1137/1.9781611978322.149), pp. 4375–4404,
confirms the rounded online pairwise, restricted, and Steiner rates in its abstract.
The proceedings PDF endpoint returned HTTP 403. The comparison to SODA covers
its abstract and bibliographic record. All section and result numbers below refer to arXiv v1.

## Scope and conventions

- The input is a fixed finite directed graph, with spanning edge subsets as preservers.
  Reachability is reflexive. A zero-length walk answers self-demands. The path-growth search ignores
  unreachable demands. The condensed algorithm can add fixed internal SCC
  connectors at the first request. An edge subset cannot create original reachability.
- An online guarantee is for every prefix. State and choices can use the input and
  demands already seen, with no access to the future trace or its length. The source
  or sink promise is used in the analysis and need not be given to the adaptive algorithm.
  The paper takes demands to be a set. The Lean trace accepts repetitions and
  counts each arrival. For a list of distinct requests, its length is the paper's
  demand cardinality. The index-sensitive rule uses zero-based arrival indices.
- The auxiliary path system is an indexed family of ordered, vertex-simple sequences.
  Its size counts vertices with multiplicity across paths. Its degree counts paths
  containing a vertex. A bridge has distinct path indices, with a river and a chain
  of arcs. A 2-bridge can occur when two distinct paths contain the same ordered pair.
  In an acyclic system all path orders extend a common strict vertex order.
- A growth algorithm uses computable reachability queries and deterministic tie-breaking.
  Correctness, the size bound, and polynomial work are distinct claims. For uniform
  asymptotic bounds the constants are fixed before the input, and for the subpolynomial
  factors every fixed exponent slack has a uniform constant.
- The Steiner application uses a fixed unweighted graph and reachable demands.
  Its optimum is the offline minimum edge count for the original demands. Counting
  nontrivial demands excludes self-pairs and repetitions. Randomized claims need the
  success and cost guarantees and the adversary model of the invoked algorithms.

## Main and background results

| Source | Scope and dependencies | Lean coverage |
| --- | --- | --- |
| Definition 1 | For each demand, equivalence of input and preserver reachability. | [Preserves](OnlineReachabilityPreservers/Online.lean) and prefix correctness. |
| Theorem 1 | Adaptive deterministic polynomial-time pairwise online bound. The sharp terms are \(n^{(2+\alpha)/(3+\alpha)+o(1)}p^{2/(3+\alpha)}\) and \(n^{2-2\alpha+o(1)}p^\alpha\), with \(+n\) and \(\alpha\in(0.700,0.701)\) the middle root of the printed cubic. The rounded upper bound is \(O(n^{.72}p^{.56}+n^{.6}p^{.7}+n)\). Uses Theorem 9, Lemma 10, and Appendix A through Theorem 38. | [The Appendix A initial exponent](OnlineReachabilityPreservers/PairwiseInitial.lean) gives a checked \(O(n+(np)^{2/3})\) bound on the actual online preserver. The sharper theorem and formal runtime remain open. |
| Theorem 2 | One of the two endpoint promises \(P\subseteq S\times V\) and \(P\subseteq V\times S\). Adaptive deterministic bound \(O(\sqrt{np\lvert S\rvert}+n)\) on general digraphs, including prefixes, with no advance knowledge of \(S,p\). Uses Theorems 9 and 11. | [Both orientations](OnlineReachabilityPreservers/DagReduction.lean) proved on general digraphs with an explicit finite edge bound. Formal runtime certification pending. |
| Theorem 3, cited [8] | Lower bound \(\Omega((np)^{2/3}+n)\) against the stronger adversary that starts with an empty graph and inserts edges before each demand. | Cited background |
| Theorem 4 | Offline deterministic polynomial-time pairwise bound \(O(n^{3/4}p^{1/2}+n^{2-\sqrt2+o(1)}p^{1/\sqrt2}+n)\), also rounded to \(O(n^{.75}p^{.5}+n^{.59}p^{.71}+n)\). Uses the independence construction in Lemma 14 and the Appendix B extremal estimate, with degeneracies and the additive \(p\) handled in the graph bound. | Open |
| Theorem 5 | Both Theorems 1 and 2 transfer to preassigned simple paths, either with the total \(p\) known or with the arrival index \(i\) as a path-selection input. In the restricted case \(S\) is given. Uses Theorems 15 and 16. Fully non-adaptive path selection with neither parameter is left open. | [Both endpoint promises and both assignment models](OnlineReachabilityPreservers/RestrictedNonAdaptive.lean) are checked on general digraphs. The [path lift](OnlineReachabilityPreservers/PathAssignments.lean) uses a subset of the shared connectors in each simple path. The sharp pairwise rates and formal runtime remain open. |
| Theorems 6 and 7, cited [1,15,21] | Prior offline approximation with \(\min(n^{4/7+\varepsilon},p^{1/2+\varepsilon})\) and online competitive ratio \(\widetilde O(p^{1/2+\varepsilon})\) from [21]. | Cited background |
| Theorems 8 and 21 | Same new online unit-cost directed Steiner forest result, randomized polynomial time and competitive ratio \(O(n^{3/5+\varepsilon})\). Theorem 21 uses the early-pair algorithm of [21], all-pairs thick-demand hitting, the thin-pair online rounding from the [24] framework, the two orientations of Theorem 2, and Lemmas 20 and 22. | Open |
| Theorem 9 | A DAG algorithm lifts to general digraphs by SCC contraction, adding at most \(2n\) edges via one in-tree and one out-tree per component. Needs online composition, representative edges and a budget monotone under reducing vertex, demand and endpoint counts. | [SCC lift with exact overhead](OnlineReachabilityPreservers/DagReduction.lean) and prefix monotonicity proved for a DAG algorithm on arbitrary lists. A generic wrapper for a rule defined only on distinct-demand traces additionally needs stable deduplication after SCC projection. |
| Algorithms 1 and 2, Lemma 10 | Forward and backward growth prefer a previously bought feasible edge at every vertex. Ordered compression keeps new-edge tails and the terminal in the forward case, or the origin and new-edge heads in the backward case. The family is acyclic, its size is exactly \(m+p\) on reachable processed requests starting with an empty preserver, and it excludes bridges with the first or last arc earlier than the river, respectively. | [Growth](OnlineReachabilityPreservers/Growth.lean) and [ordered compression](OnlineReachabilityPreservers/Bridges.lean) checked. |
| Theorem 11, Lemmas 12 and 13 | DAG restricted bound. Lemma 12 selects a path with many high-incidence vertices in reverse-arrival insertion. Lemma 13 groups later incidences by sink and uses forbidden ordered 2- and 3-bridges. Exact counting of new-edge tails gives the same bound and handles the shared-endpoint case explicitly. | [Both cases](OnlineReachabilityPreservers/Restricted.lean) checked with the exact incidence argument. |
| Lemma 14, cited [8] | Independence lemma connects bridge-free path systems to extremal offline preserver size. The constructive direction uses minimally necessary edges and shortcutting, with tightness in the extremal sense. | Cited dependency of Theorem 4 |
| Algorithm 3 and Theorem 15 | For a deterministic current-state path rule with a uniform prefix budget \(F\) at \(p>0\), buy paths with more than \(F/p\) missing edges before assigning the remaining paths against the frozen graph. Fewer than \(p\) such purchases, and any \(p\) preassigned paths have union size at most \(2F\). Use the allowed demand domain for the restricted case. | [Checked](OnlineReachabilityPreservers/KnownBudget.lean), with strict integer comparison and preservation of the rule's paths. |
| Algorithms 4–5 and Theorem 16 | Precompute Algorithm 3 at positive dyadic budgets \(q\) starting at a linear-cost threshold. The arrival index chooses its first covering budget. Footnote 4 requires the sum of dyadic bounds to be dominated by the final term and bounded doubling of the bound. For \(p\) below the starting threshold, use the linear term directly. Domains and planned budgets can be capped by the finite pair population or the number of distinct arrivals. | [Checked](OnlineReachabilityPreservers/IndexSensitive.lean) under the two growth inequalities specified by footnote 4, with explicit constants and executable dyadic selection. |
| Theorems 17–19 and Lemma 20 | Prior algorithm of [24] and its early- and thin-demand routines. Lemma 20 lower-bounds OPT by a constant times \(\sqrt p\) for distinct nontrivial demands via terminal incidence. | Theorems 17–19 are cited dependencies. [Lemma 20](OnlineReachabilityPreservers/SteinerCounting.lean) is checked as \(p\le \mathrm{OPT}^2\). |
| Lemma 22 | Among \(p'\) nontrivial demands hit by the sampled hubs, each creates at least one previously unsatisfied terminal–hub connection. This implies \(p'\le 2\lvert S\rvert\,\mathrm{OPT}\) using oriented terminal incidence. | [Checked](OnlineReachabilityPreservers/SteinerCounting.lean) for every offline solution, with a monotone preserver and both hub subrequests served. |

## Appendix dependencies

| Source | Mathematical obligation |
| --- | --- |
| Definition 2 | Half-\(k\)-bridge-free means no bridge of size at most \(k\) whose last arc precedes the river. |
| Lemmas 23 and 39 | Clean by pruning low incidence and splitting high degrees and long paths, keeping constant fractions of all incidences. Bound the new numbers of vertices and paths and show ordered bridge-freeness survives the splits. The proof as written starts from original budgets and may increase cardinalities by splitting. To obtain a witness within the original budgets needs a rescaled starting system or a subsequent restriction argument. |
| Definition 3 and Lemma 24 | \(R(\pi_1,\pi_3)\) consists of paths that meet \(\pi_1\) before meeting \(\pi_3\) on the middle path, with \(\pi_3\) earlier in arrival order than the middle path. [IntersectionOrder](OnlineReachabilityPreservers/IntersectionOrder.lean) proves the strict left order, weak right order, and fiber bound under a common vertex order. Right intersections are also strict in Appendix B. |
| Lemmas 25–27 | The corrected tail inequality is checked in [SourceAudit](OnlineReachabilityPreservers/SourceAudit.lean). [PairwiseInitial](OnlineReachabilityPreservers/PairwiseInitial.lean) proves the chain lower count and the initial \(O(n+(np)^{2/3}+p)\) incidence bound in the acyclic setting by thresholding without splits. The unrestricted version of the bound remains open. |
| Lemma 28 | Close pairs in the ordered \(R\)-fibers charge into sampled branching subsystems. For \(\ell\ge h\ge Cp/(\ell d^2)\), the mean \(Q\)-count is \(\Omega(h\sum_R\lvert R\rvert^2/(\ell p))\). The right-side distance in the definition of close pairs must compare \(\pi_a\) with \(\pi_b\). |
| Lemmas 29–31 | Weak majorization of prefix sums, then an integral version, bounds the second moment of path lengths from an input \(H\)-bound with exponents \(a,b\). State integrability for the continuous step. [Lemma 29](OnlineReachabilityPreservers/Majorization.lean) is checked. |
| Lemmas 32–33 | Use the input extremal bound on predecessor subsystems to bound the number of long paths, then convert this into deterministic and expected counts of high branching-degree vertices. |
| Lemmas 34–36 | Dyadic branching buckets control \(Q_1\) with both endpoints off the base. The restricted-path estimate controls \(Q_2\) with its last endpoint on the base. The sum is the upper \(Q\)-bound needed for bootstrapping. |
| Lemma 37 and Theorem 38 | Compare the lower and upper \(Q\)-bounds with \(h\asymp p/(\ell d^2)\), including the cases \(h>\ell\) or \(h>d\). Derive the recurrence on exponents, use its increasing fixed-point convergence, and justify the small slack and rounding uniformly. |
| Lemmas 40–42 and Theorem 43 | In full bridge-free systems, branching has degree one. Use the offline second-moment estimate with its logarithmic term and bootstrap \(b\mapsto(2b+1)/(2b+2)\) to \(1/\sqrt2\). Show which terms can be absorbed, including losses, before applying Lemma 14. |

Here \(\ell,d\) are average path length and vertex degree and \(H\) is the
half-bridge-free extremal function. The analogous full bridge-free function is \(\beta\).
See [source notes](SOURCE_NOTES.md) for explicit discrepancies and the distinction between a
false intermediate assertion and an incomplete proof step.

## Repository provenance

The starting upstream revision was `7bacf7871a0dddd88d72e1ab50a219967e9464f4`.
All fetched heads and commit/path histories were searched for the paper title,
arXiv ID, and relevant path names. The existing
[reachability contracts](https://github.com/gbodwin/paper-formalizations/tree/94dcaef65d355cc1dd8f071eaeb0789fee60ed4e)
and [half-cover](https://github.com/gbodwin/paper-formalizations/tree/a12bcc14266a97efeb9c62006bb414d8f59b7a5f)
are for *A Note on Distance-Preserving Graph Sparsification*. Its later
[SCC quotient](https://github.com/gbodwin/paper-formalizations/blob/11690f560db73f1f05ef121d5687a1e088168482/A%20Note%20on%20Distance-Preserving%20Graph%20Sparsification/SlackSparsification/SCCQuotient.lean)
and [internal connector](https://github.com/gbodwin/paper-formalizations/blob/1f4df0b5e56e2e60ff763986179d9abd39e0db09/A%20Note%20on%20Distance-Preserving%20Graph%20Sparsification/SlackSparsification/SCCInternal.lean)
give reusable reachability arguments, phrased there over an undirected ambient graph
and oriented arcs. Their offline sourcewise bound does not supply an online algorithm.
No existing Site in the owner's PaperLab listing matched the target title.
The [publications entry](https://gregbodwin.com/publications/index.html) had an arXiv
link and no Lean link at the start of this work.
