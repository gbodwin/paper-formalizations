# Verification

The repository pins Lean 4.34.0 and mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Run the project checks from the
repository root.

```sh
lake exe cache get
lake build
bash scripts/CheckModuleIndex.sh
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

The audit visits all declarations by defining module, including private and
generated declarations. Its permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`. Kernel replay is a separate gate.
An exact-source replay grants no coverage to a paper statement outside the
[statement map](STATEMENT_MAP.md).

## Checked checkpoints

- [e37ed035](https://github.com/gbodwin/paper-formalizations/commit/e37ed03514ebee7204137132576a7ad8802bb662)
  proves the DAG path computation, online restricted bounds, and two printed
  formula checks. Local replay and the 158-declaration audit passed.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44387973208).
- [3cce29a0](https://github.com/gbodwin/paper-formalizations/commit/3cce29a02db7177505d83bedf214f7ddb1a5ca6b)
  adds ordered compression and the SCC lift. Local replay and the 282-declaration
  audit passed. An independent source reviewer checked the actual fold and its
  prefix quantifiers, both orientations of the finite bound, the constructed
  internal trees, and the distinction between executable searches and a formal
  time bound. The bound is on the selected edge set of the original graph.
  The interval of this review is Definition 1, Algorithms 1–2, Lemma 10,
  Theorems 9 and 11, and the restricted size and reachability clauses of Theorem 2.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44389748461).
- [c54962da](https://github.com/gbodwin/paper-formalizations/commit/c54962da3ba37706ddbd166ca73abd84922c823d)
  adds the transfers in Theorems 15 and 16, the Steiner counting lemmas, weak
  majorization, and the path-split counterexample. Local replay and the
  374-declaration audit passed. Independent review checked those source
  correspondences and the scope of the counterexample.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44392779212).
- [f1085830](https://github.com/gbodwin/paper-formalizations/commit/f1085830ed76f1c1aaa05f5c17db4cbfbb17f7ab)
  proves the endpoint-restricted cases of Theorem 5. All 18 paper modules
  replayed locally and the 465-declaration paper audit passed. Independent
  review confirmed the four assignment models, one simple path per reachable
  request, the union bound in the original graph, and prefix monotonicity.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44398649036).
- [72680592](https://github.com/gbodwin/paper-formalizations/commit/72680592486fd47e054b8672ccc9f02c7f9053df)
  adds the common-order versions of Lemmas 24, 26, and 27 and the resulting
  pairwise baseline for the actual online algorithm on general digraphs.
  The 549-declaration paper audit and kernel replay passed. Independent
  review confirmed the collision count, the bridge orientation, and the
  application to prefix purchases with shared SCC connectors.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44400107019).
- [7b80446b](https://github.com/gbodwin/paper-formalizations/commit/7b80446bfef33bc86e8c5291af571f059cc79d15)
  checks the acyclic lower branching count of Lemma 28, the combinatorial
  bound of Lemma 41, and the arithmetic exponent limits. The 651-declaration
  paper audit and replay of the changed modules passed. Independent review
  confirmed the branch window convention, injective charge, density
  comparison, and the scalar limits.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44404138536).
- [4c61e637](https://github.com/gbodwin/paper-formalizations/commit/4c61e637816f9ee537635d61350dfb4537e05787)
  adds deterministic offline pruning, the constructive DAG upper reduction
  in Lemma 14, the offline initial bound, and individual exponent
  rearrangements for Lemmas 37 and 42. The 721-declaration paper audit and
  local replay passed. Independent review confirmed the critical-edge
  argument, SCC lift, and the corrected Lemma 42 exponent.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44406935877).
- [9958e5fa](https://github.com/gbodwin/paper-formalizations/commit/9958e5fafde86f75b06374b457ad4cf97dad163c)
  checks Lemma 30 and the acyclic second-moment estimate of Lemma 31 using
  a uniform inductive bound on subfamilies. The 742-declaration paper audit
  and local kernel replay passed. Independent review checked the sorted
  subfamilies, retained path order, and continuous and discrete estimates.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44409841296).
- [c7489db5](https://github.com/gbodwin/paper-formalizations/commit/c7489db56d05ecf38d57a41b506e54b059090f24)
  adds the predecessor estimates, finite expected count, dyadic moment bound,
  and check of the overlap in Lemma 31. The 793-declaration paper audit
  and local kernel replay passed. Independent review confirmed the
  branch multiplicities and the actual induced vertex sets.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44412599474).
- [4f743d67](https://github.com/gbodwin/paper-formalizations/commit/4f743d67d05f1cf47bef1ebe2bbb229db505ae66)
  verifies the two acyclic splits, preserves all incidences, and proves the
  logarithmic offline moment and sampled upper count. The 868-declaration
  paper audit and local replay passed. Independent review checked projection
  of bridges, the incidence caps, and the moments on actual samples.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44416098982).
- [2ff66b52](https://github.com/gbodwin/paper-formalizations/commit/2ff66b52ed4d27f0951354a0fa8f9db6f6c5c591)
  checks the lower mean count, the three-term offline comparison, and the
  overlap in Lemma 40. The 877-declaration paper audit and replay of the
  changed modules passed. Independent review confirmed the exact mean,
  exponent range, and types of constants in the comparison.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44417701299).
- [01446903](https://github.com/gbodwin/paper-formalizations/commit/014469039e70e9ae0c92a860d01f13242b454459)
  applies the acyclic offline incidence update to the constructed offline
  preserver and proves the rounded bound on general digraphs. The
  917-declaration paper audit and kernel replay passed. Independent review
  checked the normalization, integer window test, and graph construction.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44420859677).
- [773a4895](https://github.com/gbodwin/paper-formalizations/commit/773a4895b0a4bd9ac87410786ecaf43d0a25cd68)
  proves the exact limiting offline edge bound with a uniform iteration
  constant. The 933-declaration paper audit and local kernel replay passed.
  Independent review confirmed the order of the constant and path-system
  quantifiers, the limiting operation, and the original-digraph guarantee.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44421721748).
- [caba3625](https://github.com/gbodwin/paper-formalizations/commit/caba3625719fc79992b6b1a1be6668e906cb8a3b)
  proves the on-base tuple count, the joint finite square-root triangle
  inequality for off-base tuples, and the scaled mean lower bound. The
  964-declaration paper audit and local kernel replay passed. Independent
  review checked the source restriction, fiber multiplicities, and dyadic cover.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44423784108).
- [86f8bb2b](https://github.com/gbodwin/paper-formalizations/commit/86f8bb2b512e70a4ceb3b94e1f0ec950bf00dc88)
  proves the normalized on-base expectation without a logarithmic loss
  and checks the uniform means of off-base bucket moments. The
  993-declaration paper audit and local kernel replay passed. Independent
  review checked the geometric regimes, normalization, and empty buckets.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44426396075).
- [b3794a3a](https://github.com/gbodwin/paper-formalizations/commit/b3794a3a736a893f3d5d2fb38e94e11226ef7822)
  proves the full acyclic branching upper bound. The 1010-declaration paper
  audit and local kernel replay passed. Independent review checked the
  separated geometric tails, all three moment powers, and cap normalization.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44428420973).
- [dee45f7d](https://github.com/gbodwin/paper-formalizations/commit/dee45f7d7ad44701b48161653191066d7681d498)
  proves the corrected finite iteration and the rounded online edge bound
  on general digraphs. The 1051-declaration paper audit and local kernel
  replay passed. Independent review checked all four terms, the window
  exceptions, and the prefix guarantee.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44430372943).
- [c5790e9f](https://github.com/gbodwin/paper-formalizations/commit/c5790e9f439539c6ad484ddf909b7a018124849b)
  proves Theorem 1's exact limiting edge bound on arbitrary digraphs. The
  1058-declaration paper audit and local kernel replay passed. Independent
  review confirmed the cubic, the exponents, and the uniform vertex-count
  slack with a single constant for all input sizes and prefixes.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44431318161).
- [5e92b045](https://github.com/gbodwin/paper-formalizations/commit/5e92b045ee08ece34299c8284c4c0395cd10639c)
  proves the rounded and limiting pairwise bounds for both path assignments
  in Theorem 5. The 1114-declaration paper audit and local kernel replay
  passed. Independent review checked the integer certificates, the clipped
  dyadic envelope, and simple original-graph paths with shared connectors.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44433680272).
- [7505df0b](https://github.com/gbodwin/paper-formalizations/commit/7505df0b4e85cccb3a62f874441c99233fc4890a)
  proves uniform all-pairs hub sampling, online hub routing and charging,
  and the balanced contribution to Theorem 21. The 1158-declaration paper
  audit and local kernel replay passed. Independent review checked the
  product counts, the cyclic reachability interval, and the exact thresholds.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44434808043).
- [ab419103](https://github.com/gbodwin/paper-formalizations/commit/ab419103b0ec7ae63f0301f00148eb88aae10c9c)
  proves monotone thin-demand cut covering and the fractional capacity bound.
  The 1227-declaration paper audit and local kernel replay passed. Independent
  review checked the integer load invariant, the finite cut enumeration, and
  charging against any feasible offline solution.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44435788128).
- [01401d01](https://github.com/gbodwin/paper-formalizations/commit/01401d01d8f39b51a469d36d11394b235196620a)
  proves the fixed-threshold rounding, irrevocable service, and expected
  thin-demand edge bound. The 1279-declaration paper audit and local kernel
  replay passed. Independent review checked the marginals, cut and prefix
  failure events, and the fallback cost on fixed traces.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44437612106).
- [d8973af3](https://github.com/gbodwin/paper-formalizations/commit/d8973af3071bd7156fa5c9b5e13491bc07b6ab95)
  replaces cut enumeration in the thin routine with a verified residual
  separator. The 1350-declaration paper audit and local kernel replay passed.
  Independent review checked signed flow with opposing arcs, the local cut
  equality, and both bounded update loops on the executed path.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44438527138).
- [011d8742](https://github.com/gbodwin/paper-formalizations/commit/011d874234fc5bad19832672f9449c1a0f9c7bd5)
  checks the counterexample to the cited inference of overlay uniqueness.
  The 1355-declaration paper audit and local kernel replay passed. Independent
  review verified the distinct-path bridge definition, the alternate route,
  and the scope of the inference refuted by the example.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44438914059).
- [02c175a3](https://github.com/gbodwin/paper-formalizations/commit/02c175a3b0dd8236d032611bcfad304d5059a1c9)
  proves feasibility, prefix monotonicity, and the combined expected late
  cost with an explicit early cost. The 1447-declaration paper audit and
  local kernel replay passed. Independent review checked the actual cutoff
  charge, the fixed thin trace, and both independent sample spaces.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44440525657).
- [46a0e93f](https://github.com/gbodwin/paper-formalizations/commit/46a0e93f6b10976af8e7ec48c704ab087af08a41)
  checks the integer Steiner thresholds and the late rate after logarithmic
  absorption. The 1461-declaration paper audit and local kernel replay
  passed. Independent review checked the uniform constant, both cutoffs,
  and the inverse-square hub failure term.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44441989079).
- [3678d99b](https://github.com/gbodwin/paper-formalizations/commit/3678d99b02eb94498d9030809f584e044f43e7fa)
  proves the unit-cost square-root junction comparison. The 1539-declaration
  paper audit and local kernel replay passed. Independent review checked the
  arborescences, heavy-demand elimination, and light edge charge.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44442385174).
- [2bd2f519](https://github.com/gbodwin/paper-formalizations/commit/2bd2f5195b7add12bd21f05cac1734cb3f944e7b)
  proves the acyclic overlay lower construction with exactly mass minus
  path count necessary edges. The 1580-declaration paper audit and local
  kernel replay passed. Independent review checked repeated-path shortcuts,
  bridge extraction, and the required consecutive-arc count.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44442685627).
- [9827de6a](https://github.com/gbodwin/paper-formalizations/commit/9827de6adf9e212d83b2e0a3ddeba0e72e90aba9)
  bounds the number of dyadic quota candidates searched. The 1580-declaration
  paper audit and local kernel replay passed. Independent review confirmed
  that the chosen levels and assigned paths agree with the previous search.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44444817085).
- [c0e42ca7](https://github.com/gbodwin/paper-formalizations/commit/c0e42ca72bd63a9d32b3c6433e11e7f5f4ef9be6)
  proves the exact acyclic cleaning budgets, both lower and upper caps,
  and the one-sixteenth incidence guarantee. Its 1623-declaration paper
  audit, kernel replay, and independent correspondence review passed.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44445138764).
- [d2a85b35](https://github.com/gbodwin/paper-formalizations/commit/d2a85b3560bb6c74ccfe8d4d0b101b1d3a7c7d67)
  proves the arbitrary-builder insertion lower bound at exact vertex and
  demand counts. The 1743-declaration paper audit and local kernel replay
  passed. Independent review checked the transcript, lattice forcing,
  counting, rounding, and the finite constant.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44447445893).
- [b07c0140](https://github.com/gbodwin/paper-formalizations/commit/b07c014083ec716ecc386e75cb70be035eed6fca)
  verifies distinct roots, unique rootward routes, the terminal block count,
  and the persistent virtual-terminal example. The 1775-declaration audit
  and local kernel replay passed. Independent review checked all three
  mathematical components and identified the leaf condition addressed
  by the stronger example.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44448933901).
- [483eff59](https://github.com/gbodwin/paper-formalizations/commit/483eff597996036412e60fec7d74861a7eae8ca0)
  checks the terminal order and strengthens the virtual-terminal example
  to leaf representatives on both sides of both roots. The 1793-declaration
  audit and local kernel replay passed. Independent review checked the
  rooted intervals and verified that the omitted original arc is required.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44450498197).
- [37b40863](https://github.com/gbodwin/paper-formalizations/commit/37b40863b90ce57bbe0f5c4f32fa341a8061cf95)
  verifies weighted fractional covering for explicitly listed binary cuts.
  The 1869-declaration audit and kernel replay passed. Independent review
  checked the exact weighted update, the cap and the normalized cost bound.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44450916781).
- [bda572f6](https://github.com/gbodwin/paper-formalizations/commit/bda572f6ccb9096b592ddf42aca4cd7413bcd28e)
  proves the actual rooted segment construction and its weighted bound.
  The 1939-declaration audit and local kernel replay passed. Independent
  review checked the prefix decomposition, the top and lower blocks,
  and the weighted count on actual arborescences.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44452159771).
- [45d8a30e](https://github.com/gbodwin/paper-formalizations/commit/45d8a30e248bb01bf47e34838ad1cf52fda96243)
  constructs the fixed inward metric tree and expands any selected links
  using shortest original routes. The 1988-declaration audit and kernel
  replay passed. Independent review checked the history count, root
  structure, exact hop lengths, and the expansion bounds.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44454016035).
- [45d24517](https://github.com/gbodwin/paper-formalizations/commit/45d245177e99aaa3e8ed6a647b11716b863ca3a1)
  embeds the shortened routes into the fixed metric tree with explicit
  terminal labels and an integer branch choice. The 2048-declaration audit
  and kernel replay passed. Independent review checked link feasibility,
  leaf coverage, deduplication and the cost bound.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44454532744).
- [aceeb3cb](https://github.com/gbodwin/paper-formalizations/commit/aceeb3cbc7ddbe12a96103526d2572b73a6b68c5)
  verifies integer capacity ceilings and the general integer cut separator.
  The 2063-declaration audit and local kernel replay passed. Independent
  review checked the rounding cost, residual cut certificate, and
  the zero-supply and coincident-terminal cases.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44455010279).
- [8a21faf6](https://github.com/gbodwin/paper-formalizations/commit/8a21faf62f574efe547367beea8333360bc3856f)
  executes weighted separation with request-local free arcs. The
  2120-declaration audit and local kernel replay passed. Independent
  review checked the cut charge, preservation of prior flows, and
  the normalized cost and update bounds.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44455872017).
- [d1da5fe1](https://github.com/gbodwin/paper-formalizations/commit/d1da5fe1faadf40d0e77a74d22f16dc75c8c72ab)
  constructs the paired metric forest and proves its offline comparator
  and expansion. The 2163-declaration audit and local kernel replay
  passed. Independent review checked root isolation, leaf
  labels, the reversed copy, zero-cost links and the cost bound.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44456704931).
- [b4bdfcce](https://github.com/gbodwin/paper-formalizations/commit/b4bdfcce48578a2955c4ca6bf4bcea300c24ee41)
  decomposes certified integer flows into simple unit routes. The
  2184-declaration audit and local kernel replay passed. Independent
  review checked the support, skew and capacity invariants and the
  degenerate endpoint and supply cases.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44458091574).
- [6bac9549](https://github.com/gbodwin/paper-formalizations/commit/6bac9549814cb4d104c90ae21755e806f14eabed)
  applies the online fractional separator to the paired forest. The
  2208-declaration audit and local kernel replay passed. Independent
  review checked current group attachments, zero links, all-prefix
  coverage at the fixed scale, and the comparison to any feasible
  original subgraph.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44458678422).
- [5efae5e2](https://github.com/gbodwin/paper-formalizations/commit/5efae5e2f4a8415bf6a4754952834aab9db69754)
  proves the one-sided group rounding probability for finite independent
  thresholds. The 2248-declaration audit and local kernel replay passed.
  Independent review checked the product count, the support of the
  estimator, and the common-prefix second moment.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44459443528).
- [d3cd6f5b](https://github.com/gbodwin/paper-formalizations/commit/d3cd6f5b32f7abcbb6ad81047859ec75b0d032e6)
  extracts the two terminal distributions at each root from a certified
  network flow. The 2311-declaration audit and local kernel replay
  passed. Independent review checked path projection, root and side
  changes, route multiplicities and the directed ancestor bounds.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44460327779).
- [bb97f686](https://github.com/gbodwin/paper-formalizations/commit/bb97f686cd5ef151d12ed05f4bee51ad0b0e3153)
  verifies integer dyadic tiers and exact finite parent cutoffs. The
  2366-declaration audit and local kernel replay passed. Independent
  review checked capacity clipping, the telescoping probabilities, group
  normalization and the degenerate thresholds.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44460812733).
- [1bf0f3d1](https://github.com/gbodwin/paper-formalizations/commit/1bf0f3d13d18a2b2467bbe287179557a05b9bbb9)
  implements the paired rounding trial and bounds its miss probability.
  The 2407-declaration audit and local kernel replay passed. Independent
  review checked the paid arcs, the shared same-root gate, the
  independent threshold events, and the final exponential bound.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44461722723).
- [eb8321c3](https://github.com/gbodwin/paper-formalizations/commit/eb8321c34bbd175f6a14b816c42afa5444e8affd)
  proves the fixed-tier purchase bound across online prefixes. The
  2448-declaration audit and local kernel replay passed. Independent
  review checked monotone charges, paid-edge identification, the exact
  marginal probability, and the ancestor profile count.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44462324546).
- [700d853d](https://github.com/gbodwin/paper-formalizations/commit/700d853dfb06754428e3094ccce44b5883d9effe)
  executes independent early trials and permanent fallback on misses.
  The 2499-declaration audit and local kernel replay passed. Independent
  review checked amplification, irrevocable retention, feasibility on
  every sample and the fixed-trace fallback estimate. It also identified
  the need for a seed-independent early trace in the full composition.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44462762946).
- [532294af](https://github.com/gbodwin/paper-formalizations/commit/532294af915963f36b31fee987b769e790c438af)
  verifies the full finite expected early edge bound against any feasible
  original solution. The 2514-declaration audit and local kernel replay
  passed. Independent review checked every trial and tier, the weighted
  sum, original expansion and fallback, and the generalized late charge.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44464387136).
- [534b7c3f](https://github.com/gbodwin/paper-formalizations/commit/534b7c3f33e49dd838345ba491e2f371b1e4f46c)
  proves the combined expected rate of Theorems 8 and 21, uses a
  seed-independent early boundary, and verifies prefix feasibility on
  every seed. The 2551-declaration audit and local kernel replay passed.
  Independent review checked the fixed-trace model, degenerate inputs,
  cutoff argument, and rate conversion.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44464960651).
- [9d2c7255](https://github.com/gbodwin/paper-formalizations/commit/9d2c72558f8b497844c0e165d48d8b5722da094a)
  moves the full Steiner evaluator to an integer hub budget. The
  2566-declaration audit and local kernel replay passed. Independent
  review checked the nonempty-graph estimates and found that an
  empty graph needed a zero-draw case. The next checkpoint adds it.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44466253050).
- [af10a045](https://github.com/gbodwin/paper-formalizations/commit/af10a045d2ba2ef7d64cdc25fca4427804073f0d)
  gives the empty graph a valid zero-draw hub sample. The
  2569-declaration audit and local kernel replay passed. Independent
  review checked the positive-count branch and the unchanged
  expected-rate and per-prefix statements for the exact evaluator.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44466968405).
- [fd9fc1ce](https://github.com/gbodwin/paper-formalizations/commit/fd9fc1ce88548d493916f8cf6d80bc681d62bddc)
  checks search and separator call budgets and a probability-preserving
  bijection for the early seed coordinates. The 2711-declaration audit
  and local kernel replay passed. Independent review found that the
  quota meter recomputed each candidate trace in separate passes. The
  following checkpoint shares the evaluated candidate results.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44467887210).
- [b0b09533](https://github.com/gbodwin/paper-formalizations/commit/b0b09533722123931ed1b85a0b7f082123a3ed4c)
  shares quota candidates and meters hop, route, SCC, forward growth and
  thin separators. The 2772-declaration audit and local kernel replay of
  the changed modules passed. Independent review checked the shared
  evaluations, output equalities and the scope of each count.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44469383213).
- [81b0420d](https://github.com/gbodwin/paper-formalizations/commit/81b0420d0a961c919392b08094862dfc2edc15b9)
  verifies the arbitrary-path fiber bound of Lemma 24 and gives a bridge-free
  example with two witnesses for the same middle path. The 2806-declaration
  audit and local kernel replay passed. Independent review checked the
  local-order proof, the strict Appendix B form and the witness example.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44470202282).
- [adbb6067](https://github.com/gbodwin/paper-formalizations/commit/adbb60678fdd8471d19d2ec75b14738c126261df)
  verifies the earlier-path pruning and split repairs. The 2849-declaration
  audit and local kernel replay passed. Independent review checked the
  per-vertex charge, local order, and distinct parents in the short bridges.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44471767518).
- [0ef5ca83](https://github.com/gbodwin/paper-formalizations/commit/0ef5ca834b492479a096d75305430e9b65ad55e9)
  proves the unrestricted initial bound and the distinct-triple count.
  The 2872-declaration audit and local kernel replay passed. Independent
  review checked that retained witnesses inject into original path triples,
  the sparse cases and preservation of the acyclic statements.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44472699012).
- [bbca66ce](https://github.com/gbodwin/paper-formalizations/commit/bbca66ce0afb565347508e051662e0de7d95a1bf)
  checks the local-order close-pair lower comparisons. The 2910-declaration
  audit and kernel replay passed. Independent review checked the online
  filter, the strict offline displacement, and the three-path cycle that
  invalidates the source-restriction step of Lemma 35.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44473906418).
- [548ecfb8](https://github.com/gbodwin/paper-formalizations/commit/548ecfb88c602067e778d6ac51ffda3267d40f2c)
  checks mass preservation and the degree and length caps through both
  splits in local path orders. The 2960-declaration audit and kernel replay
  passed. Independent review checked the corner projection, order and counts.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44474896147).
- [3cc2d31d](https://github.com/gbodwin/paper-formalizations/commit/3cc2d31db18981177d4ed6361da6a2c5cd2539d9)
  verifies the shared window normalization and the sampled path-pair
  upper count for Appendix B in local orders. The 2978-declaration audit
  and kernel replay passed. Independent review checked the exact absorption,
  preservation of the acyclic bound and the off-base uniqueness.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44475741797).
- [1b4fd730](https://github.com/gbodwin/paper-formalizations/commit/1b4fd7308b5b8e803ec363311300ed5775152984)
  checks induced list subsystems and both original cleaning budgets.
  The 3009-declaration audit and local kernel replay passed. Independent
  review checked inherited order, the old acyclic statement, and the
  different constants before and after opposite-intersection pruning.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44476586666).
- [5a5ea8a7](https://github.com/gbodwin/paper-formalizations/commit/5a5ea8a78cf3eb842e6306de4a7eeb9c6a4a4681)
  checks the sampled upper moment for local orders and the initial cubic
  estimate under unique intersections. The 3022-declaration audit and
  local kernel replay passed. Independent review checked the exact induced
  lists, the caps and preservation of the previous moment statement.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44477790171).
- [da12bf52](https://github.com/gbodwin/paper-formalizations/commit/da12bf5247e2296bbc8264786ba5b2bb3d203ef0)
  proves the unrestricted offline recurrence and Theorem 43 with zero
  exponent slack. The 3041-declaration audit and local kernel replay
  passed. Independent review checked the actual sampled subfamilies,
  sparse and out-of-window cases, uniform constant and pointwise limit.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44478646760).
- [8f48cdc3](https://github.com/gbodwin/paper-formalizations/commit/8f48cdc37651aa7eb187edadae2be01636be336a)
  counts residual and route inspections for weighted fractional runs.
  The 3103-declaration audit and local kernel replay passed. Independent
  review checked equal outputs, the failed flow and final cut searches,
  and the scope of the operation counters.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44480003591).
- [bbd7ad3c](https://github.com/gbodwin/paper-formalizations/commit/bbd7ad3cc5add798d78c98d1820335c4c1a56fda)
  checks the local predecessor and weighted branching counts of Lemmas 32–34
  and the source-restricted estimate. The 3140-declaration audit and local
  kernel replay passed. Independent review checked inherited order, unique
  intersections and the assumptions on the induced subfamilies.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44480859399).
- [6104d2ad](https://github.com/gbodwin/paper-formalizations/commit/6104d2ade5c2fb0baf408e858b0de36970b4efc3)
  checks the source-restricted suffix and dyadic count for the filtered
  on-base tuples. It also checks both Lemma 32 estimates for every selected
  long subfamily. The 3168-declaration audit and local kernel replay passed.
  Independent review checked the suffix anchor, retained targets and fibers.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44481784001).
- [8bae4dae](https://github.com/gbodwin/paper-formalizations/commit/8bae4dae8a723bba42f647f79af003be2526f9fe)
  proves the filtered on-base expectation without logarithmic loss. The
  3177-declaration audit and local kernel replay passed. Independent review
  checked the actual support sizes, geometric sum and normalization.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44482679729).
- [a9e847cf](https://github.com/gbodwin/paper-formalizations/commit/a9e847cf529da03768b708ba641edfa0307cf15f)
  verifies the actual samples and dyadic triangle inequality in the
  off-base second moment. The 3190-declaration audit and local kernel
  replay passed. Independent review checked the actual ranked subfamilies,
  inheritance of the envelope and the moment averaging.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44483573807).
- [375f9fb8](https://github.com/gbodwin/paper-formalizations/commit/375f9fb86e1bd094b343df72e71f48c8738b2afa)
  proves the full off-base expectation on local paths. The 3195-declaration
  audit and local kernel replay passed. Independent review checked the
  actual dyadic bucket inputs and normalization by the incidence averages.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44484293414).
- [06911506](https://github.com/gbodwin/paper-formalizations/commit/06911506d7a21d8b11408d2941e932c8f094f03e)
  proves the whole on-base expectation and combines it with the off-base
  terms in Lemma 36. The 3235-declaration audit and local kernel replay
  passed. Independent review checked both anchor directions, the base as a
  right branch, the dyadic sum and normalization.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44484838977).
- [d9ff71ea](https://github.com/gbodwin/paper-formalizations/commit/d9ff71ea51fc181718cdb3df2425f09de1a3c1d6)
  proves the corrected finite online recurrence for arbitrary simple
  paths. The 3252-declaration audit and local kernel replay passed.
  Independent review checked the window, exact lower and upper tuple
  counts, split budgets, and the single pruning factor for every iterate.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44485409782).
- [abada20c](https://github.com/gbodwin/paper-formalizations/commit/abada20c6c58a7c086b3966d4cbcb862d78aab4b)
  proves the unrestricted limit of Theorem 38 with one vertex-dependent
  exponent slack. The 3258-declaration audit and local kernel replay passed.
  Independent review checked the two sparse ranges, the uniform coefficient,
  and the domain of all finite ordered simple paths.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44486348837).
- [439fa13c](https://github.com/gbodwin/paper-formalizations/commit/439fa13c4030805bf0f8667134f9f427bbfe051d)
  composes reachability and successor counts for the deterministic
  online and offline algorithms. The 3285-declaration audit and local
  kernel replay passed. Independent review checked the exact outputs,
  prefix replay and operation scope.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44487967461).
- [c9385791](https://github.com/gbodwin/paper-formalizations/commit/c9385791d652e1980503b1a7c1f8d643add4f4a9)
  caches the thin separator and bounds the whole fractional run by
  successful load updates and one terminal test per request. The
  3318-declaration audit and kernel replay passed. Independent review
  found repeated interval searches in the cut reconstruction. The next
  checkpoint shares that interval before filtering its edges.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44489545275).
- [9db6e5e1](https://github.com/gbodwin/paper-formalizations/commit/9db6e5e11609f7604d2bc17cc1b8b090eeb64861)
  shares the interval during cut reconstruction and accounts for every
  thin rounding prefix, including the optional final replay. The
  3326-declaration audit and local kernel replay passed. Independent
  review checked exact output, fallback and the shared interval.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44490802990).
- [6de57197](https://github.com/gbodwin/paper-formalizations/commit/6de5719783466d2332e156aaa99476962e07df14)
  checks the larger splitting counterexample and the acyclic extremal
  converse. The 3361-declaration audit and local kernel replay passed.
  Independent review checked both counterexamples on seven vertices,
  acyclicity and exact distinct demand counts in both lower-bound cases.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44492464048).
- [ae7dad3a](https://github.com/gbodwin/paper-formalizations/commit/ae7dad3a83360577717531a831517dd1e3ec150f)
  checks the expected bit budget for drawing the Steiner seeds. The
  3405-declaration audit and local kernel replay passed. Independent
  review checked the early bit equivalence, finite first-acceptance events,
  the series and zero-size cases. The sampler analysis is per coordinate.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44493464434).
- [f131c5f5](https://github.com/gbodwin/paper-formalizations/commit/f131c5f59e6c22a468ea2b91a4a6eb27874d86b4)
  evaluates each early prefix's fractional run once for the miss check
  and metric union, and accounts for the ordinary route expansions.
  The 3424-declaration audit and local kernel replay passed. Independent
  review checked the exact seed and fallback, and identified the metric
  weight and template queries beyond the measured operations.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44494015139).
- [4e8ea0d9](https://github.com/gbodwin/paper-formalizations/commit/4e8ea0d9c922457291e17512a1c5255571bcd68b)
  checks the ordinary seeded Steiner outputs and the polynomial bound
  on the composed search charges at every feasible prefix. The
  3467-declaration audit and local kernel replay passed. Independent
  review checked the split, both hub legs, thick fallback, exact prefix
  outputs and the scope of the search bound. The two-vertex execution
  matched the ordinary purchases `[0, 1, 1, 1]` and exercised the three
  late cases separately.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44494902764).
- [19e4833e](https://github.com/gbodwin/paper-formalizations/commit/19e4833ec715705c6e3b4abc21f85cdc96fc7c26)
  verifies polynomial search budgets for six preassigned path rules and
  an indexed pairwise prefix. The 3501-declaration audit and local kernel
  replay passed. Independent review matched the optional paths, certification
  and final search, quotient and lift allowances, and both endpoint scopes.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44495797797).
- [748f0c1e](https://github.com/gbodwin/paper-formalizations/commit/748f0c1e61f94fdbb3950a488e78725b5b156cb8)
  verifies cleaning in a common vertex order for every full and half-bridge
  size. The 3495-declaration audit and local kernel replay passed.
  Independent review checked the shortcut's river and last path, and that
  one system meets all the caps and size bounds while preserving every exclusion.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44497008109).
- [573b7928](https://github.com/gbodwin/paper-formalizations/commit/573b792880ed08a76a499f15f191f1263fcdccd2)
  bounds the integers in the signed augmentation, capacity and rounding
  routines. The 3508-declaration audit and local kernel replay passed.
  Independent review checked the actual flow recursion, capacity cases and
  rounding operands, including the zero-size cases.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44498327136).
- [94a8bfc8](https://github.com/gbodwin/paper-formalizations/commit/94a8bfc8e0f6c5ddaf9f0b363e1f8d701986b40f)
  checks the retry evaluator against the uniform law on all three seed
  types. The 3555-declaration audit and local kernel replay passed.
  Independent review checked the first-success counts, expected bits,
  finite joint event probabilities and empty-coordinate cases.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44501074024).
- [a360f90e](https://github.com/gbodwin/paper-formalizations/commit/a360f90e4cffc1e2dafcddde42f78e7c184be2fd)
  computes one table of original hop distances for the early evaluator.
  The 3610-declaration audit and local kernel replay passed.
  Independent review checked the unreachable sentinel, both tree directions,
  exact separation and rounding, and the one-time graph inspections.
  A two-vertex run returned the same graph and added 12 arc inspections.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44502188351).
- [5481d01e](https://github.com/gbodwin/paper-formalizations/commit/5481d01e0284e534d058986aa77ba56385b919ef)
  shares the distance table across the complete sequence of seeded prefixes.
  The 3619-declaration audit and local kernel replay passed. Independent
  review checked exact equality of graphs and counts. The two-vertex run
  paid 12 extra arc inspections for the whole list. The generated C still
  built the paired template inside the prefix callback at this checkpoint.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44503067005).
- [b55af670](https://github.com/gbodwin/paper-formalizations/commit/b55af670556a2e99afbe36c737a39e5da536f1f2)
  materializes the paired forest, priced and free links, scale, and fuel
  before creating the prefix callback. The 3622-declaration audit and local
  kernel replay passed. Independent review checked the exact replay and
  the generated C for one preparation and the fixed weighted-loop inputs.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44504990104).
- [6decf613](https://github.com/gbodwin/paper-formalizations/commit/6decf61358fc75b5284ebd51e0b1395d2d3b4303)
  proves the balanced conclusion at a common-order maximum with positive
  budgets. The 3630-declaration audit and local kernel replay passed.
  Independent review checked the finite maximum and asked for its eligibility,
  maximality, and the upper retained mass to be explicit in the conclusion.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44505667587).
- [0f6ac5e1](https://github.com/gbodwin/paper-formalizations/commit/0f6ac5e190d8c497e993d12ed52bdb0ff81a40bf)
  states the initial family's eligibility and maximality and both sides of
  the retained-mass bound. The 3631-declaration audit, local kernel replay,
  and independent review of the common-order scope passed.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44506685244).
- [b0648629](https://github.com/gbodwin/paper-formalizations/commit/b0648629f2e9e39783094bda204573c22d2357ed)
  counts distance-table key comparisons in the shared paired template.
  The 3661-declaration audit and local kernel replay passed. Independent
  review checked both orientations, the exact prefix list, and one table
  and template preparation in generated C. The two-vertex replay reported
  12 arc inspections and 20 key comparisons for the shared preparations.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44507701923).
- [e80372d7](https://github.com/gbodwin/paper-formalizations/commit/e80372d7481b8df888533363f94479a7e63481e5)
  checks the same rounding decisions with counts of stored weight reads for
  one fractional state. The 3710-declaration audit and local kernel replay
  passed. Independent review checked the exact trial union, the two ancestor
  minima, the per-tier bound, and reuse of computed rows in generated C.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44509167990).
- [126cc61f](https://github.com/gbodwin/paper-formalizations/commit/126cc61fa32e9d6773dba8484252ea66d66934f9)
  proves vertex projection for full bridges of every size and for half
  bridges through size four. It also checks the width-two degree split
  that creates a half-6-bridge and both original cleaning budgets and all
  four caps through size three. The 3758-declaration audit, local kernel
  replay, and independent correspondence review passed.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44510793894).
- [04d7e20a](https://github.com/gbodwin/paper-formalizations/commit/04d7e20ad764a5aa53d5b537898c0dbf1babb50d)
  includes rounding comparisons at every arrival prefix. The 3773-declaration
  audit and local kernel replay passed. Independent review checked the two
  nested prefix counts and confirmed the compiled one-time preparation and
  single evaluation of each nonempty early row. The two-vertex example's
  per-prefix charges are `[0, 539960, 539960, 539960]` and its two preparations
  cost 12 arc inspections and 20 template comparisons.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44512109459).
- [1c24a035](https://github.com/gbodwin/paper-formalizations/commit/1c24a035b1b705d6f7455507ff9e7eff9c278c54)
  caches rounded capacities within each weighted separator and gives a
  bound on their integer numerator. The 3816-declaration audit and local
  kernel replay passed. Independent review confirmed free-edge precedence,
  the same charge function and cut trace, and one evaluation per priced
  capacity row in generated C. A one-arc, two-request example kept the
  same cut and charge while adding 21 in weight-read charges.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44513133106).
- [d2bb0ed5](https://github.com/gbodwin/paper-formalizations/commit/d2bb0ed5fac3075f28f86d621ac0b80f4115782d)
  chooses a maximizing simple-list family in each bridge mode and proves
  both cleaning budgets, both mass bounds, and all four caps at cutoff
  three. The 3823-declaration audit, local kernel replay, and independent
  correspondence review passed.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44513724542).
- [031078a5](https://github.com/gbodwin/paper-formalizations/commit/031078a5ae4ec1bc70dea3236a9544fc2008fc74)
  includes cached capacity weight reads throughout replay. The
  3855-declaration audit and local kernel replay passed. Independent review
  checked the exact prefix graphs and the nested charge bound. The
  two-vertex example keeps the previous preparation charges, and its
  per-prefix charges are `[0, 539964, 539964, 539964]`.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44515200844).
- [64d2c2be](https://github.com/gbodwin/paper-formalizations/commit/64d2c2be8b4a63a06f14a08a4850b6950ea970f1)
  adds one weight read per forest link in preparation and proves one
  polynomial for all measured searches and original distance-table reads.
  The 3874-declaration audit and local kernel replay passed. Independent
  review confirmed exact prefix graph and charge equality and a single
  shared setup in generated C. The two-vertex setup reports 12 arc
  inspections, 20 template comparisons, and 19 weighted-plan comparisons.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44516110338).
- [3b5d3975](https://github.com/gbodwin/paper-formalizations/commit/3b5d3975ffc208ab2e7a9911e415074471c15263)
  checks the corresponding unrestricted maximum separately for every
  cutoff up to size three, with the same retained-mass interval and
  original-average caps. The 3880-declaration audit and kernel replay of
  the changed modules passed. Independent review checked both modes,
  the unchanged cutoff, and the distinction between failed splitting
  arguments and open existence statements.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44516744399).
- [e7e8c7f3](https://github.com/gbodwin/paper-formalizations/commit/e7e8c7f3f2971ffed6ce6a4cac1d001d1f9e8473)
  proves the general path-family converse in two demand regimes with
  one uniform constant and exact distinct demand counts. The 3891-declaration
  audit, kernel replay of both changed modules, and independent review
  passed. The review checked the noncircular use of Theorem 43.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44523705923).
- [4a45291a](https://github.com/gbodwin/paper-formalizations/commit/4a45291a9cce82ee8f9318cb867ee048b7bf4b45)
  builds a capacity table once per separator, eliminates the inner key
  searches and deduplication, and bounds the measured operations of the
  same complete prefix replay. The 3904-declaration audit, local kernel
  replay of the changed modules, and independent correspondence review passed.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44527803975).
- [74fd8d97](https://github.com/gbodwin/paper-formalizations/commit/74fd8d97ae35aa8edb4d7d0c2e921f8a60efb53f)
  checks fully bridge-free examples with an arbitrarily large gap between
  the incidence mass minus the demand count and the minimum preserver size
  for the specified overlay. The 4149-declaration audit, local kernel replay,
  and independent correspondence review passed.
  [Exact GitHub Actions run](https://github.com/gbodwin/paper-formalizations/actions/runs/44532334205).

PaperLab version 14 pins 98 links to `af10a045` and contains 14 boxed L
notes. The deployment render and local controls passed. The research
publications entry linked to the arXiv manuscript at the deployment check.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [Research entry](https://gregbodwin.com/publications/index.html#publication-2410.20471).

PaperLab version 15 pins 103 links to `bbca66ce` and contains 15 boxed L
notes, including the Lemma 35 cycle. The deployment render and local
controls passed. The research entry again linked to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44473906418).

PaperLab version 16 pins 104 links to `da12bf52` and contains 15 boxed L
notes. The live deployment and local controls passed. The research entry
again linked to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44478646760).

PaperLab version 17 pins 110 links to `abada20c` and contains 15 boxed L
notes. It includes both unrestricted incidence theorems and the full
Lemma 35 repair. The deployed render and local controls passed. The
research entry again linked to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44486348837).

PaperLab version 18 pins 116 links to `6de57197` and contains 15 boxed L
notes. It presents the larger cyclic counterexamples, the acyclic converse
at an exact demand count, and the thin rounding and deterministic search
bounds. The deployed render and local controls passed. Production requires
the owner's ChatGPT sign-in. The research entry linked to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44492464048).

PaperLab version 19 pins 119 links to `19e4833e` and contains 15 boxed L
notes. The displayed CI link matches the exact proof source. The deployed
render and local controls passed. Production requires the owner's ChatGPT
sign-in. The research entry linked to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44495797797).

PaperLab version 20 pins 123 links to `5481d01e` and contains 15 boxed L
notes. The deployed render and local controls passed. Its coverage includes
acyclic cleaning at every bridge size, the seed law, and the shared hop table.
Production requires the owner's ChatGPT sign-in. The research entry linked
to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44503067005).

PaperLab version 21 pins 128 links to `126cc61f` and contains 15 boxed L
notes. It explains the half-6-bridge after a degree split and links the
full projection theorem, the exact common-order cleaning maximum, and
the arbitrary-path caps through size three. The deployed render and the
local controls passed. Production requires the owner's ChatGPT sign-in.
The research publication entry linked to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44510793894).

PaperLab version 22 pins 130 links to `33ed503f` and contains 15 boxed L
notes. The deployed render and local controls passed. The production page
requires owner sign-in. The public research entry linked to the arXiv
manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44517165176).

PaperLab version 23 pins 132 links to `4a45291a` and contains 15 boxed L
notes. The live render and local controls passed. Production requires
owner sign-in. The research entry linked to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44527803975).

PaperLab version 24 pins 133 links to `74fd8d97` and contains 15 boxed L
notes. The Lemma 14 note links the overlay gap and the relevant pages in
the two papers. The deployed render and local controls passed. Production
requires owner sign-in. The research entry linked to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44532334205).

PaperLab version 25 pins 134 links to `40848cb2` and contains 15 boxed L
notes. Lean proves cutoff-four cleaning at the unrestricted maximum in
both bridge modes with both original budgets and bounds around the witness's
averages. Independent review, the 4,182-declaration paper audit, and local
kernel replay of all 217 project modules passed. CI passed on the exact
commit. The deployed render and interactive controls passed. Production
requires owner sign-in. The research entry linked to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44541654229).

PaperLab version 26 pins 139 links to `6db0b116` and contains 15 boxed L
notes. Independent review, the 4,339-declaration paper audit, and local
kernel replay of all 221 project modules passed. CI passed on the exact
commit. The rendered deployment and interactive controls passed. Production
requires owner sign-in. The research entry linked to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44551482548).

PaperLab version 27 pins 145 links to `c7dc4922` and contains 15 boxed L
notes. The new declarations check the expected bit and edge counts under
independent infinite fair bits. Independent review, the 4,422-declaration
paper audit and replay of the changed Lean modules passed. Exact CI also
replayed every project module. The rendered deployment and interactive
controls passed. Production requires owner sign-in. The research entry
linked to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44558374523).

PaperLab version 28 pins 149 links to `73eef382` and contains 15 boxed L
notes. The checkpoint checks a fixed polynomial budget of fair bits and a
fallback that adds at most one edge in expectation. Independent review,
the 4,491-declaration paper audit, and local replay of the changed defining
modules passed. Exact CI replayed every project module. The deployment
render and interactive controls passed. Production requires owner sign-in.
The research entry linked to the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44564977060).

PaperLab version 29 pins 153 links to `b9276da5` and contains 15 boxed L
notes. Independent review, the 4,610-declaration paper audit, and local replay
of all 224 project modules passed. Exact CI also replayed every module. The
checkpoint combines a lattice lower bound with one shared Steiner preparation
and charges preparation even when the fixed bit word is exhausted.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44573210334).

PaperLab version 30 pins 154 links to `27dde48c` and contains 15 boxed L
notes. The exact-count offline lower bound passed independent review, the
4,646-declaration paper audit, and local replay of the changed modules. Exact
CI replayed every project module. The deployment render and interactive controls
passed. Production requires owner sign-in. The research entry linked to arXiv.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44576863074).

PaperLab version 31 pins 156 links to `4813ceba` and contains 15 boxed L
notes. Independent review, the 4,681-declaration paper audit, and local
replay of the changed defining modules passed. Exact CI replayed every
project module. Arithmetic ranks agree with the canonical seed order,
including rank and inverse lookups. The deployed render and interactive
controls passed. Production requires owner sign-in. The research entry
linked to arXiv.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44579972345).

PaperLab version 32 pins 158 links to `4a44baf9` and contains 15 boxed L
notes. The checkpoint proves the original-average caps for arbitrary full
bridge exclusion through cutoff four, retaining at least one 119th of the
maximizing mass. Independent review, the 4,870-declaration paper audit,
local replay of the changed modules, and exact CI replay all passed.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44584502650).

PaperLab version 33 pins 162 links to `6b17874a` and contains 15 boxed L
notes. The checkpoint extends the full bridge cleaning through cutoff five
and proves the distinct-demand SCC lift. Independent review, the
4,943-declaration paper audit, and local replay of the changed modules
passed. The first exact CI attempt reached its 30-minute limit during
kernel replay. The retry passed a full replay of every project module.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [Successful exact retry](https://github.com/gbodwin/paper-formalizations/actions/runs/44589591602/attempts/2).

PaperLab version 34 pins 173 links to `6fd5569f` and contains 15 boxed L
notes. It explains binary seed ranks, the finite-bit cursor, the size-five
half-bridge after vertex splitting, and the all-range comparison using two
lattice rates. Independent review, the 5,132-declaration paper audit, and
replay of the changed modules passed. Exact CI replayed every project
module. The deployment render, proof links, and local controls were
checked. Production requires owner sign-in. Greg Bodwin's publication
entry listed the arXiv manuscript.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44597705263).

PaperLab version 35 pins 175 links to `6f4056fc` and contains 15 boxed L
notes. The checkpoint proves exact-count lattice lower bounds in every
positive dimension and the three-lattice comparison with polynomial loss.
Independent review, the 5,173-declaration paper audit, and local replay
of the changed modules passed. Exact CI replayed every project module.
The deployed render, pinned sources, and local controls were checked.
Production requires owner sign-in.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44600398705).

PaperLab version 36 pins 179 links to `d55352c8` and contains 15 boxed L
notes. The checkpoint checks the successful cursor interval and the combined
comparison count for one sort followed by binary rank lookups. It passed
independent review, the 5,261-declaration paper audit, local replay of the
changed modules, and exact CI replay of every project module. The render,
source links, and local controls were checked. Production requires owner
sign-in.
[PaperLab](https://paperlab-online-reachability-preservers.greg-bodwin.chatgpt.site)
· [CI for its Lean checkpoint](https://github.com/gbodwin/paper-formalizations/actions/runs/44603724969).

## Independent statement review

The review of [35e4e0ea](https://github.com/gbodwin/paper-formalizations/commit/35e4e0eac89c85c678c10c16ccff415e8c8de768)
checked the correspondence of the arXiv text with all 43 numbered results,
three definitions, and five algorithms. Its Lean build, audit of 5,418
paper declarations, and local kernel replay of the changed defining
modules passed. The review confirmed the scopes of the main edge and
competitive bounds, the replacement proofs, and the distinction between
the false inequality in Lemma 25 and the construction counterexamples.
The statement map and source notes incorporate its coverage clarifications.
[Exact Lean CI run](https://github.com/gbodwin/paper-formalizations/actions/runs/44609382701).

Independent follow-up review checked the standalone Lemmas 12 and 13.
It verified the degree immediately after reverse insertion, the distinct
demand count used in the coefficient 24, and the dependency on the direct
proof of Theorem 11.
[Reviewed counting proofs](OnlineReachabilityPreservers/RestrictedIncidence.lean).

Independent review checked the shared vertex partition, preservation of
mass and degrees, the number of piece slots, and the original-mass caps.
It confirmed the (M/16) bound under the preprocessing hypotheses and the
unchanged (M/119) bound for the earlier full-bridge cutoffs.
[Reviewed partition proofs](OnlineReachabilityPreservers/VertexPartitionCleaning.lean)
· [Reviewed frozen caps](OnlineReachabilityPreservers/LocalFrozenCleaning.lean).

Independent review checked the demand-dependent early Steiner rate and the
uniform choice of height and constant before the graph and demand trace.
It also checked the empty prefix and positive comparator cost for nonempty
feasible traces of non-self requests.
[Reviewed demand-dependent proof](OnlineReachabilityPreservers/SteinerCompetitive.lean).

Independent review checked the list-backed deterministic forward run's
prefix edge sets, duplicate-free invariant, and comparison polynomial.
The generated code uses the charged list scans and purchase pass. The
comparison model charges each pair equality or minimum call once.
[Reviewed list evaluator](OnlineReachabilityPreservers/DeterministicListWork.lean).

Independent review checked the prepared least-vertex labels, duplicate-free
condensation, and equality of the forward quotient run on any supplied prefix.
The generated evaluator shares one transpose and one label table across the
two projections. Its comparison budget includes list lookup and deduplication.
[Reviewed SCC and quotient evaluator](OnlineReachabilityPreservers/SccListWork.lean).

The lifted comparison proofs use the ordinary original-arc representatives
and shortest-hop connectors. The sink and source evaluators return the same
graphs on every prefix, including the empty prefix, and bound the sum of
key comparisons when the prefixes are evaluated separately. The offline
evaluator uses the exact sorted deletion order on the condensation and the
same lift. Its pointwise theorem covers reachable, unreachable, self, and
repeated requests. The ledger counts operations on abstract keys.
[Exact general-digraph comparison proofs](OnlineReachabilityPreservers/SccLiftListWork.lean)
· [Exact greedy deletion order](OnlineReachabilityPreservers/OfflineListWork.lean).

The common-partition cleaning theorem handles both bridge modes at every
cutoff under explicit partition hypotheses. It counts only occupied copies
and pieces. With the full original incidence mass, both upper caps, and at
most four thirds of both original support budgets, the cleaned witness stays
within both original budgets and retains at least one sixteenth of the mass.
Its four caps are relative to the original averages.
[Common-partition proof](OnlineReachabilityPreservers/CommonPartitionCleaning.lean).

The sharper opposite-intersection pruning bound leaves the first incidence
of each retained path uncharged. Every original nonempty path retains its
last vertex. This gives the exact mass bound with the count of nonempty
paths, and reversed copies of the vertex order attain it. The frozen
peeling extension assumes every original path is nonempty, the original
upper caps hold on the pruned system, and the original mean length is bounded.
[Pruning and sharpness](OnlineReachabilityPreservers/OppositePruningGain.lean).

The ordered-piece proof isolates a nested reversal pattern in the only
remaining repeated-parent case for a four-corner half-bridge. Its absence
permits the usual two splits and the frozen one-sixteenth cleaning bound.
Two concrete proofs check splitting with the printed mean and with exact
factor-four widths. The eight-vertex printed-mean example has uniform
degree two and mean length four. Only the length-eight path requires a
midpoint split, and the resulting half-4-bridge persists after the loops end.
Independent review checked the repeated-parent analysis and both exact examples.
A four-path example from the audit keeps the nested obstruction under every
arrival permutation. Each central row is the inner partner of the other.
[Conditional split proof](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean)
· [Verified average-width witnesses](OnlineReachabilityPreservers/AverageSplitAudit.lean).

Independent review checked both directions of the criterion for a fixed
ordered split. A surviving nested reversal has four required piece steps.
They give a half-4-bridge with the later inner partner as the river. Every
new half-4-bridge projects to a forbidden bridge or forces such a reversal.
The previous sufficient condition is a corollary with the same hypotheses.
The review also checked that mirrored cuts in packed ranks preserve path
order and transport strict last-arc arrival. This gives frozen half-four
cleaning when the input excludes full bridges through size three. In the
dense case both expanded supports fit the rectangle estimate and the
construction retains at least one 119th of the original mass after
peeling. The sparse case uses a separate fully bridge-free witness.
[Exact split criterion](OnlineReachabilityPreservers/ContiguousHalfCleaning.lean)
· [Arrival transport](OnlineReachabilityPreservers/SynchronizedPathSplits.lean)
· [Frozen proof](OnlineReachabilityPreservers/LocalFrozenCleaning.lean).

The vertex-projection extension was reviewed independently. When distinct
corners collide, a closed portion of the projected chain has at least two
arcs. Erasing closed portions keeps the river and leaves a bridge at least
two sizes smaller. With full exclusion through size \(r\), this prevents
collisions for half-bridges of size at most \(r+2\), allowing both the last
arc and the river to keep their arrival indices. Taking \(r=3\) extends
the frozen cleaning construction through half cutoff five with the same
full-through-three input condition. The review checked the small-mass
witness and the restriction and peeling guarantees in the dense case.
[Projection with size loss](OnlineReachabilityPreservers/BridgeVertexProjection.lean)
· [Vertex splitting](OnlineReachabilityPreservers/LocalRegularization.lean)
· [Conditional cleaning through five](OnlineReachabilityPreservers/LocalFrozenCleaning.lean).

## Execution examples

A finite execution check of the PaperLab example gave cumulative purchases
`[0, 3, 4, 5, 5]`. The list-backed evaluator gave the same edge sets with
cumulative comparison counts `[0, 657, 1383, 1967, 2553]`. A graph with a
two-vertex SCC confirmed the internal and
crossing edges on a cyclic input. A five-vertex example with two nontrivial
SCCs and a repeated raw crossing arc returned labels `[0,0,2,2,4]` and
exactly the two projected arcs `(0,2)` and `(2,4)`. The label table and
condensation together took 1,796 comparisons. The three projected requests
used 1,933 comparisons including preparation. Every prefix had the ordinary
quotient forward run's edge set. The empty prefix has no edges, an
unreachable forward request returns `none`, and a self-request returns an
empty path. An execution of the complete Steiner draw evaluator on a
two-vertex graph, with a repeated demand and a self-request, gave
cumulative purchases `[0, 1, 1, 1]`.
The bit-driven replay on that one-arc graph at height zero consumed 201
supplied zero bits, gave the same cumulative purchases, and returned the
following two bits unread. An empty input returned no result.
Using the graph-based orders, the height-zero replay gave the same result.
At height one, the decoder consumed 7,177 supplied zero bits and returned
the next two bits unread.

On the cyclic input with a duplicated crossing arc, the lifted sink and
source evaluators both matched the ordinary edge sets over five arrivals,
with counts `[0, 6, 6, 6, 6, 6]`. The sink replay charged 19,936 key
comparisons across those six prefixes. The lifted offline evaluator also
matched each supplied prefix. On the directed diamond the greedy list
evaluator kept `(0,2)` and `(2,3)`, as dictated by the original lexicographic
deletion order. The empty graph on zero vertices returned an empty list and
zero comparisons.

A 30-vertex family of 11 paths with no full bridge at any cutoff had
39 incidences, maximum length 19, and maximum degree 10. Two common partitions
produced 31 occupied vertex copies and 12 nonempty pieces, with maximum
length 10 and maximum degree 5. The occupied supports fit the four-thirds
allowances and the upper caps use the original budgets and mass.

The weighted-capacity replay builds a table once per separator and constructs
residual graphs from the stored values and their unique keys. The two-vertex
run with two weighted requests returned the same cut and charge as the ordinary
run. Its measured search and table work was 174, compared with 141 measured
search operations in the ordinary run. The complete replay's per-prefix
charges were `[0, 541260, 541260, 541260]` and its three shared preparations
cost 12, 20, and 19. [Checked separator comparison](OnlineReachabilityPreservers/SteinerCapacityWork.lean)
· [Checked complete replay bound](OnlineReachabilityPreservers/SteinerDistanceReplay.lean).
