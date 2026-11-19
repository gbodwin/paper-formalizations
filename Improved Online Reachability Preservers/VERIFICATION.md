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

A finite execution check of the PaperLab example gave cumulative purchases
`[0, 3, 4, 5, 5]`. A graph with a two-vertex SCC confirmed the internal and
crossing edges on a cyclic input. The empty prefix has no edges, an
unreachable forward request returns `none`, and a self-request returns an
empty path.
