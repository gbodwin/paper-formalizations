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

A finite execution check of the PaperLab example gave cumulative purchases
`[0, 3, 4, 5, 5]`. A graph with a two-vertex SCC confirmed the internal and
crossing edges on a cyclic input. The empty prefix has no edges, an
unreachable forward request returns `none`, and a self-request returns an
empty path.
