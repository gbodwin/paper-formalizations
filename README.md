# Bodwin paper formalizations

Lean 4 formalizations of Greg Bodwin's papers, using mathlib.

## Bodwin–Patel: A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners

The implementation lives in the top-level [A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners](<A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners/>) folder.
Run the verification commands below from the repository root.

The VFT main theorem and Corollary 2 are proved end to end: the defined weighted greedy algorithm
returns a fault-tolerant spanner, constructs its small blocking set, and satisfies
explicit finite versions of Theorem 1 and Corollary 2. This is not yet a
formalization of every claim in the paper.

The main declaration is
`VFTSpanners.vft_greedy_theorem_one` in
[`PaperTheorem.lean`](<A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners/VFTSpanners/PaperTheorem.lean>).
For a finite simple undirected graph on `n` vertices, nonnegative real edge
weights, and integers `k ≥ 1`, `f ≥ 1`, its actual greedy output `H` satisfies:

- `H` is a subgraph of the input and uses the same edge weights.
- After any at most `f` vertex faults, every weighted distance is stretched by
  at most `k`, with disconnected distances represented by infinity.
- `|E(H)| ≤ 36 f² b(max(2, floor(n/f)), k+1)`, where `b(N,g)` is **defined** as
  the maximum edge count over all `N`-vertex simple graphs with girth greater
  than `g`.

The main theorem assumes neither a blocking set nor a favorable sample. Both
are constructed in the proof. The zero-fault case is proved separately.

For stretch `2r-1`, positive integers `r,f`, and `m = |E(H)|`,
`VFTSpanners.corollary_two` additionally proves
`m^r ≤ 72^r n^(r+1) f^(r-1)` together with the subgraph and distance guarantees.
This has **no Moore-bound hypothesis**. The new `Moore.lean` proves
`b(n,2r)^r ≤ 2^r n^(r+1)` by vertex pruning and short-path counting, with a
constant uniform in `n` and `r`. No additional external dependency is needed.

| Paper component | Status |
| --- | --- |
| Weighted VFT greedy algorithm and correctness | Proved |
| Equivalence of its walk test and shortest-distance test | Proved, including zero weights |
| Definition 3 and Lemma 3, small blocking set | Proved |
| Lemma 4, cycle removal and fixed-size sampling | Proved, with exact counts and explicit constants |
| Theorem 1, VFT setting | Proved in the finite rounded form above |
| Corollary 2, VFT setting | Proved unconditionally in integer-power form, with constant 72 |
| Folklore Moore bound | Proved in a coarse form with uniform constant 2 |
| EFT setting, optimality lower bound, final EFT limitation construction | Not formalized |

See the [statement map](docs/statement-map.md) for the exact correspondence,
parameter conventions, and remaining scope, and the
[verification record](docs/verification.md) for the checks performed.

## New Results on Linear Size Distance Preservers

A checked **partial** formalization lives in the top-level [New Results on Linear Size Distance Preservers](<New Results on Linear Size Distance Preservers/>) folder. It includes the branching and batching argument, distance preservation from an explicitly supplied consistent shortest-path selection, the deterministic induced-matching step, and a corrected finite weighted construction. It also proves a concrete counterexample to the Euclidean weighting displayed in arXiv v4 Theorem 5. The original existential theorem is not refuted.

This does **not** yet prove all four main theorems end to end. The paper folder documents every remaining hypothesis and missing component. Both paper libraries are included in the build, module-index check, and declaration-level axiom audit.

## Verification

The repository pins Lean 4.34.0 and mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`; dependencies are locked in
`lake-manifest.json`. GitHub Actions builds the full library on pushes and pull
requests, checks the module index, and audits every project declaration.

The audit rejects proof holes and all axiom dependencies other than
`propext`, `Classical.choice`, and `Quot.sound`. A successful build alone is not
used as evidence that a proof is complete.

For anyone reproducing the verification:

```sh
lake exe cache get
lake build
bash scripts/CheckModuleIndex.sh
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

Source: Greg Bodwin and Shyamal Patel, [arXiv:1812.05778v2](https://arxiv.org/abs/1812.05778v2),
1 June 2019. Released under the MIT license; dependencies retain their own licenses.
