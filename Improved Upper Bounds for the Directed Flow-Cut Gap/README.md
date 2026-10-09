# Improved Upper Bounds for the Directed Flow-Cut Gap

Greg Bodwin and Luba Samborska · FOCS 2026 · [arXiv:2604.03412v3](https://arxiv.org/abs/2604.03412v3)

**Partial formalization. The main flow-cut bounds are not yet proved.**
This checkpoint preserves three completed components and reproducible checks of
three source-proof issues. It does not certify the whole paper or all advertised
algorithmic claims.

## Checked components

`DirectedFlowCutGap.Basic` defines actual directed simple paths as injective
vertex sequences with consecutive graph edges. It excludes both endpoints from
vertex weights and cuts, allows zero weights/costs, and uses extended nonnegative
real distances with infinity for disconnection. It proves threshold/all-path
equivalence and the exact residual-graph characterization that retains a demand
pair's two endpoints. A cut consisting only of the endpoints cannot cut an
existing path.

`DirectedFlowCutGap.MultiplicativeWeights` proves the positive-weight component
of a corrected Theorem 33 reduction. Given an explicit cost oracle that returns
admissible sets of cost at most α times their weighted cost potential, it
constructs a finite family internally. With positive lower weight w_min, it uses

- η = min(1, α w_min)
- T = ceil(log(W/w_min)/η) + 1
- Uniform inclusion fraction at most 4 α w(e) for every item e

The cost sequence, selected sets, potential growth, and marginal bound are proved,
not supplied as hypotheses. `exists_finite_mw_family` is the main declaration.
Its cost-oracle assumption is explicit; graph instantiation, zero weights,
preprocessing, scale normalization and polynomial execution remain separate.
This component repairs the printed unscaled update rather than repeating its
incorrect logarithmic estimate.

`DirectedFlowCutGap.PackingCovering.strong_duality` proves finite incidence
packing/covering duality by geometric separation. It produces an attained
packing maximum and covering minimum with equal objective values, and an
optimal cover whose coordinates are at most one. Zero capacities and empty
index types are supported; every indexed hyperedge is assumed nonempty. No
LP-duality theorem is supplied as a premise. Identification with actual graph
path families and computational complexity remain separate.

## Source issues and remaining work

[CORRECTIONS.md](CORRECTIONS.md) records three independently checked failures of
printed proof components: endpoint deletion in Lemma 18, lost demands in
Theorem 29's contraction, and Theorem 33's unscaled multiplicative update. They
are not counterexamples to the headline bounds. The original PDF is unchanged.
The checker in `verification/` reproduces the finite examples; it is not a Lean
proof certificate.

The remaining work includes:

- Loop erasure, distance composition, finite path enumeration and minimizers
- Identify actual graph path families with the proved packing/covering model
- Endpoint-correct path witnesses and cost-reduction constructions
- Candidate-cut optimization, random level cuts, stopped epochs and charging
- Path-system counting and witness thinning
- Edge/vertex, uniform-weight, unit-cost and W-to-n reductions
- Uniform n^(1/3+ε) and n^ε sqrt(W) bounds, with constants independent of weights
- Sparsest-cut and weak-decomposition corollaries and their necessary bridges
- Rational encodings, probability guarantees and algorithmic complexity
- Full-paper statement, build, axiom, kernel and independent semantic audit gates

The source inventory contains all 33 numbered results, three definitions and two
algorithms. No missing theorem is replaced by a custom axiom or `sorry`.

## Verification

Lean 4.34.0 and the repository's pinned mathlib revision are unchanged.
The three source modules and aggregate compile with `autoImplicit=false`.
All 239 declarations pass the allowed-axiom audit, and all three components plus the aggregate pass official separate kernel replay. Evidence is recorded in `verification/`. These are component
checks, not a full-paper release.

Run from the repository root:

```sh
lake exe cache get
lake build DirectedFlowCutGap
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/AxiomAudit.lean"
lake env lean "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/KernelReplay.lean"
python "Improved Upper Bounds for the Directed Flow-Cut Gap/verification/check_counterexamples.py"
```

Pinned PDF SHA-256:
`a0f6f3a73acbfbb1c82fe04d739283c87b3e34d7f6ff850543dcb42b702c3a46`.
Pinned TeX archive SHA-256:
`9d76894e97711df52b099d4f77061c7b5737a86958fc67d2f981b1be1680ce9e`.
