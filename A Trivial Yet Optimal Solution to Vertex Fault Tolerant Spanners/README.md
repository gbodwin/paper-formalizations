# A Trivial Yet Optimal Solution to Vertex Fault Tolerant Spanners

Greg Bodwin and Shyamal Patel · [arXiv:1812.05778](https://arxiv.org/abs/1812.05778)

Lean 4 formalization of the paper's VFT main theorem and Corollary 2.

- [Main theorem](VFTSpanners/PaperTheorem.lean): `VFTSpanners.vft_greedy_theorem_one`.
- [Corollary 2](VFTSpanners/Corollary.lean): `VFTSpanners.corollary_two`.
- [All proof modules](VFTSpanners/), imported by [VFTSpanners.lean](VFTSpanners.lean).
- [Statement map and remaining scope](../docs/statement-map.md).
- [Verification record](../docs/verification.md).

The shared Lake configuration and pinned dependencies are in the repository root.
Run these commands there:

```sh
lake exe cache get
lake build
lake exe mk_all --check --lib VFTSpanners
lake env lean scripts/AxiomAudit.lean
bash scripts/KernelCheck.sh
```

See the [repository README](../README.md) for the precise theorem statements and scope.
