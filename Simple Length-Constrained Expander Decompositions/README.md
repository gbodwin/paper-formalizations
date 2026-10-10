# Simple Length-Constrained Expander Decompositions

Bodwin, Haeupler, Hershkowitz and Tan; SOSA 2026. Source: [arXiv:2510.10227v1](https://arxiv.org/abs/2510.10227v1).

The principal proof chains are now implemented in Lean for finite simple graphs and **integer s ≥ 2**. Theorem 1.3 (arboricity) and Theorems 5.1/1.2 (decompositions) have passed exact-commit CI. The repaired Theorems 4.1/1.4 (union sparsity) have passed local kernel checks and independent semantic review; their new checkpoint's CI is tracked separately.

This is an active full-paper verification effort, not a claim that every literal source statement or arbitrary-real-s interpretation is verified. See `STATEMENT_MAP.md` for exact scope and `CORRECTIONS.md` for the ordered-demand, integral-demand, and scaled-maximality repairs. `VERIFICATION.md` separates compilation, declaration-level axiom inspection, kernel replay, semantic review and exact-commit CI. `SOURCE.json` pins the original source.
