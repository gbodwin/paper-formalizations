# Simple Length-Constrained Expander Decompositions

Bodwin, Haeupler, Hershkowitz and Tan; SOSA 2026. Source: [arXiv:2510.10227v1](https://arxiv.org/abs/2510.10227v1).

The main proof chains are implemented in Lean, with explicit corrections. The sharp 2/s bounds are checked for **integer s≥2**. The simplified n^O(1/s) decomposition and union statements also have complete **all-real s≥2** proof chains, using explicit 8/s exponents in their degree-weighted specializations. A Lean counterexample family proves that the exact all-real 2/s arboricity reading is false.

Compilation, all-declaration axiom audits, independent kernel replay, independent semantic reviews, and exact-commit CI are recorded separately in `VERIFICATION.md`. Full literal-source certification is not claimed. `STATEMENT_MAP.md` gives the precise statement correspondence and remaining scope; `CORRECTIONS.md` explains the matching, integrality, maximality, and parameter-domain repairs. `SOURCE.json` pins provenance.

**Completion verdict:** the main results are certified with disclosed corrections at `ab37e45d850a2cb182193cec7ab9d1ca4b6da20b`; exact CI 38064342543 passed. [The full coverage audit](COVERAGE_AUDIT.md) inventories every numbered item and identifies the original claims not established.
