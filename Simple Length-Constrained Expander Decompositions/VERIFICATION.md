# Verification record

## Hiker and finite-termination checkpoint — 10 October 2026

All 11 current paper modules compiled using pinned Lean 4.34.0 (293d5d0c0c3f3dded4688b3ccd6a33939ac5102b) and mathlib 5ed2965256430c3649e86755f9576b54eca72435. Local checks completed before this checkpoint was packaged:

- The all-declarations audit passed for **185 LengthExpander declarations**, allowing only `propext`, `Classical.choice`, and `Quot.sound`. See `verification/axiom-audit.log` and its reproducible `Audit.lean`.
- Independent Lean kernel replay passed for all **11 project modules**, individually and sequentially. See `verification/kernel-check.log`.
- `verification/source-hashes.json` pins the Lean source files corresponding to this checkpoint.
- Exact-commit remote CI is **pending publication of this checkpoint**. Earlier checkpoint dc2fdebcaadeaa64ce1bb6c36463b5a89e491a80 passed run 38053315596; that result does not certify these new sources.

### Proven component scope

- Finite directed integral demand budgets, witness cost bounds, and the corrected ratio-of-sums inequality.
- Actual graph-walk metric semantics and length-increase cuts; an attained maximum separated-demand volume and positive sparse witnesses.
- Ordered matching labels and earlier-walk exclusion; the short-cycle maximum-label conclusion (Lemma 3.2), fixed-length increasing-walk uniqueness (Lemma 3.3), and the resulting exact n² dispersion bound.
- Genuine matching permutations and graph hiker walks; one hiker per vertex, increasing labels, exact total traversal count 2|E|, and an exact-length **walk** version of weak counting (Lemma 3.4).
- Finite termination by decreasing cardinality of actual h-near ordered pairs; a constructed maximal sparse-cut sequence, with no assumed termination oracle.
- A conditional reduction from the **remaining union-cost bound** to a decomposition. The returned decomposition is the unscaled sum; the larger scaled sum is used only to bound its cost.

### Semantic review and remaining work

The independent review in `verification/independent-semantic-review-20261010.json` covers its four hash-pinned modules and confirms the corrected maximality argument at the mathematical level. It predates the final hiker modules and the reduction module; a refreshed independent review is still required. Compilation/kernel replay are not substitutes for that review.

Deletion/medium counting, fixed-size sampling, the explicit density/arboricity theorem, the repaired directed-demand/integral-extraction Appendix A bridge, the union-cost bound, and the end-to-end main theorems remain unfinished. **No main theorem is certified.** The graph-level maximality counterexample in `CORRECTIONS.md` is independently checked mathematically, but not yet Lean-formalized.

### Companion status

The original private PaperLab is published at https://paperlab-length-expander-decompositions.greg-bodwin.chatgpt.site. Its current version contains the full source reading edition and initial corrections; it has not yet been refreshed with this checkpoint or the unscaled-maximality correction. JavaScript syntax and all 139 local anchor references passed. Browser visual QA is still unverified.

Shared toolchain/dependency directories are reused read-only. Local compiler work uses one thread and the shared serialization lock.
