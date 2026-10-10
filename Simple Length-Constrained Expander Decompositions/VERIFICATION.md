# Verification record

## Direct decomposition checkpoint — 10 October 2026

All **27 paper modules** compiled with pinned Lean 4.34.0 (293d5d0c0c3f3dded4688b3ccd6a33939ac5102b) and mathlib 5ed2965256430c3649e86755f9576b54eca72435.

- **432 declarations** pass the all-declarations audit, allowing only `propext`, `Classical.choice`, and `Quot.sound`. See `verification/axiom-audit.log` and `Audit.lean`.
- All **27 modules** pass sequential independent kernel replay. The log contains the unchanged 26-module gate and the final added degree-specialization replay.
- `verification/source-hashes.json` pins every checked source; the root import includes exactly these modules. Unpublished dispersion drafts are excluded.
- Exact-commit CI for this new checkpoint is **pending publication**. The preceding matching-bridge checkpoint 9e696639dd68352984343ce7ac917b199c3ec4b9 has passed build, module-index, and declaration-audit checks in [run 38060122110](https://github.com/gbodwin/paper-formalizations/actions/runs/38060122110); kernel replay is running as of 14:47 UTC.
- The forest-partition checkpoint [6da8e4bbfeb388755dc4aaced3617de0f8b5188f](https://github.com/gbodwin/paper-formalizations/commit/6da8e4bbfeb388755dc4aaced3617de0f8b5188f) passed every stage of [exact CI 38059239134](https://github.com/gbodwin/paper-formalizations/actions/runs/38059239134), completed 14:37:52 UTC. Together with its independent semantic review, this certifies Theorem 1.3 in the finite simple graph, integer s ≥ 2 regime.

### Newly proved decomposition results

`LengthExpander.exists_direct_decomposition` in `DirectDecomposition.lean` constructs the actual unscaled cut for arbitrary finite simple graphs, integral capacities and node weights, h ≥ 0, φ ≥ 0, and **integer s ≥ 2**. Its explicit cut slack is

**8s·(2|A|)^(2/s).**

The proof avoids the still-open union-sparsity theorem. The repaired auxiliary matching graph has exactly the sum of the maximum witness volumes as its edge count. Its density bound therefore bounds total witness volume directly. Sparsity gives total cut cost ≤ φ times that sum; finite maximality supplies expansion for the unscaled total cut. No `unionBound`, dispersion, fractional feasibility, or rounding result is an input to this theorem.

`LengthExpander.exists_degree_decomposition` in `DegreeDecomposition.lean` specializes to unit capacities and the original graph's degree node weighting. The degree-sum identity gives |A|=2m, and m≤n² yields the explicit Theorem 1.2-style bound

**cut cost ≤ 64s·n^(4/s)·φ·m.**

Both results retain zero/empty cases and do not divide by m or |A|. They have passed compilation, all-declaration audit, kernel replay, and a separate hash-pinned independent semantic review. Exact-checkpoint CI remains pending. Arbitrary real-valued s is not claimed by these natural-parameter theorems.

### Checked dependency chain

- Actual ordered matching labels, short-cycle exclusion, unique short increasing walks, and n² dispersion.
- Genuine matching permutations/hikers with exact total traversal 2|E|; conversion of short walks to mathlib simple paths.
- Constructed finite deletion blockers, medium counting, and exact fixed-size sample incidence counting with explicit subgraph-walk transfer.
- Uniform average degree d ≤ 8s·n^(2/s), hereditary restriction, sparse elimination orders, and a constructed edge partition into ceil(8s·n^(2/s)) actual forests. No Nash–Williams oracle is used.
- Separate outgoing/incoming demand copies: exactly 2|A| vertices and |D| edges. Actual sparse-cut maximum witnesses supply support-disjoint stages, exact union edge counts, sequential near/far geometry, and reverse-order parallel greediness.
- A support-preserving factor-two integral extraction theorem, proved by maximality and saturated-endpoint charging. It remains available for the separate union proof; the new decomposition proof does not use it.

### Review scope and remaining obligations

Five hash-pinned semantic reports in `verification/` cover the foundational cut/termination modules; hikers/path/deletion; sampling/density/elimination/forest/extraction; the five matching/sequence modules; and the two final decomposition modules. These source-level reviews are separate from the kernel and CI gates.

The **union-sparsity theorem (Theorems 4.1/1.4 and Appendix A's dispersion argument) remains incomplete**. The unpublished dispersion construction, budgets, size and separated-witness bridge still need integration. The arbitrary-real-s extension also remains open. Full-paper completion is therefore not claimed. The original conditional reduction is retained as an earlier component; the new direct theorem has no such remaining premise. The numerical scaled-maximality counterexample is independently checked mathematically, while its full graph-level Lean encoding remains pending.

### Private companion

The existing [private PaperLab](https://paperlab-length-expander-decompositions.greg-bodwin.chatgpt.site) is deployed at source 04e848a3f1c3bed8724e215f65a46b10d8f93607, deployment appgdep_6aca4ac163d4819190f0787ddc8f7920. It preserves the full reading edition and corrections, and currently describes the preceding 298-declaration forest checkpoint. Refreshing it with the direct decomposition results is pending.

JavaScript syntax, all 139 local anchors, and repeated/back/reset hiker-control behavior passed. Actual browser visual/accessibility QA remains unverified. Shared toolchain/dependency directories are reused read-only; local compiler work uses one thread and the shared serialization lock.
