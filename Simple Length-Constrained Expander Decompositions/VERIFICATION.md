# Verification record

## Repaired union checkpoint — 10 October 2026

All **40 paper modules** compile with pinned Lean 4.34.0 (293d5d0c0c3f3dded4688b3ccd6a33939ac5102b) and mathlib 5ed2965256430c3649e86755f9576b54eca72435.

- **546 declarations** pass the all-declarations audit, allowing only `propext`, `Classical.choice`, and `Quot.sound`. See `verification/axiom-audit.log` and `Audit.lean`.
- All **40 modules** pass sequential independent kernel replay. The log contains the unchanged 38-module gate plus the final constant-bound and degree-union replays.
- `verification/source-hashes.json` pins every checked module; the root imports exactly this set.
- Exact-commit CI for this union checkpoint is **pending publication**. No union exact-CI success is claimed yet.
- The direct-decomposition checkpoint [f5ae64a0957a1f54c54f916f7a86a00222301733](https://github.com/gbodwin/paper-formalizations/commit/f5ae64a0957a1f54c54f916f7a86a00222301733) passed all stages of [exact CI 38061154976](https://github.com/gbodwin/paper-formalizations/actions/runs/38061154976), including build, module-index, allowed-axiom audit and independent kernel replay.
- The repaired matching-bridge checkpoint 9e696639dd68352984343ce7ac917b199c3ec4b9 passed [exact CI 38060122110](https://github.com/gbodwin/paper-formalizations/actions/runs/38060122110).
- The forest-partition checkpoint 6da8e4bbfeb388755dc4aaced3617de0f8b5188f passed [exact CI 38059239134](https://github.com/gbodwin/paper-formalizations/actions/runs/38059239134), completed 14:37:52 UTC.

### Newly proved union results

`LengthExpander.union_sparseCut_explicit` in `UnionBoundConstants.lean` proves the repaired Theorem 4.1 for any finite sequence of nonnegative cuts with positive total attained witness volume, arbitrary integral capacities and node weights, h ≥ 0, and **integer s ≥ 2**. The actual output cut is `(1+1/(s−1)) * totalCut Cs`. It is `(2h,(s−1)/2)`-sparse with parameter

**512s·|A|^(2/s) · (sum of cut costs)/(sum of attained witness volumes).**

The witness is constructed, integral, A-respecting, originally 2h-near and strictly h(s−1)-separated after the scaled union. A sparse orientation and incoming-neighbor pairing replace the source's rooted-forest construction. Pairing loses a factor two, projection has exactly 2A(u) copies, support-preserving integral extraction loses another factor two, and rescaling costs at most twice as much. The intermediate exact loss is 16(K+1), K=ceil(8s(2|A|)^(2/s)). All losses are explicit.

`LengthExpander.degree_sparseSequence_union` in `DegreeUnion.lean` proves Theorem 1.4's simplified form, for a **nonempty** sparse sequence with unit capacities and the original graph's degree weights, with explicit parameter **2048s·n^(4/s)·φ**. Nonemptiness supplies the positive denominator and positive output demand volume. Zero-volume inputs are not declared sparse using a totalized division convention.

### Certified decomposition results

`LengthExpander.exists_direct_decomposition` constructs the actual unscaled cut with explicit slack **8s·(2|A|)^(2/s)**. The auxiliary matching graph's exact edge count equals summed witness volume, so its density directly bounds total cost; finite maximality gives expansion. This proof does not use a union-sparsity premise.

`LengthExpander.exists_degree_decomposition` specializes to unit capacities and the original degree weighting, with cost **≤64s·n^(4/s)·φ·m**. Both results include zero/empty cases and h=0 or φ=0. Their exact checkpoint is certified above.

### Certified arboricity and dependency chain

Theorem 1.3 has an explicit density bound d≤8s·n^(2/s) and a constructed edge partition into ceil(8s·n^(2/s)) actual forests. No Nash–Williams oracle is used. Its checked chain includes actual matching permutations/hikers, exact traversal total 2|E|, short increasing simple paths, a constructed finite deletion blocker, medium counting, exact fixed-size sample incidence counting, hereditary density, and sparse elimination orders.

The matching bridge uses separate outgoing and incoming demand copies: exactly 2|A| vertices and |D| edges. Actual maximum cut witnesses supply support-disjoint stages, exact union edge count, sequential near/far geometry and reversed parallel greediness. Integral extraction is proved by bounded maximality and saturated-endpoint charging, without an integral transportation oracle.

### Independent review and remaining scope

Six hash-pinned semantic reports in `verification/` cover foundations/cuts/termination; hikers/path/deletion; sampling/density/forests/extraction; matching/sequence geometry; direct decompositions; and all thirteen new union modules. These source-level reviews are distinct from kernel replay and CI. The final union review checks mass, row/column capacities, support preservation, strict separation, constants, positive denominators, theorem scope and absence of circular assumptions.

The main result chains are complete in the stated finite simple graph and integer-s≥2 regime. **Full literal-source verification is not claimed.** Arbitrary-real-s scope remains unclaimed; the source's literal one-copy matching, fractional-as-integral demand, and arbitrary-arboricity-oracle constant 8α(|A|,s) are not silently adopted. The numerical scaled-maximality counterexample is independently checked mathematically; its graph-level Lean encoding remains pending. See `CORRECTIONS.md` and `STATEMENT_MAP.md` for these boundaries.

### Private companion

The existing [private PaperLab](https://paperlab-length-expander-decompositions.greg-bodwin.chatgpt.site) is deployed at source c9ec7454dd79c026e44ac84de0dd984593204b7f, deployment appgdep_6aca53d4261881919caa2734e63b67f5 (version 6). It preserves the full reading edition and corrections and accurately marks the 27-module decomposition checkpoint's exact CI as passed. Updating it with the union checkpoint is the next publication step.

JavaScript syntax, all 139 local anchor references, and repeated/back/reset hiker-control behavior passed. The complete HTML has 1848 unique IDs. Actual browser visual/accessibility QA remains unverified. Shared toolchain/dependency directories are reused read-only; local compiler work uses one thread and the shared serialization lock.
