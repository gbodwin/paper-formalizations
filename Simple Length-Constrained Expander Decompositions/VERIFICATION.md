# Verification record

## Repaired union and parameter-domain checkpoint — 10 October 2026

All **42 paper modules** compile with pinned Lean 4.34.0 (293d5d0c0c3f3dded4688b3ccd6a33939ac5102b) and mathlib 5ed2965256430c3649e86755f9576b54eca72435.

- **572 declarations** pass the all-declarations audit, allowing only `propext`, `Classical.choice`, and `Quot.sound`. See `verification/axiom-audit.log` and `Audit.lean`.
- All **42 modules** pass sequential independent kernel replay. The log contains the unchanged 38-module gate plus four added-module replays. The canonical module index also passes the actual mk_all --check tool.
- `verification/source-hashes.json` pins every checked module; the root imports exactly this set.
- Exact-commit CI for this corrected checkpoint is **pending publication**. The prior union checkpoint 8220c07643124bd8557972eee63dc1ab4320dcb5 compiled successfully but failed its module-index formatting check in run 38062420082; the audit and kernel steps were skipped. The final imports are now canonical and the actual local mk_all check passes. No union exact-CI success is claimed yet.
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

Seven hash-pinned semantic reports in `verification/` cover foundations/cuts/termination; hikers/path/deletion; sampling/density/forests/extraction; matching/sequence geometry; direct decompositions; all thirteen union modules; and the graph-level nonmonotonicity and real-parameter repair modules. These source-level reviews are distinct from kernel replay and CI. The final union review checks mass, row/column capacities, support preservation, strict separation, constants, positive denominators, theorem scope and absence of circular assumptions.

The main result chains are complete in the stated finite simple graph and integer-s≥2 regime. **Full literal-source verification is not claimed.** The exact real-s exponent is false without a domain restriction, as witnessed mathematically by K_{a,a} at s=5/2. The new RealParameterArboricity module proves the valid all-real rounded and smooth forest bounds; real-s cut-theorem extensions remain unclaimed; the source's literal one-copy matching, fractional-as-integral demand, and arbitrary-arboricity-oracle constant 8α(|A|,s) are not silently adopted. The graph-level nonmonotonicity obstruction is now kernel-checked in RescalingCounterexample: a capacity-100 edge expands at length 2/5 and not at 4/5, for h=1,s=2,φ=35 and unit budgets. The larger two-edge maximal-sequence example remains independently checked mathematically. See `CORRECTIONS.md` and `STATEMENT_MAP.md` for these boundaries.

### Private companion

The existing [private PaperLab](https://paperlab-length-expander-decompositions.greg-bodwin.chatgpt.site) is deployed at source 95e5c67b1c0882c627373ff83731415648bce266, deployment appgdep_6aca5717710881918fcf0741107309fd (version 8). It preserves the full reading edition, the 40-module union milestone, and the newly explicit real-s source correction. Its union CI indicator will be updated to the corrected exact commit after publication.

JavaScript syntax, all 139 local anchor references, and repeated/back/reset hiker-control behavior passed. The complete HTML has 1848 unique IDs. Actual browser visual/accessibility QA remains unverified. Shared toolchain/dependency directories are reused read-only; local compiler work uses one thread and the shared serialization lock.

### Real-parameter repair

`real_parallelGreedy_iff_floor` proves exact equivalence between the literal real-threshold predicate and the natural floor threshold. `real_parallelGreedy_forest_partition` constructs an actual forest partition with K=ceil(8 floor(s) n^(2/floor(s))) and proves K≤ceil(8s n^(4/s)), including n=0. This is a valid repaired all-real theorem, not the exact printed 2/s exponent.
