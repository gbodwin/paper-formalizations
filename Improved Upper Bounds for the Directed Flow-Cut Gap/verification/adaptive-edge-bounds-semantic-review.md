# Semantic review: final edge rounding estimates

Drafts reviewed 9 October 2026, 05:06–05:10 UTC; final frozen sources reconciled 05:17 UTC, against arXiv:2604.03412v3 and the separately reviewed frozen vertex estimates and concrete dyadic graph reduction.

**No mathematical or quantifier defect found in these two inspected final sources. Both strict compilation logs are empty, exhaustive owned-declaration axiom audits pass, and isolated official kernel replays pass.** No Lean source was edited and no compiler was run by the reviewer. This report concerns all-cost integral edge-cut rounding; it does not certify runtime, LP duality, or remote publication.

## Exact final source bytes

Paths are relative to `repo/Improved Upper Bounds for the Directed Flow-Cut Gap/DirectedFlowCutGap/`.

| File | SHA-256 |
| --- | --- |
| `EdgeRounding.lean` | `49399a26181c964163d1a56abb5ea94f6fdad11a8cc58cde45bbc558c9dc8de3` |
| `AdaptiveEdgeBound.lean` | `3a8bcf3305d7aa08570bd3048785a606094f2c907ac7971aa0f05ac8c63f2c0d` |

Both complete drafts were read and exact copies retained. The final bytes were independently hashed and their complete diffs inspected. EdgeRounding changed only coercion proof syntax and omitted unused typeclass assumptions; AdaptiveEdgeBound changed only two `letI` declarations to `let` for empty-type proof witnesses. The construction and substantive theorem statements are unchanged. The earlier reviewed hashes were `12b1b641d75da8d38b824eb5887b84a182383ae0eccb07a877642b2065635fa3` and `32e3421fd7687f5427fe2eaa9fe222a6e848ddbe1550f201a5867ee5dcdbd83f`. The separately reviewed final `AdaptiveVertexBound` hash is `379c29e78caa1ad57b8773fb4dec0763b1b8a7b21fcb16eb25e061f9b8edfbd4`, and final `EdgeToVertexReduction` hash is `1d7bd95d3aba569f18fbbcd2cff7a502c44b5cd0de19a1aabcc8b4abcd91caa3`. Those dependencies have their own local verification receipts; the new modules also have their own receipts, inspected below.

## Actual edges and all-cost interface

`HasEdgeRoundingFactor` quantifies over every nonnegative cost vector after the graph, fractional weights, and proposed nonnegative factor. Its output explicitly belongs to `graphEdges G`, is an integral cut for the actual edge-threshold demand relation, and satisfies the actual fractional edge objective bound. Thus arbitrary values assigned to ordered pairs that are not edges cannot create spurious fractional budget or selected nonedges.

`actualEdgeWeight` masks exactly those nonedges. The finite potential equality identifies the ambient ordered-pair sum with the graph-edge objective. The real-valued oracle converts an arbitrary componentwise nonnegative real cost vector into nonnegative reals and preserves both feasibility and objective. Zero-cost edges are included, and there is no strictly-positive-cost assumption or division by the fractional objective. This is a usable conditional rounding interface, rather than an assertion that an unspecified oracle solves the main theorem.

## Logarithmic gadget overhead and constants

The concrete gadget bound is retained as `gadgetSize n = 2n(log₂ n+4)`. The overhead is at least one, and its subpolynomial majorant uses `log(n+2)` with positive logarithm denominator `log 2`. For every fixed real exponent `a` and every positive slack `η`, `gadget_power_uniform` selects a positive constant before all positive integer sizes and proves

`gadgetSize(n)^a ≤ D n^(a+η)`.

The proof first bounds `overhead(n)^a` by `overhead(n)^ceil₊(a)` and applies the existing fixed-natural-power subpolynomial theorem. This step remains valid even if the auxiliary real exponent is negative, since the overhead is at least one and the natural ceiling dominates that exponent. The applications use positive exponents. Multiplication by `n^a` and addition of real exponents explicitly require and retain `n≥1`; no zero-base real-power identity is used in that branch.

The bounded size and mass oracles quantify over all actual finite graph instances with cardinality and mass at most their stated budgets. Their conclusions follow by ordinary monotonicity of real powers for nonnegative exponents. No monotonicity of an exact-parameter flow-cut-gap function is postulated.

## Final size and mass bounds

For the size estimate, the source first obtains the uniform vertex estimate with slack `ε/2`, before all graph instances, and then absorbs the logarithmic gadget overhead with a second `ε/2`. The dyadic reduction contributes its actual cost loss four and bounds `n′≤2n(log₂n+4)` and `W′≤4W`. Therefore the final size factor is

`4 C D n^(1/3+ε)`.

The mass estimate instead starts from the vertex factor `C n^(ε/2) sqrt(W)`. The same overhead absorption gives `n^ε`, while the actual gadget mass budget contributes the additional factor `sqrt(4)`. The resulting factor is

`4 C D sqrt(4) n^ε sqrt(W)`.

Both positive constants are selected before every finite type, graph, edge weight vector, and cost vector. The final statements return actual edge subsets, genuine threshold-demand cuts, and bounds on the original edge-cost objective. The intermediate vertex-oracle assumptions are discharged by the proved vertex estimates; no desired edge conclusion remains a premise. Empty vertex types are handled separately by the empty edge cut, and zero mass/objective cases are covered without division. The final `HasEdgeRoundingFactor` corollaries retain the all-cost quantifier order and do not fix one favorable cost vector.

These are the two mathematical edge-rounding estimates underlying the paper's main size and weight results (`tex/intro.tex:222–240`) after the concrete edge-to-vertex reduction (`tex/intro.tex:276–281`). A multiflow-gap statement additionally needs the separate rounding-to-distribution and flow-duality bridges. No polynomial-time implementation claim follows merely from the noncomputable existential code here.

## Independently inspected local verification

Both `edge-rounding-compile.log` and `adaptive-edge-bound-compile.log` are empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). The module audit drivers enumerate all owned declarations, reject an empty enumeration, and recursively permit only `propext`, `Classical.choice`, and `Quot.sound`. The logs report all 15 EdgeRounding declarations and all 19 AdaptiveEdgeBound declarations passed, including the final size and mass theorems and all-cost interfaces.

| Module | Axiom audit log SHA-256 | Official kernel replay log SHA-256 |
| --- | --- | --- |
| EdgeRounding | `8c9a5247f4249a6ca67ae90923be02800712765c8842c293294ab0b2474ba2cd` | `484b8091418c14c677219e8276564b75f697e1e687bb723fe16c263415b77610` |
| AdaptiveEdgeBound | `51c3df56904359eb8517b0bdfe07229c69a979174ddd8e969efecf04b47f793f` | `44715dd9aa8e570719a83e57d5ad85c89b0de1734c188544b18382762f1bce3c` |

The replay drivers invoke official `LeanChecker.replayFromImports` on their exact target modules before printing the corresponding PASS. Both result logs contain that PASS. This checks target declarations with the imported dependency environment; it is not a second independent verifier or a fresh rebuild of all dependencies in each isolated invocation.

These two modules are absent from the seventh checkpoint, so that manifest was not reused to certify them. Their final source hashes and individual receipts support the status above. A later aggregate source manifest should bind the enlarged dependency closure and root. No Git commit, remote push, or external CI result is claimed here.

## Eighth-checkpoint cross-check

At 05:34 UTC the full enlarged checkpoint completed. The reviewer independently matched all 53 source hashes, all 52 component imports plus root, all 53 unique official kernel-replay PASS targets, and the actual 2,854-declaration recursive allowed-axiom audit. The sources reviewed here are included and unchanged. See `eighth-independent-verification-review.md` for exact evidence hashes, fresh-build scope, count reconciliation, and local-versus-remote limitations.
