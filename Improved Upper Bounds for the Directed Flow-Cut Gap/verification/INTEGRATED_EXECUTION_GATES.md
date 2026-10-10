# Exact-source execution gates for the 251-component candidate

The verified partial baseline remains 193 components at 7d242865. This candidate must pass its own complete build, strict compilation, exhaustive axiom audit, every runtime suite and all-module kernel replay before promotion. It remains an unfinished paper formalization.

Three additional runtime suites passed on separate diagnostic commits before integration:

- GraphExecution: 5 groups, commit `ad83144c7b1b36d8feeefd49dca738cfd2ea1312`, [CI 38062277843](https://github.com/gbodwin/paper-formalizations/actions/runs/38062277843). Exact fixture SHA-256 `665cfe0d3c329f7ff13ce2f9aff2727b7bf34ad80192ab53fd52d1031a416717`.
- WeightedTape: 4 groups, commit `7f31dbef28ef7efa3e94ccf00c33a725137e1325`, [CI 38064436701](https://github.com/gbodwin/paper-formalizations/actions/runs/38064436701). Exact fixture SHA-256 `b24364d5d71ab2ede94d0ab7bb1dabff02617d700678903388b664d074a43ec6`.
- ZeroSafePacking: 3 groups, commit `47e045d1bbd2f20150d1ec1bfce18d42671ee88b`, [CI 38064134272](https://github.com/gbodwin/paper-formalizations/actions/runs/38064134272). Exact fixture SHA-256 `65dc0e466fb03bb2f216d9f61ffb32d2a1e0895049f663afb6ccf547f0f6df6e`.

All fixture assertions and output parsers are preserved in this integration. Graph tests exercise malformed guards, padded labels, shortcut reachability, survivors and port materialization. Weighted/tape tests exercise all seven tickets of a 3:4 distribution, bounded rejection/defaults, bit effects and accumulated ledgers. Zero-safe tests exercise support fallback, an original-capacity bottleneck, exact physical metadata, a cached startup provider call and the final weighted draw.

These are finite regressions on the actual Lean bodies. The zero-safe provider is a deliberately simple absent-cut provider over nonempty finite subsets; it does not instantiate the full graph-cut provider. The statements use local instrumented Boolean/list/native-slot charges. The original graph provider quality join, initial encoded representation, immutable-frame/movement substitution, physical allocator/transient storage and final whole-paper runtime remain separate obligations.

The 58 additions also passed source-level semantic review in two cohorts. The six proof-repaired modules preserve all public assumptions and conclusions and every computational definition. A private PMF helper was corrected to use the common universe required by its Monad instance. Source review does not replace the exact-commit compiler, axiom, kernel or execution gates.
