# Independent review of the eighth local checkpoint

Checked 9 October 2026, 05:34 UTC. **Exact source and replay coverage reconcile: 52 component modules plus root, all 53 current hashes unchanged, 2,854 declarations audited, and 53 distinct official kernel-replay PASS targets.** No compiler was run and no Lean source was edited by this reviewer.

All 53 source hashes were independently recomputed and match `eighth-prebuild-source-manifest.json`. The exact module set derived from those paths equals the replay driver's module set and the 53 distinct completed PASS names, without omissions, extras, or duplicates. The root imports precisely the 52 listed component modules.

`verify-eighth.sh` uses `set -euo pipefail`, freshly recompiles the eleven added modules with `-j1 -DautoImplicit=false -DwarningAsError=true`, rebuilds the root, runs the full owned-project recursive allowed-axiom audit, replays every target through official LeanChecker, and compares the source hashes afterward. All eleven fresh compile logs and the aggregate root compile log are empty. The coordinator reported runner exit zero; the independently inspected completed results agree.

The new modules are EdgeRounding, AdaptiveEdgeBound, EdgeFlow, CandidateGridRounding, CandidatePotentialSoundness, CandidateGridOptimizer, FiniteHarmonicThreshold, SparsestVertexBridge, SparsestVertexCorollary, SparsestEdgeBridge, and SparsestEdgeCorollary. Their exact final-source semantic reports are `adaptive-edge-bounds-semantic-review.md`, `edge-flow-semantic-review.md`, `candidate-grid-semantic-review.md`, and `normalized-sparsest-semantic-review.md`; these filenames retain their initial historical `draft` suffix while their contents record final frozen verified status.

| Evidence | SHA-256 |
| --- | --- |
| `eighth-prebuild-source-manifest.json` | `e1aac987444643ed91e7a442dc616f91acf056e356199c74b3cf76b617a85a3b` |
| `verify-eighth.sh` | `f8a48b1f8bae9ec643feb62ff73caf192d933f0ef10e31a396fa568976a3e4b1` |
| `AxiomAudit.lean` | `759fc1e2029222969cb7a5a243c2a159d64c8f12c767dc1c277e97e9878555cb` |
| `KernelReplay.lean` | `305c99ef8ae1de7808af5a0206b2c4187cc9e183e930a46957ab1f6526f15e53` |
| `axiom-audit.log` | `e4bc093f456338f79dd92029b57828daadddee56a7f7dec9ee5c149b7caedd73` |
| `kernel-replay.log` | `56826e15eb258ae1513ced8db24931543f0182581a8d0d29c6bea035d9064fb9` |

The aggregate axiom driver checks every declaration owned by an imported `DirectedFlowCutGap` module, rejects an empty enumeration, and recursively permits only `propext`, `Classical.choice`, and `Quot.sound`. Its actual measured count is **2,854**. Naively adding historical standalone counts to the previous 2,574 gives 2,855. The completed ownership diagnostic localizes the entire one-count difference to CandidatePotentialSoundness: it owns 11 declarations in the fresh aggregate versus 12 in its earlier standalone count; all ten other addition counts match. The old standalone log printed only a count, so the exact differing generated name and ownership mechanism are not established by the retained evidence. No particular duplicate name is asserted. All seven explicitly named source definitions/theorems in CandidatePotentialSoundness are present in the fresh ownership list; its exact source is unchanged and official replay passes. The fresh exhaustive aggregate audit is authoritative, rather than a sum of historical standalone counts.

This checkpoint freshly rebuilds the eleven additions and root, not every earlier source from scratch. All earlier component source hashes remain bound by the current manifest and their earlier build evidence. Official `replayFromImports` replays each target with its imported dependency environment; it is not a second independent verifier, runtime certificate, or remote CI check.

The checkpoint excludes the subsequent weak-decomposition, attained-optimum, and integral-network-flow/augmentation drafts. Their semantic draft reviews remain distinct. Normalized sparsest statements are per-assignment edge/vertex rounding contracts with explicit `W_avg=|P|W/S` (or raw W under `S=|P|`), not an unqualified attribution of the source's unstated Corollary 7 normalization. Finite-grid optimization is exact finite existence and integrality, with polynomial implementation still open. No Git commit or remote publication is asserted by this receipt.

## Ownership diagnostic receipt

`eighth-source-ownership.log` contains exactly 2,854 OWNED records with 2,854 distinct complete declaration names and a matching TOTAL line. Parsing preserves quoted private names containing spaces. Its SHA-256 is `a21096a9acd43e373650a64426bed39524cc3d72c9f368974258072c856349a7`. The diagnostic introduces no proof source changes and supplies ownership/count evidence, not an additional semantic premise. The historical one-count difference is scoped above; the retained logs do not support a more specific generated-name attribution.
