# Integrated +6 exact-source CI gate

Independent review of source `c189a4e93786b47c7dbc23146c6b44a5b9cc75dc` and evidence `bcaffe932463ff6c13b94643b5b9146d94b3b9ea` passed, as reported by the parent. This records source/log/hash reconciliation, not independent execution. The reviewer is idle.

This gate checks out **c189a4e93786b47c7dbc23146c6b44a5b9cc75dc** into a clean `source/` directory. The old conditional-source pin is not used for integration evidence. The old reviewed diagnostics remain the inherited warning baseline, which is appropriate because their source files are unchanged.

One push-only job on `integration/conditional-plus6-ci-20261015`; no matrix; shared single-worker concurrency group. A repository-wide fail-closed preflight rejects other queued/in-progress/waiting/pending/requested runs and existing runner compiler/checker processes. The general Lean workflow excludes this branch, and the older paper workflow listens on another branch. No website or security settings change.

The official Lean 4.34.0 release archive SHA256 is enforced as `caaa98356098c85dc0fcbbd28e1ec66f39eb6551829972b752ff20e1286b646b`; the version must identify commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. The immutable manifest hash and all nine package revisions are checked; mathlib must be `5ed2965256430c3649e86755f9576b54eca72435`. The official cache program is bootstrapped sequentially and used normally. No Lake parallel build scheduler or runtime shim is used.

Inventory is computed directly from source imports: **36 library modules + 2 already-imported support leaves = 38 individual replay targets**, plus one aggregate = **39 compilations**. Audit scripts are separate verification entry points, not the two additional leaves. The 23 inherited modules must reproduce the exact 36-warning baseline after path normalization; all 15 +6/subset/integration modules and the aggregate use warning-as-error. All compiler/checker calls are awaited sequentially. The combined audit requires 373 roots, 19,646 recursively traversed constants, 14 opaque bodies, and only `propext`, `Classical.choice`, `Quot.sound`.

The artifact preserves source/trigger identity, all tracked source hashes, source-derived inventory, exact commands, raw diagnostics, failures, object hashes, warning classification, audit rows, archive digest, resource/process diagnostics, and evidence SHA256 manifest. Audit-generated files are copied to the artifact and removed from the clean source checkout before the final unchanged-source check.

Preparation uses static checks only; no local Lean compiler or checker is started. The initial shell API read returned HTTP 403. The authorized GitHub connector successfully reported zero active/queued/waiting/pending/requested runs; that connector is used for subsequent monitoring. An initial read of a nonexistent remote-tracking ref failed after fetch; the branch is available through FETCH_HEAD/local integration branch and remote state is checked with ls-remote. These are access/ref diagnostics, not proof failures.

See [remaining scope](REMAINING_SCOPE.md). The run succeeded on its first attempt; see [OUTCOME.md](OUTCOME.md) for exact identities and the artifact download limitation. No whole-paper completion claim.
