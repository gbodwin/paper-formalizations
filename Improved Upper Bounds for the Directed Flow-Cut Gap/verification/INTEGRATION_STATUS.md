# UNVERIFIED 251-component integration

Recovered source snapshot: 2026-10-10T11:19:02.476639+00:00.
Fresh diagnostic prepared: 2026-10-10.
Current source inventory SHA-256: `f9c44c804d50a6a7316bc613f0e12bb88cfbfd0859abf2d2cdee1c5724d27f92`.
The original recovered inventory SHA-256 was `d97d8c7713c7be345595abff195aef75aaa940bb9ceb1497779a381e6c4336a7`.

All 193 parent component sources are preserved; 58 components are added.
The exact aggregate has not passed a build, axiom audit, kernel replay or runtime
regression. Existing regressions are retained, and the exact eight-body
finite-data/binary-graph driver required by the 193-component candidate is now
integrated using the seven assertion-preserving elaboration repairs from commit 7d242865.
The 193-source CI passed those eight bodies; execution on this 251-source aggregate is PENDING. Twelve new graph, weighted/tape and zero-safe packing fixture groups passed on separate source-bound diagnostic branches and are now included in this aggregate workflow. Full exact-commit CI and the
remaining source-specific execution and semantic gates are required.
The verified partial baseline is now 193 components at 7d242865, with full CI 38054205285 and independent source reviews passed. This candidate
does not finish the paper.

## Fresh elaboration repairs, 2026-10-10

The exact recovered 251-source build failed at nine sites in BinaryRetainedTape, EncodedRoundingEntry, and BinaryWeightedPackingConfidence (CI 38061661077). This successor repairs monadic map elaboration, explicit state/distribution rewrites, a unit-row sum proof, and two parser-sensitive field projections. All declaration signatures and computational definitions are preserved. The 193 inherited components remain byte-for-byte unchanged. The modified 251-source snapshot is UNVERIFIED until its own complete gates pass; it is no longer the untouched recovered draft.

A follow-up replaces three ambiguous reverse bind-map rewrites with explicit theorem applications after targeted CI 38063266300. Only proof elaboration changes; the same assumptions and computational bodies remain.

CI 38063196227 then compiled the repaired EncodedRoundingEntry and BinaryWeightedPackingConfidence, exposing downstream EncodedRoundingRepetition elaboration issues. Its private PMF monad helper now uses the required shared universe; two support/length proofs are repaired. All public theorem statements and computational definitions remain unchanged.

CI 38064361619 compiled BinaryRetainedTape, its cost companion and EncodedRoundingRepetition. Two downstream modules required proof-only repairs: remove no-progress dsimp tactics in BinaryRetainedRoundingCost, unfold the retained totals let in EncodedWeightedVertexQuery’s erased operations certificate, and raise its one large proof’s heartbeat budget. No public theorem premise or conclusion changes, and no executed data field changes. The twelve new fixture groups are now integrated with the inherited eight-body suite; all gates must pass on this exact successor.

The latest aggregate build (38065479595) reached the last two component proofs. This successor removes two unreachable StateT tactic tails, removes a strict-linter no-op change in EncodedRoundingEntry, and narrows the large Ready.operations_bound polynomial solver to six relevant inequalities with a local recursion budget. These are proof-only edits with exactly unchanged public premises, conclusions and executable data fields. All aggregate gates remain required.

CI38066509358 compiled BinaryRetainedRoundingCost and reached downstream BinaryRetainedEntryCost. This successor explicitly types its four PMF-bind support projections and aligns the weighted-query arithmetic hypotheses with their definitionally identical scalar aliases. Both proof patterns were strictly compiled locally. No public theorem assumptions, conclusions or executable definitions change. All exact aggregate gates remain required.

CI38067940684 compiled the weighted query and all prior repairs, leaving two proof-side alias/projection failures in BinaryRetainedEntryCost. This successor unfolds the named local aliases and applies the existing ledger draw equation and bound directly. No public theorem assumptions, conclusions or executable definitions change. Exact aggregate gates remain required.

CI38069086794 resolved the ledger draw projection, leaving one definitionally equal support-type mismatch in BinaryRetainedEntryCost. This repair explicitly unfolds StateT.run. Public statements and executable fields remain unchanged. Aggregate acceptance still requires all exact-source gates.

CI38070243240 compiled BinaryRetainedEntryCost and reached the final downstream BinaryRetainedPathwiseCost. Fifteen support-transport helpers declared but did not include the necessary primitive support premise hbit. This repair explicitly includes it, changing those helpers' elaborated signatures to the intended conditional statements. The final pathwise_bound and finite_source_support theorem statements are unchanged and supply the premise using proved Boolean full support. No executable definition changes. Rejection-let exposure and all-regime branch discharge are also repaired. This assumption activation is recorded separately from prior proof-only fixes; aggregate CI and bounded semantic recheck remain required.
CI38071560152 accepted the restored support hypothesis and reached a single deterministic heartbeat timeout in allRegime_support. This successor replaces generic branch search with the three explicit source guards and allows a local elaboration budget. The v9 helper signatures and final public statements are unchanged. Stale summary metadata is also corrected to explicitly report the fifteen helper-premise changes, matching the existing detailed record and independent exact-source review. All exact aggregate gates, including signature output, remain required.
