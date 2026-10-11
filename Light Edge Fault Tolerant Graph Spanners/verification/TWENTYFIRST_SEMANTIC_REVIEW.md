# Actual refinement rigidity and maximality contradiction: semantic review

Verdict: PASS for the bounded six-module component, 2026-10-11 16:00 UTC.
Reviewer: distance-preserver owner, reciprocal read-only review. No compiler or child was used by this reviewer. The owner's strict builds, full declaration audit and six official kernel replays are separate evidence.

## Exact source binding

All six production sources were read completely and independently SHA-256 checked:

- NativePriorityComparison: 0964c252c39a413963679290576f90f86aba7e04cf69b2cdf7f6a37774890996
- NativeSignatureStages: 4e1b930c85cd971a5c3d2246d188916153383478505969485b741a40dcb3a3e0
- NativeRefinementRigidity: e32010cf62452911ee8376f81670d8eb3116de6a51c3f2d2b2a47b7e3db5f81e
- NativeExchangeImprovement: 2a4af48856d5abaf18044b08c0a33c92477611a52ea2a5518871f03f202b7ab1
- NativeImprovingExchange: 12a7a3b8c7ba84724ae1a9c376dc9475adbff1b88b3346441e97178cf33aa436
- NativeMaximalCountercase: b3e919dd1c0f64fc355f85a0c0f399680984d9e24956e832f64e41e2925a4612

All 107 frozen root/module SHA-256 entries were checked. All 100 prior mathematical source bytes have the exact Git blob hashes of parent 964b388d3bfbaf970fe3a4a01475524ff3e04951. The preserved source comparison is recorded in twentyfirst-review-preservation.json. This is a bounded semantic inspection of the new proof and its dependency contracts, not a fresh whole-library audit.

## Mathematical checks

1. Within-block route preservation genuinely coarsens the old component relation. Since each component relation refines the given partition, a previously nonsplitting color cannot become splitting. Set inclusion gives the correct monotonic direction for the minimum priority. The no-split sentinel is the number of colors, strictly larger than every actual color value; empty-color and no-split branches are handled explicitly.
2. The signature is built from the actual iterated refinement and actual least splitting color. Strict pair-count ranking is applied only after partition comparability is established. No claim equates arbitrary partitions from equal cardinalities.
3. Strong induction derives equality of the recomputed partitions and priorities from non-improvement plus preservation of the old within-stage colored connections. Earlier stages provide an actual equal signature prefix; any strict comparable coarsening or priority increase contradicts maximality. The selected-color result uses m<N so that the required next stage m+1 is inside the same finite horizon.
4. The strict selected coarsening has an actual inserted original edge witnessing new reachability between old distinct components. The swap preserves each old stage through the two genuine replacement routes and the exact next-stage edge boundaries. No assumption identifies the competitor's new refinement prefix with the old one.
5. The earlier color class is a finite set of actual original edge identities. Restriction equality is proved before tree properties are transported. The lower-level exchange constructs d rather than accepting it as a witness. The old last-color e-deleted route avoids both changed identities for the required reason, and the changed native tree supplies the replacement d-route at its actual lower level. All other earlier native trees retain exactly their prior original-edge subgraphs. Parallel identities are not merged by the colored-edge accounting.
6. The final countercase starts from the actual TreePartitionCriterion, k earlier native trees and two actual vertices disconnected in the last color. Its cycle witness supplies e, the finite level, the deleted-edge route and N<=|V|^2. The least splitting color is proved earlier, and the strict comparison is lifted to the common |V|^2 horizon using m<N. The result constructs an admissible competitor with a larger actual signature. The maximum contradiction therefore yields pairwise last-color reachability, including the correct vacuous behavior for an empty vertex domain; it does not assert nonempty connectedness there.

## Scope and exclusions

No mathematical blocker, added conclusion premise or new source correction was found. The explicit earlier-tree seed remains an inductive input. Constructing the full sequence of such seeds, extracting a last-color spanning tree and assembling the final packing family remain separate obligations. This packet does not by itself establish the general tree-packing theorem, Mader splitting, Steiner expansion, or the complete EFT lightness/runtime conclusions. The separately proved finite maximum existence has the expected explicit seed contract; this review does not silently join it into an unproved full packing induction.
