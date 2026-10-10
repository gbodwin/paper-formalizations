# Verified continuation — 2026-10-10

Base: `7bacf7871a0dddd88d72e1ab50a219967e9464f4`.
The first recovered progress checkpoint is `4586315682b50b614254127ab13cc5e59bc484c7`.
Pins unchanged: Lean 4.34.0 and mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

## Proven scope

- `exists_nontree_cycle_edge_ge` and `exists_nontree_cycle_max`: every cycle has a maximum-weight edge outside a bottleneck tree, including equal-weight ties.
- `subdivideEdge` and `subdivideWeight`: actual one-edge subdivision on `Option V` with weights on unordered edges.
- `exists_subdivision_lift`: every old walk lifts with unchanged weight.
- `exists_subdivision_contraction`: walks between old vertices contract without increased weight when both replacement weights are nonnegative.
- `subdivision_distance_eq`: equality of infimum-based weighted distances, including zero replacement weights and disconnected vertex pairs.
- `subdivideEdge_connected` and `subdivideWeight_positive_edges`: connectedness and positive edge weights are preserved under the stated assumptions.
- `exists_subdivision_old_walk`: a walk avoiding the inserted vertex is exactly an embedded walk in the original graph with the subdivided edge removed.
- `subdivision_cycle_contract`: every simple cycle in the subdivision contracts to an actual original simple cycle of exactly the same total weight. Cycles through the inserted degree-two vertex and cycles avoiding it are handled separately; rotation handles arbitrary starting vertices.

The historical task reported later unpublished one-edge proofs, but no source artifact for that work was recoverable. These prerequisites were reconstructed on the retained repository checkpoint, and cycle contraction was then added. No missing source is presumed verified.

## Checks on this exact proof source

- `lake build LightSpanners`: passed, 15 source modules plus aggregate, 1348 jobs.
- Project all-declarations audit: passed, 213 declarations, including generated/private declarations; only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
- Expanded selected-declaration axiom audit: passed.
- Independent `leanchecker -v` replay: passed for all 15 modules sequentially.
- Source import-index equality: all 15 module files match the 15 aggregate imports.
- `git diff --check`: passed.

The logs prefixed `continuation-2026-10-10-` in this directory record these checks. No `sorry`, project axiom, or assumed substitute for cycle correspondence was introduced.

The repository-wide default build, root `CheckModuleIndex.sh`, and root `AxiomAudit.lean` were not rerun locally for unrelated paper libraries. Branch GitHub Actions runs the repository-wide gate separately; a remote CI result must be checked for the exact published commit before claiming that gate passed.

## Remaining paper scope

The formalized cycle direction is subdivision-to-original contraction, not yet a full bijection of cycles or a weighted-girth preservation theorem. Inverse cycle lifting, maximum-edge transfer, repeated heavy-MST-edge subdivision, tree/minimum-total-weight transfer, and the Euler-tour vertex-copy graph construction remain open. Bucket-safe walk dispersion, the hiker counting protocol, independent edge sampling, and the final lightness theorem also remain open. The paper is not fully verified.

## Reproduce

```sh
lake exe cache get
lake build LightSpanners
lake env lean 'An Alternate Proof of Near-Optimal Light Spanners/verification/AllDeclarationsAudit.lean'
lake env lean 'An Alternate Proof of Near-Optimal Light Spanners/verification/SelectedAxioms.lean'
for source in 'An Alternate Proof of Near-Optimal Light Spanners'/LightSpanners/*.lean; do
  lake env leanchecker -v "LightSpanners.$(basename "$source" .lean)" || exit 1
done
```
