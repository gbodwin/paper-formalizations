# Continuation checkpoint — 2026-10-10

Base: `7bacf7871a0dddd88d72e1ab50a219967e9464f4`.
Pins unchanged: Lean 4.34.0 and mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

## Proven scope

- `exists_nontree_cycle_edge_ge` and `exists_nontree_cycle_max`: the cycle maximum can be selected outside a bottleneck tree, with ties permitted.
- Explicit subdivision graph on `Option V` and an unordered-edge weight function.
- `exists_subdivision_lift`: all original walks lift with unchanged weight.
- `exists_subdivision_contraction`: subdivision walks between old vertices contract without increasing weight when both replacement weights are nonnegative.
- `subdivision_distance_eq`: equality of the actual infimum-based weighted distances, including zero replacement weights and disconnected vertex pairs.

The historical task reported later unpublished one-edge proofs, but no source artifact for that work was recoverable. The present modules reconstruct these prerequisites on the retained repository checkpoint. No unpublished source is presumed verified here.

## Checks actually completed

- `lake build +LightSpanners.TreeCycle`: passed.
- `lake build +LightSpanners.EdgeSubdivision`: passed (only deprecated-tactic warnings).
- No `sorry`, project axiom, or assumed cycle-correspondence statement is introduced.

Expanded aggregate compilation, all-declarations axiom audit, import-index check, independent kernel replay, and repository CI are pending for this continuation. Do not interpret the preceding local compilation as those additional checks.

## Remaining

Simple-cycle correspondence, weighted-girth transfer through repeated subdivision, the unit-spanning-cycle graph construction, bucket-path dispersion and counting, independent sampling, and the final lightness theorem remain open. This is a progress checkpoint, not verification of the complete paper.
