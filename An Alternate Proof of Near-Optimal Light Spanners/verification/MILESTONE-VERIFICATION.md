# Verified milestone — 2026-10-09

Recovered the previously saved greedy/MST/unit-cycle milestone and added the
numerical heavy-edge subdivision estimates from Lemma 3.5. No graph-subdivision
construction, cycle correspondence, or final lightness theorem is claimed.

Pinned environment: Lean 4.34.0, mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

Checks completed successfully on the exact current proof sources:

- `lake build LightSpanners`: all 12 modules and aggregate; 1345 jobs.
- All-declarations audit: 181 declarations, only `propext`, `Classical.choice`,
  and `Quot.sound`; no project axioms or `sorryAx`.
- Selected axiom checks, including subdivision bounds: permitted axioms only.
- Repository import-index check: all four libraries report `No update necessary`.
- Independent `leanchecker -v` replay: exit code 0 for Basic, Construction,
  Counting, Distance, Girth, Greedy, Kruskal, MinimumTree, Subdivision,
  UnitCycle, UnitCycleWeight, and Weight.
- `git diff --check`: passed.

Earlier upload attempts were interrupted before publication. This recovery is
based on main `8d7295fd8d86b3d1be0881064ec56a03e840f659` and preserves all other
paper sources. The earlier runtime-reset limitation has now been resolved.

Reproduce from the repository root:

```sh
lake exe cache get
lake build LightSpanners
lake env lean "An Alternate Proof of Near-Optimal Light Spanners/verification/AllDeclarationsAudit.lean"
lake env lean "An Alternate Proof of Near-Optimal Light Spanners/verification/SelectedAxioms.lean"
bash scripts/CheckModuleIndex.sh
for module in Basic Construction Counting Distance Girth Greedy Kruskal MinimumTree Subdivision UnitCycle UnitCycleWeight Weight; do
  lake env leanchecker -v "LightSpanners.$module" || exit 1
done
```
