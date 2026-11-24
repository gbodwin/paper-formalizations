import DirectedFlowCutGap.MeasuredBudgetGridBounds
import DirectedFlowCutGap.MeasuredGraphPlanTotals
import DirectedFlowCutGap.MeasuredBudgetCandidateLists

/-! Build both original grid lists from the graph prices, with the measured
price reductions and geometric grid arithmetic. -/
namespace DirectedFlowCutGap.MeasuredGraphBudgetGrid

open scoped BigOperators NNRat
open BinaryFractionalWalkOracle (Adjacency)
open BinaryRational (StoredBounded)
open ConcurrentEdgeOracle (Edge Resource resource)
open ConcurrentEdgeCoverWidths (MatrixFits)
open FractionalCoverRawCore (RawRow get rational decodeRow)
open MeasuredBudgetGridBounds (floor ceiling capacity floorWork ceilingWork capacityWork)
open MeasuredDoublingBudgetGrid (grid gridWork grid_value grid_charge)
open MeasuredGraphPlanTotals (arcValues arcValues_bounds)
open RationalEdgeThresholds (Weights)
open RawNonnegativeRational (Code)

variable {n : ℕ}

def decode (q : Code × Code) : ℚ≥0 × ℚ≥0 := (q.1.value,q.2.value)

def pairs (lo hi limit : Code) : List (Code × Code) × ℕ :=
  let fees := grid lo hi
  let masses := grid Code.one limit
  (fees.1.flatMap (fun q => masses.1.map (fun u => (q,u))),fees.2+masses.2)

theorem pairs_value (lo hi limit : Code) :
    (pairs lo hi limit).1.map decode =
      (ConcurrentEdgeBudgetGrid.grid lo.value hi.value).flatMap fun q =>
        (ConcurrentEdgeBudgetGrid.grid 1 limit.value).map fun u => (q,u) := by
  simp only [pairs,← Code.value_one,← grid_value,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def,decode]

theorem pairs_charge (lo hi limit : Code) {L H M : ℕ} (low : lo.Bounded L) (high : hi.Bounded H)
    (mass : limit.Bounded M) : (pairs lo hi limit).2 ≤ gridWork L H+gridWork 0 M :=
  Nat.add_le_add (grid_charge lo hi low high) (grid_charge Code.one limit Code.bounded_one mass)

attribute [local irreducible] grid in
theorem pair_fields (lo hi limit : Code) {L H M : ℕ} (low : lo.Bounded L) (high : hi.Bounded H)
    (mass : limit.Bounded M) {pair : Code × Code} (present : pair ∈ (pairs lo hi limit).1) :
    pair.1.Bounded (2*L+H+2) ∧ pair.2.Bounded (M+2) := by
  dsimp only [pairs] at present
  obtain ⟨f,fee,inside⟩ := List.mem_flatMap.mp present
  obtain ⟨u,volume,rfl⟩ := List.mem_map.mp inside
  exact ⟨MeasuredDoublingBudgetGrid.grid_field lo hi low high fee,
    by simpa only [Nat.mul_zero,Nat.zero_add] using
      MeasuredDoublingBudgetGrid.grid_field Code.one limit Code.bounded_one mass volume⟩

private def all {n : ℕ} : Adjacency n := Vector.replicate n (Vector.replicate n true)

private theorem arcValue (A : Adjacency n) (c : Weights n) (e : Edge n) :
    (FractionalCoverRawCore.get (arcValues A c).1 (resource e)).value = RationalEdgeDecomposition.originalWeight A c e := by
  apply Subtype.ext
  change rational (FractionalCoverRawCore.get (arcValues A c).1 (resource e)) =
    (RationalEdgeDecomposition.originalWeight A c e : ℚ)
  rw [← FractionalCoverRawCore.decode_value, MeasuredGraphPlanTotals.arcValues_value]

private theorem allValue (c : Weights n) (e : Edge n) :
    (FractionalCoverRawCore.get (arcValues all c).1 (resource e)).value = ConcurrentEdgeZeroPrices.rawPrice c e := by
  rw [arcValue]
  simp only [RationalEdgeDecomposition.originalWeight,all,Vector.getElem_replicate,ite_true]
  rfl

theorem edgeFloor_value (c : Weights n) :
    (floor (arcValues all c).1).1.value = ConcurrentEdgeCappedPrices.floorPrice c := by
  rw [MeasuredBudgetGridBounds.floor_value,
    ← (finProdFinEquiv : Edge n ≃ Resource n).prod_comp]
  change (∏ e : Edge n, if 0 < (FractionalCoverRawCore.get _ (resource e)).value then
    min 1 (FractionalCoverRawCore.get _ (resource e)).value else 1) = _
  simp only [allValue,ConcurrentEdgeCappedPrices.floorPrice,ConcurrentEdgeCappedPrices.floorFactor]

theorem edgeCeiling_value (A : Adjacency n) (c : Weights n) (m : ℕ) :
    (ceiling (arcValues A c).1 m).1.value = ConcurrentEdgeBudgetGrid.costCeiling A c m := by
  rw [MeasuredBudgetGridBounds.ceiling_value,
    ← (finProdFinEquiv : Edge n ≃ Resource n).sum_comp
      (fun i => (FractionalCoverRawCore.get (arcValues A c).1 i).value)]
  change (m : ℚ≥0)*∑ e : Edge n,(FractionalCoverRawCore.get _ (resource e)).value = _
  simp only [arcValue,ConcurrentEdgeBudgetGrid.costCeiling,RationalEdgeDecomposition.originalTotal]

def edge (A : Adjacency n) (c : Weights n) (m : ℕ) : List (Code × Code) × ℕ :=
  let full := arcValues all c
  let relevant := arcValues A c
  let left := floor full.1
  let right := ceiling relevant.1 m
  let cap := capacity n m 2
  let result := pairs left.1 right.1 cap.1
  (result.1,full.2+relevant.2+left.2+right.2+cap.2+result.2)

theorem edge_value (A : Adjacency n) (c : Weights n) (m : ℕ) :
    (edge A c m).1.map decode = ConcurrentEdgeBudgetGrid.pairs A c m := by
  simp only [edge,pairs_value,edgeFloor_value,edgeCeiling_value,MeasuredBudgetGridBounds.capacity_value,
    ConcurrentEdgeBudgetGrid.pairs,ConcurrentEdgeBudgetGrid.massCeiling]

def edgeWork (n m B : ℕ) : ℕ :=
  let r := n*n
  r*(40*(B+1)^2)+r*(40*(B+1)^2)+floorWork r B+ceilingWork r m B+capacityWork n m 2+
    (gridWork (r*B) (m+r*(B+1))+gridWork 0 (m+2*n))

theorem edge_charge (A : Adjacency n) (c : Weights n) (m : ℕ) {B : ℕ} (fit : MatrixFits c B) :
    (edge A c m).2 ≤ edgeWork n m B := by
  obtain ⟨shape,read⟩ := arcValues_bounds all c fit
  obtain ⟨present,readPresent⟩ := arcValues_bounds A c fit
  obtain ⟨left,leftPaid⟩ := MeasuredBudgetGridBounds.floor_bounds _ shape
  obtain ⟨right,rightPaid⟩ := MeasuredBudgetGridBounds.ceiling_bounds _ m present
  obtain ⟨cap,capPaid⟩ := MeasuredBudgetGridBounds.capacity_bounds n m 2
  have budget := pairs_charge _ _ _ left right cap
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add read readPresent)
    leftPaid) rightPaid) capPaid) budget

attribute [local irreducible] grid floor ceiling capacity in
theorem edge_fields (A : Adjacency n) (c : Weights n) (m : ℕ) {B : ℕ} (fit : MatrixFits c B)
    {p : Code × Code} (active : p ∈ (edge A c m).1) :
    p.1.Bounded (ConcurrentEdgeBudgetWidths.priceWidth n m B) ∧
      p.2.Bounded (ConcurrentEdgeBudgetWidths.massWidth n m) := by
  have lo := (MeasuredBudgetGridBounds.floor_bounds _ (arcValues_bounds all c fit).1).1
  have hi := (MeasuredBudgetGridBounds.ceiling_bounds _ m (arcValues_bounds A c fit).1).1
  have cap := (MeasuredBudgetGridBounds.capacity_bounds n m 2).1
  let low := (floor (arcValues all c).1).1
  let high := (ceiling (arcValues A c).1 m).1
  let limit := (capacity n m 2).1
  change p ∈ (pairs low high limit).1 at active
  simpa only [ConcurrentEdgeBudgetWidths.priceWidth,ConcurrentEdgeBudgetWidths.massWidth,Nat.mul_comm 2 n] using
    pair_fields low high limit lo hi cap active

private theorem vertexValue (c : BinaryFractionalRows.Row n) (i : Fin n) :
    (FractionalCoverRawCore.get (MeasuredCanonicalCover.readVertex c).1 i).value = ConcurrentVertexBudget.raw c i := by
  simp only [MeasuredCanonicalCover.readVertex_value,MeasuredConcurrentCover.vertexPrices,
    FractionalCoverRawCore.get_ofFn,ConcurrentVertexBudget.raw]

def vertex (c : BinaryFractionalRows.Row n) (m : ℕ) : List (Code × Code) × ℕ :=
  let read := MeasuredCanonicalCover.readVertex c
  let left := floor read.1
  let right := ceiling read.1 m
  let cap := capacity n m 1
  let result := pairs left.1 right.1 cap.1
  (result.1,read.2+left.2+right.2+cap.2+result.2)

theorem vertex_value (c : BinaryFractionalRows.Row n) (m : ℕ) :
    (vertex c m).1.map decode = ConcurrentVertexBudget.pairs c m := by
  simp only [vertex,pairs_value,MeasuredBudgetGridBounds.floor_value,MeasuredBudgetGridBounds.ceiling_value,
    vertexValue,MeasuredBudgetGridBounds.capacity_value,pow_one,ConcurrentVertexBudget.pairs,
    ConcurrentVertexBudget.floorPrice,ConcurrentVertexBudget.floorFactor,ConcurrentVertexBudget.priceCeiling,
    ConcurrentVertexBudget.massCeiling]

def vertexWork (n m B : ℕ) : ℕ :=
  n*(40*(B+1)^2)+floorWork n B+ceilingWork n m B+capacityWork n m 1+
    (gridWork (n*B) (m+n*(B+1))+gridWork 0 (m+n))

theorem vertex_charge (c : BinaryFractionalRows.Row n) (m : ℕ) {B : ℕ}
    (fit : ∀ i, StoredBounded (c.get i) B) : (vertex c m).2 ≤ vertexWork n m B := by
  have h : FractionalCoverRawCore.RowBounded (MeasuredCanonicalCover.readVertex c).1 B := by
    rw [MeasuredCanonicalCover.readVertex_value]
    exact MeasuredConcurrentCover.vertexPrices_fits c fit
  obtain ⟨left,leftPaid⟩ := MeasuredBudgetGridBounds.floor_bounds _ h
  obtain ⟨right,rightPaid⟩ := MeasuredBudgetGridBounds.ceiling_bounds _ m h
  obtain ⟨cap,capPaid⟩ := MeasuredBudgetGridBounds.capacity_bounds n m 1
  have budget := pairs_charge _ _ _ left right cap
  simp only [Nat.one_mul] at budget
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (MeasuredCanonicalCover.readVertex_charge c fit)
    leftPaid) rightPaid) capPaid |> fun h => Nat.add_le_add h budget

attribute [local irreducible] grid floor ceiling capacity in
theorem vertex_fields (c : BinaryFractionalRows.Row n) (m : ℕ) {B : ℕ}
    (fit : ∀ i, StoredBounded (c.get i) B) {p : Code × Code} (active : p ∈ (vertex c m).1) :
    p.1.Bounded (MeasuredBudgetCandidateLists.vertexPriceWidth n m B) ∧
      p.2.Bounded (MeasuredBudgetCandidateLists.vertexMassWidth n m) := by
  have shape : FractionalCoverRawCore.RowBounded (MeasuredCanonicalCover.readVertex c).1 B := by
    rw [MeasuredCanonicalCover.readVertex_value]
    exact MeasuredConcurrentCover.vertexPrices_fits c fit
  have lo := (MeasuredBudgetGridBounds.floor_bounds _ shape).1
  have hi := (MeasuredBudgetGridBounds.ceiling_bounds _ m shape).1
  have cap := (MeasuredBudgetGridBounds.capacity_bounds n m 1).1
  let low := (floor (MeasuredCanonicalCover.readVertex c).1).1
  let high := (ceiling (MeasuredCanonicalCover.readVertex c).1 m).1
  let limit := (capacity n m 1).1
  change p ∈ (pairs low high limit).1 at active
  simpa only [MeasuredBudgetCandidateLists.vertexPriceWidth,MeasuredBudgetCandidateLists.vertexMassWidth,Nat.one_mul] using
    pair_fields low high limit lo hi cap active

end DirectedFlowCutGap.MeasuredGraphBudgetGrid
