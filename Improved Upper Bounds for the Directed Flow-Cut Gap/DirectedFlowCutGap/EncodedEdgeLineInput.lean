import DirectedFlowCutGap.EdgeLineReduction
import DirectedFlowCutGap.EncodedEdgeRounding
import DirectedFlowCutGap.EncodedVertexSolver
import DirectedFlowCutGap.EdgeRounding
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Rational input for edge fractional covering

The vertex covering solver receives the actual indexed line graph. Only
entered edge nodes contribute to a demanded path. A nonedge slot or a port
has zero price. Weights read back from a returned row are the original edge
weights, including the edges incident to either endpoint of a demand.
-/

namespace DirectedFlowCutGap.EncodedEdgeLineInput

open scoped NNReal
open EdgeLineReduction RawNonnegativeRational FractionalCoverRawCore
open EncodedVertexSolver EncodedEdgeRounding
open RetainedGridState

structure Input (n : ℕ) where
  adjacency : Vector (Vector Bool n) n
  demands : List (EncodedEdgeGadget.Pair n)
  costs : Vector (Vector Code n) n

def Input.graph {n : ℕ} (D : Input n) : Digraph (Fin n) where
  Adj u v := D.adjacency[u.val][v.val] = true

noncomputable def Input.cost {n : ℕ} (D : Input n) (e : EncodedEdgeGadget.Pair n) : ℝ≥0 :=
  D.costs[e.1.val][e.2.val].realValue

def lineSize (n : ℕ) : ℕ := n * 2 + n * n

def index (n : ℕ) : Fin (lineSize n) ≃ Node (Fin n) :=
  ((Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finProdFinEquiv)
    finProdFinEquiv).trans finSumFinEquiv).symm

def source {n : ℕ} (u : Fin n) : Fin (lineSize n) := (index n).symm (start u)
def sink {n : ℕ} (v : Fin n) : Fin (lineSize n) := (index n).symm (finish v)
def edgeIndex {n : ℕ} (e : EncodedEdgeGadget.Pair n) : Fin (lineSize n) := (index n).symm (arc e)

private def adjacent {n : ℕ} (D : Input n) (x : Node (Fin n)) : Node (Fin n) → Bool
  | .inl (v, false) => departs x && decide (base x = v)
  | .inl (_, true) => false
  | .inr (u, v) => departs x && decide (base x = u) && D.adjacency[u.val][v.val]

private theorem adjacent_iff {n : ℕ} (D : Input n) (x y : Node (Fin n)) :
    adjacent D x y = true ↔ (EdgeLineReduction.graph D.graph).Adj x y := by
  rcases y with ⟨v, b⟩ | ⟨u, v⟩
  · cases b <;> simp [adjacent, EdgeLineReduction.graph, adjacency]
  · simp [adjacent, EdgeLineReduction.graph, adjacency, Input.graph, and_assoc]

private def nodePrice {n : ℕ} (D : Input n) : Node (Fin n) → Code
  | .inl _ => Code.zero
  | .inr (s, t) => if D.adjacency[s.val][t.val] then D.costs[s.val][t.val] else Code.zero

def lineInput {n : ℕ} (D : Input n) : GraphInput (lineSize n) :=
  ⟨Vector.ofFn (fun i => Vector.ofFn fun j => adjacent D (index n i) (index n j)),
   D.demands.map (fun (s, t) => (source s, sink t)),
   Vector.ofFn (fun i => nodePrice D (index n i))⟩

theorem lineInput_adj {n : ℕ} (D : Input n) (i j : Fin (lineSize n)) :
    (lineInput D).graph.Adj i j ↔ (EdgeLineReduction.graph D.graph).Adj (index n i) (index n j) := by
  simp only [FractionalCoverRawGraph.Input.graph, lineInput, Vector.getElem_ofFn]
  exact adjacent_iff ..

theorem lineInput_cost_width {n B : ℕ} (D : Input n) (hB : 1 ≤ B)
    (hc : ∀ u v : Fin n, (D.costs[u.val][v.val]).num.size ≤ B ∧
      (D.costs[u.val][v.val]).den.size ≤ B) (i : Fin (lineSize n)) :
    let q := get (lineInput D).costs i
    q.num.size ≤ B ∧ q.den.size ≤ B := by
  have hq : get (lineInput D).costs i = nodePrice D (index n i) := by
    simp only [lineInput, FractionalCoverRawCore.get, Vector.getElem_ofFn]
  dsimp only
  rw [hq]
  have hz : Code.zero.num.size ≤ B ∧ Code.zero.den.size ≤ B := by
    exact ⟨Nat.zero_le B, hB⟩
  rcases index n i with port | ⟨u, v⟩
  · exact hz
  · simp only [nodePrice]
    split_ifs
    · exact hc u v
    · exact hz

theorem lineInput_demand {n : ℕ} (D : Input n) (i j : Fin (lineSize n)) :
    (i, j) ∈ (lineInput D).demands ↔
      ∃ s t, (s, t) ∈ D.demands ∧ i = source s ∧ j = sink t := by
  simp [lineInput, List.mem_map, Prod.exists, Prod.mk.injEq, eq_comm]

def projectWeight {n : ℕ} {A : Type} (w : Fin (lineSize n) → A) (e : EncodedEdgeGadget.Pair n) : A :=
  w (edgeIndex e)

theorem lineInput_dist {n : ℕ} (D : Input n) (w : Fin (lineSize n) → ℝ≥0) (s t : Fin n) :
    vertexDistance (lineInput D).graph w (source s) (sink t) =
      edgeDistance D.graph (projectWeight w) s t := by
  exact (FiniteGraphRelabeling.vertexDistance_eq (index n).symm
    (FiniteGraphRelabeling.inverse_adj (index n) (lineInput_adj D)) w
    (start s) (finish t)).trans (distance_eq_arcWeight D.graph _ s t)

theorem feasible_lineInput {n : ℕ} (D : Input n) (w : Fin (lineSize n) → ℝ≥0) :
    IsFractionalCut (lineInput D).graph w {d | d ∈ (lineInput D).demands} ↔
      IsFractionalEdgeCut D.graph (projectWeight w) {d | d ∈ D.demands} := by
  constructor
  · intro h s t hst
    rw [← lineInput_dist D w]
    exact h _ _ ((lineInput_demand D _ _).mpr ⟨s, t, hst, rfl, rfl⟩)
  · intro h i j hij
    obtain ⟨s, t, hst, rfl, rfl⟩ := (lineInput_demand D i j).mp hij
    rw [lineInput_dist D w]
    exact h s t hst

noncomputable def comparator {n : ℕ} (D : Input n) (w : EncodedEdgeGadget.Pair n → ℝ≥0)
    (i : Fin (lineSize n)) : ℝ≥0 :=
  vertexWeight (actualEdgeWeight D.graph w) (index n i)

@[simp] theorem projectWeight_comparator {n : ℕ} (D : Input n) (w : EncodedEdgeGadget.Pair n → ℝ≥0)
    (e : EncodedEdgeGadget.Pair n) : projectWeight (comparator D w) e = actualEdgeWeight D.graph w e := by
  simp only [projectWeight, comparator, edgeIndex, Equiv.apply_symm_apply, arc, vertexWeight]

theorem comparator_feasible {n : ℕ} (D : Input n) (w : EncodedEdgeGadget.Pair n → ℝ≥0)
    (h : IsFractionalEdgeCut D.graph w {d | d ∈ D.demands}) :
    IsFractionalCut (lineInput D).graph (comparator D w) {d | d ∈ (lineInput D).demands} := by
  rw [feasible_lineInput D]
  intro s t hst
  rw [edgeDistance_congr_on_edges D.graph s t (w' := w)]
  · exact h s t hst
  · intro a b ha
    rw [show (projectWeight (comparator D w)) (a, b) = _ from projectWeight_comparator D w _,
      actualEdgeWeight_of_adj _ _ ha]

private theorem linePrice {n : ℕ} (D : Input n) (x : Node (Fin n)) :
    capacity (lineInput D) ((index n).symm x) = (nodePrice D x).realValue := by
  simp only [capacity, lineInput, FractionalCoverRawCore.get, Vector.getElem_ofFn]
  exact congrArg (fun y => (nodePrice D y).realValue) ((index n).apply_symm_apply x)

theorem weightedCost_lineInput {n : ℕ} (D : Input n) (w : Fin (lineSize n) → ℝ≥0) :
    weightedCost (capacity (lineInput D)) w = weightedEdgeCost D.graph D.cost (projectWeight w) := by
  classical
  unfold weightedCost
  rw [← (index n).symm.sum_comp (fun i => capacity (lineInput D) i * w i),
    Fintype.sum_sum_type]
  simp only [linePrice, nodePrice, Code.realValue, Code.value_zero, NNRat.cast_zero,
    zero_mul, Finset.sum_const_zero, zero_add]
  unfold weightedEdgeCost graphEdges
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  rintro ⟨s, t⟩ _
  cases h : D.adjacency[s.val][t.val] <;>
    simp [h, Input.graph, Input.cost, projectWeight, edgeIndex, arc, Code.realValue]

theorem totalWeight_comparator {n : ℕ} (D : Input n) (w : EncodedEdgeGadget.Pair n → ℝ≥0) :
    totalWeight (comparator D w) = totalEdgeWeight D.graph w := by
  classical
  unfold totalWeight comparator
  rw [(index n).sum_comp, Fintype.sum_sum_type]
  simp only [vertexWeight, Finset.sum_const_zero, zero_add, totalEdgeWeight, graphEdges, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp [actualEdgeWeight]

theorem totalEdgeWeight_project_le {n : ℕ} (D : Input n) (w : Fin (lineSize n) → ℝ≥0) :
    totalEdgeWeight D.graph (projectWeight w) ≤ totalWeight w := by
  unfold totalEdgeWeight totalWeight
  calc
    _ ≤ ∑ e, projectWeight w e := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ ∑ x : Node (Fin n), w ((index n).symm x) := by
      rw [Fintype.sum_sum_type]
      exact le_add_of_nonneg_left bot_le
    _ = _ := (index n).symm.sum_comp _

def roundingInput {n : ℕ} (D : Input n) (row : RawRow (lineSize n)) : EncodedEdgeGadget.Input n :=
  ⟨D.adjacency,
    Vector.ofFn (fun s => Vector.ofFn fun t => get row (edgeIndex (s, t))),
    D.costs⟩

@[simp] theorem roundingInput_weight {n : ℕ} (D : Input n) (row : RawRow (lineSize n)) :
    (roundingInput D row).weight = projectWeight (fun i => (get row i).realValue) := by
  funext e
  simp only [roundingInput, EncodedEdgeGadget.Input.weight, Vector.getElem_ofFn, projectWeight]

def toEdges {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) : PairFlags n :=
  Vector.ofFn fun s => Vector.ofFn fun t =>
    D.adjacency[s.val][t.val] && mask[(edgeIndex (s, t)).val]

def toLine {n : ℕ} (mask : PairFlags n) : Flags (lineSize n) :=
  Vector.ofFn fun i => match index n i with
    | .inl _ => false
    | .inr (s, t) => mask[s.val][t.val]

private theorem edge_selected {n : ℕ} (mask : PairFlags n) (e : EncodedEdgeGadget.Pair n) :
    e ∈ selectedEdges mask ↔ flag mask e = true := by
  rw [selectedEdges, Finset.mem_filter]
  simp

theorem toEdges_mem {n : ℕ} (D : Input n) (mask : Flags (lineSize n))
    (e : EncodedEdgeGadget.Pair n) :
    e ∈ selectedEdges (toEdges D mask) ↔ D.graph.Adj e.1 e.2 ∧ mask[(edgeIndex e).val] = true := by
  rcases e with ⟨s, t⟩
  rw [edge_selected]
  simp only [toEdges, flag, Vector.getElem_ofFn, Bool.and_eq_true, Input.graph]

theorem toLine_selected {n : ℕ} (mask : PairFlags n) :
    EncodedUnitCostReplication.selectedSet (toLine mask) = ((selectedEdges mask).image arc).image (index n).symm := by
  classical
  ext i
  rw [Finset.image_image]
  simp only [EncodedUnitCostReplication.selectedSet, Finset.mem_filter, Finset.mem_univ, true_and,
    toLine, Vector.getElem_ofFn, Finset.mem_image, Function.comp_apply]
  cases hi : index n i with
  | inl v =>
    simp [hi, ← (index n).apply_eq_iff_eq, arc]
  | inr e =>
    rcases e with ⟨s, t⟩
    simp [hi, ← (index n).apply_eq_iff_eq, arc, edge_selected, flag]

theorem toEdges_selected {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) :
    selectedEdges (toEdges D mask) =
      arcs ((EncodedUnitCostReplication.selectedSet mask).image (index n)) ∩ graphEdges D.graph := by
  classical
  ext e
  rcases e with ⟨s, t⟩
  rw [selectedEdges, Finset.mem_filter, Finset.mem_inter, mem_arcs, mem_graphEdges]
  simp only [Finset.mem_univ, true_and, toEdges, flag, Vector.getElem_ofFn, Bool.and_eq_true, Input.graph]
  have h : arc (s, t) ∈ (EncodedUnitCostReplication.selectedSet mask).image (index n) ↔
      mask[(edgeIndex (s, t)).val] = true := by
    simp [Finset.mem_image, ← (index n).eq_symm_apply, EncodedUnitCostReplication.selectedSet, edgeIndex]
  rw [h]
  exact and_comm

theorem toEdges_toLine {n : ℕ} (D : Input n) (mask : PairFlags n) :
    selectedEdges (toEdges D (toLine mask)) = (selectedEdges mask) ∩ graphEdges D.graph := by
  ext e
  rcases e with ⟨s, t⟩
  rw [toEdges_mem, Finset.mem_inter, mem_graphEdges, edge_selected]
  simp only [toLine, Vector.getElem_ofFn]
  change (D.graph.Adj s t ∧
    (match index n ((index n).symm (arc (s, t))) with
     | .inl _ => false
     | .inr (a, b) => mask[a.val][b.val]) = true) ↔ _
  rw [Equiv.apply_symm_apply]
  exact and_comm

theorem toEdges_cost {n : ℕ} (D : Input n) (mask : Flags (lineSize n)) :
    edgeCutCost D.graph D.cost (selectedEdges (toEdges D mask)) =
      cutCost (capacity (lineInput D)) (EncodedUnitCostReplication.selectedSet mask) := by
  classical
  let w : Fin (lineSize n) → ℝ≥0 := fun i => if mask[i.val] then 1 else 0
  have line : weightedCost (capacity (lineInput D)) w =
      cutCost (capacity (lineInput D)) (EncodedUnitCostReplication.selectedSet mask) := by
    unfold weightedCost cutCost EncodedUnitCostReplication.selectedSet
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases h : mask[i.val] <;> simp [h, w]
  rw [← line, weightedCost_lineInput, edgeCutCost]
  have hset : (selectedEdges (toEdges D mask)).filter (fun e => D.graph.Adj e.1 e.2) =
      (graphEdges D.graph).filter fun e => mask[(edgeIndex e).val] = true := by
    ext e
    simp only [Finset.mem_filter, toEdges_mem, mem_graphEdges]
    tauto
  rw [hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  cases h : mask[(edgeIndex e).val] <;> simp [h, projectWeight, w]

theorem toLine_cost {n : ℕ} (D : Input n) (mask : PairFlags n) :
    cutCost (capacity (lineInput D)) (EncodedUnitCostReplication.selectedSet (toLine mask)) =
      edgeCutCost D.graph D.cost (selectedEdges mask) := by
  classical
  rw [← toEdges_cost, toEdges_toLine]
  unfold edgeCutCost
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_inter, mem_graphEdges]
  tauto

theorem toEdges_cut {n : ℕ} (D : Input n) (mask : Flags (lineSize n))
    (h : IsIntegralCut (lineInput D).graph (EncodedUnitCostReplication.selectedSet mask)
      {d | d ∈ (lineInput D).demands}) :
    IsIntegralEdgeCut D.graph (selectedEdges (toEdges D mask)) {d | d ∈ D.demands} := by
  rw [toEdges_selected]
  intro s t hst
  apply EdgeLineReduction.pullback_cut
  exact FiniteGraphRelabeling.cutsPair_pullback (index n).symm
    (FiniteGraphRelabeling.inverse_adj (index n) (lineInput_adj D)) _
    (h _ _ ((lineInput_demand D _ _).mpr ⟨s, t, hst, rfl, rfl⟩))

theorem toLine_cut {n : ℕ} (D : Input n) (mask : PairFlags n)
    (h : IsIntegralEdgeCut D.graph (selectedEdges mask) {d | d ∈ D.demands}) :
    IsIntegralCut (lineInput D).graph (EncodedUnitCostReplication.selectedSet (toLine mask))
      {d | d ∈ (lineInput D).demands} := by
  intro i j hij
  obtain ⟨s, t, hst, rfl, rfl⟩ := (lineInput_demand D i j).mp hij
  rw [toLine_selected]
  apply FiniteGraphRelabeling.cutsPair_pullback (index n) (lineInput_adj D)
  simpa only [source, sink, Equiv.apply_symm_apply] using EdgeLineReduction.lift_cut D.graph _ (h s t hst)

end DirectedFlowCutGap.EncodedEdgeLineInput
