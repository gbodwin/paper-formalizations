import DirectedFlowCutGap.EncodedCubeRootThreshold
import DirectedFlowCutGap.EncodedUnitCostPreparation
import DirectedFlowCutGap.WeightSelfReduction

/-!
# Retained rational heavy-vertex residual arrays

The heavy mask is one exact raw-rational comparison per original vertex. The
survivors retain original arcs, doubled weights and unchanged costs. This is
deletion, with no shortcut edges. The fixed-weight preparation can therefore
feed the arbitrary-cost unit-cost reduction after its actual size is retained.
-/

namespace DirectedFlowCutGap.EncodedHeavyVertexPreparation

open scoped BigOperators NNReal
open RawNonnegativeRational EncodedUnitCostReplication

def heavyMask {n : ℕ} (D : Input n) (τ : Code) : Vector Bool n :=
  Vector.ofFn (n := n) fun i => τ.le D.weights[i.val]

theorem heavyMask_refines {n : ℕ} (D : Input n) (τ : Code) (i : Fin n) :
    (heavyMask D τ)[i.val]=true ↔ i∈WeightSelfReduction.heavy D.weight τ.realValue := by
  simp [heavyMask,WeightSelfReduction.mem_heavy,Input.weight,Code.realValue]

theorem heavyMask_comparison_bits {n : ℕ} (D : Input n) (τ : Code) (b t : ℕ)
    (hw : ∀ i : Fin n, D.weights[i.val].Bounded b) (hτ : τ.Bounded t) (i : Fin n) :
    Nat.size (τ.num*D.weights[i.val].den) ≤ t+b+1 ∧
      Nat.size (D.weights[i.val].num*τ.den) ≤ t+b+1 := by
  have h := Code.comparison_intermediates hτ (hw i)
  exact ⟨(Nat.size_le_size h.1).trans_eq Nat.size_pow,(Nat.size_le_size h.2).trans_eq Nat.size_pow⟩

def survivorEquiv {n : ℕ} (D : Input n) (τ : Code) :
    RetainedSurvivorEnumeration.Survivor (heavyMask D τ) ≃
      WeightSelfReduction.Residual D.weight τ.realValue where
  toFun a := ⟨a.val,by
    intro h
    have ht := (heavyMask_refines D τ a.val).mpr h
    simp [a.property] at ht⟩
  invFun a := ⟨a.val,by
    apply Bool.eq_false_iff.mpr
    exact fun h => a.property ((heavyMask_refines D τ a.val).mp h)⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext rfl

structure Residual (n : ℕ) where
  size : ℕ
  heavy : Vector Bool n
  labels : Vector (Fin n) size
  data : Input size
  work : ℕ

/-- The survivor enumeration, list length and vector are retained once. The
allowances cover original finRange, heavy-mask comparison and vector creation,
list-to-array conversion, label mapping and every residual array cell. -/
def build {n : ℕ} (D : Input n) (τ : Code) : Residual n :=
  let heavy := heavyMask D τ
  let r := RetainedSurvivorEnumeration.scan heavy (List.finRange n)
  let N := r.1.length
  let labels₀ : Vector (RetainedSurvivorEnumeration.Survivor heavy) N := ⟨r.1.toArray,by simp [N]⟩
  let labels := labels₀.map Subtype.val
  { size := N, heavy := heavy, labels := labels
    data :=
      { adjacency := Vector.ofFn (n := N) fun i => Vector.ofFn (n := N) fun j =>
          D.adjacency[labels[i.val].val][labels[j.val].val]
        weights := Vector.ofFn (n := N) fun i => (Code.ofNat 2).mul D.weights[labels[i.val].val]
        costs := Vector.ofFn (n := N) fun i => D.costs[labels[i.val].val] }
    work := r.2+40*N^2+75*N+33*n+39 }

@[simp] theorem build_size {n : ℕ} (D : Input n) (τ : Code) :
    (build D τ).size = (RetainedSurvivorEnumeration.labels (heavyMask D τ)).length := rfl

theorem build_size_le {n : ℕ} (D : Input n) (τ : Code) : (build D τ).size ≤ n :=
  RetainedSurvivorEnumeration.labels_length_le _

noncomputable def indexEquiv {n : ℕ} (D : Input n) (τ : Code) :
    Fin (build D τ).size ≃ WeightSelfReduction.Residual D.weight τ.realValue :=
  (RetainedSurvivorEnumeration.equiv (heavyMask D τ)).trans (survivorEquiv D τ)

@[simp] theorem indexEquiv_apply {n : ℕ} (D : Input n) (τ : Code) (i : Fin (build D τ).size) :
    indexEquiv D τ i = survivorEquiv D τ
      ((RetainedSurvivorEnumeration.vector (heavyMask D τ))[i.val]) := rfl

@[simp] theorem labels_get {n : ℕ} (D : Input n) (τ : Code) (i : Fin (build D τ).size) :
    (build D τ).labels[i.val] = (indexEquiv D τ i).val := by
  simp only [indexEquiv_apply]
  simp [build,survivorEquiv,RetainedSurvivorEnumeration.vector,RetainedSurvivorEnumeration.labels]

theorem build_graph {n : ℕ} (D : Input n) (τ : Code) (i j : Fin (build D τ).size) :
    (build D τ).data.graph.Adj i j ↔
      (WeightSelfReduction.graph D.graph D.weight τ.realValue).Adj (indexEquiv D τ i) (indexEquiv D τ j) := by
  change (build D τ).data.adjacency[i.val][j.val]=true ↔ _
  have he : (build D τ).data.adjacency[i.val][j.val] =
      D.adjacency[(build D τ).labels[i.val].val][(build D τ).labels[j.val].val] := by simp [build]
  rw [he]
  simp only [labels_get]
  rfl

theorem build_weight {n : ℕ} (D : Input n) (τ : Code) (i : Fin (build D τ).size) :
    (build D τ).data.weight i = WeightSelfReduction.weight D.weight τ.realValue (indexEquiv D τ i) := by
  have he : (build D τ).data.weights[i.val] =
      (Code.ofNat 2).mul D.weights[(build D τ).labels[i.val].val] := by simp [build]
  simp only [Input.weight,he,labels_get,WeightSelfReduction.weight,Code.realValue,Code.value_mul,
    Code.value_ofNat,NNRat.cast_mul]
  norm_num

theorem build_cost {n : ℕ} (D : Input n) (τ : Code) (i : Fin (build D τ).size) :
    (build D τ).data.cost i = WeightSelfReduction.cost D.weight D.cost τ.realValue (indexEquiv D τ i) := by
  have he : (build D τ).data.costs[i.val] = D.costs[(build D τ).labels[i.val].val] := by simp [build]
  simp only [Input.cost,he,labels_get,WeightSelfReduction.cost]

theorem build_totalWeight {n : ℕ} (D : Input n) (τ : Code) :
    totalWeight (build D τ).data.weight = totalWeight (WeightSelfReduction.weight D.weight τ.realValue) := by
  simp only [totalWeight,build_weight]
  exact (indexEquiv D τ).sum_comp _

theorem build_weightedCost {n : ℕ} (D : Input n) (τ : Code) :
    weightedCost (build D τ).data.cost (build D τ).data.weight =
      weightedCost (WeightSelfReduction.cost D.weight D.cost τ.realValue)
        (WeightSelfReduction.weight D.weight τ.realValue) := by
  simp only [weightedCost,build_cost,build_weight]
  exact (indexEquiv D τ).sum_comp (fun v => WeightSelfReduction.cost D.weight D.cost τ.realValue v *
    WeightSelfReduction.weight D.weight τ.realValue v)

theorem build_totalWeight_le {n : ℕ} (D : Input n) (τ : Code) :
    totalWeight (build D τ).data.weight ≤ 2*(n : ℝ≥0)*τ.realValue := by
  rw [build_totalWeight]
  simpa using WeightSelfReduction.residual_totalWeight_le D.weight τ.realValue

theorem build_weightedCost_le {n : ℕ} (D : Input n) (τ : Code) :
    weightedCost (build D τ).data.cost (build D τ).data.weight ≤ 2*weightedCost D.cost D.weight := by
  rw [build_weightedCost]
  exact WeightSelfReduction.residual_weightedCost_le D.weight D.cost τ.realValue

theorem build_work_bound {n : ℕ} (D : Input n) (τ : Code) :
    (build D τ).work ≤ 40*n^2+115*n+40 := by
  have hs := build_size_le D τ
  have hsq := Nat.mul_le_mul hs hs
  have hr := RetainedSurvivorEnumeration.scan_work (heavyMask D τ) (List.finRange n)
  simp only [List.length_finRange] at hr
  change (RetainedSurvivorEnumeration.scan (heavyMask D τ) (List.finRange n)).2+
    40*(build D τ).size^2+75*(build D τ).size+33*n+39 ≤ _
  rw [hr]
  nlinarith

theorem build_weights_bounded {n : ℕ} (D : Input n) (τ : Code) (b : ℕ)
    (h : ∀ i : Fin n, D.weights[i.val].Bounded b) (i : Fin (build D τ).size) :
    (build D τ).data.weights[i.val].Bounded (b+1) := by
  have ht : (Code.ofNat 2).Bounded 1 := by norm_num [Code.ofNat,Code.Bounded]
  have he : (build D τ).data.weights[i.val] =
      (Code.ofNat 2).mul D.weights[(build D τ).labels[i.val].val] := by simp [build]
  rw [he]
  simpa only [Nat.add_comm] using Code.bounded_mul ht (h (build D τ).labels[i.val])

theorem build_costs_bounded {n : ℕ} (D : Input n) (τ : Code) (b : ℕ)
    (h : ∀ i : Fin n, D.costs[i.val].Bounded b) (i : Fin (build D τ).size) :
    (build D τ).data.costs[i.val].Bounded b := by
  have he : (build D τ).data.costs[i.val] = D.costs[(build D τ).labels[i.val].val] := by simp [build]
  rw [he]
  exact h _

end DirectedFlowCutGap.EncodedHeavyVertexPreparation
