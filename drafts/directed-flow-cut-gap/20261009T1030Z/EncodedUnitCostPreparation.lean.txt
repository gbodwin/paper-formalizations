import DirectedFlowCutGap.EncodedPortPreparation

/-!
# Materialized rational preparation for the unit-cost reduction

The input is an arbitrary Boolean graph with nonnegative raw rational weights
and costs. The executable construction retains the permanent-port arrays, the
shortcut matrix, the survivor list, its size, and its label array once each.
The output's size is ordinary stored data, so no caller needs to regenerate a
survivor list to obtain an executable array dimension.

The declared word model is the one used by `EncodedShortcutReachability` and
`RawNonnegativeRational`. Counter arithmetic and counter-product wrappers are
ghost instrumentation. Natural-number arithmetic is charged per operation;
operand widths are bounded separately. The setup budget pays low-mask raw
division/comparisons, port decoding, adjacency reads, all vector-loop
subtractions/callbacks/pushes and allocations. The assembly budget additionally
pays `finRange`, the survivor list traversal, conversion to arrays, the label
map, every output row wrapper, and all final graph/weight/cost cells.
-/

namespace DirectedFlowCutGap.EncodedUnitCostPreparation

open scoped BigOperators NNReal
open RawNonnegativeRational EncodedUnitCostReplication EncodedPortPreparation
open IntegralNetworkFlow.Tabulated

structure Prepared (n : ℕ) where
  size : ℕ
  ports : Vector (Fin (3*n)) size
  data : Input size
  work : ℕ

def originalPortCost {n : ℕ} (costs : Vector Code n) : Port n → Code
  | .inl v => costs[v.val]
  | .inr _ => Code.zero

/-- Reuse a previously retained graph, weights and port labels when only the
original costs change. Sixty operations per output cell cover port decoding,
one input-cost read or zero record, and the vector loop/record allocation. -/
def Prepared.replaceCosts {n : ℕ} (out : Prepared n) (costs : Vector Code n) : Prepared n :=
  let cs := Vector.ofFn (n := out.size) fun i => originalPortCost costs (decodePort out.ports[i.val])
  { out with
    data := { out.data with costs := cs }
    work := 60*out.size+20 }

/-- Conservative fixed-loop budget for low-mask and three-block port setup.
The quadratic allowance pays at most 80 operations per port-adjacency cell;
the linear allowance pays all masks, decode branches and vector setup. -/
def portWork (n : ℕ) : ℕ := 80*(3*n)^2+160*n+60

def build {n : ℕ} (D : Input n) : Prepared n :=
  let P := portData D
  let matrix := P.materialize
  let r := RetainedSurvivorEnumeration.scan P.removed (List.finRange (3*n))
  let N := r.1.length
  let labels : Vector (RetainedSurvivorEnumeration.Survivor P.removed) N :=
    ⟨r.1.toArray,by simp [N]⟩
  let ports := labels.map Subtype.val
  { size := N
    ports := ports
    data :=
      { adjacency := Vector.ofFn (n := N) fun i => Vector.ofFn (n := N) fun j =>
          matrix.adjacency[ports[i.val].val][ports[j.val].val]
        weights := Vector.ofFn (n := N) fun i => preparedWeightCode D (decodePort ports[i.val])
        costs := Vector.ofFn (n := N) fun i => preparedCostCode D (decodePort ports[i.val]) }
    work := portWork n+matrix.work+r.2+10*(3*n)+40*N^2+100*N+30 }

@[simp] theorem build_size {n : ℕ} (D : Input n) :
    (build D).size = (RetainedSurvivorEnumeration.labels (portData D).removed).length := rfl

theorem build_size_le {n : ℕ} (D : Input n) : (build D).size ≤ 3*n :=
  RetainedSurvivorEnumeration.labels_length_le (portData D).removed

@[simp] theorem build_size_replaceCosts {n : ℕ} (D : Input n) (costs : Vector Code n) :
    (build {D with costs := costs}).size = (build D).size := rfl

/-- Exact data equality to rebuilding the mathematical preparation with new
costs, although the executable `replaceCosts` reuses every fixed array. -/
theorem replaceCosts_data {n : ℕ} (D : Input n) (costs : Vector Code n) :
    ((build D).replaceCosts costs).data = (build {D with costs := costs}).data := rfl

theorem replaceCosts_work_bound {n : ℕ} (D : Input n) (costs : Vector Code n) :
    ((build D).replaceCosts costs).work ≤ 180*n+20 := by
  change 60*(build D).size+20 ≤ _
  have hs := build_size_le D
  omega

/-- Used only in proofs. Runtime output pullback will scan the retained `ports`
array and never evaluate this equivalence or its inverse. -/
noncomputable def preparedEquiv {n : ℕ} (D : Input n) :
    Fin (build D).size ≃ UnitCostReduction.PreparedVertex D.weight :=
  (RetainedSurvivorEnumeration.equiv (portData D).removed).trans (survivorEquiv D)

@[simp] theorem preparedEquiv_apply {n : ℕ} (D : Input n) (i : Fin (build D).size) :
    preparedEquiv D i = survivorEquiv D
      ((RetainedSurvivorEnumeration.vector (portData D).removed)[i.val]) := rfl

@[simp] theorem ports_get {n : ℕ} (D : Input n) (i : Fin (build D).size) :
    (build D).ports[i.val] =
      ((RetainedSurvivorEnumeration.vector (portData D).removed)[i.val]).val := by
  simp [build,RetainedSurvivorEnumeration.vector,RetainedSurvivorEnumeration.labels]

@[simp] theorem preparedEquiv_val {n : ℕ} (D : Input n) (i : Fin (build D).size) :
    (preparedEquiv D i).val = decodePort (build D).ports[i.val] := by
  rw [preparedEquiv_apply,ports_get]
  rfl

@[simp] theorem build_weights_get {n : ℕ} (D : Input n) (i : Fin (build D).size) :
    (build D).data.weights[i.val] = preparedWeightCode D (decodePort (build D).ports[i.val]) := by
  simp [build]

@[simp] theorem build_costs_get {n : ℕ} (D : Input n) (i : Fin (build D).size) :
    (build D).data.costs[i.val] = preparedCostCode D (decodePort (build D).ports[i.val]) := by
  simp [build]

theorem build_graph {n : ℕ} (D : Input n) (i j : Fin (build D).size) :
    (build D).data.graph.Adj i j ↔
      (UnitCostReduction.preparedGraph D.graph D.weight).Adj (preparedEquiv D i) (preparedEquiv D j) := by
  simp only [preparedEquiv_apply]
  simpa [Input.graph,build,
    RetainedSurvivorEnumeration.vector,RetainedSurvivorEnumeration.labels] using
    preparedShortcut_refines D
      ((RetainedSurvivorEnumeration.vector (portData D).removed)[i.val])
      ((RetainedSurvivorEnumeration.vector (portData D).removed)[j.val])

theorem build_weight {n : ℕ} (D : Input n) (i : Fin (build D).size) :
    (build D).data.weight i = UnitCostReduction.preparedWeight D.weight (preparedEquiv D i) := by
  simp only [preparedEquiv_apply]
  simpa [Input.weight,build,
    RetainedSurvivorEnumeration.vector,RetainedSurvivorEnumeration.labels] using
    preparedWeight_refines D ((RetainedSurvivorEnumeration.vector (portData D).removed)[i.val])

theorem build_cost {n : ℕ} (D : Input n) (i : Fin (build D).size) :
    (build D).data.cost i = UnitCostReduction.preparedCost D.weight D.cost (preparedEquiv D i) := by
  simp only [preparedEquiv_apply]
  simpa [Input.cost,build,
    RetainedSurvivorEnumeration.vector,RetainedSurvivorEnumeration.labels] using
    preparedCost_refines D ((RetainedSurvivorEnumeration.vector (portData D).removed)[i.val])

theorem build_totalWeight {n : ℕ} (D : Input n) :
    totalWeight (build D).data.weight = totalWeight (UnitCostReduction.preparedWeight D.weight) := by
  simp only [totalWeight,build_weight]
  exact (preparedEquiv D).sum_comp _

theorem build_weightedCost {n : ℕ} (D : Input n) :
    weightedCost (build D).data.cost (build D).data.weight =
      weightedCost (UnitCostReduction.preparedCost D.weight D.cost)
        (UnitCostReduction.preparedWeight D.weight) := by
  simp only [weightedCost,build_cost,build_weight]
  exact (preparedEquiv D).sum_comp (fun v =>
    UnitCostReduction.preparedCost D.weight D.cost v * UnitCostReduction.preparedWeight D.weight v)

theorem build_totalWeight_le_double {n : ℕ} (D : Input n) :
    totalWeight (build D).data.weight ≤ 2*totalWeight D.weight := by
  rw [build_totalWeight]
  exact UnitCostReduction.prepared_totalWeight_le_double D.weight

theorem build_weightedCost_le_double {n : ℕ} (D : Input n) :
    weightedCost (build D).data.cost (build D).data.weight ≤ 2*weightedCost D.cost D.weight := by
  rw [build_weightedCost]
  exact UnitCostReduction.prepared_weightedCost_le_double D.weight D.cost

/-- The hypotheses needed by the checked concrete clone enumeration are now
proved from the original array input. They are uniform in the cost vector. -/
theorem build_preparedBounds {n : ℕ} (D : Input n) (hn : 0<n) :
    (build D).data.PreparedBounds n := by
  refine ⟨hn,build_size_le D,?_,?_⟩
  · rw [build_totalWeight]
    simpa using UnitCostReduction.prepared_totalWeight_le_card D.weight
  · intro i
    simp only [build_cost,build_weight]
    simpa using UnitCostReduction.prepared_cost_charge D.weight D.cost
      (by simpa using hn) (preparedEquiv D i)

theorem build_work_bound {n : ℕ} (D : Input n) :
    (build D).work ≤
      9*n^2*(CountedSearch.searchBound (3*n) 24+224)+571*n+111 := by
  have hm := (portData D).materialize_work
  have hs := build_size_le D
  have hsq : (build D).size^2 ≤ (3*n)^2 := Nat.pow_le_pow_left hs 2
  have hr := RetainedSurvivorEnumeration.scan_work (portData D).removed (List.finRange (3*n))
  simp only [List.length_finRange] at hr
  change portWork n+(portData D).materialize.work+
    (RetainedSurvivorEnumeration.scan (portData D).removed (List.finRange (3*n))).2+
    10*(3*n)+40*(build D).size^2+100*(build D).size+30 ≤ _
  rw [hr]
  unfold portWork
  nlinarith

theorem build_weight_bounded {n : ℕ} (D : Input n) (b : ℕ)
    (h : ∀ v : Fin n, D.weights[v.val].Bounded b) (i : Fin (build D).size) :
    (build D).data.weights[i.val].Bounded (b+1) := by
  rw [build_weights_get]
  exact preparedWeight_bounded D b h _

theorem build_cost_bounded {n : ℕ} (D : Input n) (b : ℕ)
    (h : ∀ v : Fin n, D.costs[v.val].Bounded b) (i : Fin (build D).size) :
    (build D).data.costs[i.val].Bounded b := by
  rw [build_costs_get]
  cases decodePort (build D).ports[i.val] with
  | inl v => exact h v
  | inr p => exact Code.bounded_mono Code.bounded_zero (Nat.zero_le _)

theorem build_normalized_bits {n : ℕ} (D : Input n) (b : ℕ)
    (hw : ∀ v : Fin n, D.weights[v.val].Bounded b)
    (hc : ∀ v : Fin n, D.costs[v.val].Bounded b) (i : Fin (build D).size) :
    Nat.size ((build D).data.normalized (build D).data.totals)[i.val].num ≤
        3*n*(3*b+5)+b+3 ∧
      Nat.size ((build D).data.normalized (build D).data.totals)[i.val].den ≤
        3*n*(3*b+5)+b+3 := by
  have h := (build D).data.normalized_bits (b+1) (build_weight_bounded D b hw)
    (fun j => Code.bounded_mono (build_cost_bounded D b hc j) (Nat.le_succ b)) i
  have hs := Nat.mul_le_mul_right (3*b+5) (build_size_le D)
  constructor <;> nlinarith [h.1,h.2]

theorem build_clone_count {n : ℕ} (D : Input n) (hn : 0<n)
    (hC : (build D).data.totals.objective.num ≠ 0) :
    (cloneList (build D).data.counts).length ≤ 4*n^2 :=
  cloneList_length_bound (build D).data n (build_preparedBounds D hn) hC

@[simp] theorem build_empty_size (D : Input 0) : (build D).size = 0 := rfl

@[simp] theorem empty_objective_zero (D : Input 0) :
    (build D).data.totals.objective.num = 0 := rfl

/-- One retained preparation followed by one retained zero/replication dispatch.
This record is suitable for a caller that supplies a cut of the replica and
later pulls it back through the same stored port labels. -/
structure Reduction (n : ℕ) where
  prepared : Prepared n
  reduced : Input.Result prepared.size

def prepareAndReduce {n : ℕ} (D : Input n) : Reduction n :=
  let out := build D
  ⟨out,out.data.reduce⟩

def Reduction.work {n : ℕ} (out : Reduction n) : ℕ :=
  out.prepared.work+out.reduced.work+4

theorem prepareAndReduce_work {n : ℕ} (D : Input n) :
    (prepareAndReduce D).work ≤
      9*n^2*(CountedSearch.searchBound (3*n) 24+224)+640*n^4+200*n^2+889*n+177 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · change 136 ≤ 177
    decide
  · have hp := build_work_bound D
    have hr := (build D).data.reduce_work_bound n (build_preparedBounds D hn)
    change (build D).work+(build D).data.reduce.work+4 ≤ _
    omega

end DirectedFlowCutGap.EncodedUnitCostPreparation
