import DirectedFlowCutGap.RawNonnegativeRational
import DirectedFlowCutGap.UnitCostReduction
import Mathlib.Data.List.NodupEquivFin

/-!
# Encoded normalization and complete-fiber replication

This is the normalization/replication stage of the repaired Theorem 29. Its
input is a retained Boolean adjacency matrix and unreduced nonnegative rational
weight/cost vectors. The source size `n` and prepared size `m` remain distinct.
The preparation invariants are explicit; this file does not yet implement the
permanent-port/shortcut preprocessing that establishes them.

The objective-zero branch returns the actual cardinality-threshold mask. The
positive branch normalizes once, retains every ceiling count, enumerates actual
clones and materializes the entire output matrix once. No real operation or
arbitrary graph callback occurs in the executable construction.
-/

namespace DirectedFlowCutGap.EncodedUnitCostReplication

open scoped BigOperators NNRat NNReal
open RawNonnegativeRational

structure Input (m : ℕ) where
  adjacency : Vector (Vector Bool m) m
  weights : Vector Code m
  costs : Vector Code m

namespace Input
variable {m : ℕ}

def graph (D : Input m) : Digraph (Fin m) where
  Adj u v := (D.adjacency[u.val])[v.val] = true

noncomputable def weight (D : Input m) (v : Fin m) : ℝ≥0 := D.weights[v.val].realValue
noncomputable def cost (D : Input m) (v : Fin m) : ℝ≥0 := D.costs[v.val].realValue

structure Totals where
  weight : Code
  objective : Code
  work : ℕ

/-- One traversal of original labels; both aggregates are retained. The 29
operations per cell cover three array reads, one multiplication, two additions,
the list case, recursion and result construction. -/
def scan (D : Input m) : List (Fin m) → Totals
  | [] => ⟨Code.zero,Code.zero,1⟩
  | v::vs =>
    let r := D.scan vs
    let p := (D.costs[v.val]).mulWithCost D.weights[v.val]
    let w := (D.weights[v.val]).addWithCost r.weight
    let c := p.1.addWithCost r.objective
    ⟨w.1,c.1,r.work+p.2+w.2+c.2+10⟩

def totals (D : Input m) : Totals := D.scan (List.finRange m)

theorem scan_weight (D : Input m) (vs : List (Fin m)) :
    (D.scan vs).weight.value = (vs.map fun v => D.weights[v.val].value).sum := by
  induction vs <;> simp [scan,Code.addWithCost, *]

theorem scan_objective (D : Input m) (vs : List (Fin m)) :
    (D.scan vs).objective.value =
      (vs.map fun v => D.costs[v.val].value*D.weights[v.val].value).sum := by
  induction vs <;> simp [scan,Code.addWithCost,Code.mulWithCost, *]

theorem scan_work (D : Input m) (vs : List (Fin m)) :
    (D.scan vs).work = 29*vs.length+1 := by
  induction vs <;> simp [scan,Code.addWithCost,Code.mulWithCost, *]
  omega

private theorem sum_finRange {A : Type*} [AddCommMonoid A] (f : Fin m → A) :
    ((List.finRange m).map f).sum = ∑ v, f v := by
  rw [← List.sum_toFinset _ (List.nodup_finRange m)]
  have h : (List.finRange m).toFinset = Finset.univ := by ext v; simp
  rw [h]

@[simp] theorem totals_weight (D : Input m) :
    D.totals.weight.realValue = totalWeight D.weight := by
  unfold totals Code.realValue
  rw [scan_weight,sum_finRange]
  simp [totalWeight,weight,Code.realValue,NNRat.cast_sum]

@[simp] theorem totals_objective (D : Input m) :
    D.totals.objective.realValue = weightedCost D.cost D.weight := by
  unfold totals Code.realValue
  rw [scan_objective,sum_finRange]
  simp [weightedCost,cost,weight,Code.realValue,NNRat.cast_sum]

theorem totals_work (D : Input m) : D.totals.work = 29*m+1 := by
  simp [totals,scan_work]

/-- All raw partial sums, including products in the objective, have linear
bit-growth in the number of processed input cells. -/
theorem scan_bounded (D : Input m) (b : ℕ)
    (hw : ∀ v : Fin m, D.weights[v.val].Bounded b)
    (hc : ∀ v : Fin m, D.costs[v.val].Bounded b) (vs : List (Fin m)) :
    (D.scan vs).weight.Bounded (vs.length*(b+1)) ∧
      (D.scan vs).objective.Bounded (vs.length*(2*b+1)) := by
  induction vs with
  | nil => simpa [scan] using And.intro Code.bounded_zero Code.bounded_zero
  | cons v vs ih =>
    have h₁ := Code.bounded_add (hw v) ih.1
    have h₂ := Code.bounded_add (Code.bounded_mul (hc v) (hw v)) ih.2
    constructor
    · simpa [scan,Code.addWithCost,Nat.add_mul,Nat.mul_add,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h₁
    · simpa [scan,Code.addWithCost,Code.mulWithCost,Nat.add_mul,Nat.mul_add,
        two_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h₂

/-- The test and mask involve only natural multiplication and comparison. -/
def zeroMask (D : Input m) : Vector Bool m := Vector.ofFn fun v =>
  Code.one.le ((Code.ofNat m).mul D.weights[v.val])

def zeroCut (D : Input m) : Finset (Fin m) :=
  Finset.univ.filter fun v => D.zeroMask[v.val] = true

theorem zeroCut_eq (D : Input m) : D.zeroCut = vertexCardThresholdCut D.weight := by
  ext v
  simp only [zeroCut,Finset.mem_filter,Finset.mem_univ,true_and,zeroMask,
    Vector.getElem_ofFn,Code.le_eq_true,Code.value_one,Code.value_mul,Code.value_ofNat]
  simp only [vertexCardThresholdCut,Finset.mem_filter,Finset.mem_univ,true_and,Fintype.card_fin]
  change (1 : ℚ≥0) ≤ m*D.weights[v.val].value ↔
    (1 : ℝ≥0) ≤ m*D.weights[v.val].realValue
  unfold Code.realValue
  norm_cast

theorem zeroCut_correct (D : Input m) (hz : D.totals.objective.num = 0) :
    IsIntegralCut D.graph D.zeroCut (thresholdDemands D.graph D.weight) ∧
      cutCost D.cost D.zeroCut = 0 := by
  have hv : D.totals.objective.value = 0 := (Code.value_eq_zero _).mpr hz
  have hC : weightedCost D.cost D.weight = 0 := by
    rw [← D.totals_objective]
    simp [Code.realValue,hv]
  rw [zeroCut_eq]
  refine ⟨vertexCardThresholdCut_isIntegralCut D.graph D.weight,?_⟩
  apply le_antisymm _ zero_le
  simpa [hC] using cutCost_vertexCardThresholdCut_le D.cost D.weight

/-- The aggregates and normalization factor are computed once before the
per-vertex loop. This function is used only in the positive-objective branch. -/
def normalized (D : Input m) (T : Totals) : Vector Code m :=
  let s := T.weight.div ((Code.ofNat 2).mul T.objective)
  Vector.ofFn fun v => s.mul D.costs[v.val]

theorem normalized_value (D : Input m) (v : Fin m) :
    (D.normalized D.totals)[v.val].realValue =
      UnitCostReduction.normalizedCost D.cost D.weight v := by
  simp [normalized,Code.realValue,UnitCostReduction.normalizedCost,
    UnitCostReduction.scale,cost,← totals_weight,← totals_objective]

def copyCounts (qs : Vector Code m) : Vector ℕ m :=
  Vector.ofFn fun v => max 1 (qs[v.val]).ceil

theorem copyCounts_eq (D : Input m) (v : Fin m) :
    (copyCounts (D.normalized D.totals))[v.val] =
      UnitCostReduction.copies (UnitCostReduction.normalizedCost D.cost D.weight) v := by
  simp only [copyCounts,Vector.getElem_ofFn,Code.ceil_eq,UnitCostReduction.copies]
  rw [← normalized_value]
  simp [Code.realValue]

/-- These are exactly the three properties proved for the prepared instance in
`UnitCostReduction`; they are not assumptions about arbitrary binary costs. -/
structure PreparedBounds (D : Input m) (n : ℕ) : Prop where
  original_nonempty : 0 < n
  card : m ≤ 3*n
  weight : totalWeight D.weight ≤ (n : ℝ≥0)
  charge : ∀ v, D.cost v ≤ (n : ℝ≥0)*(D.cost v*D.weight v)

end Input

/-- Each clone carries its retained original label and its local index. -/
abbrev Clone {m : ℕ} (k : Vector ℕ m) := Σ v : Fin m, Fin k[v.val]

/-- A bounded ascending loop emits exactly one clone per iteration. -/
def cloneFrom {m : ℕ} (k : Vector ℕ m) (v : Fin m) (start : ℕ) :
    (count : ℕ) → start+count ≤ k[v.val] → List (Clone k) × ℕ
  | 0,_ => ([],1)
  | count+1,h =>
    let r := cloneFrom k v (start+1) count (by omega)
    (⟨v,⟨start,by omega⟩⟩::r.1,r.2+8)

theorem cloneFrom_length {m : ℕ} (k : Vector ℕ m) (v : Fin m)
    (start count : ℕ) (h : start+count ≤ k[v.val]) :
    (cloneFrom k v start count h).1.length = count := by
  induction count generalizing start <;> simp [cloneFrom, *]

theorem cloneFrom_work {m : ℕ} (k : Vector ℕ m) (v : Fin m)
    (start count : ℕ) (h : start+count ≤ k[v.val]) :
    (cloneFrom k v start count h).2 = 8*count+1 := by
  induction count generalizing start <;> simp [cloneFrom, *]
  omega

theorem cloneFrom_get {m : ℕ} (k : Vector ℕ m) (v : Fin m)
    (start count : ℕ) (h : start+count ≤ k[v.val]) (i : ℕ)
    (hi : i < (cloneFrom k v start count h).1.length) :
    (cloneFrom k v start count h).1[i] = ⟨v,⟨start+i,by
      rw [cloneFrom_length] at hi
      omega⟩⟩ := by
  induction count generalizing start i with
  | zero => simp [cloneFrom] at hi
  | succ count ih =>
    cases i with
    | zero => simp [cloneFrom]
    | succ i =>
      have ht : i < (cloneFrom k v (start+1) count (by omega)).1.length := by
        simpa only [cloneFrom,List.length_cons,Nat.succ_lt_succ_iff] using hi
      simpa [cloneFrom,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        ih (start+1) (by omega) i ht

theorem cloneFrom_row {m : ℕ} (k : Vector ℕ m) (v : Fin m) :
    (cloneFrom k v 0 k[v.val] (by omega)).1 =
      (List.finRange k[v.val]).map (Sigma.mk v) := by
  apply List.ext_getElem
  · simp [cloneFrom_length]
  · intro i hi hj
    rw [cloneFrom_get]
    simp

/-- Append copying is charged: each emitted row is copied once into the final
list. Counts are read once per original label. -/
def cloneRows {m : ℕ} (k : Vector ℕ m) : List (Fin m) → List (Clone k) × ℕ
  | [] => ([],1)
  | v::vs =>
    let row := cloneFrom k v 0 k[v.val] (by omega)
    let tail := cloneRows k vs
    (row.1++tail.1,row.2+tail.2+2*row.1.length+6)

theorem cloneRows_value {m : ℕ} (k : Vector ℕ m) (vs : List (Fin m)) :
    (cloneRows k vs).1 = vs.sigma (fun v => List.finRange k[v.val]) := by
  induction vs <;> simp [cloneRows,cloneFrom_row, *]

theorem cloneRows_work {m : ℕ} (k : Vector ℕ m) (vs : List (Fin m)) :
    (cloneRows k vs).2 = 10*(vs.map fun v => k[v.val]).sum+7*vs.length+1 := by
  induction vs <;> simp [cloneRows,cloneFrom_work,cloneFrom_length, *]
  omega

def cloneList {m : ℕ} (k : Vector ℕ m) : List (Clone k) :=
  (cloneRows k (List.finRange m)).1

theorem cloneList_nodup {m : ℕ} (k : Vector ℕ m) : (cloneList k).Nodup := by
  rw [cloneList,cloneRows_value]
  exact (List.nodup_finRange m).sigma (fun _ => List.nodup_finRange _)

@[simp] theorem mem_cloneList {m : ℕ} (k : Vector ℕ m) (a : Clone k) : a ∈ cloneList k := by
  rcases a with ⟨v,i⟩
  simp [cloneList,cloneRows_value]

theorem cloneList_length {m : ℕ} (k : Vector ℕ m) :
    (cloneList k).length = Fintype.card (Clone k) := by
  have h : (cloneList k).toFinset = Finset.univ := by ext a; simp
  rw [← List.toFinset_card_of_nodup (cloneList_nodup k),h,Finset.card_univ]

theorem cloneList_length_bound {m : ℕ} (D : Input m) (n : ℕ)
    (h : D.PreparedBounds n) (hC : D.totals.objective.num ≠ 0) :
    (cloneList (Input.copyCounts (D.normalized D.totals))).length ≤ 4*n^2 := by
  have hpos : 0 < weightedCost D.cost D.weight := by
    rw [← D.totals_objective]
    change (0 : ℝ≥0) < (D.totals.objective.value : ℝ≥0)
    exact_mod_cast (Code.value_pos _).mpr (Nat.pos_of_ne_zero hC)
  rw [cloneList_length]
  have hk : (fun v : Fin m => (Input.copyCounts (D.normalized D.totals))[v.val]) =
      UnitCostReduction.copies (UnitCostReduction.normalizedCost D.cost D.weight) := by
    funext v
    exact D.copyCounts_eq v
  change Fintype.card (VertexReplication.Vertex _) ≤ _
  rw [VertexReplication.card_vertex]
  rw [show (∑ v : Fin m, (Input.copyCounts (D.normalized D.totals))[v.val]) =
      ∑ v, UnitCostReduction.copies (UnitCostReduction.normalizedCost D.cost D.weight) v
    from congrArg (fun f : Fin m → ℕ => ∑ v, f v) hk]
  simpa only [UnitCostReduction.ReplicatedVertex,VertexReplication.card_vertex] using
    UnitCostReduction.normalized_copied_card_le D.cost D.weight hpos n
      h.original_nonempty (by simpa using h.card) h.weight h.charge

/-- The enumerated labels are converted once to a retained random-access
vector; all matrix generation below uses that vector. -/
def labelVector {m : ℕ} (k : Vector ℕ m) : Vector (Clone k) (cloneList k).length :=
  ⟨(cloneList k).toArray,by simp⟩

@[simp] theorem labelVector_get {m : ℕ} (k : Vector ℕ m)
    (i : Fin (cloneList k).length) :
    (labelVector k)[i.val] = (cloneList k).get i := by
  simp [labelVector]

structure Replica {m : ℕ} (k : Vector ℕ m) where
  labels : Vector (Clone k) (cloneList k).length
  adjacency : Vector (Vector Bool (cloneList k).length) (cloneList k).length
  weights : Vector Code (cloneList k).length
  costs : Vector Code (cloneList k).length
  work : ℕ

/-- Materialization charges the actual clone generation plus list-to-array
copying, 40 operations per matrix cell, and 40 operations per output vertex.
These allowances include array loop tests, both index subtractions, callback
and push operations, row-vector wrappers, and each array allocation. The
10m+20 allowance covers the linear `List.finRange` loop and outer wrappers.
The dense matrix therefore has a quadratic charge in its actual clone count.
There is no oracle graph evaluation hidden in any cell computation. -/
def materialize {m : ℕ} (D : Input m) (k : Vector ℕ m) : Replica k :=
  let r := cloneRows k (List.finRange m)
  let N := r.1.length
  let labels : Vector (Clone k) N := ⟨r.1.toArray,by simp [N]⟩
  { labels := labels
    adjacency := Vector.ofFn (n := N) fun i => Vector.ofFn (n := N) fun j =>
      (D.adjacency[(labels[i.val]).1.val])[(labels[j.val]).1.val]
    weights := Vector.ofFn (n := N) fun i => D.weights[(labels[i.val]).1.val]
    costs := Vector.replicate N Code.one
    work := r.2+10*m+40*N^2+40*N+20 }

@[simp] theorem materialize_labels {m : ℕ} (D : Input m) (k : Vector ℕ m) :
    (materialize D k).labels = labelVector k := rfl

@[simp] theorem materialize_adjacency {m : ℕ} (D : Input m) (k : Vector ℕ m)
    (i j : Fin (cloneList k).length) :
    ((materialize D k).adjacency[i.val])[j.val] =
      (D.adjacency[((labelVector k)[i.val]).1.val])[((labelVector k)[j.val]).1.val] := by
  simp [materialize,labelVector,cloneList]

@[simp] theorem materialize_weight {m : ℕ} (D : Input m) (k : Vector ℕ m)
    (i : Fin (cloneList k).length) :
    (materialize D k).weights[i.val] = D.weights[((labelVector k)[i.val]).1.val] := by
  simp [materialize,labelVector,cloneList]

@[simp] theorem materialize_cost {m : ℕ} (D : Input m) (k : Vector ℕ m)
    (i : Fin (cloneList k).length) : (materialize D k).costs[i.val] = Code.one := by
  change (Vector.replicate (cloneList k).length Code.one)[i.val] = Code.one
  simp

/-- Exact indexed refinement to complete-fiber adjacency. In particular,
different local clone indices do not alter adjacency. -/
theorem materialize_graph_refines {m : ℕ} (D : Input m) (k : Vector ℕ m)
    (i j : Fin (cloneList k).length) :
    ((materialize D k).adjacency[i.val])[j.val] = true ↔
      (VertexReplication.graph D.graph (fun v => k[v.val])).Adj
        ((labelVector k)[i.val]) ((labelVector k)[j.val]) := by
  rw [materialize_adjacency]
  rfl

theorem materialize_weight_refines {m : ℕ} (D : Input m) (k : Vector ℕ m)
    (i : Fin (cloneList k).length) :
    ((materialize D k).weights[i.val]).realValue =
      VertexReplication.weight (fun v => k[v.val]) D.weight ((labelVector k)[i.val]) := by
  rw [materialize_weight]
  rfl

/-- The retained label vector enumerates every mathematical clone once. -/
theorem labelVector_bijective {m : ℕ} (k : Vector ℕ m) :
    Function.Bijective (fun i : Fin (cloneList k).length => (labelVector k)[i.val]) := by
  simp only [labelVector_get]
  constructor
  · exact List.nodup_iff_injective_get.mp (cloneList_nodup k)
  · intro a
    exact List.mem_iff_get.mp (mem_cloneList k a)

/-- This equivalence is used in proofs only. The executable graph reads the
retained vector directly and does not evaluate this inverse. -/
noncomputable def cloneEquiv {m : ℕ} (k : Vector ℕ m) :
    Fin (cloneList k).length ≃ Clone k :=
  Equiv.ofBijective (fun i => (labelVector k)[i.val]) (labelVector_bijective k)

/-- The actual selected clone set, interpreted through retained output labels. -/
def selectedClones {m : ℕ} (k : Vector ℕ m)
    (selected : Vector Bool (cloneList k).length) : Finset (Clone k) :=
  (Finset.univ.filter fun i : Fin (cloneList k).length => selected[i.val] = true).image
    (fun i => (labelVector k)[i.val])

@[simp] theorem mem_selectedClones_label {m : ℕ} (k : Vector ℕ m)
    (selected : Vector Bool (cloneList k).length) (i : Fin (cloneList k).length) :
    (labelVector k)[i.val] ∈ selectedClones k selected ↔ selected[i.val] = true := by
  simp only [selectedClones,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj,he⟩
    have hji := (labelVector_bijective k).1 he
    simpa [hji] using hj
  · intro hi
    exact ⟨i,hi,rfl⟩

/-- Scan every retained output label. A partially selected fiber is never
pulled back. The nine operations cover two array reads, parent extraction,
comparison, two Boolean operations, list case, sequencing and allocation. -/
def fiberScan {m N : ℕ} (k : Vector ℕ m) (labels : Vector (Clone k) N)
    (selected : Vector Bool N) (v : Fin m) : List (Fin N) → Bool × ℕ
  | [] => (true,1)
  | i::is =>
    let r := fiberScan k labels selected v is
    ((decide ((labels[i.val]).1 ≠ v) || selected[i.val]) && r.1,r.2+9)

theorem fiberScan_value {m N : ℕ} (k : Vector ℕ m) (labels : Vector (Clone k) N)
    (selected : Vector Bool N) (v : Fin m) (is : List (Fin N)) :
    (fiberScan k labels selected v is).1 = true ↔
      ∀ i ∈ is, (labels[i.val]).1 = v → selected[i.val] = true := by
  induction is with
  | nil => simp [fiberScan]
  | cons i is ih =>
    simp only [fiberScan,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,ih,
      List.forall_mem_cons]
    tauto

theorem fiberScan_work {m N : ℕ} (k : Vector ℕ m) (labels : Vector (Clone k) N)
    (selected : Vector Bool N) (v : Fin m) (is : List (Fin N)) :
    (fiberScan k labels selected v is).2 = 9*is.length+1 := by
  induction is <;> simp [fiberScan, *]
  omega

def retainedIndices {N : ℕ} (selected : Vector Bool N) : List (Fin N) :=
  (List.finRange selected.toArray.size).map (Fin.cast selected.size_toArray)

@[simp] theorem mem_retainedIndices {N : ℕ} (selected : Vector Bool N) (i : Fin N) :
    i∈retainedIndices selected := by
  apply List.mem_map.mpr
  refine ⟨⟨i.val,by simpa only [Vector.size_toArray] using i.isLt⟩,by simp,?_⟩
  apply Fin.ext
  rfl

def fullFiberMask {m N : ℕ} (k : Vector ℕ m) (labels : Vector (Clone k) N)
    (selected : Vector Bool N) : Vector Bool m :=
  let indices := retainedIndices selected
  Vector.ofFn (n := m) fun v => (fiberScan k labels selected v indices).1

/-- The output cut is read through its retained array size, so an implicit type
index cannot trigger clone re-enumeration. The charge includes the one index
list, its proof-only relabeling map, every full-fiber scan and vector generation. -/
def fullFiberMaskWithCost {m N : ℕ} (k : Vector ℕ m) (labels : Vector (Clone k) N)
    (selected : Vector Bool N) : Vector Bool m × ℕ :=
  (fullFiberMask k labels selected,m*(9*selected.toArray.size+20)+14*selected.toArray.size+10)

theorem fullFiberMaskWithCost_work {m N : ℕ} (k : Vector ℕ m)
    (labels : Vector (Clone k) N) (selected : Vector Bool N) :
    (fullFiberMaskWithCost k labels selected).2 = 9*m*N+20*m+14*N+10 := by
  simp [fullFiberMaskWithCost]
  ring

def fullFiberCut {m : ℕ} (k : Vector ℕ m)
    (selected : Vector Bool (cloneList k).length) : Finset (Fin m) :=
  Finset.univ.filter fun v => (fullFiberMask k (labelVector k) selected)[v.val] = true

/-- Equality to the frozen reduction's full-fiber pullback, for every sampled
Boolean cut. This is a statement about the actual returned mask. -/
theorem fullFiberCut_eq {m : ℕ} (k : Vector ℕ m)
    (selected : Vector Bool (cloneList k).length) :
    fullFiberCut k selected = VertexReplication.fullFibers (selectedClones k selected) := by
  ext v
  simp only [fullFiberCut,Finset.mem_filter,Finset.mem_univ,true_and,fullFiberMask,
    Vector.getElem_ofFn,fiberScan_value,mem_retainedIndices,forall_true_left,
    VertexReplication.mem_fullFibers]
  constructor
  · intro h i
    obtain ⟨j,hj⟩ := (labelVector_bijective k).2 (⟨v,i⟩ : Clone k)
    rw [← hj,mem_selectedClones_label]
    exact h j (congrArg Sigma.fst hj)
  · intro h j hj
    cases ha : (labelVector k)[j.val] with
    | mk u i =>
      simp only [ha] at hj
      subst u
      have hmem := h i
      rw [← ha] at hmem
      exact (mem_selectedClones_label k selected j).mp hmem

theorem fullFiberCut_correct {m : ℕ} (D : Input m) (k : Vector ℕ m)
    (hk : ∀ v : Fin m, 0 < k[v.val])
    (selected : Vector Bool (cloneList k).length)
    (h : IsIntegralCut (VertexReplication.graph D.graph (fun v => k[v.val]))
      (selectedClones k selected)
      (thresholdDemands (VertexReplication.graph D.graph (fun v => k[v.val]))
        (VertexReplication.weight (fun v => k[v.val]) D.weight))) :
    IsIntegralCut D.graph (fullFiberCut k selected) (thresholdDemands D.graph D.weight) := by
  rw [fullFiberCut_eq]
  exact VertexReplication.threshold_cut_pullback (fun v => ⟨0,hk v⟩) D.weight _ h

theorem fullFiberMask_work_bound {m : ℕ} (D : Input m) (n : ℕ)
    (h : D.PreparedBounds n) (hC : D.totals.objective.num ≠ 0)
    (selected : Vector Bool (cloneList (Input.copyCounts (D.normalized D.totals))).length) :
    (fullFiberMaskWithCost (Input.copyCounts (D.normalized D.totals))
      (materialize D (Input.copyCounts (D.normalized D.totals))).labels selected).2 ≤
      108*n^3+56*n^2+60*n+10 := by
  have hN := cloneList_length_bound D n h hC
  have hprod := Nat.mul_le_mul h.card hN
  rw [fullFiberMaskWithCost_work]
  nlinarith [h.card]

theorem materialize_work {m : ℕ} (D : Input m) (k : Vector ℕ m) :
    (materialize D k).work =
      40*(cloneList k).length^2+50*(cloneList k).length+17*m+21 := by
  have hsum : ((List.finRange m).map fun v => k[v.val]).sum = (cloneList k).length := by
    rw [cloneList_length,Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact Input.sum_finRange _
  simp only [materialize,cloneRows_work,List.length_finRange]
  change 10*((List.finRange m).map fun v => k[v.val]).sum+7*m+1+10*m+
    40*(cloneList k).length^2+40*(cloneList k).length+20 = _
  rw [hsum]
  omega

theorem materialize_work_bound {m : ℕ} (D : Input m) (n : ℕ)
    (h : D.PreparedBounds n) (hC : D.totals.objective.num ≠ 0) :
    (materialize D (Input.copyCounts (D.normalized D.totals))).work ≤
      640*n^4+200*n^2+51*n+21 := by
  have hN := cloneList_length_bound D n h hC
  have hN₂ := Nat.mul_le_mul hN hN
  rw [materialize_work]
  nlinarith [h.card]

namespace Input
variable {m : ℕ}

theorem normalized_bounded (D : Input m) (b : ℕ)
    (hw : ∀ v : Fin m, D.weights[v.val].Bounded b)
    (hc : ∀ v : Fin m, D.costs[v.val].Bounded b) (v : Fin m) :
    (D.normalized D.totals)[v.val].Bounded (m*(b+1)+(1+m*(2*b+1))+b) := by
  have h := D.scan_bounded b hw hc (List.finRange m)
  simp only [List.length_finRange] at h
  have htwo : (Code.ofNat 2).Bounded 1 := by norm_num [Code.Bounded,Code.ofNat]
  have hs := Code.bounded_div h.1 (Code.bounded_mul htwo h.2)
  simpa only [normalized,totals,Vector.getElem_ofFn] using Code.bounded_mul hs (hc v)

/-- The code returned to the caller retains the normalization and clone count
arrays. Its zero arm contains the actual Boolean mask to return immediately. -/
inductive Result (m : ℕ)
  | zero (mask : Vector Bool m) (work : ℕ)
  | replicated (normalized : Vector Code m) (counts : Vector ℕ m)
      (output : Replica counts) (work : ℕ)

def Result.work {m : ℕ} : Result m → ℕ
  | .zero _ work => work
  | .replicated _ _ _ work => work

/-- Explicit zero-objective dispatch. The positive arm computes the aggregate
scale once, computes each normalized cost once, then computes each ceiling once.
Its 60m+40 additional operations charge normalization/ceil vector construction,
including loop tests, index subtractions, callback/push operations, allocations
and the branch. This also covers the initial linear input-label generation.
The zero arm's 40m+20 allowance covers that generation and its threshold mask. -/
def reduce (D : Input m) : Result m :=
  let t := D.totals
  if t.objective.num = 0 then
    .zero D.zeroMask (t.work+40*m+20)
  else
    let qs := D.normalized t
    let k := copyCounts qs
    let out := materialize D k
    .replicated qs k out (t.work+out.work+60*m+40)

theorem reduce_zero (D : Input m) (h : D.totals.objective.num = 0) :
    D.reduce = .zero D.zeroMask (D.totals.work+40*m+20) := by simp [reduce,h]

theorem reduce_positive (D : Input m) (h : D.totals.objective.num ≠ 0) :
    D.reduce = .replicated (D.normalized D.totals) (copyCounts (D.normalized D.totals))
      (materialize D (copyCounts (D.normalized D.totals)))
      (D.totals.work+(materialize D (copyCounts (D.normalized D.totals))).work+60*m+40) := by
  simp [reduce,h]

/-- The complete dispatch/materialization charge is polynomial in the original
size, independent of the numerical magnitude of the binary input costs. -/
theorem reduce_work_bound (D : Input m) (n : ℕ) (h : D.PreparedBounds n) :
    D.reduce.work ≤ 640*n^4+200*n^2+318*n+62 := by
  by_cases hC : D.totals.objective.num = 0
  · rw [reduce_zero D hC]
    simp only [Result.work,totals_work]
    nlinarith [h.card]
  · rw [reduce_positive D hC]
    simp only [Result.work,totals_work]
    have hout := materialize_work_bound D n h hC
    nlinarith [h.card]

/-- Explicit actual-representation bounds: the unreduced numerator and
denominator lengths grow linearly in prepared input size and input bit width.
No bound on the numerical size of the costs is assumed. -/
theorem normalized_bits (D : Input m) (b : ℕ)
    (hw : ∀ v : Fin m, D.weights[v.val].Bounded b)
    (hc : ∀ v : Fin m, D.costs[v.val].Bounded b) (v : Fin m) :
    Nat.size (D.normalized D.totals)[v.val].num ≤ m*(b+1)+(1+m*(2*b+1))+b+1 ∧
    Nat.size (D.normalized D.totals)[v.val].den ≤ m*(b+1)+(1+m*(2*b+1))+b+1 :=
  Code.bounded_bits (D.normalized_bounded b hw hc v)

end Input

end DirectedFlowCutGap.EncodedUnitCostReplication
