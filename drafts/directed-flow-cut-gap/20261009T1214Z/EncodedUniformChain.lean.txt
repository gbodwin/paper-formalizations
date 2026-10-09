import DirectedFlowCutGap.EncodedUniformWeightParameters
import DirectedFlowCutGap.EncodedPreparationOutput

/-!
# Actual Boolean chain graph with retained size and labels

The executable edge test distinguishes consecutive copies of one vertex from
an original edge connecting a last copy to a first copy. Labels use the checked
bounded clone enumeration. The output stores its size explicitly; every array
constructor and subsequent consumer can use that retained size directly.
-/

namespace DirectedFlowCutGap.EncodedUniformChain

open scoped BigOperators NNReal
open RawNonnegativeRational EncodedUnitCostReplication

def chainAdj {m : ℕ} (P : Input m) (k : Vector ℕ m) (a b : Clone k) : Bool :=
  (decide (a.1=b.1) && decide (b.2.val=a.2.val+1)) ||
    (decide (a.2.val+1=k[a.1.val]) && decide (b.2.val=0) && P.adjacency[a.1.val][b.1.val])

theorem chainAdj_refines {m : ℕ} (P : Input m) (k : Vector ℕ m) (a b : Clone k) :
    chainAdj P k a b = true ↔
      (UniformWeightReduction.graph P.graph (fun v => k[v.val])).Adj a b := by
  simp [chainAdj,UniformWeightReduction.graph,Input.graph,and_assoc]

structure Chain {m : ℕ} (k : Vector ℕ m) where
  size : ℕ
  size_eq : size=(cloneList k).length
  labels : Vector (Clone k) size
  data : Input size
  cutoff : ℕ
  work : ℕ

/-- The 60-per-cell budget pays two label reads, fiber/index tests, an optional
input edge read and all vector-loop callbacks/pushes/wrappers. The linear
budget also pays list length, array conversion, uniform-weight/unit-cost array
construction and the raw reciprocal/ceiling used for the integer cutoff. -/
def materialize {m : ℕ} (P : Input m) (average : Code) (k : Vector ℕ m) : Chain k :=
  let r := cloneRows k (List.finRange m)
  let N := r.1.length
  let labels : Vector (Clone k) N := ⟨r.1.toArray,by simp [N]⟩
  { size := N, size_eq := rfl, labels := labels
    data :=
      { adjacency := Vector.ofFn (n := N) fun i => Vector.ofFn (n := N) fun j =>
          chainAdj P k labels[i.val] labels[j.val]
        weights := Vector.replicate N average
        costs := Vector.replicate N Code.one }
    cutoff := (Code.one.div average).ceil
    work := r.2+10*m+60*N^2+40*N+35 }

@[simp] theorem materialize_size {m : ℕ} (P : Input m) (average : Code) (k : Vector ℕ m) :
    (materialize P average k).size = (cloneList k).length := rfl

@[simp] theorem materialize_labels {m : ℕ} (P : Input m) (average : Code) (k : Vector ℕ m) :
    (materialize P average k).labels = labelVector k := rfl

theorem materialize_graph {m : ℕ} (P : Input m) (average : Code) (k : Vector ℕ m)
    (i j : Fin (materialize P average k).size) :
    (materialize P average k).data.graph.Adj i j ↔
      (UniformWeightReduction.graph P.graph (fun v => k[v.val])).Adj
        ((EncodedUnitCostReplication.cloneEquiv k) i) ((EncodedUnitCostReplication.cloneEquiv k) j) := by
  change _ ↔ (UniformWeightReduction.graph P.graph (fun v => k[v.val])).Adj
    (labelVector k)[i.val] (labelVector k)[j.val]
  simpa [materialize,Input.graph,labelVector,cloneList] using
    chainAdj_refines P k (labelVector k)[i.val] (labelVector k)[j.val]

theorem materialize_weight {m : ℕ} (P : Input m) (average : Code) (k : Vector ℕ m)
    (i : Fin (materialize P average k).size) :
    (materialize P average k).data.weight i = average.realValue := by
  simp [materialize,Input.weight]

theorem materialize_cost {m : ℕ} (P : Input m) (average : Code) (k : Vector ℕ m)
    (i : Fin (materialize P average k).size) :
    (materialize P average k).data.cost i = 1 := by
  simp [materialize,Input.cost,Code.realValue]

theorem materialize_work {m : ℕ} (P : Input m) (average : Code) (k : Vector ℕ m) :
    (materialize P average k).work =
      60*(cloneList k).length^2+50*(cloneList k).length+17*m+36 := by
  have hsum : ((List.finRange m).map fun v => k[v.val]).sum = (cloneList k).length := by
    rw [cloneList_length,Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [← List.sum_toFinset _ (List.nodup_finRange m)]
    have he : (List.finRange m).toFinset=Finset.univ := by ext i; simp
    rw [he]
  simp only [materialize,cloneRows_work,List.length_finRange]
  change 10*((List.finRange m).map fun v => k[v.val]).sum+7*m+1+10*m+
    60*(cloneList k).length^2+40*(cloneList k).length+35 = _
  rw [hsum]
  omega

open EncodedUniformWeightParameters in
theorem computed_work_bound {n : ℕ} (D : Input n)
    (h : 0 < (compute D).total.realValue) :
    (materialize (compute D).ports (compute D).average (compute D).counts).work ≤
      2160*n^2+351*n+36 := by
  rw [materialize_work]
  have hN := clone_count D h
  have hsq := Nat.mul_le_mul hN hN
  nlinarith

open EncodedUniformWeightParameters in
def expand {n : ℕ} (D : Input n) : Chain (compute D).counts :=
  let p := compute D
  materialize p.ports p.average p.counts

open EncodedUniformWeightParameters in
theorem expand_size_bound {n : ℕ} (D : Input n) (h : 0 < (compute D).total.realValue) :
    (expand D).size ≤ 6*n := clone_count D h

open EncodedUniformWeightParameters
open EncodedPortPreparation

theorem semantic_graph {n : ℕ} (D : Input n) (a b : Clone (compute D).counts) :
    (UniformWeightReduction.graph (compute D).ports.graph
      (fun v => (compute D).counts[v.val])).Adj a b ↔
    (UniformWeightReduction.expandedGraph D.graph D.weight).Adj
      (EncodedUniformWeightParameters.cloneEquiv D a) (EncodedUniformWeightParameters.cloneEquiv D b) := by
  have he : decodePort a.1=decodePort b.1 ↔ a.1=b.1 := (portEquiv n).injective.eq_iff
  change (UniformWeightReduction.graph (portInput D).graph
    (fun v => (compute D).counts[v.val])).Adj a b ↔ _
  simp only [UniformWeightReduction.expandedGraph,UniformWeightReduction.graph,
    cloneEquiv_fst,cloneEquiv_snd_val,compute_counts,port_graph,he]

noncomputable def indexEquiv {n : ℕ} (D : Input n) :
    Fin (expand D).size ≃ UniformWeightReduction.ExpandedVertex D.weight :=
  (EncodedUnitCostReplication.cloneEquiv (compute D).counts).trans
    (EncodedUniformWeightParameters.cloneEquiv D)

@[simp] theorem indexEquiv_apply {n : ℕ} (D : Input n) (i : Fin (expand D).size) :
    indexEquiv D i = EncodedUniformWeightParameters.cloneEquiv D
      (EncodedUnitCostReplication.cloneEquiv (compute D).counts i) := rfl

theorem expand_graph {n : ℕ} (D : Input n) (i j : Fin (expand D).size) :
    (expand D).data.graph.Adj i j ↔
      (UniformWeightReduction.expandedGraph D.graph D.weight).Adj (indexEquiv D i) (indexEquiv D j) := by
  exact (materialize_graph (compute D).ports (compute D).average (compute D).counts i j).trans
    (semantic_graph D _ _)

theorem expand_weight {n : ℕ} (D : Input n) (i : Fin (expand D).size) :
    (expand D).data.weight i = UniformWeightReduction.uniformWeight D.weight (indexEquiv D i) := by
  rw [show (expand D).data.weight i = (compute D).average.realValue from
    materialize_weight (compute D).ports (compute D).average (compute D).counts i,compute_average]
  rfl

theorem expand_totalWeight {n : ℕ} (D : Input n) :
    totalWeight (expand D).data.weight = totalWeight (UniformWeightReduction.uniformWeight D.weight) := by
  simp only [totalWeight,expand_weight]
  exact (indexEquiv D).sum_comp _

theorem expand_totalWeight_le {n : ℕ} (D : Input n) (h : 0 < (compute D).total.realValue) :
    totalWeight (expand D).data.weight ≤ 2*totalWeight D.weight := by
  rw [expand_totalWeight]
  exact UniformWeightReduction.expanded_totalWeight_le D.weight (by simpa using h)

@[simp] theorem expand_cutoff {n : ℕ} (D : Input n) : (expand D).cutoff = cutoff D := rfl

theorem expand_cutoff_bounds {n : ℕ} (D : Input n) (h : nontrivial D = true) :
    0 < (expand D).cutoff ∧ (expand D).cutoff ≤ (expand D).size :=
  ⟨cutoff_positive D h,cutoff_le_clones D h⟩

inductive Result (n : ℕ)
  | trivial (mask : Vector Bool n) (work : ℕ)
  | expanded (parameters : Parameters n) (output : Chain parameters.counts) (work : ℕ)

def Result.work {n : ℕ} : Result n → ℕ
  | .trivial _ work => work
  | .expanded _ _ work => work

/-- Test raw clipped mass before entering the integer core. All port arrays,
parameters and chain labels are retained exactly once by this dispatcher. -/
def reduce {n : ℕ} (D : Input n) : Result n :=
  let p := compute D
  if Code.one.le p.total then
    let out := materialize p.ports p.average p.counts
    .expanded p out (p.work+out.work+10)
  else .trivial (Vector.replicate n false) (p.work+4*n+10)

theorem reduce_work_bound {n : ℕ} (D : Input n) :
    (reduce D).work ≤ 2880*n^2+918*n+97 := by
  by_cases h : nontrivial D = true
  · have hW := (nontrivial_iff D).mp h
    have hp : 0 < (compute D).total.realValue := by rw [compute_total]; exact lt_of_lt_of_le (by norm_num) hW
    have hw := computed_work_bound D hp
    simp only [reduce,show Code.one.le (compute D).total=true from h,↓reduceIte,Result.work,compute_work]
    nlinarith
  · simp only [nontrivial] at h
    have hf : Code.one.le (compute D).total=false := by
      cases hh : Code.one.le (compute D).total <;> simp_all
    simp only [reduce,hf,Bool.false_eq_true,ite_false,Result.work,compute_work]
    omega

end DirectedFlowCutGap.EncodedUniformChain
