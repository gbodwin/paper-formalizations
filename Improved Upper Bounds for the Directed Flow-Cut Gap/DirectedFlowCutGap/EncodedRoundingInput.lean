import DirectedFlowCutGap.EncodedIntegerShortestPaths
import DirectedFlowCutGap.RetainedDemandMask

/-!
# Concrete input mask and shortest-cut arrays

Every array entry is computed once and retained. The generic tabulator exposes
the cost returned by every callback and charges every suffix-copy cell during
array construction. It is used only with the displayed counted distance and
Boolean routines. Threshold L is compared as an integer; it never determines
a loop length here. Thus even a huge binary threshold incurs its bit length,
not a loop of L iterations, in this input stage.
-/
namespace DirectedFlowCutGap.EncodedRoundingInput
open scoped BigOperators NNReal
open RetainedGridState
open EncodedIntegerShortestPaths

/-- Copying concatenation is charged even if a runtime could reuse storage. -/
def collect {α : Type*} : List (α × ℕ) → Array α × ℕ
  | [] => (#[],1)
  | e::es =>
      let r := collect es
      (#[e.1]++r.1,e.2+r.2+2*r.1.size+8)

theorem collect_value {α : Type*} (xs : List (α × ℕ)) :
    (collect xs).1.toList = xs.map Prod.fst := by
  induction xs <;> simp [collect, *]

theorem collect_size {α : Type*} (xs : List (α × ℕ)) :
    (collect xs).1.size = xs.length := by
  have h := congrArg List.length (collect_value xs)
  simpa using h

theorem collect_work {α : Type*} (xs : List (α × ℕ)) :
    (collect xs).2 = (xs.map Prod.snd).sum+xs.length^2+7*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
      simp only [collect,collect_size,List.length_cons,List.map_cons,List.sum_cons,ih]
      ring

/-- The source list and destination array both have explicitly paid copies. -/
def tabulate {α : Type*} {m : ℕ} (f : Fin m → α × ℕ) : Vector α m × ℕ :=
  let r := collect (List.ofFn f)
  (⟨r.1,by rw [collect_size,List.length_ofFn]⟩,r.2+8*m+1)

def arrayBound (m : ℕ) : ℕ := m^2+15*m+2

theorem tabulate_value {α : Type*} {m : ℕ} (f : Fin m → α × ℕ) :
    (tabulate f).1 = Vector.ofFn (fun i => (f i).1) := by
  apply Vector.toList_inj.mp
  change (collect (List.ofFn f)).1.toList = (Vector.ofFn (fun i => (f i).1)).toList
  rw [collect_value,Vector.toList_ofFn,List.map_ofFn]
  rfl

@[simp] theorem tabulate_get {α : Type*} {m : ℕ} (f : Fin m → α × ℕ) (i : Fin m) :
    (tabulate f).1[i.val] = (f i).1 := by
  rw [tabulate_value,Vector.getElem_ofFn]

theorem tabulate_work {α : Type*} {m : ℕ} (f : Fin m → α × ℕ) :
    (tabulate f).2 = (∑ i : Fin m, (f i).2)+arrayBound m := by
  simp only [tabulate,collect_work,List.map_ofFn,List.sum_ofFn,List.length_ofFn,arrayBound,Function.comp_def]
  ring

theorem tabulate_bound {α : Type*} {m : ℕ} (f : Fin m → α × ℕ) (C : ℕ)
    (h : ∀ i, (f i).2 ≤ C) : (tabulate f).2 ≤ m*C+arrayBound m := by
  rw [tabulate_work]
  apply Nat.add_le_add_right
  calc
    (∑ i : Fin m, (f i).2) ≤ ∑ _i : Fin m, C := Finset.sum_le_sum (fun i _ => h i)
    _ = m*C := by simp

variable {n : ℕ}

/-- One bounded shortest-path execution for each ordered original pair. -/
def demandMask (E : IntegerShortestPaths.Enumeration (Fin n))
    (adjacency : PairFlags n) (L : ℕ) : PairFlags n × ℕ :=
  let ones : Row n := Vector.replicate n 1
  let r := tabulate fun s : Fin n => tabulate fun t : Fin n =>
    let d := distance E adjacency ones s t
    (decide ((L : WithTop ℕ) ≤ d.1),d.2+4)
  (r.1,r.2+2*n+2)

def maskBound (n : ℕ) : ℕ :=
  n*(n*(distanceBound n+4)+arrayBound n)+arrayBound n+2*n+2

theorem demandMask_value (E : IntegerShortestPaths.Enumeration (Fin n))
    (adjacency : PairFlags n) (L : ℕ) :
    (demandMask E adjacency L).1 = RetainedDemandMask.compute (graph adjacency) E L := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp only [demandMask,tabulate_value,RetainedDemandMask.compute,Vector.getElem_ofFn,
    distance_value,Vector.getElem_replicate]

theorem demandMask_correct (E : IntegerShortestPaths.Enumeration (Fin n))
    (adjacency : PairFlags n) (L : ℕ) :
    remainingSet (demandMask E adjacency L).1 =
      CandidateSchedule.unweightedDemands (graph adjacency) (L : ℝ≥0) := by
  rw [demandMask_value]
  exact RetainedDemandMask.compute_correct (graph adjacency) E L

theorem demandMask_bound (E : IntegerShortestPaths.Enumeration (Fin n))
    (adjacency : PairFlags n) (L : ℕ) : (demandMask E adjacency L).2 ≤ maskBound n := by
  have hinner (s : Fin n) := tabulate_bound (fun t : Fin n =>
    let d := distance E adjacency (Vector.replicate n 1) s t
    (decide ((L : WithTop ℕ) ≤ d.1),d.2+4)) (distanceBound n+4)
      (fun t => Nat.add_le_add_right (distance_bound E adjacency _ s t) 4)
  have houter := tabulate_bound (fun s : Fin n => tabulate fun t : Fin n =>
    let d := distance E adjacency (Vector.replicate n 1) s t
    (decide ((L : WithTop ℕ) ≤ d.1),d.2+4))
      (n*(distanceBound n+4)+arrayBound n) hinner
  simpa only [demandMask,maskBound,Nat.add_assoc] using Nat.add_le_add_right houter (2*n+2)

/-- A direct cell test allocates no intermediate cut list. All distances are
retained only until their Boolean result has been inserted into the array. -/
def cutFlags (E : IntegerShortestPaths.Enumeration (Fin n)) (adjacency : PairFlags n)
    (a : Row n) (s : Fin n) (j : ℕ) : Flags n × ℕ :=
  tabulate fun v : Fin n =>
    let d := distance E adjacency a s v
    let b := IntegerLevelCuts.cellTest d.1 a[v.val] j
    (b.1,d.2+b.2+8)

def cutBound (n : ℕ) : ℕ := n*(distanceBound n+12)+arrayBound n

theorem cutFlags_bound (E : IntegerShortestPaths.Enumeration (Fin n))
    (adjacency : PairFlags n) (a : Row n) (s : Fin n) (j : ℕ) :
    (cutFlags E adjacency a s j).2 ≤ cutBound n := by
  apply tabulate_bound
  intro v
  have hd := distance_bound E adjacency a s v
  have hb := IntegerLevelCuts.cellTest_count_le (distance E adjacency a s v).1 a[v.val] j
  dsimp only
  omega

theorem cutFlags_set (E : IntegerShortestPaths.Enumeration (Fin n))
    (adjacency : PairFlags n) (a : Row n) (s : Fin n) (j : ℕ) :
    cutSet (cutFlags E adjacency a s j).1 =
      (IntegerLevelCuts.cut E (graph adjacency) (fun v => a[v.val]) s j).1 := by
  ext v
  rw [mem_cutSet,IntegerLevelCuts.mem_cut]
  simp only [cutFlags,tabulate_get,distance_value]

def cutOracle (E : IntegerShortestPaths.Enumeration (Fin n))
    (adjacency : PairFlags n) {L : ℕ} (hL : 0<L) : CutOracle (graph adjacency) L hL where
  cut a s j := (cutFlags E adjacency a s j.val).1
  cut_eq := by
    intro a s j
    rw [cutFlags_set]
    exact IntegerLevelCuts.cut_correct E (graph adjacency) (fun v => a[v.val]) hL s j

/-- Equal Boolean sets force equality of the actual retained arrays. -/
theorem flags_eq_of_cutSet_eq (a b : Flags n) (h : cutSet a = cutSet b) : a=b := by
  apply Vector.ext
  intro i hi
  have hh : a[i]=true ↔ b[i]=true := by
    have hm : (⟨i,hi⟩ : Fin n) ∈ cutSet a ↔ (⟨i,hi⟩ : Fin n) ∈ cutSet b := by rw [h]
    simpa only [mem_cutSet] using hm
  cases ha : a[i] <;> cases hb : b[i] <;> simp_all

theorem cutOracle_ext {G : Digraph (Fin n)} {L : ℕ} {hL : 0<L}
    (C D : CutOracle G L hL) (h : C.cut=D.cut) : C=D := by
  cases C
  cases D
  cases h
  rfl

theorem cutOracle_eq (E : IntegerShortestPaths.Enumeration (Fin n))
    (adjacency : PairFlags n) {L : ℕ} (hL : 0<L) :
    cutOracle E adjacency hL = integerCutOracle (G := graph adjacency) hL E := by
  have h : (cutOracle E adjacency hL).cut =
      (integerCutOracle (G := graph adjacency) hL E).cut := by
    funext a s j
    apply flags_eq_of_cutSet_eq
    rw [(cutOracle E adjacency hL).cut_eq,(integerCutOracle hL E).cut_eq]
  exact cutOracle_ext _ _ h

/-- Input-mask finite distance numerators use at most size(n) bits, while L
is an explicitly charged input operand, even in the easy enormous-L regime. -/
theorem mask_distance_bits (E : IntegerShortestPaths.Enumeration (Fin n))
    (adjacency : PairFlags n) (s t : Fin n) (d : ℕ)
    (hd : (distance E adjacency (Vector.replicate n 1) s t).1 = d) : d.size ≤ n.size := by
  apply Nat.size_le_size
  simpa using distance_within E adjacency (Vector.replicate n 1) s t 1
    (by intro v; simp) d hd

/-- The input stage carries the binary threshold width explicitly; the
numerical value of L does not occur in maskBound. -/
def maskOperandBits (n L : ℕ) : ℕ := L.size+(n+1).size+2

theorem mask_threshold_bits (n L : ℕ) : 1+L.size ≤ maskOperandBits n L := by
  unfold maskOperandBits
  omega

theorem mask_scalar_bits (n L k : ℕ) (hk : k ≤ max L (n+1)) :
    1+k.size ≤ maskOperandBits n L := by
  rcases le_total L (n+1) with h | h
  · rw [max_eq_right h] at hk
    have hs := Nat.size_le_size hk
    unfold maskOperandBits
    omega
  · rw [max_eq_left h] at hk
    have hs := Nat.size_le_size hk
    unfold maskOperandBits
    omega

end DirectedFlowCutGap.EncodedRoundingInput
