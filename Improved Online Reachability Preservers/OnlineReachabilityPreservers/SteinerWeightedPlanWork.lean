import OnlineReachabilityPreservers.SteinerForestLabelWork
import OnlineReachabilityPreservers.SteinerFinReplayWork

/-! Build and price both forest arc classes in one pass through the paired list. -/

namespace OnlineReachabilityPreservers

private structure WeightedArcLists (B : Type*) where
  paid : List B
  free : List B
  total : ℕ
  comparisons : ℕ
  work : ℕ

private def weightedArcListsWithWordWork {A B : Type*} (copy : A → B) (read : A → ℕ × ℕ × ℕ) :
    List A → WeightedArcLists B
  | [] => ⟨[], [], 0, 0, 5⟩
  | edge :: edges =>
    let rest := weightedArcListsWithWordWork copy read edges
    let row := read edge
    let lifted := copy edge
    if 0 < row.1 then
      ⟨lifted :: rest.paid,rest.free,rest.total+row.1,rest.comparisons+row.2.1,
       rest.work+row.2.2+22⟩
    else
      ⟨rest.paid,lifted :: rest.free,rest.total,rest.comparisons+row.2.1,rest.work+row.2.2+22⟩

private theorem weightedArcListsWithWordWork_spec {A B : Type*} (copy : A → B)
    (read : A → ℕ × ℕ × ℕ) (edges : List A) :
    let out := weightedArcListsWithWordWork copy read edges
    out.paid = (edges.filter fun e => 0 < (read e).1).map copy ∧
      out.free = (edges.filter fun e => (read e).1 = 0).map copy ∧
      out.total = (edges.map fun e => (read e).1).sum ∧
      out.comparisons = (edges.map fun e => (read e).2.1).sum ∧
      out.work = (edges.map fun e => (read e).2.2).sum+22*edges.length+5 := by
  induction edges with
  | nil => simp [weightedArcListsWithWordWork]
  | cons e edges ih =>
    obtain ⟨paid,free,total,comparisons,words⟩ := ih
    by_cases weight : 0 < (read e).1
    · have nonzero := Nat.ne_of_gt weight
      simp [weightedArcListsWithWordWork, weight, nonzero, paid, free, total, comparisons, words,
        Nat.mul_succ, Nat.add_comm]
      omega
    · have zero : (read e).1 = 0 := Nat.eq_zero_of_not_pos weight
      simp [weightedArcListsWithWordWork, zero, paid, free, total, comparisons, words,
        Nat.mul_succ, Nat.add_comm]
      omega

private theorem forestListWeightWithWordWork_spec {V : Type*} [LinearOrder V] {h : ℕ}
    (read : V × V → ℕ × ℕ) (B : ℕ) (budget : ∀ d, (read d).2 ≤ B)
    (e : HeightForestVertex V h × HeightForestVertex V h) :
    let out := forestDistanceQueryWithWordWork read e
    let old := forestWeightWithDistanceWork read e
    out.1 = old.1 ∧ out.2.1 = old.2 ∧ out.2.2 ≤ 10*h+8*B+34 := by
  obtain ⟨values,work⟩ := forestDistanceQueryWithWordWork_spec read B budget e
  exact ⟨congrArg Prod.fst values,congrArg Prod.snd values,work⟩

variable {V : Type*} [LinearOrder V] {height : ℕ}

local instance : DecidableEq (ForestNetworkVertex V height) :=
  (inferInstance : LinearOrder (ForestNetworkVertex V height)).toDecidableEq

private def copyForestArc : (HeightForestVertex V height × HeightForestVertex V height) ↪
    (ForestNetworkVertex V height × ForestNetworkVertex V height) :=
  forestNetworkCopy.prodMap forestNetworkCopy

private theorem toFinset_map_filter_eq {A B : Type*} [DecidableEq A] [DecidableEq B]
    (copy : A ↪ B) (keep : A → Bool) (xs : List A) :
    ((xs.filter keep).map copy).toFinset = (xs.toFinset.filter (keep ·)).map copy := by
  ext key
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, Finset.mem_map, Finset.mem_filter]

private theorem sum_list_work_le {A : Type*} (rows : List A) (charge : A → ℕ) (bound : ℕ)
    (each : ∀ e, charge e ≤ bound) :
    (rows.map charge).sum ≤ rows.length*bound := by
  induction rows with
  | nil => simp
  | cons e rest ih =>
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm] using
      Nat.add_le_add (each e) ih

/-- Price the two arc classes together, using one table read per link.
Each classified list is already duplicate-free. The second output charges
that pass and the arithmetic for the exact scale and separator fuel. -/
def prepareForestWeightsFromListWithWordWork
    (edges : List (HeightForestVertex V height × HeightForestVertex V height))
    (distinct : edges.Nodup) (read : V × V → ℕ × ℕ) : ForestWeightPlan V height × ℕ :=
  let lift := copyForestArc (V := V) (height := height)
  let weight := forestDistanceQueryWithWordWork read
  let out := weightedArcListsWithWordWork lift weight edges
  let spec := weightedArcListsWithWordWork_spec lift weight edges
  have paid : out.paid.Nodup := spec.1.symm ▸ (distinct.filter _).map lift.injective
  have free : out.free.Nodup := spec.2.1.symm ▸ (distinct.filter _).map lift.injective
  let scale := max 1 out.total
  let bits := bitLengthWithWork scale
  let fuel := max 1 bits.1 * out.total + 1
  (((arcsFromDistinctList out.paid paid,arcsFromDistinctList out.free free),
    (scale,fuel),out.comparisons),out.work+bits.2+18)

theorem prepareForestWeightsFromListWithWordWork_spec
    (edges : List (HeightForestVertex V height × HeightForestVertex V height)) (distinct : edges.Nodup)
    (read : V × V → ℕ × ℕ) (B K : ℕ)
    (readCap : ∀ d, (read d).2 ≤ B) (valueCap : ∀ d, (read d).1 ≤ K) :
    let out := prepareForestWeightsFromListWithWordWork edges distinct read
    out.1 = prepareForestWeights (arcsFromDistinctList edges distinct) (forestWeightWithDistanceWork read) ∧
      out.2 ≤ edges.length*(10*height+8*B+56)+7*(1+edges.length*K)+26 := by
  let copy := copyForestArc (V := V) (height := height)
  let weight := forestDistanceQueryWithWordWork (h := height) read
  let plain := forestWeightWithDistanceWork (height := height) read
  let gathered := weightedArcListsWithWordWork copy weight edges
  let out := prepareForestWeightsFromListWithWordWork edges distinct read
  let scale := max 1 gathered.total
  obtain ⟨paid,free,total,compares,words⟩ := weightedArcListsWithWordWork_spec copy weight edges
  have weightEq (e) : (weight e).1 = (plain e).1 :=
    (forestListWeightWithWordWork_spec read B readCap e).1
  have reportEq (e) : (weight e).2.1 = (plain e).2 :=
    (forestListWeightWithWordWork_spec read B readCap e).2.1
  have workCap (e) : (weight e).2.2 ≤ 10*height+8*B+34 :=
    (forestListWeightWithWordWork_spec read B readCap e).2.2
  have totalEq : gathered.total = ∑ e ∈ edges.toFinset, (plain e).1 := by
    rw [total,List.sum_toFinset _ distinct]
    exact congrArg List.sum (List.map_congr_left fun e _ => weightEq e)
  have comparesEq : gathered.comparisons = ∑ e ∈ edges.toFinset, (plain e).2 := by
    rw [compares,List.sum_toFinset _ distinct]
    exact congrArg List.sum (List.map_congr_left fun e _ => reportEq e)
  have scaleEq : scale = max 1 (∑ e ∈ edges.toFinset, (plain e).1) := congrArg (max 1) totalEq
  have fuelEq : max 1 (bitLengthWithWork scale).1 * gathered.total + 1 =
      ((max 1 (∑ e ∈ edges.toFinset, (plain e).1)).log2+1)*(∑ e ∈ edges.toFinset, (plain e).1)+1 := by
    rw [(bitLengthWithWork_spec scale).1,max_size_eq_log2_add_one,scaleEq,totalEq]
  constructor
  · unfold prepareForestWeightsFromListWithWordWork
    dsimp only
    rw [prepareForestWeights_exact,arcsFromDistinctList_eq edges distinct]
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext (Prod.ext scaleEq fuelEq) comparesEq)
    · dsimp only
      rw [arcsFromDistinctList_eq, paid, toFinset_map_filter_eq]
      simp only [weightEq, decide_eq_true_eq, copy, copyForestArc, plain]
    · dsimp only
      rw [arcsFromDistinctList_eq, free, toFinset_map_filter_eq]
      simp only [weightEq, decide_eq_true_eq, copy, copyForestArc, plain]
  · have value (e) : (weight e).1 ≤ K := by
      rw [weightEq]
      exact valueCap (heightForestLabel e.1,heightForestLabel e.2)
    have price := sum_list_work_le edges (fun e => (weight e).1) K value
    have word := sum_list_work_le edges (fun e => (weight e).2.2) (10*height+8*B+34) workCap
    change gathered.total = _ at total
    change gathered.work = _ at words
    have scaleCap : scale ≤ 1+edges.length*K := by
      unfold scale
      omega
    have overhead := (bitLengthWork_le scale).trans (by
      gcongr)
    change gathered.work+(bitLengthWithWork scale).2+18 ≤ _
    rw [words]
    rw [show 10*height+8*B+56 = (10*height+8*B+34)+22 by omega,Nat.mul_add]
    omega

end OnlineReachabilityPreservers
