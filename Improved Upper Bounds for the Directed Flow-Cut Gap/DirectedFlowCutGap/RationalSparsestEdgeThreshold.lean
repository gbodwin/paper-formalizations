import DirectedFlowCutGap.RationalSparsestEdgeDistances
import DirectedFlowCutGap.RationalHarmonicThreshold

/-! Select the harmonic threshold from a computed distance table. An
unreachable demand supplies a zero-cost cut immediately. An all-zero finite
table is reported separately from a positive threshold. -/
namespace DirectedFlowCutGap.RationalSparsestEdgeThreshold

open scoped BigOperators NNRat NNReal ENNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalSparsestEdgeDistances

inductive Selection (m : ℕ) where
  | unreachable (index : Fin m)
  | zero
  | threshold (index : Fin m) (value : ℚ≥0)

def table {m n : ℕ} (A : Adjacency n) (w : Weights n) (pairs : Vector (Fin n × Fin n) m) :
    Vector (Option ℚ≥0) m :=
  pairs.map (distance A w)

private def finite {m : ℕ} (profile : Vector (Option ℚ≥0) m) (i : Fin m) : ℚ≥0 :=
  profile[i.val].getD 0

private def missing {m : ℕ} (profile : Vector (Option ℚ≥0) m) : Option (Fin m) :=
  (List.finRange m).find? fun i => profile[i.val].isNone

def select {m : ℕ} (profile : Vector (Option ℚ≥0) m) : Selection m :=
  match missing profile with
  | some i => .unreachable i
  | none =>
    match RationalHarmonicThreshold.choose (finite profile) with
    | none => .zero
    | some i =>
      let τ := finite profile i
      if 0<τ then .threshold i τ else .zero

private theorem all_present {m : ℕ} (profile : Vector (Option ℚ≥0) m) (h : missing profile=none)
    (i : Fin m) : profile[i.val]=some (finite profile i) := by
  rw [missing,List.find?_eq_none] at h
  have remains := h i (List.mem_finRange i)
  unfold finite
  cases v : profile[i.val] with
  | none => simp [v] at remains
  | some x => rfl

theorem table_spec {m : ℕ} (profile : Vector (Option ℚ≥0) m) :
    let count := RationalHarmonicThreshold.count (finite profile)
    match select profile with
    | .unreachable i => profile[i.val]=none
    | .zero => ∀ i : Fin m, profile[i.val]=some 0
    | .threshold i τ =>
      (∀ j : Fin m, profile[j.val]=some (finite profile j)) ∧
      profile[i.val]=some τ ∧ 0<τ ∧ 0<count τ ∧
        (∑ j, (finite profile j : ℝ≥0)) ≤
          FiniteHarmonicThreshold.harmonicWeight m * ((τ : ℝ≥0)*(count τ : ℝ≥0)) := by
  unfold select
  dsimp only
  cases absent : missing profile with
  | some i =>
    have none := List.find?_some (p := fun j : Fin m => profile[j.val].isNone) absent
    exact Option.isNone_iff_eq_none.mp none
  | none =>
    let d := finite profile
    have present := all_present profile absent
    by_cases h : 0<∑ i, (d i : ℝ≥0)
    · obtain ⟨i,chosen,pos,count,sparsity⟩ := RationalHarmonicThreshold.choose_spec d h
      change RationalHarmonicThreshold.choose (finite profile)=some i at chosen
      rw [chosen]
      dsimp only
      rw [ite_eq_left pos]
      exact ⟨present,present i,pos,count,sparsity⟩
    · have vanishes (i : Fin m) : d i=0 := by
        have le : (d i : ℝ≥0) ≤ ∑ j, (d j : ℝ≥0) :=
          Finset.single_le_sum (fun j _ => (zero_le : 0≤(d j : ℝ≥0))) (Finset.mem_univ i)
        have zero : (d i : ℝ≥0)=0 := le_antisymm (le.trans (le_of_not_gt h)) zero_le
        exact_mod_cast zero
      have result (i : Fin m) : profile[i.val]=some 0 := by
        rw [present i]
        exact congrArg some (vanishes i)
      cases chosen : RationalHarmonicThreshold.choose (finite profile) with
      | none => exact result
      | some i =>
        dsimp only
        rw [show finite profile i=0 from vanishes i,ite_eq_right (lt_irrefl (0 : ℚ≥0))]
        exact result

def choose {m n : ℕ} (A : Adjacency n) (w : Weights n) (pairs : Vector (Fin n × Fin n) m) : Selection m :=
  select (table A w pairs)

noncomputable def actualDistance {m n : ℕ} (A : Adjacency n) (w : Weights n)
    (pairs : Vector (Fin n × Fin n) m) (i : Fin m) : ℝ≥0 :=
  SparsestEdgeBridge.demandDistance (graph A) (weights w) pairs[i.val]

theorem choose_spec {m n : ℕ} (A : Adjacency n) (w : Weights n) (pairs : Vector (Fin n × Fin n) m) :
    let D := actualDistance A w pairs
    match choose A w pairs with
    | .unreachable i => edgeDistance (graph A) (weights w) pairs[i.val].1 pairs[i.val].2=⊤
    | .zero => ∀ i : Fin m, edgeDistance (graph A) (weights w) pairs[i.val].1 pairs[i.val].2=0
    | .threshold i τ =>
      (∀ j : Fin m, edgeDistance (graph A) (weights w) pairs[j.val].1 pairs[j.val].2≠⊤) ∧
      D i=(τ : ℝ≥0) ∧ 0<τ ∧ 0<(FiniteHarmonicThreshold.above D (τ : ℝ≥0)).card ∧
        (∑ j, D j) ≤ FiniteHarmonicThreshold.harmonicWeight m *
          ((τ : ℝ≥0)*((FiniteHarmonicThreshold.above D (τ : ℝ≥0)).card : ℝ≥0)) := by
  let P := table A w pairs
  let D := actualDistance A w pairs
  have input (i : Fin m) : P[i.val]=distance A w pairs[i.val] := by simp only [P,table,Vector.getElem_map]
  have checks := table_spec P
  change (match select P with
    | .unreachable i => edgeDistance (graph A) (weights w) pairs[i.val].1 pairs[i.val].2=⊤
    | .zero => ∀ i : Fin m, edgeDistance (graph A) (weights w) pairs[i.val].1 pairs[i.val].2=0
    | .threshold i τ =>
      (∀ j : Fin m, edgeDistance (graph A) (weights w) pairs[j.val].1 pairs[j.val].2≠⊤) ∧
      D i=(τ : ℝ≥0) ∧ 0<τ ∧ 0<(FiniteHarmonicThreshold.above D (τ : ℝ≥0)).card ∧
        (∑ j, D j) ≤ FiniteHarmonicThreshold.harmonicWeight m *
          ((τ : ℝ≥0)*((FiniteHarmonicThreshold.above D (τ : ℝ≥0)).card : ℝ≥0)))
  cases found : select P with
  | unreachable i =>
    rw [found] at checks
    change P[i.val]=none at checks
    rw [input i] at checks
    exact (none_iff A w _).mp checks
  | zero =>
    rw [found] at checks
    intro i
    have result : P[i.val]=some 0 := checks i
    rw [input i] at result
    rw [← distance_exact A w pairs[i.val],result]
    simp [observe]
  | threshold i τ =>
    rw [found] at checks
    obtain ⟨present,atIndex,positive,nonempty,score⟩ := checks
    have exact (j : Fin m) : (finite P j : ℝ≥0)=D j :=
      finite_value A w pairs[j.val] ((input j).symm.trans (present j))
    have distanceChoice : (τ : ℝ≥0)=D i := finite_value A w pairs[i.val] ((input i).symm.trans atIndex)
    have count : RationalHarmonicThreshold.count (finite P) τ=(FiniteHarmonicThreshold.above D (τ : ℝ≥0)).card := by
      rw [RationalHarmonicThreshold.count_cast]
      congr 2
      exact funext exact
    refine ⟨?_,distanceChoice.symm,positive,count ▸ nonempty,?_⟩
    · intro j noPath
      have bad := (none_iff A w _).mpr noPath
      rw [← input j,present j] at bad
      cases bad
    · rw [count] at score
      simpa only [exact] using score

end DirectedFlowCutGap.RationalSparsestEdgeThreshold
