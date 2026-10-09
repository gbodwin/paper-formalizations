import DirectedFlowCutGap.BitSamplerCoupling

/-!
# Literal selection from finite integer masses

The selector scans the retained list, compares with the next mass, and subtracts
that mass when advancing. Its exact finite counting law is proved from those
branches. The ideal law below is only a specification: the existing bounded
fair-bit sampler must still be composed with the selector, and integer masses
must be constructed from the actual retained rational event amounts.

The natural-operation annotation is not a bit-runtime claim. A binary body,
stored-width bounds and the whole-program probability/cost join remain open.
-/
namespace DirectedFlowCutGap.IntegerWeightedChoice
open scoped BigOperators

variable {A : Type*}

def total (xs : List (A × ℕ)) : ℕ := (xs.map Prod.snd).sum

def choose : List (A × ℕ) → ℕ → Option A
  | [], _ => none
  | (a,w)::xs, u => if u < w then some a else choose xs (u-w)

/-- Each branch charges its literal test, return, subtraction and list step. -/
def chooseCharged : List (A × ℕ) → ℕ → Option A × ℕ
  | [], _ => (none,1)
  | (a,w)::xs, u =>
      if u < w then (some a,4) else
        let r := chooseCharged xs (u-w)
        (r.1,r.2+6)

theorem chooseCharged_value (xs : List (A × ℕ)) (u : ℕ) :
    (chooseCharged xs u).1 = choose xs u := by
  induction xs generalizing u with
  | nil => rfl
  | cons x xs ih =>
      rcases x with ⟨a,w⟩
      by_cases h : u<w <;> simp [chooseCharged,choose,h,ih]

theorem chooseCharged_bound (xs : List (A × ℕ)) (u : ℕ) :
    (chooseCharged xs u).2 ≤ 6*xs.length+1 := by
  induction xs generalizing u with
  | nil => simp [chooseCharged]
  | cons x xs ih =>
      rcases x with ⟨a,w⟩
      by_cases h : u<w
      · simp [chooseCharged,h]
      · simp only [chooseCharged,if_neg h,List.length_cons]
        have ht := ih (u-w)
        omega

/-- A bounded draw always chooses an actual positive-mass entry, even when
zero masses occur elsewhere in the list. -/
theorem choose_some {xs : List (A × ℕ)} {u : ℕ} (hu : u < total xs) :
    ∃ a w, choose xs u = some a ∧ (a,w) ∈ xs ∧ 0 < w := by
  induction xs generalizing u with
  | nil => simp [total] at hu
  | cons x xs ih =>
      rcases x with ⟨a,w⟩
      by_cases h : u<w
      · exact ⟨a,w,by simp [choose,h],by simp,by omega⟩
      · have ht : u-w < total xs := by
          simp only [total,List.map_cons,List.sum_cons] at hu
          omega
        obtain ⟨b,v,hb,hm,hv⟩ := ih ht
        exact ⟨b,v,by simpa [choose,h] using hb,by simp [hm],hv⟩

def selectedMass (xs : List (A × ℕ)) (p : A → Bool) : ℕ :=
  (xs.map fun x => if p x.1 then x.2 else 0).sum

/-- Exact counting for the actual prefix-mass branches. -/
theorem selection_count (xs : List (A × ℕ)) (p : A → Bool) :
    (∑ u ∈ Finset.range (total xs), if (choose xs u).any p then 1 else 0) =
      selectedMass xs p := by
  induction xs with
  | nil => simp [total,selectedMass]
  | cons x xs ih =>
      rcases x with ⟨a,w⟩
      simp only [total,List.map_cons,List.sum_cons]
      rw [Finset.sum_range_add]
      have head : (∑ u ∈ Finset.range w,
          if (choose ((a,w)::xs) u).any p then 1 else 0) =
          if p a then w else 0 := by
        calc
          _ = ∑ _u ∈ Finset.range w, if p a then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro u hu
            simp [choose,Finset.mem_range.mp hu]
          _ = _ := by cases hp : p a <;> simp [hp]
      have tail : (∑ u ∈ Finset.range (total xs),
          if (choose ((a,w)::xs) (w+u)).any p then 1 else 0) =
          selectedMass xs p := by
        simpa [choose,show ∀ u : ℕ, ¬w+u<w by omega] using ih
      rw [head,tail]
      simp [selectedMass]

noncomputable section
open FiniteAmplification BitSamplerCoupling

variable [Fintype A]

def law (xs : List (A × ℕ)) (h : 0 < total xs) : PMF (Option A) := by
  letI : NeZero (total xs) := ⟨ne_of_gt h⟩
  exact (PMF.uniformOfFintype (Fin (total xs))).map (fun u => choose xs u.val)

/-- The ideal bounded-uniform input gives exactly the recorded integer-mass
ratio. No approximate fair-bit implementation is identified with this law. -/
theorem law_probability (xs : List (A × ℕ)) (h : 0 < total xs) (p : A → Bool) :
    probability (law xs h) (fun x => x.any p = true) =
      (selectedMass xs p : ℝ) / (total xs : ℝ) := by
  classical
  letI : NeZero (total xs) := ⟨ne_of_gt h⟩
  rw [law,probability_eq_expected_indicator,expectedCost_map]
  have hatom (u : Fin (total xs)) :
      ((PMF.uniformOfFintype (Fin (total xs))) u).toReal = (total xs : ℝ)⁻¹ := by
    simp
  simp only [expectedCost,hatom]
  rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range]
  have hc : (∑ u ∈ Finset.range (total xs),
      if (choose xs u).any p = true then (1 : ℝ) else 0) = (selectedMass xs p : ℝ) := by
    exact_mod_cast selection_count xs p
  rw [hc]
  ring

end
end DirectedFlowCutGap.IntegerWeightedChoice
