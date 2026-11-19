import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic

/-! Independent finite samples shared by the directed Steiner routines. -/

namespace OnlineReachabilityPreservers

open Finset

noncomputable def constrainedSamples {I S : Type*} [Fintype I] [Fintype S] (allowed : I → Finset S) :
    Finset (I → S) := by
  classical
  exact univ.filter fun sample => ∀ i, sample i ∈ allowed i

theorem constrainedSamples_card {I S : Type*} [Fintype I] [Fintype S] (allowed : I → Finset S) :
    (constrainedSamples allowed).card = ∏ i, (allowed i).card := by
  classical
  let e : {s // s ∈ constrainedSamples allowed} ≃ ∀ i, {u // u ∈ allowed i} :=
    { toFun := fun s i => ⟨s.1 i, (mem_filter.mp s.2).2 i⟩
      invFun := fun f => ⟨fun i => (f i).1,mem_filter.mpr ⟨mem_univ _,fun i => (f i).2⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => funext fun _ => Subtype.ext rfl }
  rw [← Fintype.card_coe,Fintype.card_congr e,Fintype.card_pi]
  simp

def lowThreshold (m u : ℕ) : Finset (Fin m) := univ.filter fun i => (i:ℕ) < u

theorem lowThreshold_card (m u : ℕ) : (lowThreshold m u).card = min m u := by
  let eqv : {i // i ∈ lowThreshold m u} ≃ Fin (min m u) :=
    { toFun := fun i => ⟨i.1.1, lt_min i.1.isLt (mem_filter.mp i.2).2⟩
      invFun := fun i => ⟨⟨i.1, i.isLt.trans_le (min_le_left _ _)⟩,
        mem_filter.mpr ⟨mem_univ _,i.isLt.trans_le (min_le_right _ _)⟩⟩
      left_inv := fun _ => Subtype.ext (Fin.ext rfl)
      right_inv := fun _ => Fin.ext rfl }
  rw [← Fintype.card_coe,Fintype.card_congr eqv,Fintype.card_fin]

noncomputable def finiteProbability {Ω : Type*} [Fintype Ω] (event : Finset Ω) : ℝ :=
  event.card / (Fintype.card Ω : ℝ)

section Probability

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]

theorem finiteProbability_nonneg (event : Finset A) : 0 ≤ finiteProbability event := by
  unfold finiteProbability
  positivity

theorem finiteProbability_mono {a b : Finset A} (inc : a ⊆ b) :
    finiteProbability a ≤ finiteProbability b := by
  unfold finiteProbability
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card inc)) (by positivity)

theorem finiteProbability_le_one (event : Finset A) : finiteProbability event ≤ 1 := by
  unfold finiteProbability
  by_cases empty : Fintype.card A = 0
  · simp [empty]
  · have pos : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr (Nat.pos_of_ne_zero empty)
    exact (div_le_iff₀ pos).mpr (by simpa only [one_mul] using Nat.cast_le.mpr (Finset.card_le_univ event))

theorem finiteProbability_univ [Nonempty A] : finiteProbability (univ : Finset A) = 1 := by
  simp [finiteProbability, (Nat.cast_pos (α := ℝ).mpr Fintype.card_pos).ne']

theorem finiteProbability_compl [DecidableEq A] [Nonempty A] (event : Finset A) :
    finiteProbability eventᶜ = 1 - finiteProbability event := by
  have nonzero := (Nat.cast_pos (α := ℝ).mpr (Fintype.card_pos (α := A))).ne'
  rw [finiteProbability, card_compl, Nat.cast_sub (Finset.card_le_univ _), sub_div, div_self nonzero]
  rfl

omit [Fintype I] in
theorem finiteProbability_biUnion_le [DecidableEq A] (s : Finset I) (event : I → Finset A) :
    finiteProbability (s.biUnion event) ≤ ∑ i ∈ s, finiteProbability (event i) := by
  unfold finiteProbability
  rw [← Finset.sum_div, ← Nat.cast_sum]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr card_biUnion_le) (by positivity)

theorem finiteProbability_product (a : Finset A) (b : Finset B) :
    finiteProbability (a ×ˢ b) = finiteProbability a * finiteProbability b := by
  simp only [finiteProbability, card_product, Fintype.card_prod, Nat.cast_mul, mul_div_mul_comm]

theorem finiteProbability_constrainedSamples [DecidableEq I] (allowed : I → Finset A) :
    finiteProbability (constrainedSamples allowed) = ∏ i, finiteProbability (allowed i) := by
  classical
  simp only [finiteProbability, constrainedSamples_card, Fintype.card_pi, Nat.cast_prod,
    Finset.prod_div_distrib]

noncomputable def coordinatePreimage (i : I) (event : Finset A) : Finset (I → A) := by
  classical exact univ.filter fun sample => sample i ∈ event

@[simp]
theorem mem_coordinatePreimage {i : I} {event : Finset A} {sample : I → A} :
    sample ∈ coordinatePreimage i event ↔ sample i ∈ event := by simp [coordinatePreimage]

theorem finiteProbability_coordinatePreimage [DecidableEq I] [Nonempty A] (i : I) (event : Finset A) :
    finiteProbability (coordinatePreimage i event) = finiteProbability event := by
  classical
  let allowed := fun j => if j = i then event else univ
  have eq : coordinatePreimage i event = constrainedSamples allowed := by
    ext sample
    simp only [mem_coordinatePreimage, constrainedSamples, mem_filter, mem_univ, true_and]
    refine ⟨fun h j => ?_, fun h => by simpa [allowed] using h i⟩
    by_cases same : j = i
    · simpa [allowed, same] using h
    · simp [allowed, same]
  rw [eq, finiteProbability_constrainedSamples]
  rw [Finset.prod_eq_single i]
  · simp [allowed]
  · intro j _ h
    simp [allowed, h, finiteProbability_univ]
  · simp

end Probability

section Threshold

variable {I : Type*} [Fintype I] [DecidableEq I]

def thresholdPath (m : ℕ) (cutoff : I → ℕ) (path : Finset I) (sample : I → Fin m) : Prop :=
  ∀ i ∈ path, (sample i).val < cutoff i

instance (m : ℕ) (cutoff : I → ℕ) (path : Finset I) (sample : I → Fin m) :
    Decidable (thresholdPath m cutoff path sample) := by
  unfold thresholdPath
  infer_instance

noncomputable def thresholdPathsEvent (m : ℕ) (cutoff : I → ℕ) (path : Finset I) : Finset (I → Fin m) := by
  classical exact univ.filter (thresholdPath m cutoff path)

@[simp]
theorem mem_thresholdPathsEvent {m : ℕ} {cutoff : I → ℕ} {path : Finset I} {sample : I → Fin m} :
    sample ∈ thresholdPathsEvent m cutoff path ↔ thresholdPath m cutoff path sample := by
  simp [thresholdPathsEvent]

theorem thresholdPathsEvent_union (m : ℕ) (cutoff : I → ℕ) (a b : Finset I) :
    thresholdPathsEvent m cutoff (a ∪ b) =
      thresholdPathsEvent m cutoff a ∩ thresholdPathsEvent m cutoff b := by
  classical
  ext f
  simp only [mem_thresholdPathsEvent, mem_inter, thresholdPath, mem_union]
  exact ⟨fun h => ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩,
    fun ⟨hl, hr⟩ i hi => hi.elim (hl i) (hr i)⟩

theorem thresholdPathsEvent_probability {m : ℕ} (mPos : 0 < m)
    (cutoff : I → ℕ) (path : Finset I) (bounded : ∀ i ∈ path, cutoff i ≤ m) :
    finiteProbability (thresholdPathsEvent m cutoff path) =
      ∏ i ∈ path, (cutoff i : ℝ) / m := by
  classical
  let allowed := fun i => if i ∈ path then lowThreshold m (cutoff i) else univ
  have eq : thresholdPathsEvent m cutoff path = constrainedSamples allowed := by
    ext sample
    rw [mem_thresholdPathsEvent]
    simp only [constrainedSamples, mem_filter, mem_univ, true_and, thresholdPath]
    constructor
    · intro okay i
      by_cases h : i ∈ path
      · have above := okay i h
        simp [allowed, h, lowThreshold, above]
      · simp [allowed, h]
    · intro okay i h
      simpa [allowed, h, lowThreshold] using okay i
  rw [eq, finiteProbability, constrainedSamples_card, Nat.cast_prod, Fintype.card_pi,
    Fintype.card_fin, Nat.cast_prod,
    ← Finset.prod_div_distrib]
  have mNe : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr mPos).ne'
  calc
    _ = ∏ i : I, if i ∈ path then (cutoff i : ℝ) / m else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ path
      · simp [allowed, hi, lowThreshold_card, min_eq_right (bounded i hi)]
      · simp [allowed, hi, mNe]
    _ = _ := by rw [← Finset.prod_filter]; simp

end Threshold

end OnlineReachabilityPreservers
