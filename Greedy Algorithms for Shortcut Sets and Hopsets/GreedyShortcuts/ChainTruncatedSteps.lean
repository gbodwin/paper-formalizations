import GreedyShortcuts.ChainSaturationSteps

/-! Finite active-step accounting for any fixed excess cutoff. The cap is
bookkeeping for the same raw-greedy run, never an alternate selection rule. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def cappedExcess (H : Finset (V × V)) (b : ℕ) : ℕ :=
  ∑ st∈T.important,min b (T.distance H st.1 st.2-T.endpointFloor st.1 st.2)

theorem cappedExcess_antitone (b : ℕ) : Antitone (fun H => T.cappedExcess H b) := by
  intro H J hHJ
  apply Finset.sum_le_sum
  intro st _
  have hd := T.distance_antitone st.1 st.2 hHJ
  change T.distance J st.1 st.2 ≤ T.distance H st.1 st.2 at hd
  omega

theorem excess_eq_cap_add_layer (H : Finset (V × V)) (b : ℕ) :
    T.excessPotential H = T.cappedExcess H b+T.layerPotential H b := by
  rw [cappedExcess,layerPotential,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro st _
  omega

/-- The cap is exactly the finite mass in the first b excess layers. -/
theorem cappedExcess_eq_layer_sum (H : Finset (V × V)) (b : ℕ) :
    T.cappedExcess H b = ∑ k∈Finset.range b,(T.excessLayer H k).card := by
  induction b with
  | zero => simp [cappedExcess]
  | succ b ih =>
    rw [Finset.sum_range_succ,←ih]
    have h0 := T.excess_eq_cap_add_layer H b
    have h1 := T.excess_eq_cap_add_layer H (b+1)
    have hs := T.layerPotential_step H b
    omega

theorem cappedExcess_le_unsaturated (H : Finset (V × V)) (b : ℕ) :
    T.cappedExcess H b ≤ b*(T.unsaturated H).card := by
  classical
  have he : T.cappedExcess H b =
      ∑ st∈T.unsaturated H,min b (T.distance H st.1 st.2-T.endpointFloor st.1 st.2) := by
    rw [cappedExcess,unsaturated,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro st _
    split_ifs <;> omega
  rw [he]
  calc
    _ ≤ ∑ _st∈T.unsaturated H,b := Finset.sum_le_sum (fun _ _ => min_le_left _ _)
    _ = _ := by simp [Nat.mul_comm]

/-- Exact raw marginal split at an arbitrary fixed integer cutoff. -/
theorem raw_drop_eq_cap_add_layer {H J : Finset (V × V)} (hHJ : H ⊆ J) (b : ℕ) :
    T.potential H-T.potential J =
      (T.cappedExcess H b-T.cappedExcess J b)+
      (T.layerPotential H b-T.layerPotential J b) := by
  have hc := T.cappedExcess_antitone b hHJ
  have hl := T.layerPotential_antitone b hHJ
  change T.cappedExcess J b ≤ T.cappedExcess H b at hc
  change T.layerPotential J b ≤ T.layerPotential H b at hl
  have he := T.excess_drop_eq H J
  rw [T.excess_eq_cap_add_layer H b,T.excess_eq_cap_add_layer J b] at he
  omega

private theorem finite_antitone_budget (q : ℕ → ℕ) (hq : Antitone q)
    (m : ℕ) (B : Finset ℕ) (hB : B ⊆ Finset.range m) :
    (∑ i∈B,(q i-q (i+1))) ≤ q 0 := by
  have ht : ∀ k,(∑ i∈Finset.range k,(q i-q (i+1)))+q k=q 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hk := hq (Nat.le_succ k)
      simp only [Nat.succ_eq_add_one] at *
      omega
  have hh : (∑ i∈B,(q i-q (i+1))) ≤ ∑ i∈Finset.range m,(q i-q (i+1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hB (fun _ _ _ => Nat.zero_le _)
  have hm := ht m
  omega

/-- Any finite set of active steps mostly paid below cutoff b shares one
initial capped-demand budget. There are no selected-endpoint restrictions. -/
theorem cap_dominated_step_budget (D b : ℕ) (hD : 3≤D) (m : ℕ)
    (B : Finset ℕ) (hBm : B ⊆ Finset.range m)
    (hactive : ∀ i∈B,¬T.stopped D ((T.algorithm D (by omega)).run i).1)
    (hdom : ∀ i∈B,
      T.potential ((T.algorithm D (by omega)).run i).1-
          T.potential ((T.algorithm D (by omega)).run (i+1)).1 ≤
        2*(T.cappedExcess ((T.algorithm D (by omega)).run i).1 b-
          T.cappedExcess ((T.algorithm D (by omega)).run (i+1)).1 b)) :
    B.card*D^2 ≤ 50*b*(T.unsaturated ∅).card := by
  classical
  let A := T.algorithm D (by omega)
  let q := fun i => T.cappedExcess (A.run i).1 b
  have hq : Antitone q := antitone_nat_of_succ_le (fun i =>
    T.cappedExcess_antitone b (A.subset_step (A.run i)))
  have ht := finite_antitone_budget q hq m B hBm
  have hf : ∀ i∈B,D^2 ≤ 50*(q i-q (i+1)) := by
    intro i hi
    have h := (T.step_squared_bounds D hD (A.run i) (hactive i hi)).2
    have hd := hdom i hi
    change D^2 ≤ 25*(T.potential (A.run i).1-T.potential (A.run (i+1)).1) at h
    change T.potential (A.run i).1-T.potential (A.run (i+1)).1 ≤ 2*(q i-q (i+1)) at hd
    omega
  calc
    B.card*D^2 = ∑ _i∈B,D^2 := by simp
    _ ≤ ∑ i∈B,50*(q i-q (i+1)) := Finset.sum_le_sum hf
    _ = 50*∑ i∈B,(q i-q (i+1)) := by rw [Finset.mul_sum]
    _ ≤ 50*q 0 := Nat.mul_le_mul_left _ ht
    _ = 50*T.cappedExcess ∅ b := rfl
    _ ≤ 50*(b*(T.unsaturated ∅).card) := Nat.mul_le_mul_left _ (T.cappedExcess_le_unsaturated ∅ b)
    _ = _ := by ring

/-- In the cover regime, b fixed low layers pay for at most 50bn steps.
The complementary steps are not counted by this theorem. -/
theorem cap_dominated_step_linear (D b : ℕ) (hD : 3≤D) (hI : Fintype.card I≤D^2)
    (m : ℕ) (B : Finset ℕ) (hBm : B ⊆ Finset.range m)
    (hactive : ∀ i∈B,¬T.stopped D ((T.algorithm D (by omega)).run i).1)
    (hdom : ∀ i∈B,
      T.potential ((T.algorithm D (by omega)).run i).1-
          T.potential ((T.algorithm D (by omega)).run (i+1)).1 ≤
        2*(T.cappedExcess ((T.algorithm D (by omega)).run i).1 b-
          T.cappedExcess ((T.algorithm D (by omega)).run (i+1)).1 b)) :
    B.card ≤ 50*b*Fintype.card V := by
  have h := T.cap_dominated_step_budget D b hD m B hBm hactive hdom
  have hu : (T.unsaturated ∅).card ≤ Fintype.card V*Fintype.card I :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans T.important_card
  have hnum : B.card*D^2 ≤ (50*b*Fintype.card V)*D^2 := by
    calc
      _ ≤ 50*b*(T.unsaturated ∅).card := h
      _ ≤ 50*b*(Fintype.card V*Fintype.card I) := Nat.mul_le_mul_left _ hu
      _ ≤ 50*b*(Fintype.card V*D^2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hI)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hnum (by positivity)

/-- Every complementary insertion retains more than half its original raw
marginal above the chosen cutoff. It need not maximize that truncated drop. -/
theorem cap_nondominated_retains_layer {H J : Finset (V × V)} (hHJ : H ⊆ J) (b : ℕ)
    (hnot : ¬T.potential H-T.potential J ≤ 2*(T.cappedExcess H b-T.cappedExcess J b)) :
    T.potential H-T.potential J < 2*(T.layerPotential H b-T.layerPotential J b) := by
  have h := T.raw_drop_eq_cap_add_layer hHJ b
  omega

end GreedyShortcuts.ChainDistance.Context
