import GreedyShortcuts.ChainExcessLayers
import GreedyShortcuts.ChainQuadraticSharp

/-! A universal budget for actual raw-greedy steps dominated by the first
excess layer. The remaining steps retain half their marginal above that layer;
no bound on the number of remaining steps is asserted. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset DirectedPaths
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

private theorem sum_antitone_drops (q : ℕ → ℕ) (hq : Antitone q) (m : ℕ) :
    (∑ i∈Finset.range m,(q i-q (i+1)))+q m=q 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hm := hq (Nat.le_succ m)
    simp only [Nat.succ_eq_add_one] at *
    omega

/-- Any finite collection of active steps whose raw marginal is at most twice
its newly saturated demand count has a single finite initial-demand budget.
The chosen edges may have uncovered or equal-label endpoints. -/
theorem saturation_dominated_step_budget (D : ℕ) (hD : 3 ≤ D) (m : ℕ)
    (B : Finset ℕ) (hBm : B ⊆ Finset.range m)
    (hactive : ∀ i∈B,¬T.stopped D ((T.algorithm D (by omega)).run i).1)
    (hdom : ∀ i∈B,
      T.potential ((T.algorithm D (by omega)).run i).1-
          T.potential ((T.algorithm D (by omega)).run (i+1)).1 ≤
        2*((T.unsaturated ((T.algorithm D (by omega)).run i).1).card-
          (T.unsaturated ((T.algorithm D (by omega)).run (i+1)).1).card)) :
    B.card*D^2 ≤ 50*(T.unsaturated ∅).card := by
  classical
  let A := T.algorithm D (by omega)
  let q := fun i => (T.unsaturated (A.run i).1).card
  have hq : Antitone q := antitone_nat_of_succ_le (fun i =>
    Finset.card_le_card (T.unsaturated_antitone (A.subset_step (A.run i))))
  have ht := sum_antitone_drops q hq m
  have hsum : (∑ i∈B,(q i-q (i+1))) ≤ q 0 := by
    have hh : (∑ i∈B,(q i-q (i+1))) ≤ ∑ i∈Finset.range m,(q i-q (i+1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hBm (fun _ _ _ => Nat.zero_le _)
    omega
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
    _ ≤ 50*q 0 := Nat.mul_le_mul_left _ hsum
    _ = _ := rfl

/-- In the paper's I≤D² cover regime these saturation-dominated active steps
number at most 50n, without a source or selected-endpoint restriction. -/
theorem saturation_dominated_step_linear (D : ℕ) (hD : 3 ≤ D) (hI : Fintype.card I ≤ D^2)
    (m : ℕ) (B : Finset ℕ) (hBm : B ⊆ Finset.range m)
    (hactive : ∀ i∈B,¬T.stopped D ((T.algorithm D (by omega)).run i).1)
    (hdom : ∀ i∈B,
      T.potential ((T.algorithm D (by omega)).run i).1-
          T.potential ((T.algorithm D (by omega)).run (i+1)).1 ≤
        2*((T.unsaturated ((T.algorithm D (by omega)).run i).1).card-
          (T.unsaturated ((T.algorithm D (by omega)).run (i+1)).1).card)) :
    B.card ≤ 50*Fintype.card V := by
  have h := T.saturation_dominated_step_budget D hD m B hBm hactive hdom
  have hu : (T.unsaturated ∅).card ≤ Fintype.card V*Fintype.card I :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans T.important_card
  have hnum : B.card*D^2 ≤ (50*Fintype.card V)*D^2 := by nlinarith
  exact Nat.le_of_mul_le_mul_right hnum (by positivity)

/-- Every insertion not dominated by newly saturated demands retains more
than half its original raw marginal above the first excess layer. -/
theorem nondominated_drop_retains_layer {H J : Finset (V × V)} (hHJ : H ⊆ J)
    (hnot : ¬T.potential H-T.potential J ≤
      2*((T.unsaturated H).card-(T.unsaturated J).card)) :
    T.potential H-T.potential J <
      2*(T.layerPotential H 1-T.layerPotential J 1) := by
  have h := T.raw_drop_eq_saturation_add_layer hHJ
  omega

end GreedyShortcuts.ChainDistance.Context
