import DirectedFlowCutGap.RationalWeakFamily
import DirectedFlowCutGap.FiniteMWTrace

/-!
# The potential invariant for each accepted cut

The next cut may depend on all the realized random choices. Exact checked
price and admissibility suffice to extend the invariant on the retained
history. No deterministic total-selector assumption is needed for this
trace-level proof.
-/

namespace DirectedFlowCutGap.CheckedMWHistory

open scoped NNRat BigOperators
open RationalWeakFamily (History)

variable {E : Type} [Fintype E] [DecidableEq E]

def initial : History E := ⟨fun _ => 1, []⟩

def advance (w : E → ℚ≥0) (α η : ℚ≥0) (s : History E) (X : Finset E) : History E :=
  ⟨fun e => s.costs e * (if e ∈ X then 1 + η / (w e * α) else 1), X :: s.cuts⟩

def price {E : Type} (s : History E) (e : E) : ℝ := s.costs e

def occurrences (s : History E) (e : E) : ℕ := s.cuts.countP (fun X => decide (e ∈ X))

structure Invariant (w : E → ℚ≥0) (α η : ℚ≥0) (P : Finset E → Prop) (s : History E) : Prop where
  admissible : ∀ X ∈ s.cuts, P X
  price_eq : price s = mwCost (fun e => (w e : ℝ)) α η (occurrences s)
  potential : mwPotential (fun e => (w e : ℝ)) (price s) ≤
    (∑ e, (w e : ℝ)) * (1 + (η : ℝ)) ^ s.cuts.length

theorem initial_invariant (w : E → ℚ≥0) (α η : ℚ≥0) (P : Finset E → Prop) :
    Invariant w α η P initial := by
  constructor
  · simp [initial]
  · funext e
    simp [initial, price, mwCost, occurrences]
  · simp [initial, price, mwPotential]

theorem positive_price {w : E → ℚ≥0} {α η : ℚ≥0} {P : Finset E → Prop} {s : History E}
    (hi : Invariant w α η P s) (hw : ∀ e, 0 < w e) (hα : 0 < α) (e : E) :
    0 < s.costs e := by
  apply (NNRat.cast_pos (K := ℝ)).mp
  change 0 < price s e
  rw [hi.price_eq]
  exact mwCost_pos _ _ _ (fun a => NNRat.cast_pos.mpr (hw a)) (NNRat.cast_pos.mpr hα) (NNRat.cast_nonneg _) _ e

omit [Fintype E] in
private theorem price_advance (w : E → ℚ≥0) (α η : ℚ≥0) (s : History E) (X : Finset E)
    (e : E) :
    price (advance w α η s X) e = price s e *
      (if e ∈ X then 1 + (η : ℝ) / ((w e : ℝ) * (α : ℝ)) else 1) := by
  by_cases h : e ∈ X <;> simp [advance, price, h]

private theorem potential_advance (w : E → ℚ≥0) (α η : ℚ≥0) (s : History E) (X : Finset E)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) :
    mwPotential (fun e => (w e : ℝ)) (price (advance w α η s X)) =
      mwPotential (fun e => (w e : ℝ)) (price s) + (η : ℝ) / (α : ℝ) * ∑ e ∈ X, price s e := by
  have hp (e : E) : price (advance w α η s X) e * (w e : ℝ) =
      price s e * (w e : ℝ) + if e ∈ X then (η : ℝ) / (α : ℝ) * price s e else 0 := by
    rw [price_advance]
    split_ifs
    · have ha := (NNRat.cast_pos (K := ℝ)).mpr hα
      have he := (NNRat.cast_pos (K := ℝ)).mpr (hw e)
      field_simp [ha.ne', he.ne']
    · ring
  classical
  unfold mwPotential
  simp_rw [hp, Finset.sum_add_distrib]
  simp [Finset.mul_sum]

theorem advance_invariant {w : E → ℚ≥0} {α η : ℚ≥0} {P : Finset E → Prop} {s : History E}
    (hi : Invariant w α η P s) (hw : ∀ e, 0 < w e) (hα : 0 < α)
    (X : Finset E) (hX : P X)
    (hprice : (∑ e ∈ X, price s e) ≤ (α : ℝ) * mwPotential (fun e => (w e : ℝ)) (price s)) :
    Invariant w α η P (advance w α η s X) := by
  constructor
  · intro Y hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact hX
    · exact hi.admissible _ hY
  · funext e
    rw [price_advance, hi.price_eq]
    unfold mwCost occurrences
    dsimp only [advance]
    rw [List.countP_cons]
    by_cases h : e ∈ X
    · simp [h, pow_succ]
    · simp [h]
  · rw [potential_advance w α η _ _ hw hα]
    let W := ∑ e, (w e : ℝ)
    let p := mwPotential (fun e => (w e : ℝ)) (price s)
    have ha := (NNRat.cast_pos (K := ℝ)).mpr hα
    have hη : 0 ≤ (η : ℝ) := NNRat.cast_nonneg _
    have hp := mul_le_mul_of_nonneg_left hprice (div_nonneg hη ha.le)
    have hc : (η : ℝ) / (α : ℝ) * ((α : ℝ) * p) = (η : ℝ) * p := by
      field_simp
    change p + (η : ℝ) / (α : ℝ) * ∑ e ∈ X, price s e ≤ W * (1 + (η : ℝ)) ^ (s.cuts.length + 1)
    rw [pow_succ]
    calc
      _ ≤ p + (η : ℝ) / (α : ℝ) * ((α : ℝ) * p) := add_le_add le_rfl hp
      _ = p * (1 + (η : ℝ)) := by rw [hc]; ring
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hi.potential (by positivity)

theorem marginal {w : E → ℚ≥0} {α η : ℚ≥0} {P : Finset E → Prop} {s : History E}
    (hi : Invariant w α η P s) (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 < η)
    (hscale : ∀ e, η ≤ w e * α) (hT : 0 < s.cuts.length) (e : E)
    (horizon : Real.log ((∑ a, (w a : ℝ)) / (w e : ℝ)) ≤ (η : ℝ) * (s.cuts.length : ℝ)) :
    (occurrences s e : ℝ) / (s.cuts.length : ℝ) ≤ 4 * (w e : ℝ) * α := by
  have hp := hi.potential
  rw [hi.price_eq] at hp
  exact FiniteMWTrace.marginal_le_four _ _ _
    (fun a => NNRat.cast_pos.mpr (hw a)) (NNRat.cast_pos.mpr hα) (NNRat.cast_pos.mpr hη)
    (fun a => by exact_mod_cast hscale a) _ _ hT hp e horizon

end DirectedFlowCutGap.CheckedMWHistory
