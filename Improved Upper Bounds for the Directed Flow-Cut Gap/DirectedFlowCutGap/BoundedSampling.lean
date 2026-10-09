import DirectedFlowCutGap.VertexRounding

/-!
# Removing the minimum-weight dependence from finite sampling

An original all-cost oracle supplies cuts avoiding an explicitly small-mass
set. This is proved by penalties, rather than assumed as a new oracle. The
resulting common-scale recurrence has a horizon bounded by the number of items
and a logarithm of the total weight. These are finite existence statements;
an implementation of the cost oracle is a separate obligation.
-/
namespace DirectedFlowCutGap.BoundedSampling
noncomputable section
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Discarding an item set of total weighted oracle budget at most one quarter
costs a factor two. Strictly positive weights on its complement handle the
zero-potential case without a limiting argument. -/
theorem oracle_avoids_small_mass
    (w : E → ℝ) (α : ℝ) (P : Finset E → Prop) (S : Finset E)
    (hw : ∀ e, 0 ≤ w e) (hα : 0 < α)
    (hsmall : α * ∑ e ∈ S, w e ≤ 1 / 4)
    (hpositive : ∀ e, e ∉ S → 0 < w e)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ α * mwPotential w c)
    (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) :
    ∃ X : Finset E, P X ∧ Disjoint X S ∧
      (∑ e ∈ X, c e) ≤ 2 * α * ∑ e, (if e ∈ S then 0 else c e * w e) := by
  let C : ℝ := ∑ e, (if e ∈ S then 0 else c e * w e)
  let M : ℝ := ∑ e ∈ S, w e
  have hC : 0 ≤ C := by
    apply Finset.sum_nonneg
    intro e he
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hc e) (hw e)
  let K : ℝ := if C = 0 then 1 else 4 * α * C
  have hK : 0 < K := by
    dsimp [K]
    split_ifs with h
    · norm_num
    · exact mul_pos (mul_pos (by norm_num) hα) (lt_of_le_of_ne hC (Ne.symm h))
  let d : E → ℝ := fun e => if e ∈ S then K else c e
  have hd : ∀ e, 0 ≤ d e := fun e => by
    dsimp [d]; split_ifs
    · exact hK.le
    · exact hc e
  have hpotential : mwPotential w d = C + K * M := by
    unfold mwPotential
    have hpoint (e : E) : d e * w e =
        (if e ∈ S then 0 else c e * w e) + K * (if e ∈ S then w e else 0) := by
      by_cases he : e ∈ S <;> simp [d, he]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [C, M]
  obtain ⟨X, hP, hX⟩ := horacle d hd
  rw [hpotential] at hX
  have hbudget : α * (C + K * M) < K := by
    have hm : α * M ≤ 1 / 4 := hsmall
    have hmul := mul_le_mul_of_nonneg_left hm hK.le
    by_cases hz : C = 0
    · have hk : K = 1 := by simp [K, hz]
      rw [hz, hk]
      nlinarith
    · have hk : K = 4 * α * C := by simp [K, hz]
      have hcp : 0 < C := lt_of_le_of_ne hC (Ne.symm hz)
      have hac : 0 < α * C := mul_pos hα hcp
      nlinarith
  have havoid : ∀ e ∈ X, e ∉ S := by
    intro e he hs
    have hsingle : d e ≤ ∑ a ∈ X, d a :=
      Finset.single_le_sum (fun a _ => hd a) he
    have hde : d e = K := by simp [d, hs]
    rw [hde] at hsingle
    linarith
  refine ⟨X, hP, Finset.disjoint_left.mpr havoid, ?_⟩
  have hcost : (∑ e ∈ X, d e) = ∑ e ∈ X, c e := by
    apply Finset.sum_congr rfl
    intro e he
    simp [d, havoid e he]
  rw [hcost] at hX
  change (∑ e ∈ X, c e) ≤ 2 * α * C
  by_cases hz : C = 0
  · have hzero (e : E) (he : e ∈ X) : c e = 0 := by
      have hs := havoid e he
      have hterm : c e * w e ≤ C := by
        have hle := Finset.single_le_sum (f := fun a =>
          if a ∈ S then (0 : ℝ) else c a * w a)
          (fun a _ => by split_ifs; exact le_rfl; exact mul_nonneg (hc a) (hw a))
          (Finset.mem_univ e)
        simpa [C, hs] using hle
      have hwp := hpositive e hs
      have hnon := mul_nonneg (hc e) (hw e)
      have hprod : c e * w e = 0 := by rw [hz] at hterm; linarith
      exact (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hwp)
    simp [Finset.sum_eq_zero hzero, hz]
  · have hk : K = 4 * α * C := by simp [K, hz]
    have hm : α * M ≤ 1 / 4 := hsmall
    have hmul := mul_le_mul_of_nonneg_left hm hK.le
    nlinarith


/-- A cardinality-controlled horizon independent of the smallest positive weight. -/
def horizon (w : E → ℝ) (α : ℝ) : ℕ :=
  ⌈2 * (Fintype.card E : ℝ) *
    Real.log (4 * α * (Fintype.card E : ℝ) * (∑ e, w e) + Fintype.card E)⌉₊ + 1

/-- The original oracle constructs an admissible family at the explicit horizon.
For vertices the linear cardinality factor is `n`; for edges it is the number
of actual items, and this theorem alone does not imply a linear-in-vertices
edge sampling bound. -/
theorem exists_bounded_family
    (w : E → ℝ) (α : ℝ) (P : Finset E → Prop)
    (hm : 0 < Fintype.card E) (hw : ∀ e, 0 ≤ w e) (hα : 0 < α)
    (horacle : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ α * mwPotential w c) :
    ∃ X : Fin (horizon w α) → Finset E,
      (∀ i, P (X i)) ∧
      (∀ i e, w e ≤ (4 * α * (Fintype.card E : ℝ))⁻¹ → e ∉ X i) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
        (horizon w α : ℝ) ≤ 8 * α * w e := by
  let m : ℝ := Fintype.card E
  have hmp : 0 < m := by
    change (0 : ℝ) < (Fintype.card E : ℝ)
    exact_mod_cast hm
  let δ : ℝ := (4 * α * m)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (by positivity)
  let S : Finset E := Finset.univ.filter fun e => w e ≤ δ
  let w' : E → ℝ := fun e => max δ (w e)
  let Q : Finset E → Prop := fun X => P X ∧ Disjoint X S
  have hδid : 4 * α * m * δ = 1 := by
    dsimp [δ]; field_simp
  have hsmall : α * ∑ e ∈ S, w e ≤ 1 / 4 := by
    have hsum : (∑ e ∈ S, w e) ≤ m * δ := by
      calc
        _ ≤ ∑ e ∈ S, δ := Finset.sum_le_sum fun e he => (Finset.mem_filter.mp he).2
        _ = (S.card : ℝ) * δ := by simp
        _ ≤ m * δ := mul_le_mul_of_nonneg_right
          (by change (S.card : ℝ) ≤ (Fintype.card E : ℝ); exact_mod_cast Finset.card_le_univ S) hδ.le
    have := mul_le_mul_of_nonneg_left hsum hα.le
    nlinarith [hδid]
  have hpositive (e : E) (he : e ∉ S) : 0 < w e := by
    have : δ < w e := by simpa [S] using he
    exact hδ.trans this
  have haux : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, Q X ∧ (∑ e ∈ X, c e) ≤ (2 * α) * mwPotential w' c := by
    intro c hc
    obtain ⟨X, hP, hdis, hcost⟩ :=
      oracle_avoids_small_mass w α P S hw hα hsmall hpositive horacle c hc
    refine ⟨X, ⟨hP, hdis⟩, hcost.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * α)
    apply Finset.sum_le_sum
    intro e he
    by_cases hs : e ∈ S
    · simp only [hs, ite_true]
      exact mul_nonneg (hc e) (hδ.le.trans (le_max_left _ _))
    · simp only [hs, ite_false]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (hc e)
  have hW : 0 ≤ ∑ e, w e := Finset.sum_nonneg fun e _ => hw e
  have hsum : (∑ e, w' e) ≤ (∑ e, w e) + m * δ := by
    calc
      _ ≤ ∑ e, (w e + δ) := Finset.sum_le_sum fun e _ =>
        max_le (by linarith [hw e]) (by linarith [hδ])
      _ = _ := by simp [Finset.sum_add_distrib, m]
  let U : ℝ := 4 * α * m * (∑ e, w e) + m
  have hU : 0 < U := by dsimp [U]; positivity
  have hratio : (∑ e, w' e) / δ ≤ U := by
    apply (div_le_iff₀ hδ).2
    have hid : U * δ = (∑ e, w e) + m * δ := by
      dsimp [U]
      nlinarith [hδid]
    rwa [hid]
  have hsumpos : 0 < ∑ e, w' e := by
    obtain ⟨e⟩ := Fintype.card_pos_iff.mp hm
    exact hδ.trans_le ((le_max_left δ (w e)).trans
      (Finset.single_le_sum (fun a _ => hδ.le.trans (le_max_left _ _)) (Finset.mem_univ e)))
  have hlog : Real.log ((∑ e, w' e) / δ) ≤ Real.log U :=
    Real.log_le_log (div_pos hsumpos hδ) hratio
  have hscale : (2 * m)⁻¹ ≤ δ * (2 * α) := by
    have hid : (2 * m) * (δ * (2 * α)) = 1 := by nlinarith [hδid]
    exact (inv_le_iff_one_le_mul₀ (by positivity : 0 < 2 * m)).2 (by nlinarith [hid])
  have ht : Real.log ((∑ e, w' e) / δ) ≤
      (2 * m)⁻¹ * (horizon w α : ℝ) := by
    have hc := Nat.le_ceil (2 * m * Real.log U)
    have hh : 2 * m * Real.log U ≤ (horizon w α : ℝ) := by
      dsimp [horizon, U, m] at *
      push_cast
      linarith
    have hdiv : Real.log U ≤ (horizon w α : ℝ) / (2 * m) :=
      (le_div_iff₀ (by positivity : 0 < 2 * m)).2 (by nlinarith [hh])
    simpa [div_eq_mul_inv, mul_comm] using hlog.trans hdiv
  obtain ⟨X, hQ, hX⟩ := exists_mw_family_of_min_weight w' (2 * α) ((2 * m)⁻¹) δ Q
    hδ (fun _ => le_max_left _ _) (by positivity) (by positivity) hscale haux
    (horizon w α) (Nat.zero_lt_succ _) ht
  refine ⟨X, fun i => (hQ i).1, ?_, ?_⟩
  · intro i e he hi
    exact Finset.disjoint_left.mp (hQ i).2 hi (by simpa [S, δ, m] using he)
  · intro e
    by_cases hs : e ∈ S
    · have habsent : ∀ i, e ∉ X i := fun i hi => Finset.disjoint_left.mp (hQ i).2 hi hs
      simp only [habsent, Finset.filter_false, Finset.card_empty, Nat.cast_zero, zero_div]
      exact mul_nonneg (mul_nonneg (by norm_num) hα.le) (hw e)
    · have hwe : δ ≤ w e := le_of_lt (by simpa [S] using hs)
      calc
        _ ≤ 4 * w' e * (2 * α) := hX e
        _ = 8 * α * w e := by
          rw [show w' e = w e from max_eq_right hwe]
          ring


/-- Specialization to actual graph cuts with a linear-in-vertices horizon.
The approximation factor is explicit; no main flow-cut estimate is assumed. -/
theorem exists_vertex_family
    {G : Digraph E} {w : E → ℝ≥0} {α : ℝ}
    (hm : 0 < Fintype.card E) (hα : 0 < α)
    (h : HasVertexRoundingFactor G w α) :
    ∃ X : Fin (horizon (fun e => (w e : ℝ)) α) → Finset E,
      (∀ i, IsIntegralCut G (X i) (thresholdDemands G w)) ∧
      ∀ e, ((Finset.univ.filter fun i => e ∈ X i).card : ℝ) /
        (horizon (fun e => (w e : ℝ)) α : ℝ) ≤ 8 * α * (w e : ℝ) := by
  obtain ⟨X, hX, _, hmarginal⟩ := exists_bounded_family
    (fun e => (w e : ℝ)) α (fun X => IsIntegralCut G X (thresholdDemands G w))
    hm (fun e => (w e).coe_nonneg) hα h.real_cost_round
  exact ⟨X, hX, hmarginal⟩

end
end DirectedFlowCutGap.BoundedSampling
