import DirectedFlowCutGap.RationalWeakFamily

/-!
# A computable horizon for the floored rational recurrence

The bound uses the size of a rational ceiling, so no evaluation of real
logarithms is needed to compute its round count. It applies to an edge
index set of size n² with total modified weight at most 2W.
-/

namespace DirectedFlowCutGap.RationalWeakFamily

open scoped NNRat BigOperators

def edgeMagnitude (n : ℕ) (W : ℚ≥0) : ℚ≥0 :=
  (n : ℚ≥0) * (2 * W + n)

def edgeRounds (n : ℕ) (W : ℚ≥0) : ℕ :=
  2 * n * (⌈edgeMagnitude n W⌉₊).size + 1

theorem edgeRounds_pos (n : ℕ) (W : ℚ≥0) : 0 < edgeRounds n W := by
  unfold edgeRounds
  omega

theorem edgeRounds_log {n : ℕ} (hn : 0 < n) (W : ℚ≥0) :
    Real.log (edgeMagnitude n W : ℝ) ≤ (2 * (n : ℝ))⁻¹ * (edgeRounds n W : ℝ) := by
  let q := edgeMagnitude n W
  let k := ⌈q⌉₊
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq : 0 < (q : ℝ) := by
    simp only [q, edgeMagnitude, NNRat.cast_mul, NNRat.cast_add, NNRat.cast_ofNat, NNRat.cast_natCast]
    positivity
  have hk : (q : ℝ) ≤ (k : ℝ) := by
    have hqk : q ≤ (k : ℚ≥0) := Nat.le_ceil q
    simpa only [NNRat.cast_natCast] using (NNRat.cast_le (K := ℝ)).2 hqk
  have hb : (k : ℝ) < (2 : ℝ) ^ k.size := by exact_mod_cast Nat.lt_size_self k
  have hl := Real.log_le_log hq (hk.trans hb.le)
  rw [Real.log_pow] at hl
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hdigits : Real.log (q : ℝ) ≤ (k.size : ℝ) := calc
    _ ≤ (k.size : ℝ) * Real.log 2 := hl
    _ ≤ (k.size : ℝ) * 1 := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg _)
    _ = _ := mul_one _
  refine hdigits.trans ?_
  have hn2 : 0 < 2 * (n : ℝ) := by positivity
  rw [inv_mul_eq_div, le_div_iff₀ hn2]
  unfold edgeRounds
  change (k.size : ℝ) * (2 * (n : ℝ)) ≤ ((2 * n * k.size + 1 : ℕ) : ℝ)
  push_cast
  nlinarith

theorem edge_floor_horizon {E : Type} [Fintype E] {n : ℕ} (hn : 0 < n)
    (card : Fintype.card E = n * n) (w : E → ℚ≥0) (W : ℚ≥0)
    (hw : (∑ e, w e) ≤ 2 * W) (e : E) :
    let floor := fun i => max ((n : ℚ≥0)⁻¹) (w i)
    let η := (2 * (n : ℚ≥0))⁻¹
    Real.log ((∑ a, (floor a : ℝ)) / (floor e : ℝ)) ≤ (η : ℝ) * (edgeRounds n W : ℝ) := by
  let N := (n : ℝ)
  let δ := N⁻¹
  let u := fun e => max δ (w e : ℝ)
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast hn
  have hδ : 0 < δ := inv_pos.mpr hN
  have hu (e : E) : δ ≤ u e := le_max_left _ _
  have hsum : (∑ a, u a) ≤ 2 * (W : ℝ) + N := by
    have hR : (∑ e, (w e : ℝ)) ≤ 2 * (W : ℝ) := by
      have h := (NNRat.cast_le (K := ℝ)).2 hw
      simpa only [NNRat.cast_sum, NNRat.cast_mul, NNRat.cast_ofNat] using h
    have heq : (Fintype.card E : ℝ) * δ = N := by
      rw [card, Nat.cast_mul]
      change N * N * N⁻¹ = N
      field_simp
    calc
      (∑ a, u a) ≤ ∑ a, ((w a : ℝ) + δ) := by
        refine Finset.sum_le_sum fun a _ => max_le ?_ ?_
        · linarith [NNRat.cast_nonneg (w a) (α := ℝ)]
        · linarith
      _ = (∑ a, (w a : ℝ)) + N := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, heq]
      _ ≤ _ := add_le_add hR (le_refl N)
  have hs : 0 < ∑ a, u a := hδ.trans_le ((hu e).trans
    (Finset.single_le_sum (fun a _ => hδ.le.trans (hu a)) (Finset.mem_univ e)))
  have hpos : 0 < u e := hδ.trans_le (hu e)
  have hr : (∑ a, u a) / u e ≤ (edgeMagnitude n W : ℝ) := by
    calc
      _ ≤ (∑ a, u a) / δ := div_le_div_of_nonneg_left hs.le hδ (hu e)
      _ ≤ (2 * (W : ℝ) + N) / δ := div_le_div_of_nonneg_right hsum hδ.le
      _ = (edgeMagnitude n W : ℝ) := by
        simp only [edgeMagnitude, NNRat.cast_mul, NNRat.cast_add, NNRat.cast_ofNat, NNRat.cast_natCast, δ,
          div_inv_eq_mul]
        change (2 * (W : ℝ) + N) * N = N * (2 * (W : ℝ) + N)
        exact mul_comm _ _
  have hl := (Real.log_le_log (div_pos hs hpos) hr).trans (edgeRounds_log hn W)
  simpa only [NNRat.cast_inv, NNRat.cast_mul, NNRat.cast_max, NNRat.cast_natCast, NNRat.cast_ofNat,
    N, δ, u] using hl

def runEdge {E : Type} [Fintype E] [DecidableEq E] (n : ℕ) (W α : ℚ≥0) (w : E → ℚ≥0)
    (oracle : (E → ℚ≥0) → Finset E) : History E :=
  runFloored w α ((2 * (n : ℚ≥0))⁻¹) ((n : ℚ≥0)⁻¹) oracle (edgeRounds n W)

theorem runEdge_length {E : Type} [Fintype E] [DecidableEq E] (n : ℕ) (W α : ℚ≥0) (w : E → ℚ≥0)
    (oracle : (E → ℚ≥0) → Finset E) : (runEdge n W α w oracle).cuts.length = edgeRounds n W :=
  run_length ..

theorem runEdge_spec {E : Type} [Fintype E] [DecidableEq E] {n : ℕ} (hn : 0 < n)
    (card : Fintype.card E = n * n) (W α : ℚ≥0) (w : E → ℚ≥0) (P : Finset E → Prop)
    (oracle : (E → ℚ≥0) → Finset E) (hα : 1 ≤ α) (hw : (∑ e, w e) ≤ 2 * W)
    (hfloor : ∀ e, 0 < w e → (n : ℚ≥0)⁻¹ ≤ w e)
    (hOracle : ∀ c : E → ℚ≥0, P (oracle c) ∧ (∑ e ∈ oracle c, c e) ≤ α * ∑ e, c e * w e)
    (hReal : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ (α : ℝ) * mwPotential (fun e => (w e : ℝ)) c) :
    let result := runEdge n W α w oracle
    (∀ X ∈ result.cuts, P X ∧ ∀ e ∈ X, 0 < w e) ∧
      (∀ e, (result.cuts.countP (fun X => decide (e ∈ X)) : ℝ) / (edgeRounds n W : ℝ) ≤
        4 * (w e : ℝ) * α) := by
  have hq : 0 < (n : ℚ≥0) := by exact_mod_cast hn
  have hscale : (2 * (n : ℚ≥0))⁻¹ ≤ (n : ℚ≥0)⁻¹ * α := by
    have hn2 : (n : ℚ≥0) ≤ 2 * (n : ℚ≥0) := by
      rw [two_mul]
      exact le_add_of_nonneg_right zero_le
    exact (inv_anti₀ hq hn2).trans (le_mul_of_one_le_right zero_le hα)
  obtain ⟨hc, ht⟩ := runFloored_spec w α _ _ P oracle (zero_lt_one.trans_le hα) (by positivity)
    (inv_pos.mpr hq) hscale hfloor hOracle hReal (edgeRounds n W) (edge_floor_horizon hn card w W hw)
  exact ⟨hc, fun e => (div_le_iff₀ (Nat.cast_pos.mpr (edgeRounds_pos n W))).mpr (ht e)⟩

end DirectedFlowCutGap.RationalWeakFamily
