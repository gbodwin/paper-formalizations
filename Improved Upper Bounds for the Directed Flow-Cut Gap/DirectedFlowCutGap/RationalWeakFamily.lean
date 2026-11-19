import DirectedFlowCutGap.WeakDecomposition

/-!
# Generating the multiplicative-weights family with rational costs

The recurrence calls the supplied rational cut routine once per round.
It records each cut and carries the actual updated rational prices. The
proof identifies these prices and occurrence counts with the previously
proved real recurrence. The cut oracle and the choice of horizon have
their own certificates.
-/

namespace DirectedFlowCutGap.RationalWeakFamily

open scoped NNReal NNRat BigOperators

variable {E : Type} [Fintype E] [DecidableEq E]

structure History (E : Type) where
  costs : E → ℚ≥0
  cuts : List (Finset E)

def run (w : E → ℚ≥0) (α η : ℚ≥0) (oracle : (E → ℚ≥0) → Finset E) : ℕ → History E
  | 0 => ⟨fun _ => 1, []⟩
  | t + 1 =>
    let history := run w α η oracle t
    let cut := oracle history.costs
    ⟨fun e => history.costs e * (if e ∈ cut then 1 + η / (w e * α) else 1),
      cut :: history.cuts⟩

omit [Fintype E] in
theorem run_length (w : E → ℚ≥0) (α η : ℚ≥0) (oracle : (E → ℚ≥0) → Finset E) (T : ℕ) :
    (run w α η oracle T).cuts.length = T := by
  induction T with
  | zero => rfl
  | succ t ih => simp [run, ih]

open Classical in
private noncomputable def liftOracle (oracle : (E → ℚ≥0) → Finset E)
    (fallback : (E → ℝ) → Finset E) (cost : E → ℝ) : Finset E :=
  if h : ∃ c : E → ℚ≥0, (fun e => (c e : ℝ)) = cost then oracle h.choose else fallback cost

omit [Fintype E] [DecidableEq E] in
private theorem liftOracle_cast (oracle : (E → ℚ≥0) → Finset E)
    (fallback : (E → ℝ) → Finset E) (cost : E → ℚ≥0) :
    liftOracle oracle fallback (fun e => (cost e : ℝ)) = oracle cost := by
  classical
  unfold liftOracle
  split
  · rename_i h
    apply congrArg oracle
    funext e
    exact_mod_cast congrFun h.choose_spec e
  · rename_i h
    exact False.elim (h ⟨cost, rfl⟩)

omit [Fintype E] in
private theorem real_refines (w : E → ℚ≥0) (α η : ℚ≥0) (oracle : (E → ℚ≥0) → Finset E)
    (fallback : (E → ℝ) → Finset E) (T : ℕ) :
    let a := liftOracle oracle fallback
    let wR := fun e => (w e : ℝ)
    let h := run w α η oracle T
    (fun e => (h.costs e : ℝ)) = mwCost wR α η (mwCount wR α η a T) ∧
      (∀ e, h.cuts.countP (fun X => decide (e ∈ X)) = mwCount wR α η a T e) ∧
      (∀ X ∈ h.cuts, ∃ i < T, X = mwCut wR α η a i) := by
  let a := liftOracle oracle fallback
  let wR := fun e => (w e : ℝ)
  induction T with
  | zero => exact ⟨by funext e; simp [run, mwCost, mwCount], by simp [run, mwCount], by simp [run]⟩
  | succ t ih =>
    obtain ⟨hp, hc, hh⟩ := ih
    have hcut : oracle (run w α η oracle t).costs = mwCut wR α η a t := by
      unfold mwCut
      rw [← hp]
      exact (liftOracle_cast oracle fallback _).symm
    refine ⟨?_, ?_, ?_⟩
    · funext e
      rw [mwCost_succ]
      have hcost := congrFun hp e
      simp only [run, hcut, NNRat.cast_mul, hcost]
      split <;> push_cast <;> rfl
    · intro e
      rw [mwCount_succ]
      simp only [run, hcut, List.countP_cons, hc, decide_eq_true_eq]
      split <;> simp
    · intro X hx
      simp only [run, List.mem_cons] at hx
      rcases hx with hx | hx
      · exact ⟨t, Nat.lt_succ_self _, hx.trans hcut⟩
      · obtain ⟨i, hi, he⟩ := hh X hx
        exact ⟨i, hi.trans (Nat.lt_succ_self _), he⟩

/-- The algorithm produces the counted family under an explicit cost-oracle
contract. The fallback is used only in the proof for non-rational costs. -/
theorem run_spec (w : E → ℚ≥0) (α η : ℚ≥0) (P : Finset E → Prop)
    (oracle : (E → ℚ≥0) → Finset E)
    (hw : ∀ e, 0 < w e) (hα : 0 < α) (hη : 0 < η)
    (hscale : ∀ e, η ≤ w e * α)
    (hOracle : ∀ c : E → ℚ≥0, P (oracle c) ∧ (∑ e ∈ oracle c, c e) ≤ α * ∑ e, c e * w e)
    (hReal : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ (α : ℝ) * mwPotential (fun e => (w e : ℝ)) c)
    (T : ℕ) (hT : ∀ e, Real.log ((∑ a, (w a : ℝ)) / (w e : ℝ)) ≤ (η : ℝ) * (T : ℝ)) :
    let result := run w α η oracle T
    (∀ X ∈ result.cuts, P X) ∧
      (∀ e, (result.cuts.countP (fun X => decide (e ∈ X)) : ℝ) ≤ 4 * (w e : ℝ) * α * T) := by
  classical
  let wR := fun e => (w e : ℝ)
  let fallback := mwOracleChoice wR α P hReal
  let choose := liftOracle oracle fallback
  have hchoose (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) :
      P (choose c) ∧ (∑ e ∈ choose c, c e) ≤ (α : ℝ) * mwPotential wR c := by
    by_cases h : ∃ q : E → ℚ≥0, (fun e => (q e : ℝ)) = c
    · obtain ⟨q, rfl⟩ := h
      rw [show choose (fun e => (q e : ℝ)) = oracle q from liftOracle_cast _ _ _]
      refine ⟨(hOracle q).1, ?_⟩
      have hr : ((∑ e ∈ oracle q, q e : ℚ≥0) : ℝ) ≤ ((α * ∑ e, q e * w e : ℚ≥0) : ℝ) :=
        NNRat.cast_le.mpr (hOracle q).2
      simpa only [mwPotential, wR, NNRat.cast_mul, NNRat.cast_sum] using hr
    · simpa only [choose, liftOracle, dite_eq_right h, fallback] using
        mwOracleChoice_spec wR α P hReal c hc
  have hwp (e : E) : 0 < wR e := NNRat.cast_pos.mpr (hw e)
  have hap : 0 < (α : ℝ) := by exact_mod_cast hα
  have hep : 0 < (η : ℝ) := by exact_mod_cast hη
  have hsc (e : E) : (η : ℝ) ≤ wR e * (α : ℝ) := by dsimp [wR]; exact_mod_cast hscale e
  obtain ⟨_, hcounts, hhistory⟩ := real_refines w α η oracle fallback T
  refine ⟨?_, ?_⟩
  · intro X hx
    obtain ⟨i, _, rfl⟩ := hhistory X hx
    exact (hchoose _ (fun e => (mwCost_pos wR α η hwp hap hep.le _ e).le)).1
  · intro e
    rw [hcounts]
    exact mwCount_le_four wR α η hwp hap hep hsc choose
      (fun c hc => (hchoose c hc).2) T e (hT e)

structure DenseHistory (n : ℕ) where
  costs : Vector ℚ≥0 n
  cuts : List (Finset (Fin n))

/-- Store each updated cost once before passing the array to the next oracle. -/
def runDense {n : ℕ} (w : Vector ℚ≥0 n) (α η : ℚ≥0)
    (oracle : Vector ℚ≥0 n → Finset (Fin n)) : ℕ → DenseHistory n
  | 0 => ⟨Vector.ofFn (fun _ => 1), []⟩
  | t + 1 =>
    let history := runDense w α η oracle t
    let cut := oracle history.costs
    ⟨Vector.ofFn fun e => history.costs[e.val] * (if e ∈ cut then 1 + η / (w[e.val] * α) else 1),
      cut :: history.cuts⟩

theorem runDense_refines {n : ℕ} (w : Vector ℚ≥0 n) (α η : ℚ≥0)
    (oracle : Vector ℚ≥0 n → Finset (Fin n)) (T : ℕ) :
    let direct := runDense w α η oracle T
    let spec := run (fun e : Fin n => w[e.val]) α η (fun costs => oracle (Vector.ofFn costs)) T
    direct.costs = Vector.ofFn spec.costs ∧ direct.cuts = spec.cuts := by
  induction T with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    obtain ⟨hc, hcut⟩ := ih
    constructor
    · simp [runDense, run, hc]
    · simp [runDense, run, hc, hcut]

omit [Fintype E] in
theorem cost_power (w : E → ℚ≥0) (α η : ℚ≥0) (oracle : (E → ℚ≥0) → Finset E)
    (T : ℕ) (e : E) :
    let state := run w α η oracle T
    state.costs e = (1 + η / (w e * α)) ^ state.cuts.countP (fun X => decide (e ∈ X)) := by
  induction T with
  | zero => simp [run]
  | succ t ih =>
    by_cases h : e ∈ oracle (run w α η oracle t).costs <;>
      simp [run, h, ih, pow_succ]

theorem dense_width {n : ℕ} (w : Vector ℚ≥0 n) (α η : ℚ≥0)
    (oracle : Vector ℚ≥0 n → Finset (Fin n)) (T B : ℕ) (e : Fin n)
    (hp : let q := (1 + η / (w[e.val] * α)); q.num ≤ 2 ^ B ∧ q.den ≤ 2 ^ B) :
    let cost := (runDense w α η oracle T).costs[e.val]
    cost.num.size ≤ B * T + 1 ∧ cost.den.size ≤ B * T + 1 := by
  let w' (e : Fin n) := w[e.val]
  let oracle' (c : Fin n → ℚ≥0) := oracle (Vector.ofFn c)
  let h := run w' α η oracle' T
  let count := h.cuts.countP (fun X => decide (e ∈ X))
  have ht : count ≤ T := List.countP_le_length.trans (run_length w' α η oracle' T).le
  have he := (runDense_refines w α η oracle T).1
  simp only [he, Vector.getElem_ofFn, Fin.eta, cost_power]
  change ((1 + η / (w[e.val] * α)) ^ count).num.size ≤ _ ∧
    ((1 + η / (w[e.val] * α)) ^ count).den.size ≤ _
  rw [NNRat.num_pow, NNRat.den_pow]
  have narrow {k : ℕ} (hk : k ≤ 2 ^ B) : (k ^ count).size ≤ B * T + 1 := by
    apply Nat.size_le.mpr
    calc
      k ^ count ≤ (2 ^ B) ^ count := Nat.pow_le_pow_left hk _
      _ = 2 ^ (B * count) := (pow_mul ..).symm
      _ ≤ 2 ^ (B * T) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ ht)
      _ < 2 ^ (B * T + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  exact ⟨narrow hp.1, narrow hp.2⟩

def penalizedCosts (w : E → ℚ≥0) (α : ℚ≥0) (c : E → ℚ≥0) : E → ℚ≥0 :=
  let penalty := α * ∑ e, c e * w e
  fun e => if 0 < w e then c e else penalty + 1

omit [DecidableEq E] in
theorem penalized_potential (w : E → ℚ≥0) (α : ℚ≥0) (c : E → ℚ≥0) :
    (∑ e, penalizedCosts w α c e * w e) = ∑ e, c e * w e := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : 0 < w e
  · simp [penalizedCosts, h]
  · have hz : w e = 0 := le_antisymm (le_of_not_gt h) zero_le
    simp [hz]

omit [DecidableEq E] in
theorem penalized_accepted (w : E → ℚ≥0) (α : ℚ≥0) (c : E → ℚ≥0) (X : Finset E)
    (hcost : (∑ e ∈ X, penalizedCosts w α c e) ≤ α * ∑ e, c e * w e) :
    (∀ e ∈ X, 0 < w e) ∧ (∑ e ∈ X, c e) ≤ α * ∑ e, c e * w e := by
  let d := penalizedCosts w α c
  have hpositive (e : E) (he : e ∈ X) : 0 < w e := by
    by_contra h
    have hsingle : d e ≤ ∑ a ∈ X, d a := Finset.single_le_sum (fun _ _ => zero_le) he
    have hbad := hsingle.trans hcost
    simp [d, penalizedCosts, h] at hbad
  refine ⟨hpositive, ?_⟩
  have heq : (∑ e ∈ X, d e) = ∑ e ∈ X, c e := by
    apply Finset.sum_congr rfl
    intro e he
    simp [d, penalizedCosts, hpositive e he]
  change (∑ e ∈ X, d e) ≤ _ at hcost
  rwa [heq] at hcost

omit [DecidableEq E] in
theorem penalized_spec (w : E → ℚ≥0) (α : ℚ≥0) (P : Finset E → Prop)
    (oracle : (E → ℚ≥0) → Finset E)
    (hOracle : ∀ c : E → ℚ≥0, P (oracle c) ∧ (∑ e ∈ oracle c, c e) ≤ α * ∑ e, c e * w e)
    (c : E → ℚ≥0) :
    let X := oracle (penalizedCosts w α c)
    P X ∧ (∀ e ∈ X, 0 < w e) ∧ (∑ e ∈ X, c e) ≤ α * ∑ e, c e * w e := by
  obtain ⟨hP, hcost⟩ := hOracle (penalizedCosts w α c)
  rw [penalized_potential] at hcost
  exact ⟨hP, penalized_accepted w α c _ hcost⟩

def runFloored (w : E → ℚ≥0) (α η δ : ℚ≥0) (oracle : (E → ℚ≥0) → Finset E) (T : ℕ) : History E :=
  run (fun e => max δ (w e)) α η (oracle ∘ penalizedCosts w α) T

theorem runFloored_spec (w : E → ℚ≥0) (α η δ : ℚ≥0) (P : Finset E → Prop)
    (oracle : (E → ℚ≥0) → Finset E) (hα : 0 < α) (hη : 0 < η) (hδ : 0 < δ)
    (hscale : η ≤ δ * α) (hfloor : ∀ e, 0 < w e → δ ≤ w e)
    (hOracle : ∀ c : E → ℚ≥0, P (oracle c) ∧ (∑ e ∈ oracle c, c e) ≤ α * ∑ e, c e * w e)
    (hReal : ∀ c : E → ℝ, (∀ e, 0 ≤ c e) →
      ∃ X : Finset E, P X ∧ (∑ e ∈ X, c e) ≤ (α : ℝ) * mwPotential (fun e => (w e : ℝ)) c)
    (T : ℕ) (hT : ∀ e, Real.log ((∑ a, ((max δ (w a) : ℚ≥0) : ℝ)) /
      ((max δ (w e) : ℚ≥0) : ℝ)) ≤ (η : ℝ) * (T : ℝ)) :
    let result := runFloored w α η δ oracle T
    (∀ X ∈ result.cuts, P X ∧ ∀ e ∈ X, 0 < w e) ∧
      (∀ e, (result.cuts.countP (fun X => decide (e ∈ X)) : ℝ) ≤ 4 * (w e : ℝ) * α * T) := by
  let w' e := max δ (w e)
  let P' (X : Finset E) := P X ∧ ∀ e ∈ X, 0 < w e
  have hm (e : E) : w e ≤ w' e := le_max_right _ _
  have hOracle' (c : E → ℚ≥0) := penalized_spec w α P oracle hOracle c
  have hq (c : E → ℚ≥0) : P' ((oracle ∘ penalizedCosts w α) c) ∧
      (∑ e ∈ (oracle ∘ penalizedCosts w α) c, c e) ≤ α * ∑ e, c e * w' e := by
    exact ⟨⟨(hOracle' c).1, (hOracle' c).2.1⟩, (hOracle' c).2.2.trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hm e) zero_le) zero_le)⟩
  have hr (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) : ∃ X : Finset E, P' X ∧
      (∑ e ∈ X, c e) ≤ (α : ℝ) * mwPotential (fun e => (w' e : ℝ)) c := by
    obtain ⟨X, hP, hav, hcost⟩ := mw_oracle_avoids_zero (fun e => (w e : ℝ)) (α : ℝ) P
      (fun _ => NNRat.cast_nonneg _) (NNRat.cast_nonneg _) hReal c hc
    refine ⟨X, ⟨hP, fun e he => NNRat.cast_pos.mp (hav e he)⟩, hcost.trans ?_⟩
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left
      (NNRat.cast_le.mpr (hm e)) (hc e)) (NNRat.cast_nonneg _)
  obtain ⟨hP, hcount⟩ := run_spec w' α η P' (oracle ∘ penalizedCosts w α)
    (fun _ => hδ.trans_le (le_max_left _ _)) hα hη
    (fun _ => hscale.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le)) hq hr T hT
  refine ⟨hP, ?_⟩
  intro e
  by_cases he : 0 < w e
  · simpa only [runFloored, w', max_eq_right (hfloor e he)] using hcount e
  · have hz : w e = 0 := le_antisymm (le_of_not_gt he) zero_le
    have habs : (runFloored w α η δ oracle T).cuts.countP (fun X => decide (e ∈ X)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro X hx hmem
      exact he ((hP X hx).2 e (decide_eq_true_eq.mp hmem))
    simp [habs, hz]

end DirectedFlowCutGap.RationalWeakFamily
