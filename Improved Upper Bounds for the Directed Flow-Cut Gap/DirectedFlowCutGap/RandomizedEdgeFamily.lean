import DirectedFlowCutGap.RationalEdgeDecomposition
import DirectedFlowCutGap.CheckedEdgeOracle
import DirectedFlowCutGap.CheckedMWHistory
import DirectedFlowCutGap.NNRatStoredBounds

/-!
# Adaptive edge families with an actual checked cut call per round

The edge solver is called with the current penalized rational prices.
Accepted cuts update the retained history. Each successful history has
the marginal bound, and the full tree has the stated failure bound under
a uniform bound on the ideal expected price for the graph.
-/

namespace DirectedFlowCutGap.RandomizedEdgeFamily

open scoped NNReal NNRat ENNReal BigOperators
open FiniteDrawTrees RationalWeakFamily RationalEdgeDecomposition
open CheckedMWHistory

abbrev Edge (n : ℕ) := Fin n × Fin n

structure Input (n : ℕ) where
  adjacency : BinaryFractionalWalkOracle.Adjacency n
  weights : RationalEdgeThresholds.Weights n
  factor : ℚ≥0
  confidence : ℕ

def adjusted {n : ℕ} (D : Input n) : Edge n → ℚ≥0 := modifiedWeight D.adjacency D.weights
def floored {n : ℕ} (D : Input n) (e : Edge n) : ℚ≥0 := max (n : ℚ≥0)⁻¹ (adjusted D e)
def scale (n : ℕ) : ℚ≥0 := (2 * (n : ℚ≥0))⁻¹
def rounds {n : ℕ} (D : Input n) : ℕ := edgeRounds n (originalTotal D.adjacency D.weights)

def request {n : ℕ} (D : Input n) (c : Edge n → ℚ≥0) : EncodedEdgeLineInput.Input n :=
  ⟨D.adjacency, RationalEdgeThresholds.demands D.adjacency D.weights,
    Vector.ofFn fun s => Vector.ofFn fun t => RawNonnegativeRational.Code.ofNNRat (c (s, t))⟩

def allowance {n : ℕ} (D : Input n) (c : Edge n → ℚ≥0) : ℚ≥0 :=
  D.factor * (∑ e, c e * adjusted D e) / 2

def expectedPriceBound {n : ℕ} (D : Input n) : Prop :=
  ∀ c : Edge n → ℚ≥0, EncodedEdgeSolver.expectedPrice (request D c) EncodedEdgeSolver.massMode ≤
    (allowance D c : ℝ)

private def keep {n : ℕ} (D : Input n) (X : Finset (Edge n)) : Prop :=
  Good D.adjacency D.weights X ∧ ∀ e ∈ X, 0 < adjusted D e

private def checked {n : ℕ} (D : Input n) (s : History (Edge n)) :
    FiniteDrawTrees.Tree (Option (Finset (Edge n))) :=
  CheckedEdgeOracle.mass D.confidence
    (request D (penalizedCosts (adjusted D) D.factor s.costs)) (allowance D s.costs)

def step {n : ℕ} (D : Input n) (s : History (Edge n)) :
    FiniteDrawTrees.Tree (Option (History (Edge n))) :=
  map (Option.map (advance (floored D) D.factor (scale n) s)) (checked D s)

def build {n : ℕ} (D : Input n) : FiniteDrawTrees.Tree (Option (History (Edge n))) :=
  AdaptiveOracleFailure.tree (step D) (rounds D) (some initial)

private theorem query_cost {n : ℕ} (D : Input n) (c : Edge n → ℚ≥0) (X : Finset (Edge n))
    (hX : X ⊆ graphEdges (request D c).graph) :
    CheckedEdgeOracle.costQ (request D c) X = ∑ e ∈ X, c e := by
  unfold CheckedEdgeOracle.costQ
  have hf : X.filter (fun e => (request D c).adjacency[e.1.val][e.2.val] = true) = X :=
    Finset.filter_eq_self.mpr fun e he => (mem_graphEdges _ _).mp (hX he)
  rw [hf]
  simp [request, RawNonnegativeRational.Code.value_ofNNRat]

private theorem floor_pos {n : ℕ} (hn : 0 < n) (D : Input n) (e : Edge n) : 0 < floored D e := by
  have hn' : 0 < (n : ℚ≥0) := by exact_mod_cast hn
  exact (inv_pos.mpr hn').trans_le (le_max_left _ _)

private theorem step_good {n : ℕ} (hn : 0 < n) (D : Input n) (hα : 0 < D.factor)
    (s s' : History (Edge n)) (hs : Invariant (floored D) D.factor (scale n) (keep D) s)
    (h : some s' ∈ (ideal (step D s)).support) :
    Invariant (floored D) D.factor (scale n) (keep D) s' ∧ s'.cuts.length = s.cuts.length + 1 := by
  simp only [step, ideal, law_map] at h
  obtain ⟨result, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  cases result with
  | none => cases he
  | some X =>
    have eq : advance (floored D) D.factor (scale n) s X = s' := Option.some.inj he
    subst s'
    let c := penalizedCosts (adjusted D) D.factor s.costs
    have ha := CheckedEdgeOracle.mass_accepted D.confidence (request D c) (allowance D s.costs) X hr
    have hP : Good D.adjacency D.weights X := ⟨ha.1, ha.2.1⟩
    have hprice := ha.2.2
    rw [query_cost D c X ha.1] at hprice
    have eqPrice : 2 * allowance D s.costs = D.factor * ∑ e, s.costs e * adjusted D e := by
      unfold allowance
      ring
    rw [eqPrice] at hprice
    obtain ⟨hpos, hbound⟩ := penalized_accepted (adjusted D) D.factor s.costs X hprice
    have hfloor : (∑ e ∈ X, s.costs e) ≤ D.factor * ∑ e, s.costs e * floored D e := by
      exact hbound.trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (le_max_right _ _) zero_le) zero_le)
    have hR := (NNRat.cast_le (K := ℝ)).mpr hfloor
    simp only [NNRat.cast_mul, NNRat.cast_sum] at hR
    exact ⟨advance_invariant hs (floor_pos hn D) hα X ⟨hP, hpos⟩ hR, rfl⟩

private theorem stage_good {n : ℕ} (hn : 0 < n) (D : Input n) (hα : 0 < D.factor)
    (T : ℕ) (s s' : History (Edge n)) (hs : Invariant (floored D) D.factor (scale n) (keep D) s)
    (h : some s' ∈ (ideal (AdaptiveOracleFailure.tree (step D) T (some s))).support) :
    Invariant (floored D) D.factor (scale n) (keep D) s' ∧ s'.cuts.length = s.cuts.length + T := by
  induction T generalizing s with
  | zero =>
    have eq : s' = s := by simp [AdaptiveOracleFailure.tree, ideal, law] at h; exact h
    subst s'
    exact ⟨hs, by simp⟩
  | succ T ih =>
    change some s' ∈ (law uniformDraw (FiniteDrawTrees.bind (step D s) (AdaptiveOracleFailure.tree (step D) T))).support at h
    rw [law_bind] at h
    obtain ⟨next, hnxt, hf⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
    cases next with
    | none => cases T <;> simp [AdaptiveOracleFailure.tree, law] at hf
    | some t =>
      obtain ⟨hI, hlen⟩ := step_good hn D hα s t hs hnxt
      obtain ⟨hout, hT⟩ := ih t hI hf
      exact ⟨hout, by omega⟩

private theorem step_failure {n : ℕ} (D : Input n) (hMean : expectedPriceBound D)
    (s : History (Edge n)) :
    ideal (step D s) none ≤ ENNReal.ofReal (((max 1 n : ℕ) : ℝ) ^ (-(D.confidence : ℝ))) := by
  let c := penalizedCosts (adjusted D) D.factor s.costs
  have hB : allowance D c = allowance D s.costs := by
    unfold allowance
    rw [penalized_potential]
  have hfeas : ∃ w, IsFractionalEdgeCut (request D c).graph w {d | d ∈ (request D c).demands} :=
    ⟨fun e => (adjusted D e : ℝ≥0), modified_feasible D.adjacency D.weights⟩
  have hfail := CheckedEdgeOracle.mass_failure D.confidence (request D c)
    (allowance D s.costs) (by simpa only [hB] using hMean c) hfeas
  have he : (Option.map (advance (floored D) D.factor (scale n) s)) ⁻¹' {none} = {none} := by
    ext a
    cases a <;> simp
  change ideal (step D s) none ≤ _
  rw [← PMF.toOuterMeasure_apply_singleton, show ideal (step D s) =
    (ideal (checked D s)).map (Option.map (advance (floored D) D.factor (scale n) s)) from law_map _ _ _,
    PMF.toOuterMeasure_map_apply, he, PMF.toOuterMeasure_apply_singleton]
  exact hfail

theorem failure {n : ℕ} (D : Input n) (hMean : expectedPriceBound D) :
    ideal (build D) none ≤
      (rounds D : ℝ≥0∞) * ENNReal.ofReal (((max 1 n : ℕ) : ℝ) ^ (-(D.confidence : ℝ))) := by
  rw [build, AdaptiveOracleFailure.tree_law]
  exact AdaptiveOracleFailure.iterate_failure _ _ (step_failure D hMean) _ _

theorem successful_family {n : ℕ} (hn : 0 < n) (D : Input n) (hα : 1 ≤ D.factor)
    (s : History (Edge n)) (hs : some s ∈ (ideal (build D)).support) :
    s.cuts.length = rounds D ∧
      (∀ X ∈ s.cuts, Good D.adjacency D.weights X ∧ ∀ e ∈ X, 0 < adjusted D e) ∧
      ∀ e, (occurrences s e : ℝ) / (s.cuts.length : ℝ) ≤
        8 * (originalWeight D.adjacency D.weights e : ℝ) * D.factor := by
  obtain ⟨hI, hlen⟩ := stage_good hn D (zero_lt_one.trans_le hα) (rounds D) initial s (initial_invariant _ _ _ _)
    hs
  have hT : s.cuts.length = rounds D := by simpa [initial] using hlen
  refine ⟨hT, hI.admissible, ?_⟩
  have hn' : 0 < (n : ℚ≥0) := by exact_mod_cast hn
  have hsc (e : Edge n) : scale n ≤ floored D e * D.factor := by
    have h2 : (n : ℚ≥0) ≤ 2 * (n : ℚ≥0) := by
      rw [two_mul]
      exact le_add_of_nonneg_right zero_le
    exact (inv_anti₀ hn' h2).trans ((le_max_left _ _).trans (le_mul_of_one_le_right zero_le hα))
  have hη : 0 < scale n := inv_pos.mpr (by positivity)
  have hsum :(∑ e, adjusted D e) ≤ 2 * originalTotal D.adjacency D.weights := by
    unfold originalTotal
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun e _ => modified_le D.adjacency D.weights e
  have hr (e : Edge n) : Real.log ((∑ a, (floored D a : ℝ)) / (floored D e : ℝ)) ≤
      (scale n : ℝ) * (s.cuts.length : ℝ) := by
    rw [hT]
    exact edge_floor_horizon hn (by simp) (adjusted D) _ hsum e
  intro e
  by_cases he : 0 < adjusted D e
  · have hm := marginal hI (floor_pos hn D) (zero_lt_one.trans_le hα) hη hsc
      (hT.symm ▸ edgeRounds_pos n _) e (hr e)
    have eq : floored D e = adjusted D e := max_eq_right (modified_positive D.adjacency D.weights e he)
    rw [eq] at hm
    refine hm.trans ?_
    have hb : (adjusted D e : ℝ) ≤ 2 * (originalWeight D.adjacency D.weights e : ℝ) := by
      exact_mod_cast modified_le D.adjacency D.weights e
    calc
      _ ≤ 4 * (2 * (originalWeight D.adjacency D.weights e : ℝ)) * D.factor :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) (NNRat.cast_nonneg _)
      _ = _ := by ring
  · have hz : occurrences s e = 0 := by
      apply List.countP_eq_zero.mpr
      intro X hX hmem
      exact he ((hI.admissible X hX).2 e (decide_eq_true_eq.mp hmem))
    simp only [hz, Nat.cast_zero, zero_div]
    positivity

theorem weighted_cost {n : ℕ} (D : Input n) (c : Edge n → ℚ≥0) :
    (weightedEdgeCost (request D c).graph (request D c).cost (fun e => (adjusted D e : ℝ≥0)) : ℝ) =
      ∑ e, (c e : ℝ) * (adjusted D e : ℝ) := by
  classical
  simp only [weightedEdgeCost, NNReal.coe_sum, graphEdges, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : (request D c).graph.Adj e.1 e.2
  · rw [ite_eq_left he]
    simp only [NNReal.coe_mul, EncodedEdgeLineInput.Input.cost, request, Vector.getElem_ofFn,
      RawNonnegativeRational.Code.realValue, RawNonnegativeRational.Code.value_ofNNRat, Fin.eta]
    rfl
  · simp only [he, ite_false]
    have hz : (adjusted D e : ℝ≥0) = 0 := (modifiedWeight_eq D.adjacency D.weights e).trans
      (actualEdgeWeight_of_not_adj _ _ he)
    have hR : (adjusted D e : ℝ) = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) hz
    rw [hR, mul_zero, NNReal.coe_zero]

/-- The expected-price premise is available with a rational factor of the
proved mass-sensitive scale. Computing a sharp factor remains separate. -/
theorem factor_exists (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (adj : BinaryFractionalWalkOracle.Adjacency n)
      (w : RationalEdgeThresholds.Weights n) (κ : ℕ), ∃ α : ℚ≥0,
      1 ≤ α ∧ (α : ℝ) ≤ 2 * (K * (n : ℝ) ^ ε *
        (totalEdgeWeight (BinaryFractionalWalkOracle.graph adj)
          (fun e => (modifiedWeight adj w e : ℝ≥0)) : ℝ) ^ (1 / 2 : ℝ)) + 2 ∧
      expectedPriceBound ⟨adj, w, α, κ⟩ := by
  obtain ⟨K, hK, bound⟩ := EncodedEdgeSolver.mass_expected_uniform ε hε
  refine ⟨K, hK, ?_⟩
  intro n adj w κ
  let m := fun e => (modifiedWeight adj w e : ℝ≥0)
  let W := (totalEdgeWeight (BinaryFractionalWalkOracle.graph adj) m : ℝ)
  let rate := K * (n : ℝ) ^ ε * W ^ (1 / 2 : ℝ)
  let α : ℚ≥0 := ((⌈2 * rate⌉₊ + 1 : ℕ) : ℚ≥0)
  have hr : 0 ≤ rate := by positivity
  have hle : 2 * rate ≤ (⌈2 * rate⌉₊ : ℝ) := Nat.le_ceil _
  have hlt : (⌈2 * rate⌉₊ : ℝ) < 2 * rate + 1 := Nat.ceil_lt_add_one (by positivity)
  have hα : 1 ≤ α := by
    unfold α
    exact_mod_cast Nat.succ_pos ⌈2 * rate⌉₊
  have hcast : (α : ℝ) = (⌈2 * rate⌉₊ : ℝ) + 1 := by
    change (((⌈2 * rate⌉₊ + 1 : ℕ) : ℚ≥0) : ℝ) = _
    rw [NNRat.cast_natCast, Nat.cast_add, Nat.cast_one]
  have hal : rate ≤ (α : ℝ) / 2 := by
    rw [hcast]
    linarith
  refine ⟨α, hα, ?_, ?_⟩
  · change (α : ℝ) ≤ 2 * rate + 2
    rw [hcast]
    linarith
  · intro c
    let D : Input n := ⟨adj, w, α, κ⟩
    have hb := bound n (request D c) m (modified_feasible adj w)
    change EncodedEdgeSolver.expectedPrice (request D c) EncodedEdgeSolver.massMode ≤
      rate * (weightedEdgeCost (request D c).graph (request D c).cost
        (fun e => (adjusted D e : ℝ≥0)) : ℝ) at hb
    rw [weighted_cost] at hb
    refine hb.trans ((mul_le_mul_of_nonneg_right hal (by positivity)).trans_eq ?_)
    change (α : ℝ) / 2 * (∑ e, (c e : ℝ) * (adjusted D e : ℝ)) = (allowance D c : ℝ)
    simp only [allowance, D, NNRat.cast_div, NNRat.cast_mul, NNRat.cast_sum, NNRat.cast_ofNat]
    ring


section FairTapeBudget

open NNRatStoredBounds

/-- The width parameter covers each original stored field and the factor. -/
def InputFits {n : ℕ} (D : Input n) (B : ℕ) : Prop :=
  Bounded D.factor B ∧ ∀ s t : Fin n, BinaryRational.StoredBounded D.weights[s.val][t.val] B

private theorem original_bounded {n B : ℕ} (D : Input n) (h : InputFits D B) (e : Edge n) :
    Bounded (originalWeight D.adjacency D.weights e) B := by
  unfold originalWeight
  split
  · exact value_bounded (BinaryFractionalRows.stored_raw_bound (h.2 e.1 e.2))
  · exact mono zero_bounded (Nat.zero_le _)

private theorem natural_bounded (a : ℕ) : Bounded (a : ℚ≥0) a := by
  have hn : (RawNonnegativeRational.Code.ofNNRat (a : ℚ≥0)).num = a := by
    simp [RawNonnegativeRational.Code.ofNNRat]
  have hd : (RawNonnegativeRational.Code.ofNNRat (a : ℚ≥0)).den = 1 := by
    simp [RawNonnegativeRational.Code.ofNNRat]
  exact ⟨hn ▸ Nat.lt_two_pow_self.le, hd ▸ Nat.one_le_pow _ _ (by decide)⟩

private theorem two_bounded : Bounded 2 1 := by
  change (2 : ℕ) ≤ 2 ^ 1 ∧ (1 : ℕ) ≤ 2 ^ 1
  decide

private theorem inverse_bounded {q : ℚ≥0} {B : ℕ} (h : Bounded q B) : Bounded q⁻¹ B := by
  rw [← one_div]
  simpa only [Nat.zero_add] using div_bounded one_bounded h

def roundBudget (n B : ℕ) : ℕ := 2 * n * (2 * n + n * n * (B + 1) + 3) + 1

theorem rounds_le {n B : ℕ} (D : Input n) (h : InputFits D B) : rounds D ≤ roundBudget n B := by
  have hW : Bounded (originalTotal D.adjacency D.weights) (n*n*(B+1)) := by
    have hh := sum_bounded (Finset.univ : Finset (Edge n))
      (originalWeight D.adjacency D.weights) B (fun e _ => original_bounded D h e)
    simpa only [originalTotal, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using hh
  let q := edgeMagnitude n (originalTotal D.adjacency D.weights)
  have hq : Bounded q (2*n+n*n*(B+1)+2) := by
    have hb := mul_bounded (natural_bounded n)
      (add_bounded (mul_bounded two_bounded hW) (natural_bounded n))
    simpa only [q, edgeMagnitude, show n + (1 + n*n*(B+1) + n + 1) = 2*n+n*n*(B+1)+2 by omega] using hb
  have hc : ⌈q⌉₊ ≤ q.num := by
    apply Nat.ceil_le.mpr
    rw [← NNRat.mul_den_eq_num]
    exact le_mul_of_one_le_right zero_le (by exact_mod_cast q.den_pos)
  have hb := (Nat.size_le_size hc).trans (RawNonnegativeRational.Code.bounded_bits hq).1
  exact Nat.add_le_add_right (Nat.mul_le_mul_left (2*n) hb) 1

private def arithmeticWidth (n B : ℕ) : ℕ := B + n + 2

private theorem adjusted_bounded {n B : ℕ} (D : Input n) (h : InputFits D B) (e : Edge n) :
    Bounded (adjusted D e) (arithmeticWidth n B) := by
  unfold adjusted modifiedWeight
  dsimp only
  split
  · exact mono zero_bounded (Nat.zero_le _)
  · exact mono (mul_bounded two_bounded (original_bounded D h e)) (by unfold arithmeticWidth; omega)

private theorem floored_bounded {n B : ℕ} (D : Input n) (h : InputFits D B) (e : Edge n) :
    Bounded (floored D e) (arithmeticWidth n B) :=
  max_bounded (mono (inverse_bounded (natural_bounded n)) (by unfold arithmeticWidth; omega))
    (adjusted_bounded D h e)

private theorem gain_bounded {n B : ℕ} (D : Input n) (h : InputFits D B) (e : Edge n) :
    Bounded (1 + scale n / (floored D e * D.factor)) (3 * arithmeticWidth n B + 1) := by
  let A := arithmeticWidth n B
  have hη : Bounded (scale n) A := mono (inverse_bounded (mul_bounded two_bounded (natural_bounded n)))
    (by unfold A arithmeticWidth; omega)
  have hα : Bounded D.factor A := mono h.1 (by unfold A arithmeticWidth; omega)
  have hp := add_bounded one_bounded (div_bounded hη (mul_bounded (floored_bounded D h e) hα))
  have he : 0 + (A + (A + A)) + 1 = 3 * A + 1 := by omega
  simpa only [A] using (he ▸ hp)

private def priceBudget (n B : ℕ) : ℕ := (3 * arithmeticWidth n B + 1) * roundBudget n B

private theorem current_bounded {n B : ℕ} (D : Input n) (h : InputFits D B) (s : History (Edge n))
    (hs : Invariant (floored D) D.factor (scale n) (keep D) s)
    (hT : s.cuts.length ≤ roundBudget n B) (e : Edge n) : Bounded (s.costs e) (priceBudget n B) := by
  let gain := 1 + scale n / (floored D e * D.factor)
  have heq : s.costs e = gain ^ occurrences s e := by
    apply (NNRat.cast_injective (α := ℝ))
    have hp := congrFun hs.price_eq e
    simpa only [price, mwCost, gain, NNRat.cast_pow, NNRat.cast_add, NNRat.cast_one,
      NNRat.cast_div, NNRat.cast_mul] using hp
  rw [heq]
  have hocc : occurrences s e ≤ roundBudget n B := List.countP_le_length.trans hT
  exact mono (pow_bounded (gain_bounded D h e) _) (Nat.mul_le_mul_left _ hocc)

private def fieldBudget (n B : ℕ) : ℕ :=
  let A := arithmeticWidth n B
  let C := priceBudget n B
  C + A + n*n*(C+A+1) + 2

private theorem query_bounded {n B : ℕ} (D : Input n) (h : InputFits D B) (s : History (Edge n))
    (hs : Invariant (floored D) D.factor (scale n) (keep D) s)
    (hT : s.cuts.length ≤ roundBudget n B) (e : Edge n) :
    Bounded (penalizedCosts (adjusted D) D.factor s.costs e) (fieldBudget n B - 1) := by
  let A := arithmeticWidth n B
  let C := priceBudget n B
  have hfields (j : Edge n) : Bounded (s.costs j * adjusted D j) (C+A) :=
    mul_bounded (current_bounded D h s hs hT j) (adjusted_bounded D h j)
  have hsum : Bounded (∑ j, s.costs j * adjusted D j) (n*n*(C+A+1)) := by
    have hh := sum_bounded (Finset.univ : Finset (Edge n))
      (fun j => s.costs j * adjusted D j) (C+A) (fun j _ => hfields j)
    simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using hh
  have hα : Bounded D.factor A := mono h.1 (by unfold A arithmeticWidth; omega)
  have hpen := add_bounded (mul_bounded hα hsum) one_bounded
  unfold penalizedCosts
  split
  · apply mono (current_bounded D h s hs hT e)
    unfold fieldBudget
    dsimp only
    omega
  · exact mono hpen (by unfold fieldBudget; dsimp only [A, C]; omega)

private theorem foldr_max_le (a : List ℕ) (B : ℕ) (ha : ∀ v ∈ a, v ≤ B) : a.foldr max 0 ≤ B := by
  induction a with
  | nil => exact Nat.zero_le _
  | cons v a ih => exact max_le (ha v List.mem_cons_self) (ih (fun w hw => ha w (List.mem_cons_of_mem _ hw)))

def readBudget (n B κ : ℕ) : ℕ :=
  roundBudget n B * EncodedSolverBits.polynomial n (EncodedEdgeLineInput.lineSize n)
    (2*n*(n+4)) (fieldBudget n B) κ

private theorem step_budget {n B : ℕ} (D : Input n) (h : InputFits D B) (s : History (Edge n))
    (hs : Invariant (floored D) D.factor (scale n) (keep D) s)
    (hT : s.cuts.length ≤ roundBudget n B) :
    Within (EncodedSolverBits.polynomial n (EncodedEdgeLineInput.lineSize n)
      (2*n*(n+4)) (fieldBudget n B) D.confidence) (step D s) := by
  let c := penalizedCosts (adjusted D) D.factor s.costs
  let R := request D c
  let budget := fieldBudget n B
  have hW (u v : Fin n) : R.costs[u.val][v.val].num.size ≤ budget ∧
      R.costs[u.val][v.val].den.size ≤ budget := by
    have hlocal := RawNonnegativeRational.Code.bounded_bits (query_bounded D h s hs hT (u,v))
    have hB : fieldBudget n B - 1 + 1 = fieldBudget n B := by
      unfold fieldBudget
      dsimp only
      omega
    simpa only [R, request, Vector.getElem_ofFn, Fin.eta, hB, budget] using hlocal
  have hb : 1 ≤ budget := by
    unfold budget fieldBudget
    dsimp only
    omega
  have hi : FractionalCoverRawCore.inputWidth (EncodedEdgeLineInput.lineInput R).costs ≤ budget := by
    unfold FractionalCoverRawCore.inputWidth
    apply foldr_max_le
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    have hlocal := EncodedEdgeLineInput.lineInput_cost_width R hb hW i
    exact max_le hlocal.1 hlocal.2
  have hcap : EncodedSolverBits.edgeBudget D.confidence R ≤ EncodedSolverBits.polynomial n
      (EncodedEdgeLineInput.lineSize n) (2*n*(n+4)) budget D.confidence := by
    dsimp only [EncodedSolverBits.edgeBudget, EncodedSolverBits.polynomial]
    gcongr
  exact within_mono (within_map (CheckedEdgeOracle.mass_within D.confidence R (allowance D s.costs)) _) hcap

theorem within_build {n B : ℕ} (hn : 0 < n) (D : Input n) (hα : 1 ≤ D.factor)
    (h : InputFits D B) : Within (readBudget n B D.confidence) (build D) := by
  let q := EncodedSolverBits.polynomial n (EncodedEdgeLineInput.lineSize n)
    (2*n*(n+4)) (fieldBudget n B) D.confidence
  let safe (i : ℕ) (s : History (Edge n)) :=
    Invariant (floored D) D.factor (scale n) (keep D) s ∧ s.cuts.length = i
  have hs : ∀ i < roundBudget n B, ∀ a, safe i a → Within q (step D a) := by
    intro i hi a ha
    exact step_budget D h a ha.1 (ha.2 ▸ hi.le)
  have hm : ∀ i a b, safe i a → some b ∈ (ideal (step D a)).support → safe (i+1) b := by
    intro i a b ha hb
    obtain ⟨hv, hl⟩ := step_good hn D (zero_lt_one.trans_le hα) a b ha.1 hb
    exact ⟨hv, hl.trans (congrArg (· + 1) ha.2)⟩
  have hi : safe 0 initial := ⟨initial_invariant _ _ _ _, rfl⟩
  have htree := AdaptiveOracleFailure.within_reachable (step D) q (roundBudget n B) safe hs hm
    (rounds D) 0 (some initial) (fun a ha => (Option.some.inj ha) ▸ hi) (by simpa using rounds_le D h)
  exact within_mono htree (Nat.mul_le_mul_right q (rounds_le D h))

theorem build_binary {n : ℕ} (D : Input n) : LazyFairBitTrees.Binary (build D) :=
  AdaptiveOracleFailure.binary_tree (step D) (fun s => LazyFairBitTrees.binary_map
    (CheckedEdgeOracle.mass_binary D.confidence _ (allowance D s.costs)) _) ..

theorem run_fairTape {n B : ℕ} (hn : 0 < n) (D : Input n) (hα : 1 ≤ D.factor) (h : InputFits D B) :
    (EncodedSolverBits.fairTape (readBudget n B D.confidence)).map
      (fun tape => ((EncodedSolverBits.run (build D) tape).map Prod.fst).join) = ideal (build D) := by
  have hel := congrArg (PMF.map Option.join)
    (EncodedSolverBits.run_fairTape (within_build hn D hα h) (build_binary D))
  simp only [PMF.map_comp, Function.comp_def] at hel
  change _ = (ideal (build D)).map id at hel
  rw [PMF.map_id] at hel
  exact hel

theorem tape_failure {n B : ℕ} (hn : 0 < n) (D : Input n) (hα : 1 ≤ D.factor)
    (h : InputFits D B) (hMean : expectedPriceBound D) :
    ((EncodedSolverBits.fairTape (readBudget n B D.confidence)).map
      (fun tape => ((EncodedSolverBits.run (build D) tape).map Prod.fst).join)) none ≤
      (rounds D : ℝ≥0∞) * ENNReal.ofReal (((max 1 n : ℕ) : ℝ) ^ (-(D.confidence : ℝ))) := by
  rw [run_fairTape hn D hα h]
  exact failure D hMean

theorem tape_complete {n B : ℕ} (hn : 0 < n) (D : Input n) (hα : 1 ≤ D.factor)
    (h : InputFits D B) (tape : List Bool) (ht : readBudget n B D.confidence ≤ tape.length) :
    ∃ result used, EncodedSolverBits.run (build D) tape = some (result, (tape.drop used, used)) ∧
      used ≤ readBudget n B D.confidence ∧ ∀ s, result = some s →
        s.cuts.length = rounds D ∧
        (∀ X ∈ s.cuts, Good D.adjacency D.weights X ∧ ∀ e ∈ X, 0 < adjusted D e) ∧
        ∀ e, (occurrences s e : ℝ) / (s.cuts.length : ℝ) ≤
          8 * (originalWeight D.adjacency D.weights e : ℝ) * D.factor := by
  have hb := build_binary D
  obtain ⟨result, used, hr, hu⟩ := EncodedSolverBits.complete (within_build hn D hα h) hb tape ht
  refine ⟨result, used, hr, hu, ?_⟩
  intro s hs
  exact successful_family hn D hα s (hs ▸ EncodedSolverBits.run_support hb hr)

end FairTapeBudget

end DirectedFlowCutGap.RandomizedEdgeFamily
