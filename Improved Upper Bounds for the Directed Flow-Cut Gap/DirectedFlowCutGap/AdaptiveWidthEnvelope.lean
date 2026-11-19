import DirectedFlowCutGap.RandomizedEdgeFamilyParameters

/-!
# Original stored widths for the calibrated adaptive edge family

The selected integer factor is computed from the rational input. This
bounds its numerator and denominator in the original stored widths and
bounds the calibrated confidence before applying the fair-bit theorem.
-/

namespace DirectedFlowCutGap.AdaptiveWidthEnvelope

open scoped NNRat BigOperators
open RandomizedEdgeFamily RationalEdgeDecomposition
open NNRatStoredBounds

abbrev StoredWeights {n : ℕ} (w : RationalEdgeThresholds.Weights n) (B : ℕ) : Prop :=
  ∀ s t : Fin n, BinaryRational.StoredBounded w[s.val][t.val] B

private theorem original_width {n B : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (h : StoredWeights w B) (e : Edge n) :
    Bounded (originalWeight adj w e) B := by
  unfold originalWeight
  split
  · exact value_bounded (BinaryFractionalRows.stored_raw_bound (h e.1 e.2))
  · exact mono zero_bounded (Nat.zero_le _)

private theorem total_width {n B : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (h : StoredWeights w B) :
    Bounded (originalTotal adj w) (n*n*(B+1)) := by
  simpa only [originalTotal, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using
    sum_bounded (Finset.univ : Finset (Edge n)) (originalWeight adj w) B (fun e _ => original_width adj w h e)

private theorem ceil_le_num (q : ℚ≥0) : ⌈q⌉₊ ≤ q.num := by
  apply Nat.ceil_le.mpr
  rw [← NNRat.mul_den_eq_num]
  exact le_mul_of_one_le_right zero_le (by exact_mod_cast q.den_pos)

private theorem mass_bits {n B : ℕ} (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (h : StoredWeights w B) :
    (massCeiling adj w).size ≤ n*n*(B+1)+2 := by
  let A := n*n*(B+1)+1
  have htwo : Bounded 2 1 := by
    change (2 : ℕ) ≤ 2 ^ 1 ∧ (1 : ℕ) ≤ 2 ^ 1
    decide
  have hp : Bounded (2 * originalTotal adj w) A := by
    simpa only [A, Nat.add_comm 1] using mul_bounded htwo (total_width adj w h)
  have hceil : massCeiling adj w ≤ 2 ^ A := max_le (Nat.one_le_pow _ _ (by decide))
    ((ceil_le_num _).trans hp.1)
  apply Nat.size_le.mpr
  exact hceil.trans_lt (by
    change 2 ^ A < 2 ^ (A+1)
    rw [pow_succ (2 : ℕ) A]
    have : 0 < 2 ^ A := by positivity
    omega)

private def exponent (r k : ℕ) : ℕ := (r.size + k - 1) / k

private theorem exponent_le (r : ℕ) {k : ℕ} (hk : 0 < k) : exponent r k ≤ r.size :=
  (ceilDiv_le_iff_le_mul hk).mpr (by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right r.size (show 1 ≤ k from hk))

def width (n B M : ℕ) : ℕ := max B (M.size + n + n*n*(B+1) + 3)

theorem calibrated_fits {n k B : ℕ} (hk : 0 < k) (M κ : ℕ)
    (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n)
    (h : StoredWeights w B) : InputFits (calibratedParameters k M κ adj w) (width n B M) := by
  let e := exponent (max 1 n) k
  let f := exponent (massCeiling adj w) 2
  let F := M * (EncodedDyadicRoot.powerTwo e).1 * (EncodedDyadicRoot.powerTwo f).1
  let c := κ+(RationalWeakFamily.edgeRounds n (originalTotal adj w)).size
  have le : (calibratedParameters k M κ adj w).factor ≤ (F:ℚ≥0) :=
    (best_factor_bounds (k:=k) (M:=M) (κ:=c) adj w).1
  obtain ⟨factor,natFactor⟩ : ∃ q : ℕ, (calibratedParameters k M κ adj w).factor=(q:ℚ≥0) := by
    unfold calibratedParameters
    rw [best_factor_nat]
    exact ⟨_,rfl⟩
  have smaller : factor ≤ F := by
    rw [natFactor] at le
    exact_mod_cast le
  have he : e ≤ n+1 :=
    (exponent_le _ hk).trans ((Nat.size_le.mpr Nat.lt_two_pow_self).trans (max_le (by omega) (by omega)))
  have hf : f ≤ n*n*(B+1)+2 := (exponent_le _ (by decide)).trans (mass_bits adj w h)
  have hdeg : M.size + e + f ≤ width n B M := by
    have h := le_max_right B (M.size + n + n*n*(B+1) + 3)
    unfold width
    omega
  have hF : F ≤ 2 ^ width n B M := by
    simp only [F, EncodedDyadicRoot.powerTwo_value]
    calc
      _ ≤ 2 ^ M.size * 2 ^ e * 2 ^ f :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.lt_size_self M).le)
      _ = 2 ^ (M.size + e + f) := by rw [pow_add, pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hdeg
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change (calibratedParameters k M κ adj w).factor.num ≤ _
    rw [natFactor,NNRat.num_natCast]
    exact smaller.trans hF
  · change (calibratedParameters k M κ adj w).factor.den ≤ _
    rw [natFactor,NNRat.den_natCast]
    exact Nat.one_le_pow _ _ (by decide)
  · intro s t
    have hB := le_max_left B (M.size + n + n*n*(B+1) + 3)
    exact ⟨(h s t).1.trans hB, (h s t).2.trans hB⟩

def confidence (n B M κ : ℕ) : ℕ := κ + roundBudget n (width n B M)

theorem calibrated_confidence {n k B : ℕ} (hk : 0 < k) (M κ : ℕ)
    (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n)
    (h : StoredWeights w B) : (calibratedParameters k M κ adj w).confidence ≤ confidence n B M κ := by
  let D := calibratedParameters k M κ adj w
  rw [calibrated_confidence_value]
  change κ + (rounds D).size ≤ confidence n B M κ
  exact Nat.add_le_add_left ((Nat.size_le.mpr Nat.lt_two_pow_self).trans
    (rounds_le D (calibrated_fits hk M κ adj w h))) κ

private theorem read_mono {n B a b : ℕ} (h : a ≤ b) : readBudget n B a ≤ readBudget n B b := by
  unfold readBudget EncodedSolverBits.polynomial
  dsimp only
  gcongr

theorem family_polynomial_reads {n k B : ℕ} (hn : 0 < n) (hk : 0 < k) (M κ : ℕ)
    (hM : 0 < M) (adj : BinaryFractionalWalkOracle.Adjacency n)
    (w : RationalEdgeThresholds.Weights n) (h : StoredWeights w B) :
    FiniteDrawTrees.Within (readBudget n (width n B M) (confidence n B M κ))
      (familyTree (calibratedParameters k M κ adj w)) :=
  FiniteDrawTrees.within_mono
    (familyTree_within hn _ (calibrated_factor_ge_one hM adj w) (calibrated_fits hk M κ adj w h))
    (read_mono (calibrated_confidence hk M κ adj w h))

end DirectedFlowCutGap.AdaptiveWidthEnvelope
