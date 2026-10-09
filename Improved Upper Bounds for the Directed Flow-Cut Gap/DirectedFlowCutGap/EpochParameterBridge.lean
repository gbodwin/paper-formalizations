import DirectedFlowCutGap.SubpolynomialBounds
import DirectedFlowCutGap.PathSystemCharging
import DirectedFlowCutGap.CandidateSchedule
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Exact graph denominators and uniform epoch parameter bounds

The graph theorem is applied at the state's actual attained-candidate cap.
Only its numerical denominator is then increased to the global envelope.
The resulting exact denominator and concrete expected-cost expression are
subpolynomial, with constants selected before the positive input size.
These adapters do not assert an algorithmic or flow-cut theorem.
-/

namespace DirectedFlowCutGap.EpochParameterBridge

noncomputable section
open scoped BigOperators NNReal ENNReal
open SubpolynomialBounds

/-- The actual binary-log recursion depth is bounded by the padded real-log depth. -/
theorem log2_add_two_le_H {n : ℕ} (hn : 1 ≤ n) : Nat.log2 n + 2 ≤ H n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (Nat.log2 n : ℝ) ≤ Real.log ((n : ℝ) + 2) / Real.log 2 := by
    exact (Real.log2_le_logb n).trans
      (div_le_div_of_nonneg_right (Real.log_le_log hnpos (by linarith)) htwo.le)
  have hceil := Nat.le_ceil (Real.log ((n : ℝ) + 2) / Real.log 2)
  have hreal : ((Nat.log2 n + 2 : ℕ) : ℝ) ≤ (H n : ℝ) := by
    simp only [H, Nat.cast_add, Nat.cast_ofNat]
    linarith
  exact_mod_cast hreal

theorem log2_add_two_real_le_H {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log2 n : ℝ) + 2 ≤ (H n : ℝ) := by
  exact_mod_cast log2_add_two_le_H hn

theorem log2_add_two_subpolynomial :
    Subpolynomial (fun n => (Nat.log2 n : ℝ) + 2) := by
  apply H_add_one_subpolynomial.mono
  intro n hn
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact (log2_add_two_real_le_H hn).trans (by linarith)

/-- The exact denominator in `PathSystemCharging.exists_stable_graph_value`. -/
def graphDenominator (n : ℕ) (b s : ℝ) : ℝ :=
  2048 * b * s * (256 * b) ^ 4 * ((Nat.log2 n : ℝ) + 2)

/-- Substitute the proved global cap and restart envelopes without changing constants. -/
def K (n : ℕ) : ℝ := graphDenominator n (B n) (r n)

theorem graphDenominator_pos (n : ℕ) {b s : ℝ} (hb : 0 < b) (hs : 0 < s) :
    0 < graphDenominator n b s := by
  unfold graphDenominator
  positivity

theorem K_pos (n : ℕ) : 0 < K n := graphDenominator_pos n (B_pos n) (r_pos n)

/-- Monotonicity concerns the numerical factor, not the optimization domain. -/
theorem graphDenominator_mono_cap (n : ℕ) {b c s : ℝ}
    (hb : 0 ≤ b) (hbc : b ≤ c) (hs : 0 ≤ s) :
    graphDenominator n b s ≤ graphDenominator n c s := by
  have hc : 0 ≤ c := hb.trans hbc
  unfold graphDenominator
  gcongr

theorem graphDenominator_le_K (n : ℕ) {b : ℝ}
    (hb : 1 ≤ b) (hB : b ≤ B n) : graphDenominator n b (r n) ≤ K n :=
  graphDenominator_mono_cap n (by linarith) hB (r_pos n).le

/-- A value inequality may be weakened after the actual-cap graph theorem is applied. -/
theorem value_bound_of_cap_le {n : ℕ} {b c s mass value : ℝ}
    (hb : 0 < b) (hbc : b ≤ c) (hs : 0 < s) (hmass : 0 ≤ mass)
    (hvalue : mass / graphDenominator n b s ≤ value) :
    mass / graphDenominator n c s ≤ value :=
  (div_le_div_of_nonneg_left hmass (graphDenominator_pos n hb hs)
    (graphDenominator_mono_cap n hb.le hbc hs.le)).trans hvalue

theorem K_subpolynomial : Subpolynomial K := by
  exact ((((Subpolynomial.const 2048).mul B_subpolynomial).mul r_subpolynomial).mul
    (((Subpolynomial.const 256).mul B_subpolynomial).pow 4)).mul
      log2_add_two_subpolynomial

/-- The quantifier order is explicit for the exact graph denominator. -/
theorem K_uniform_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → K n ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := K_subpolynomial ε hε
  exact ⟨C, hC, fun n hn => (le_abs_self (K n)).trans (hbound n hn)⟩

theorem confidence_log_nonneg (q n : ℕ) :
    0 ≤ Real.log (((J n : ℝ) + 1) * ((n : ℝ) + 2) ^ q) := by
  apply Real.log_nonneg
  have hJ : (1 : ℝ) ≤ (J n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (J n)
    linarith
  have hn : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  exact one_le_mul_of_one_le_of_one_le hJ (one_le_pow₀ hn)

theorem confidence_log_subpolynomial (q : ℕ) :
    Subpolynomial (fun n => Real.log (((J n : ℝ) + 1) * ((n : ℝ) + 2) ^ q)) := by
  apply (log_union_bound_subpolynomial q).mono
  intro n _
  have h := confidence_log_nonneg q n
  rw [abs_of_nonneg h, abs_of_nonneg (by linarith)]
  linarith

/-- The concrete cost envelope with any fixed natural confidence exponent. -/
def expectedCostEnvelope (q n : ℕ) : ℝ :=
  ((J n : ℝ) + 1) *
    (r n * K n * Real.log (((J n : ℝ) + 1) * ((n : ℝ) + 2) ^ q) + B n + 1)

theorem expectedCostEnvelope_pos (q n : ℕ) : 0 < expectedCostEnvelope q n := by
  have hr := r_pos n
  have hK := K_pos n
  have hB := B_pos n
  have hlog := confidence_log_nonneg q n
  unfold expectedCostEnvelope
  positivity

theorem expectedCostEnvelope_subpolynomial (q : ℕ) :
    Subpolynomial (expectedCostEnvelope q) :=
  J_add_one_subpolynomial.mul
    ((((r_subpolynomial.mul K_subpolynomial).mul
      (confidence_log_subpolynomial q)).add B_subpolynomial).add
      (Subpolynomial.const 1))

/-- Every positive exponent has one positive constant valid at every positive size. -/
theorem expectedCostEnvelope_uniform_bound (q : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 1 ≤ n → expectedCostEnvelope q n ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := expectedCostEnvelope_subpolynomial q ε hε
  exact ⟨C, hC, fun n hn => (le_abs_self _).trans (hbound n hn)⟩

/-- The global hard-regime assumption supplies the actual state's scale inequality. -/
theorem hard_regime_of_global {n : ℕ} {b L : ℝ} (hb : b ≤ B n)
    (hglobal : 64 * B n ≤ (n : ℝ) ^ ((1 : ℝ) / 3))
    (hL : (n : ℝ) ^ ((1 : ℝ) / 3) ≤ L) : 64 * b ≤ L :=
  (mul_le_mul_of_nonneg_left hb (by norm_num)).trans (hglobal.trans hL)

/-- The real cube-root scale supplies the graph theorem's integer-power condition. -/
theorem size_le_cube_of_cuberoot_le {n : ℕ} {L : ℝ}
    (hL : (n : ℝ) ^ ((1 : ℝ) / 3) ≤ L) : (n : ℝ) ≤ L ^ (3 : ℕ) := by
  have hroot : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (n : ℝ) := by
    simpa only [Nat.cast_ofNat, one_div] using
      Real.rpow_inv_natCast_pow (Nat.cast_nonneg (α := ℝ) n) (by norm_num : (3 : ℕ) ≠ 0)
  rw [← hroot]
  exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg n) _) hL 3

/-- All real-positive hard-regime side conditions follow at the actual cap. -/
theorem hard_regime_graph_domain {n : ℕ} {b L : ℝ} (hb : 1 ≤ b)
    (hB : b ≤ B n) (hglobal : 64 * B n ≤ (n : ℝ) ^ ((1 : ℝ) / 3))
    (hL : (n : ℝ) ^ ((1 : ℝ) / 3) ≤ L) :
    0 < L ∧ 64 * b ≤ L ∧ (n : ℝ) ≤ L ^ (3 : ℕ) := by
  have hactual := hard_regime_of_global hB hglobal hL
  exact ⟨by linarith, hactual, size_le_cube_of_cuberoot_le hL⟩

/-- One size threshold handles every actual cap below the proved envelope. -/
theorem exists_uniform_hard_regime_threshold :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ b : ℝ, b ≤ B n → 64 * b ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by
  obtain ⟨n₀, hn₀, hbound⟩ :=
    exists_hard_regime_threshold (show (0 : ℝ) < 1 / 3 by norm_num)
  exact ⟨n₀, hn₀, fun n hn b hb =>
    (mul_le_mul_of_nonneg_left hb (by norm_num)).trans (hbound n hn)⟩

section StateBridge

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : Digraph V} {D : Finset (V × V)} {L : ℝ≥0}

/-- Convert the actual finite remaining-label sum into the graph theorem's label type. -/
theorem state_sum_outsideMass (S : CandidateSchedule.State G D L)
    (w : (V × V) → V → ℝ≥0) :
    (∑ p : S.remaining, (CandidateOptimization.outsideMass S.cut (w p) : ℝ)) =
      (EpochAccounting.familyMass S.remaining S.cut w : ℝ) := by
  rw [EpochAccounting.familyMass, NNReal.coe_sum]
  exact (Finset.sum_subtype S.remaining (fun _ => Iff.rfl)
    (fun p : V × V => (CandidateOptimization.outsideMass S.cut (w p) : ℝ))).symm

/-- Apply graph charging to the attained candidates at the state's actual cap.
In particular, candidate minimality is never transferred to an enlarged cap. -/
theorem exists_state_graph_value (S : CandidateSchedule.State G D L) (s : ℝ≥0)
    (hB : 1 ≤ S.scale) (hL : 64 * (S.scale : ℝ) ≤ (L : ℝ))
    (hs : 1 < s) (hready : S.Ready s) (hpositive : S.optimum ≠ 0)
    (hLn : (L : ℝ) ≤ Fintype.card V) (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ 3) :
    ∃ u v, LevelResidualPath G S.cut u v ∧
      (S.mass : ℝ) * ((L : ℝ) / Fintype.card V) ^ (3 / 2 : ℝ) /
        graphDenominator (Fintype.card V) S.scale s ≤
      ∑ p ∈ S.remaining, (levelSeparationValue G (S.weight p) p.1 u v).toReal := by
  classical
  have hBR : (1 : ℝ) ≤ S.scale := by exact_mod_cast hB
  have hsR : (1 : ℝ) < s := by exact_mod_cast hs
  have hLp : (0 : ℝ) < L := by linarith
  have hnpos : 0 < Fintype.card V := by
    have : (0 : ℝ) < Fintype.card V := hLp.trans_le hLn
    exact_mod_cast this
  let : Nonempty V := Fintype.card_pos_iff.mp hnpos
  have hmass := state_sum_outsideMass S S.weight
  have hopt := state_sum_outsideMass S S.candidate
  change _ = (S.mass : ℝ) at hmass
  change _ = (S.optimum : ℝ) at hopt
  have hstable : (S.mass : ℝ) ≤ (s : ℝ) * (S.optimum : ℝ) := by
    exact_mod_cast S.stable_gate s hready hpositive
  have hmasspos : (0 : ℝ) < S.mass := by
    have hmassone : 1 ≤ S.mass := (S.one_le_optimum hpositive).trans S.optimum_le_mass
    have : (1 : ℝ) ≤ S.mass := by exact_mod_cast hmassone
    linarith
  obtain ⟨u, v, hR, hvalue⟩ := PathSystemCharging.exists_stable_graph_value G
    (fun p : S.remaining => p.val) (fun p => S.weight p) (fun p => S.candidate p) S.cut
    hBR hL hsR hLn hnL
    (fun p => S.feasible p p.property p.val.1 p.val.2 (Set.mem_singleton _))
    (fun p v hv => by exact_mod_cast S.cap p p.property v hv)
    (fun p z hz => by
      have hz' : CandidateOptimization.IsCandidate G {p.val} S.cut
          ((4 * S.scale) / L) z := by
        have hcap_eq : (4 * S.scale / L : ℝ≥0) =
            ⟨4 * (S.scale : ℝ) / (L : ℝ), by positivity⟩ := by
          ext
          change ((4 * S.scale / L : ℝ≥0) : ℝ) = 4 * (S.scale : ℝ) / (L : ℝ)
          simp
        rw [hcap_eq]
        exact hz
      exact_mod_cast (S.candidate_spec p.property).2.2 z hz')
    (by simpa only [hmass, hopt] using hstable)
    (by simpa only [hmass] using hmasspos)
  refine ⟨u, v, hR, ?_⟩
  have hvalues : (∑ p : S.remaining,
      (levelSeparationValue G (S.weight p) p.val.1 u v).toReal) =
      ∑ p ∈ S.remaining, (levelSeparationValue G (S.weight p) p.1 u v).toReal :=
    (Finset.sum_subtype S.remaining (fun _ => Iff.rfl)
      (fun p : V × V => (levelSeparationValue G (S.weight p) p.1 u v).toReal)).symm
  simpa only [hmass, graphDenominator, hvalues] using hvalue

/-- The global denominator is introduced only after actual-cap charging succeeds. -/
theorem exists_state_graph_value_global (S : CandidateSchedule.State G D L)
    (hB : 1 ≤ S.scale) (hBglobal : (S.scale : ℝ) ≤ B (Fintype.card V))
    (hL : 64 * (S.scale : ℝ) ≤ (L : ℝ))
    (hready : S.Ready ⟨r (Fintype.card V), (r_pos _).le⟩)
    (hpositive : S.optimum ≠ 0)
    (hLn : (L : ℝ) ≤ Fintype.card V) (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ 3) :
    ∃ u v, LevelResidualPath G S.cut u v ∧
      (S.mass : ℝ) * ((L : ℝ) / Fintype.card V) ^ (3 / 2 : ℝ) / K (Fintype.card V) ≤
      ∑ p ∈ S.remaining, (levelSeparationValue G (S.weight p) p.1 u v).toReal := by
  have hs : (1 : ℝ≥0) < ⟨r (Fintype.card V), (r_pos _).le⟩ :=
    one_lt_r (Fintype.card V)
  obtain ⟨u, v, hR, hvalue⟩ := exists_state_graph_value S _ hB hL hs hready hpositive hLn hnL
  refine ⟨u, v, hR, ?_⟩
  exact value_bound_of_cap_le
    (by
      have : (1 : ℝ) ≤ S.scale := by exact_mod_cast hB
      linarith)
    hBglobal (r_pos _) (by positivity) hvalue

end StateBridge
end
end DirectedFlowCutGap.EpochParameterBridge
