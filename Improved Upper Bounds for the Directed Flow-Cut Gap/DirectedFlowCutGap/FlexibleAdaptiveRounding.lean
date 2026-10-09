import DirectedFlowCutGap.FlexibleCandidateSchedule
import DirectedFlowCutGap.AdaptiveCost

/-!
# A distinct adaptive law for any exact-family provider

This law installs the supplied provider, then uses the unchanged generic epoch
law. Its support and expectation bounds are proved directly. No equality to
the compact-selector law or to its sampled weight vectors is assumed.
-/
namespace DirectedFlowCutGap.FlexibleAdaptiveRounding
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal ENNReal
open CandidateSchedule CandidateSchedule.State AdaptiveEpoch AdaptiveRounding AdaptiveCost
open FlexibleCandidateSchedule FiniteAmplification EpochParameterBridge
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : Digraph V} {D : Finset (V × V)} {L : ℝ≥0}
variable (P : FamilyProvider G D L)

/-- Fuel is the initial number of labels. Every nonterminal epoch uses at least
one label, so this recursion is finite for every sample sequence. -/
def solve (P : FamilyProvider G D L) (r : ℝ≥0) (hr : 1 < r) : ℕ → State G D L → PMF (State G D L)
  | 0, S => PMF.pure (S.selectedStabilize P r hr)
  | fuel + 1, S =>
      let T := S.selectedStabilize P r hr
      if T.optimum = 0 then PMF.pure T else
        (samplePMF G (fun p : Label T => T.weight p.val) (fun p => p.val.1)).bind
          (fun ω => solve P r hr fuel (epoch r T ω).state)

/-- Every supported output is connected to the input by an actual finite
optimizer-and-level-cut trace, installing the supplied family at each restart. -/
theorem solve_support_execution (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ)
    (S : State G D L) {T : State G D L} (hT : T ∈ (solve P r hr fuel S).support) :
    ∃ k q, Trace P r S k q T := by
  induction fuel generalizing S with
  | zero =>
      have he : T = S.selectedStabilize P r hr := by simpa [solve] using hT
      subst T
      refine ⟨S.selectedRestartCount P r hr, 0, ?_⟩
      simpa [State.selectedStabilize] using
        (Trace.stabilize_prefix (Trace.start (S₀ := S)) hr (j := S.selectedRestartCount P r hr) le_rfl)
  | succ fuel ih =>
      simp only [solve] at hT
      split_ifs at hT with hz
      · have he : T = S.selectedStabilize P r hr := by simpa using hT
        subst T
        refine ⟨S.selectedRestartCount P r hr, 0, ?_⟩
        simpa [State.selectedStabilize] using
          (Trace.stabilize_prefix (Trace.start (S₀ := S)) hr (j := S.selectedRestartCount P r hr) le_rfl)
      · obtain ⟨ω, hω, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp hT
        obtain ⟨k, q, hrun⟩ := ih _ ht
        have hstab : Trace P r S (S.selectedRestartCount P r hr) 0 (S.selectedStabilize P r hr) := by
          simpa [State.selectedStabilize] using Trace.stabilize_prefix
            (Trace.start (S₀ := S)) hr (j := S.selectedRestartCount P r hr) le_rfl
        have hepoch := run_trace r (S.selectedStabilize P r hr).mass
          (sampleLevels (S.selectedStabilize P r hr) ω) (sampleOrder (S.selectedStabilize P r hr) ω.1) hstab
        exact ⟨_, _, trace_trans P r hepoch hrun⟩

/-- With the proved label-count fuel, every run terminates at zero optimum. -/
theorem solve_support_zero (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ)
    (S : State G D L) (hfuel : S.remaining.card ≤ fuel)
    {T : State G D L} (hT : T ∈ (solve P r hr fuel S).support) : T.optimum = 0 := by
  induction fuel generalizing S with
  | zero =>
      have he : T = S.selectedStabilize P r hr := by simpa [solve] using hT
      subst T
      apply optimum_eq_zero_of_remaining_empty
      rw [selectedStabilize_remaining]
      exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hfuel)
  | succ fuel ih =>
      simp only [solve] at hT
      split_ifs at hT with hz
      · have he : T = S.selectedStabilize P r hr := by simpa using hT
        simpa only [he] using hz
      · obtain ⟨ω, hω, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp hT
        apply ih _ _ ht
        have hprogress := epoch_progress r hr.le (S.selectedStabilize P r hr)
          (S.selectedStabilize_ready P r hr) hz ω
        rw [selectedStabilize_remaining] at hprogress
        omega

/-- Geometric mass fuel is a second, sharper termination proof. The base case
uses the actual unit lower bound on any unresolved fractional cut. -/
theorem solve_support_zero_of_mass_fuel (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ)
    (S : State G D L) (hfuel : (S.selectedStabilize P r hr).mass < r ^ fuel)
    {T : State G D L} (hT : T ∈ (solve P r hr fuel S).support) : T.optimum = 0 := by
  induction fuel generalizing S with
  | zero =>
      have he : T = S.selectedStabilize P r hr := by simpa [solve] using hT
      subst T
      by_contra hpos
      have hlo := (S.selectedStabilize P r hr).one_le_optimum hpos
      have hm := (S.selectedStabilize P r hr).optimum_le_mass
      simpa using (not_lt_of_ge (hlo.trans hm)) hfuel
  | succ fuel ih =>
      simp only [solve] at hT
      split_ifs at hT with hz
      · have he : T = S.selectedStabilize P r hr := by simpa using hT
        simpa only [he] using hz
      · obtain ⟨ω, hω, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp hT
        let U := (epoch r (S.selectedStabilize P r hr) ω).state
        by_cases hnext : (U.selectedStabilize P r hr).optimum = 0
        · have ht' : T ∈ (solve P r hr fuel U).support := ht
          have he : T = U.selectedStabilize P r hr := by
            cases fuel <;> simpa [solve, hnext] using ht'
          simpa only [he] using hnext
        · apply ih U _ ht
          have hdrop := next_start_mass P r (S.selectedStabilize P r hr).mass hr U
            (run_mass_le r (S.selectedStabilize P r hr).mass (sampleLevels (S.selectedStabilize P r hr) ω) _ _)
            (epoch_stopped r (S.selectedStabilize P r hr) ω) hnext
          have hmul : r * (U.selectedStabilize P r hr).mass < r * r ^ fuel := by
            simpa only [pow_succ, mul_comm] using hdrop.trans_lt hfuel
          exact lt_of_mul_lt_mul_left hmul zero_le

/-- All supported outputs, including probabilistic failure events, are valid. -/
theorem solve_support_integralCut (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ)
    (S : State G D L) (hfuel : S.remaining.card ≤ fuel)
    {T : State G D L} (hT : T ∈ (solve P r hr fuel S).support) :
    IsIntegralCut G T.cut (D : Set (V × V)) :=
  T.integralCut_of_zero (solve_support_zero P r hr fuel S hfuel hT)

/-- The cap bound counts real installations only, throughout all analysis epochs. -/
theorem solve_support_scale_le (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ)
    (S : State G D L) {J : ℕ} (hJ : S.mass < r ^ (J + 1))
    {T : State G D L} (hT : T ∈ (solve P r hr fuel S).support) :
    T.scale ≤ 4 ^ J * S.scale := by
  obtain ⟨k, q, h⟩ := solve_support_execution P r hr fuel S hT
  exact h.scale_le hr hJ

/-- The returned finite cut law, with no optimizer-state finiteness requirement. -/
def outputPMF (r : ℝ≥0) (hr : 1 < r) (S : State G D L) : PMF (Finset V) :=
  (solve P r hr S.remaining.card S).map State.cut

theorem outputPMF_valid (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    {X : Finset V} (hX : X ∈ (outputPMF P r hr S).support) :
    IsIntegralCut G X (D : Set (V × V)) := by
  obtain ⟨T, hT, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hX
  exact solve_support_integralCut P r hr _ S le_rfl hT

/-- The bounded solver's final cut law, using its genuine finite adaptive binds. -/
def boundedOutput (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ) (S : State G D L) : PMF (Finset V) :=
  (solve P r hr fuel S).map State.cut

@[simp] theorem boundedOutput_zero (r : ℝ≥0) (hr : 1 < r) (S : State G D L) :
    boundedOutput P r hr 0 S = PMF.pure S.cut := by
  simp [boundedOutput, solve, PMF.pure_map]

theorem boundedOutput_succ (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ) (S : State G D L) :
    boundedOutput P r hr (fuel + 1) S =
      if (S.selectedStabilize P r hr).optimum = 0 then PMF.pure S.cut else
        (inputLaw (S.selectedStabilize P r hr)).bind
          (fun ω => boundedOutput P r hr fuel (epoch r (S.selectedStabilize P r hr) ω).state) := by
  unfold boundedOutput
  rw [solve]
  split_ifs <;> simp [PMF.pure_map, PMF.map_bind, inputLaw]

/-- Geometric fuel proves validity for every supported final cut. -/
theorem boundedOutput_valid (r : ℝ≥0) (hr : 1 < r) (fuel : ℕ) (S : State G D L)
    (hfuel : S.mass < r ^ fuel) {X : Finset V} (hX : X ∈ (boundedOutput P r hr fuel S).support) :
    IsIntegralCut G X (D : Set (V × V)) := by
  obtain ⟨T, hT, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hX
  exact T.integralCut_of_zero (solve_support_zero_of_mass_fuel P r hr fuel S
    ((selectedStabilize_mass_le P r hr S).trans_lt hfuel) hT)

/-- All actual optimizer installations preserve the initial scale's unit lower bound. -/
theorem execution_scale_one_le (r : ℝ≥0) {S₀ S : State G D L} {k q : ℕ}
    (h : Trace P r S₀ k q S) (h₀ : 1 ≤ S₀.scale) : 1 ≤ S.scale := by
  rw [h.scale_eq]
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) h₀

/-- The actual control trace supplies the scale invariant used by every epoch. -/
theorem execution_scale_bounds (r : ℝ≥0) (hr : 1 < r) {S₀ S : State G D L} {k q J : ℕ}
    (h : Trace P r S₀ k q S) (h₀ : 1 ≤ S₀.scale) (hJ : S₀.mass < r ^ (J + 1))
    (B : ℝ) (hB : ((4 ^ J * S₀.scale : ℝ≥0) : ℝ) ≤ B) :
    1 ≤ S.scale ∧ (S.scale : ℝ) ≤ B := by
  refine ⟨execution_scale_one_le P r h h₀, ?_⟩
  apply le_trans _ hB
  exact_mod_cast h.scale_le hr hJ

/-- The finite tower identity sums the unconditional epoch bound over bounded
adaptive history. No distribution on the entire optimizer-state type is assumed finite. -/
theorem boundedOutput_expected_of_invariant [Nonempty V] (r : ℝ≥0) (hr : 1 < r)
    (S₀ : State G D L) (B H : ℝ)
    (hinvariant : ∀ (S : State G D L) (k q : ℕ), Trace P r S₀ k q S →
      1 ≤ S.scale ∧ (S.scale : ℝ) ≤ B)
    (hL : 64 * B ≤ (L : ℝ)) (hLn : (L : ℝ) ≤ Fintype.card V)
    (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ 3) (hH : 0 ≤ H)
    (hfailure : (Fintype.card V : ℝ) ^ 3 * Real.exp (-H) ≤ 1)
    (hC : 0 ≤ epochCostBound r V L B H) (fuel : ℕ)
    (S : State G D L) (k q : ℕ) (hS : Trace P r S₀ k q S) :
    expectedCost (boundedOutput P r hr fuel S) (fun X => (X.card : ℝ)) ≤
      (S.cut.card : ℝ) + (fuel : ℝ) * epochCostBound r V L B H := by
  induction fuel generalizing S k q with
  | zero => simp
  | succ fuel ih =>
      rw [boundedOutput_succ]
      split_ifs with hz
      · simp only [expectedCost_pure]
        exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hC)
      · have hstab : Trace P r S₀ (k + S.selectedRestartCount P r hr) q (S.selectedStabilize P r hr) := by
          exact Trace.stabilize_prefix hS hr le_rfl
        have hb := hinvariant _ _ _ hstab
        have hepoch := expected_epoch_le r hr (S.selectedStabilize P r hr) B H hb.1 hb.2
          hL hLn hnL hz hH hfailure
        rw [expectedCost_bind]
        calc
          _ ≤ ∑ ω, (inputLaw (S.selectedStabilize P r hr) ω).toReal *
              (((epoch r (S.selectedStabilize P r hr) ω).state.cut.card : ℝ) +
                (fuel : ℝ) * epochCostBound r V L B H) := by
            apply Finset.sum_le_sum
            intro ω hω
            apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
            exact ih _ _ _ (run_trace r (S.selectedStabilize P r hr).mass
              (sampleLevels (S.selectedStabilize P r hr) ω) (sampleOrder (S.selectedStabilize P r hr) ω.1) hstab)
          _ = expectedCost (inputLaw (S.selectedStabilize P r hr))
                (fun ω => (((epoch r (S.selectedStabilize P r hr) ω).state.cut \ (S.selectedStabilize P r hr).cut).card : ℝ)) +
              S.cut.card + (fuel : ℝ) * epochCostBound r V L B H := by
            change expectedCost (inputLaw (S.selectedStabilize P r hr))
              (fun ω => ((epoch r (S.selectedStabilize P r hr) ω).state.cut.card : ℝ) +
                (fuel : ℝ) * epochCostBound r V L B H) = _
            rw [expected_add_const, expected_epoch_card, selectedStabilize_cut]
          _ ≤ _ := by
            simp only [Nat.cast_add, Nat.cast_one]
            linarith

/-- The invariant in the tower theorem is derived from the global installation
budget; it is not an optimizer assumption. -/
theorem boundedOutput_expected [Nonempty V] (r : ℝ≥0) (hr : 1 < r)
    (S : State G D L) (J : ℕ) (B H : ℝ) (h₀ : 1 ≤ S.scale)
    (hJ : S.mass < r ^ (J + 1)) (hB : ((4 ^ J * S.scale : ℝ≥0) : ℝ) ≤ B)
    (hL : 64 * B ≤ (L : ℝ)) (hLn : (L : ℝ) ≤ Fintype.card V)
    (hnL : (Fintype.card V : ℝ) ≤ (L : ℝ) ^ 3) (hH : 0 ≤ H)
    (hfailure : (Fintype.card V : ℝ) ^ 3 * Real.exp (-H) ≤ 1) :
    expectedCost (boundedOutput P r hr (J + 1) S) (fun X => (X.card : ℝ)) ≤
      (S.cut.card : ℝ) + ((J : ℝ) + 1) * epochCostBound r V L B H := by
  have hbase := execution_scale_bounds P r hr (Trace.start (S₀ := S)) h₀ hJ B hB
  have hBp : 0 < B := by
    have hscale : (1 : ℝ) ≤ S.scale := by exact_mod_cast h₀
    linarith [hbase.2]
  have hC : 0 ≤ epochCostBound r V L B H := by
    have hK := (graphDenominator_pos (Fintype.card V) hBp
      (by exact_mod_cast lt_trans zero_lt_one hr)).le
    unfold epochCostBound sizeFactor
    positivity
  simpa only [Nat.cast_add, Nat.cast_one] using boundedOutput_expected_of_invariant P r hr S B H
    (fun T k q hT => execution_scale_bounds P r hr hT h₀ hJ B hB)
    hL hLn hnL hH hfailure hC (J + 1) S 0 0 Trace.start

end
end DirectedFlowCutGap.FlexibleAdaptiveRounding
