import DirectedFlowCutGap.CandidateSchedule
import DirectedFlowCutGap.FrozenEpochProbability

/-!
# Actual bounded analysis epochs

An epoch scans a prescribed ordering of the remaining demand labels, using
actual closed-unit levels. It stops before changing the frozen weights, on
zero optimum, or when current mass falls below the recorded starting mass
by the factor `r`. The outer finite recursion and finite sampling law are in
`AdaptiveRounding`. These mathematical definitions do not assert a runtime.
-/
namespace DirectedFlowCutGap.AdaptiveEpoch
noncomputable section
open scoped BigOperators NNReal ENNReal
open CandidateSchedule CandidateSchedule.State
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : Digraph V} {D : Finset (V × V)} {L : ℝ≥0}

/-- All sampled levels, including endpoints, produce correct cuts. -/
abbrev UnitLevel := {d : ℝ≥0 // d ≤ 1}

/-- The current mass comparison is part of every active round. -/
def Active (r M : ℝ≥0) (S : State G D L) : Prop :=
  S.Ready r ∧ S.optimum ≠ 0 ∧ M ≤ r * S.mass

/-- A scan result records its actual number of performed rounds. -/
structure Result (G : Digraph V) (D : Finset (V × V)) (L : ℝ≥0) where
  state : State G D L
  rounds : ℕ

/-- Stop before a restart or analysis split. Samples after stopping are unused. -/
def run (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) : List (V × V) → Result G D L
  | [] => ⟨S, 0⟩
  | p :: ps =>
      if h : Active r M S ∧ p ∈ S.remaining then
        let R := run r M level (S.round p h.2 (level p).val (level p).property) ps
        ⟨R.state, R.rounds + 1⟩
      else ⟨S, 0⟩

@[simp] theorem run_nil (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) : run r M level S [] = ⟨S, 0⟩ := rfl

/-- Every round in a scan is an actual legal round of the original control trace. -/
theorem run_execution (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (order : List (V × V)) {S₀ S : State G D L} {k q : ℕ}
    (hS : Execution r S₀ k q S) :
    Execution r S₀ k (q + (run r M level S order).rounds)
      (run r M level S order).state := by
  induction order generalizing S q with
  | nil => simpa using hS
  | cons p ps ih =>
      simp only [run]
      split_ifs with h
      · simpa only [Nat.add_assoc, Nat.add_comm 1] using
          ih (Execution.sample hS h.1.1 h.1.2.1 p h.2 (level p).val (level p).property)
      · simpa using hS

theorem run_rounds_le_length (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V)) :
    (run r M level S order).rounds ≤ order.length := by
  induction order generalizing S with
  | nil => simp
  | cons p ps ih =>
      simp only [run]
      split_ifs with h
      · exact Nat.succ_le_succ (ih _)
      · exact Nat.zero_le _

theorem run_weight (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V)) :
    (run r M level S order).state.weight = S.weight := by
  induction order generalizing S with
  | nil => rfl
  | cons p ps ih =>
      simp only [run]
      split_ifs with h
      · exact ih _
      · rfl

theorem run_scale (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V)) :
    (run r M level S order).state.scale = S.scale := by
  simpa using (run_execution r M level order (Execution.start (S₀ := S))).scale_eq

theorem run_mass_le (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V)) :
    (run r M level S order).state.mass ≤ S.mass := by
  simpa using (run_execution r M level order (Execution.start (S₀ := S))).mass_bound

theorem run_rounds_card (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V)) :
    (run r M level S order).state.remaining.card +
      (run r M level S order).rounds = S.remaining.card := by
  simpa using (run_execution r M level order (Execution.start (S₀ := S))).rounds_card

theorem run_remaining_subset (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V)) :
    (run r M level S order).state.remaining ⊆ S.remaining := by
  induction order generalizing S with
  | nil => exact Finset.Subset.refl _
  | cons p ps ih =>
      simp only [run]
      split_ifs with h
      · exact (ih _).trans (Finset.erase_subset _ _)
      · exact Finset.Subset.refl _

theorem run_cut_subset (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V)) :
    S.cut ⊆ (run r M level S order).state.cut := by
  induction order generalizing S with
  | nil => exact Finset.Subset.refl _
  | cons p ps ih =>
      simp only [run]
      split_ifs with h
      · exact Finset.subset_union_left.trans
          (ih (S.round p h.2 (level p).val (level p).property))
      · exact Finset.Subset.refl _

/-- A stopped state stays fixed for all unused samples. -/
theorem run_of_not_active (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V)) (hS : ¬Active r M S) :
    run r M level S order = ⟨S, 0⟩ := by
  cases order with
  | nil => rfl
  | cons p ps => simp [run, show ¬(Active r M S ∧ p ∈ S.remaining) from fun h => hS h.1]

/-- All performed cut vertices belong to the corresponding virtual frozen union. -/
theorem run_cut_subset_virtual (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V)) :
    (run r M level S order).state.cut ⊆ S.cut ∪
      order.toFinset.biUnion (fun p => levelCut G (S.weight p) p.1 (level p).val) := by
  induction order generalizing S with
  | nil => simp
  | cons p ps ih =>
      simp only [run]
      split_ifs with h
      · have hi := ih (S.round p h.2 (level p).val (level p).property)
        simpa only [State.round, List.toFinset_cons, Finset.biUnion_insert,
          Finset.union_assoc] using hi
      · exact Finset.subset_union_left

/-- If a prefix ends active, no earlier sample in that prefix was skipped. -/
theorem run_rounds_eq_length_of_active (r M : ℝ≥0)
    (level : (V × V) → UnitLevel) (S : State G D L) (order : List (V × V))
    (hsub : order.toFinset ⊆ S.remaining) (hn : order.Nodup)
    (hactive : Active r M (run r M level S order).state) :
    (run r M level S order).rounds = order.length := by
  induction order generalizing S with
  | nil => rfl
  | cons p ps ih =>
      have hp : p ∈ S.remaining := hsub (by simp)
      by_cases h : Active r M S ∧ p ∈ S.remaining
      · simp only [run, dite_eq_left h] at hactive ⊢
        change (run r M level (S.round p h.2 (level p).val (level p).property) ps).rounds + 1 = ps.length + 1
        congr 1
        apply ih _ _ hn.of_cons hactive
        intro q hq
        exact Finset.mem_erase.mpr ⟨fun he => (List.nodup_cons.mp hn).1 (he ▸ List.mem_toFinset.mp hq),
          hsub (by simp [hq])⟩
      · simp only [run, dite_eq_right h] at hactive
        exact (h ⟨hactive, hp⟩).elim

/-- On the reached event the adaptive cut is exactly the virtual frozen prefix. -/
theorem run_cut_eq_virtual_of_full (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V))
    (hfull : (run r M level S order).rounds = order.length) :
    (run r M level S order).state.cut = S.cut ∪
      order.toFinset.biUnion (fun p => levelCut G (S.weight p) p.1 (level p).val) := by
  induction order generalizing S with
  | nil => simp
  | cons p ps ih =>
      by_cases h : Active r M S ∧ p ∈ S.remaining
      · simp only [run, dite_eq_left h] at hfull ⊢
        have hi := ih (S.round p h.2 (level p).val (level p).property)
          (Nat.add_right_cancel hfull)
        simpa only [State.round, List.toFinset_cons, Finset.biUnion_insert,
          Finset.union_assoc] using hi
      · simp only [run, dite_eq_right h, List.length_cons] at hfull
        change 0 = ps.length + 1 at hfull
        omega

/-- Concatenating actual control traces adds the two global counters. -/
theorem execution_trans (r : ℝ≥0) {S₀ S T : State G D L} {k q j t : ℕ}
    (h₁ : Execution r S₀ k q S) (h₂ : Execution r S j t T) :
    Execution r S₀ (k + j) (q + t) T := by
  induction h₂ with
  | start => simpa using h₁
  | restart h hbad ih => simpa only [Nat.add_assoc] using Execution.restart ih hbad
  | sample h hready hpos p hp d hd ih =>
      simpa only [Nat.add_assoc] using Execution.sample ih hready hpos p hp d hd

/-- Empty remaining labels imply the exact zero-optimum termination test. -/
theorem optimum_eq_zero_of_remaining_empty (S : State G D L)
    (hS : S.remaining = ∅) : S.optimum = 0 := by
  simp [State.optimum, EpochAccounting.familyMass, hS]

/-- A legal complete ordering can stop only at the specified epoch boundary. -/
theorem run_stopped (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V))
    (hn : order.Nodup) (he : order.toFinset = S.remaining) :
    ¬Active r M (run r M level S order).state := by
  induction order generalizing S with
  | nil =>
      have hz := optimum_eq_zero_of_remaining_empty S (by simpa using he.symm)
      exact fun h => h.2.1 hz
  | cons p ps ih =>
      have hp : p ∈ S.remaining := by rw [← he]; simp
      simp only [run]
      split_ifs with h
      · apply ih _ hn.of_cons
        change ps.toFinset = S.remaining.erase p
        rw [← he, List.toFinset_cons, Finset.erase_insert (by simpa using (List.nodup_cons.mp hn).1)]
      · exact fun ha => h ⟨ha, hp⟩

theorem active_initial (r : ℝ≥0) (hr : 1 ≤ r) (S : State G D L)
    (hready : S.Ready r) (hpos : S.optimum ≠ 0) : Active r S.mass S := by
  refine ⟨hready, hpos, ?_⟩
  calc
    S.mass = 1 * S.mass := by simp
    _ ≤ r * S.mass := mul_le_mul_of_nonneg_right hr zero_le

/-- A positive, stabilized epoch necessarily performs its first real round. -/
theorem run_rounds_pos (r : ℝ≥0) (hr : 1 ≤ r) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V))
    (he : order.toFinset = S.remaining) (hready : S.Ready r) (hpos : S.optimum ≠ 0) :
    0 < (run r S.mass level S order).rounds := by
  cases order with
  | nil =>
      exact (hpos (optimum_eq_zero_of_remaining_empty S (by simpa using he.symm))).elim
  | cons p ps =>
      have hp : p ∈ S.remaining := by rw [← he]; simp
      have ha : Active r S.mass S ∧ p ∈ S.remaining := ⟨active_initial r hr S hready hpos, hp⟩
      simp only [run, dite_eq_left ha]
      exact Nat.zero_lt_succ _

/-- First-round progress gives a strict outer fuel decrease without a probability claim. -/
theorem run_remaining_card_lt (r : ℝ≥0) (hr : 1 ≤ r)
    (level : (V × V) → UnitLevel) (S : State G D L) (order : List (V × V))
    (he : order.toFinset = S.remaining) (hready : S.Ready r) (hpos : S.optimum ≠ 0) :
    (run r S.mass level S order).state.remaining.card < S.remaining.card := by
  have hpos := run_rounds_pos r hr level S order he hready hpos
  have hc := run_rounds_card r S.mass level S order
  omega

/-- Stabilization preserves the label set and cut and never increases mass. -/
theorem stabilize_mass_le (r : ℝ≥0) (hr : 1 < r) (S : State G D L) :
    (S.stabilize r hr).mass ≤ S.mass := by
  have hpow : 1 ≤ r ^ S.restartCount r hr := one_le_pow₀ hr.le
  calc
    _ = 1 * (S.stabilize r hr).mass := by simp
    _ ≤ r ^ S.restartCount r hr * (S.stabilize r hr).mass :=
      mul_le_mul_of_nonneg_right hpow zero_le
    _ ≤ S.mass := S.trajectory_mass_bound r hr le_rfl

@[simp] theorem stabilize_remaining (r : ℝ≥0) (hr : 1 < r) (S : State G D L) :
    (S.stabilize r hr).remaining = S.remaining := S.trajectory_remaining r _

@[simp] theorem stabilize_cut (r : ℝ≥0) (hr : 1 < r) (S : State G D L) :
    (S.stabilize r hr).cut = S.cut := S.trajectory_cut r _

/-- A failed stable gate forces at least one actual installation. -/
theorem restartCount_pos_of_not_ready (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    (hS : ¬S.Ready r) : 0 < S.restartCount r hr := by
  apply Nat.pos_of_ne_zero
  intro hz
  apply hS
  simpa [State.stabilize, hz] using S.stabilize_ready r hr

/-- If an epoch stops before a restart, that first installation supplies the
same factor-`r` mass loss as an analysis split. -/
theorem stabilize_restart_mass (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    (hS : ¬S.Ready r) : r * (S.stabilize r hr).mass ≤ S.mass := by
  have hpos := restartCount_pos_of_not_ready r hr S hS
  have hpow : r ≤ r ^ S.restartCount r hr := by
    simpa using pow_le_pow_right₀ hr.le hpos
  exact (mul_le_mul_of_nonneg_right hpow zero_le).trans (S.trajectory_mass_bound r hr le_rfl)

/-- At a nonterminal next start, either boundary reason gives the required
geometric decrease. No equality between current and starting mass is used. -/
theorem next_start_mass (r M : ℝ≥0) (hr : 1 < r) (S : State G D L)
    (hmass : S.mass ≤ M) (hstop : ¬Active r M S)
    (hnext : (S.stabilize r hr).optimum ≠ 0) :
    r * (S.stabilize r hr).mass ≤ M := by
  by_cases hready : S.Ready r
  · have hzero : S.optimum ≠ 0 := by
      intro hz
      have hc : S.restartCount r hr = 0 :=
        Nat.eq_zero_of_le_zero (Nat.find_min' (S.exists_ready r hr)
          (show (S.trajectory r 0).Ready r from Or.inl hz))
      exact hnext (by simpa [State.stabilize, hc] using hz)
    have hsmall : r * S.mass < M := lt_of_not_ge (fun hM => hstop ⟨hready, hzero, hM⟩)
    exact (mul_le_mul_of_nonneg_left (stabilize_mass_le r hr S) zero_le).trans hsmall.le
  · exact (stabilize_restart_mass r hr S hready).trans hmass

/-- Remaining-label value is bounded by its epoch-start sum, since all
separation values are nonnegative and the surviving weights stay frozen. -/
theorem remaining_value_le (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (S : State G D L) (order : List (V × V)) (u v : V) :
    (∑ p ∈ (run r M level S order).state.remaining,
      (levelSeparationValue G ((run r M level S order).state.weight p) p.1 u v).toReal) ≤
    ∑ p ∈ S.remaining, (levelSeparationValue G (S.weight p) p.1 u v).toReal := by
  rw [run_weight]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (run_remaining_subset r M level S order) (by intros; positivity)

end
end DirectedFlowCutGap.AdaptiveEpoch
