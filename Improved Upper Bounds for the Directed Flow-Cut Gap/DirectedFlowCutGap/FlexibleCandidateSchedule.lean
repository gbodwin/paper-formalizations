import DirectedFlowCutGap.AdaptiveEpoch
import DirectedFlowCutGap.CandidateGridOptimizer

/-!
# Adaptive control with an independently selected exact minimum

An exact family provider may choose any minimizer at each state. Only its
objective is identified with the intrinsic optimum; neither vectors nor
output distributions are identified with the compact-selector construction.
The recurrence and traces below perform the supplied provider's installations.
They are mathematical finite constructions, not a polynomial runtime claim.
-/
namespace DirectedFlowCutGap.FlexibleCandidateSchedule
noncomputable section
open scoped BigOperators NNReal ENNReal
open CandidateSchedule CandidateSchedule.State CandidateOptimization EpochAccounting
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A selector supplies actual weights and certifies each selected minimum.
An implementation must separately provide these data and prove these fields. -/
structure FamilyProvider (G : Digraph V) (D : Finset (V × V)) (L : ℝ≥0) where
  family : State G D L → (V × V) → V → ℝ≥0
  feasible : ∀ S p, p ∈ S.remaining →
    IsCandidate G {p} S.cut ((4 * S.scale) / L) (family S p)
  minimal : ∀ S p, p ∈ S.remaining → ∀ z,
    IsCandidate G {p} S.cut ((4 * S.scale) / L) z →
    outsideMass S.cut (family S p) ≤ outsideMass S.cut z

variable {G : Digraph V} {D : Finset (V × V)} {L : ℝ≥0}

namespace FamilyProvider

theorem objective_eq (P : FamilyProvider G D L) (S : State G D L) :
    familyMass S.remaining S.cut (P.family S) = S.optimum := by
  apply le_antisymm
  · exact Finset.sum_le_sum fun p hp => P.minimal S p hp (S.candidate p)
      (S.candidate_spec hp).1
  · exact S.optimum_minimal _ (P.feasible S)

/-- The original choice is one possible provider; it is not imposed on others. -/
def compact : FamilyProvider G D L where
  family := State.candidate
  feasible := fun S _ hp => (S.candidate_spec hp).1
  minimal := fun S _ hp => (S.candidate_spec hp).2.2

end FamilyProvider
end
end DirectedFlowCutGap.FlexibleCandidateSchedule

namespace DirectedFlowCutGap.CandidateSchedule.State
noncomputable section
open scoped BigOperators NNReal ENNReal
open CandidateOptimization EpochAccounting FlexibleCandidateSchedule
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : Digraph V} {D : Finset (V × V)} {L : ℝ≥0}
variable (P : FamilyProvider G D L)

/-- Install the provider's actual family, preserving the cut and labels. -/
def selectedInstall (S : State G D L) : State G D L where
  remaining := S.remaining
  cut := S.cut
  weight := P.family S
  scale := 4 * S.scale
  remaining_subset := S.remaining_subset
  feasible := fun p hp => (P.feasible S p hp).1
  cap := fun p hp => (P.feasible S p hp).2.2
  processed := S.processed

@[simp] theorem selectedInstall_mass (S : State G D L) :
    (S.selectedInstall P).mass = S.optimum := P.objective_eq S

/-- A deterministic restart test. A successful installation is immediately retested. -/
def selectedAdvance (r : ℝ≥0) (S : State G D L) : State G D L :=
  if S.Ready r then S else S.selectedInstall P

theorem selectedAdvance_of_not_ready {r : ℝ≥0} (S : State G D L) (h : ¬S.Ready r) :
    S.selectedAdvance P r = S.selectedInstall P := by simp [selectedAdvance, h]

theorem selectedRestart_decreases {r : ℝ≥0} (S : State G D L) (h : ¬S.Ready r) :
    r * (S.selectedInstall P).mass < S.mass := by
  rw [selectedInstall_mass]
  exact lt_of_not_ge (fun hs => h (Or.inr hs))

theorem selectedRestart_mass_lower {r : ℝ≥0} (S : State G D L) (h : ¬S.Ready r) :
    1 ≤ (S.selectedInstall P).mass := by
  rw [selectedInstall_mass]
  exact S.one_le_optimum (fun hz => h (Or.inl hz))

/-- This trajectory becomes constant on reaching the first ready state. -/
def selectedTrajectory (P : FamilyProvider G D L) (r : ℝ≥0) (S : State G D L) : ℕ → State G D L
  | 0 => S
  | n + 1 => (S.selectedTrajectory P r n).selectedAdvance P r

@[simp] theorem selectedTrajectory_zero (r : ℝ≥0) (S : State G D L) :
    S.selectedTrajectory P r 0 = S := rfl

@[simp] theorem selectedTrajectory_succ (r : ℝ≥0) (S : State G D L) (n : ℕ) :
    S.selectedTrajectory P r (n + 1) = (S.selectedTrajectory P r n).selectedAdvance P r := rfl

theorem selectedTrajectory_remaining (r : ℝ≥0) (S : State G D L) (k : ℕ) :
    (S.selectedTrajectory P r k).remaining = S.remaining := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [selectedTrajectory_succ]
      unfold selectedAdvance
      split_ifs <;> exact ih

theorem selectedTrajectory_cut (r : ℝ≥0) (S : State G D L) (k : ℕ) :
    (S.selectedTrajectory P r k).cut = S.cut := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [selectedTrajectory_succ]
      unfold selectedAdvance
      split_ifs <;> exact ih

/-- Any fuel with `M_initial < r^fuel` suffices; the proof uses actual uncut paths. -/
theorem selectedExists_ready_le (r : ℝ≥0) (S : State G D L) (N : ℕ)
    (hN : S.mass < r ^ N) : ∃ k ≤ N, (S.selectedTrajectory P r k).Ready r := by
  by_contra h
  have hbad : ∀ i ≤ N, ¬(S.selectedTrajectory P r i).Ready r := by
    intro i hi hr
    exact h ⟨i, hi, hr⟩
  have hstep : ∀ i < N, r * (S.selectedTrajectory P r (i + 1)).mass ≤
      (S.selectedTrajectory P r i).mass := by
    intro i hi
    rw [selectedTrajectory_succ, selectedAdvance_of_not_ready P _ (hbad i hi.le)]
    exact (selectedRestart_decreases P _ (hbad i hi.le)).le
  have hlo : 1 ≤ (S.selectedTrajectory P r N).mass := by
    apply (one_le_optimum _ (fun hz => hbad N le_rfl (Or.inl hz))).trans
    exact optimum_le_mass _
  have hpow := restart_power_le (fun i => (S.selectedTrajectory P r i).mass) r S.mass N
    hstep hlo (by simp)
  exact (not_le_of_gt hN) hpow

theorem selectedExists_ready (r : ℝ≥0) (hr : 1 < r) (S : State G D L) :
    ∃ k, (S.selectedTrajectory P r k).Ready r := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt S.mass hr
  obtain ⟨k, _, hk⟩ := S.selectedExists_ready_le P r N hN
  exact ⟨k, hk⟩

/-- Number of actual installations before the first ready state. -/
def selectedRestartCount (r : ℝ≥0) (hr : 1 < r) (S : State G D L) : ℕ :=
  Nat.find (S.selectedExists_ready P r hr)

def selectedStabilize (r : ℝ≥0) (hr : 1 < r) (S : State G D L) : State G D L :=
  S.selectedTrajectory P r (S.selectedRestartCount P r hr)

theorem selectedStabilize_ready (r : ℝ≥0) (hr : 1 < r) (S : State G D L) :
    (S.selectedStabilize P r hr).Ready r := Nat.find_spec (S.selectedExists_ready P r hr)

theorem selectedNot_ready_before (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    {i : ℕ} (hi : i < S.selectedRestartCount P r hr) : ¬(S.selectedTrajectory P r i).Ready r :=
  Nat.find_min (S.selectedExists_ready P r hr) hi

theorem selectedRestartCount_le_fuel (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    (N : ℕ) (hN : S.mass < r ^ N) : S.selectedRestartCount P r hr ≤ N := by
  obtain ⟨k, hk, hready⟩ := S.selectedExists_ready_le P r N hN
  exact (Nat.find_min' (S.selectedExists_ready P r hr) hready).trans hk

theorem selectedTrajectory_mass_bound (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    {k : ℕ} (hk : k ≤ S.selectedRestartCount P r hr) :
    r ^ k * (S.selectedTrajectory P r k).mass ≤ S.mass := by
  apply geometric_mass_bound (fun i => (S.selectedTrajectory P r i).mass) r k
  intro i hi
  have hbad := S.selectedNot_ready_before P r hr (hi.trans_le hk)
  rw [selectedTrajectory_succ, selectedAdvance_of_not_ready P _ hbad]
  exact (selectedRestart_decreases P _ hbad).le

theorem selectedTrajectory_scale (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    {k : ℕ} (hk : k ≤ S.selectedRestartCount P r hr) :
    (S.selectedTrajectory P r k).scale = 4 ^ k * S.scale := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hbad := S.selectedNot_ready_before P r hr (Nat.lt_of_succ_le hk)
      rw [selectedTrajectory_succ, selectedAdvance_of_not_ready P _ hbad]
      change 4 * (S.selectedTrajectory P r k).scale = 4 ^ (k + 1) * S.scale
      rw [ih (Nat.le_of_succ_le hk), pow_succ]
      ring

theorem selectedRestartCount_power_le (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    (hpos : 0 < S.selectedRestartCount P r hr) : r ^ S.selectedRestartCount P r hr ≤ S.mass := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hlo : 1 ≤ (S.selectedStabilize P r hr).mass := by
    unfold selectedStabilize
    rw [hk, selectedTrajectory_succ, selectedAdvance_of_not_ready P _ (S.selectedNot_ready_before P r hr (by omega))]
    exact selectedRestart_mass_lower P _ (S.selectedNot_ready_before P r hr (by omega))
  calc
    _ = r ^ S.selectedRestartCount P r hr * 1 := by simp
    _ ≤ r ^ S.selectedRestartCount P r hr * (S.selectedStabilize P r hr).mass :=
      mul_le_mul_of_nonneg_left hlo zero_le
    _ ≤ S.mass := S.selectedTrajectory_mass_bound P r hr le_rfl

theorem selectedRestartCount_log_le (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    (hpos : 0 < S.selectedRestartCount P r hr) :
    (S.selectedRestartCount P r hr : ℝ) ≤ Real.log (S.mass : ℝ) / Real.log (r : ℝ) := by
  have hrR : 1 < (r : ℝ) := by exact_mod_cast hr
  have hpow : (r : ℝ) ^ S.selectedRestartCount P r hr ≤ (S.mass : ℝ) := by
    exact_mod_cast S.selectedRestartCount_power_le P r hr hpos
  have hlog := Real.log_le_log (pow_pos (lt_trans zero_lt_one hrR) _) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos hrR)).mpr hlog

theorem selectedStabilize_scale_le (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    {J : ℕ} (hJ : S.selectedRestartCount P r hr ≤ J) :
    (S.selectedStabilize P r hr).scale ≤ 4 ^ J * S.scale := by
  unfold selectedStabilize
  rw [S.selectedTrajectory_scale P r hr le_rfl]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hJ) zero_le


/-- Once the first ready state is reached, additional deterministic fuel
leaves the state unchanged. -/
theorem selectedTrajectory_constant (r : ℝ≥0) (S : State G D L) {i j : ℕ}
    (hij : i ≤ j) (hi : (S.selectedTrajectory P r i).Ready r) :
    S.selectedTrajectory P r j = S.selectedTrajectory P r i := by
  induction j with
  | zero =>
      have he : i = 0 := by omega
      subst i
      rfl
  | succ j ih =>
      by_cases hij' : i ≤ j
      · rw [selectedTrajectory_succ, ih hij']
        simp [selectedAdvance, hi]
      · have he : i = j + 1 := by omega
        subst i
        rfl

/-- Any certified geometric fuel runs the actual recurrence to its first-ready
result. The Nat.find used for analysis does not add an implementation oracle. -/
theorem selectedTrajectory_eq_stabilize (r : ℝ≥0) (hr : 1 < r)
    (S : State G D L) (N : ℕ) (hN : S.mass < r ^ N) :
    S.selectedTrajectory P r N = S.selectedStabilize P r hr :=
  S.selectedTrajectory_constant P r (S.selectedRestartCount_le_fuel P r hr N hN)
    (S.selectedStabilize_ready P r hr)

end
end DirectedFlowCutGap.CandidateSchedule.State

namespace DirectedFlowCutGap.FlexibleCandidateSchedule
noncomputable section
open scoped BigOperators NNReal ENNReal
open CandidateSchedule CandidateSchedule.State CandidateOptimization EpochAccounting AdaptiveEpoch
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : Digraph V} {D : Finset (V × V)} {L : ℝ≥0}
variable {P : FamilyProvider G D L}

/-- Complete deterministic control traces, with arbitrary legal samples.
The two counters count optimizer installations and actual cuts separately. -/
inductive Trace (P : FamilyProvider G D L) (r : ℝ≥0) (S₀ : State G D L) :
    ℕ → ℕ → State G D L → Prop
  | start : Trace P r S₀ 0 0 S₀
  | restart {k q : ℕ} {S : State G D L} :
      Trace P r S₀ k q S → ¬S.Ready r → Trace P r S₀ (k + 1) q (S.selectedInstall P)
  | sample {k q : ℕ} {S : State G D L} :
      Trace P r S₀ k q S → S.Ready r → S.optimum ≠ 0 →
      (p : V × V) → (hp : p ∈ S.remaining) →
      (d : ℝ≥0) → (hd : d ≤ 1) → Trace P r S₀ k (q + 1) (S.round p hp d hd)

/-- The constructed first-ready schedule is a legal finite execution prefix. -/
theorem Trace.stabilize_prefix {r : ℝ≥0} {S₀ S : State G D L} {k q : ℕ}
    (h : Trace P r S₀ k q S) (hr : 1 < r) {j : ℕ}
    (hj : j ≤ S.selectedRestartCount P r hr) : Trace P r S₀ (k + j) q (S.selectedTrajectory P r j) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
      have hbad := S.selectedNot_ready_before P r hr (Nat.lt_of_succ_le hj)
      rw [selectedTrajectory_succ, selectedAdvance_of_not_ready P _ hbad]
      exact Trace.restart (ih (Nat.le_of_succ_le hj)) hbad

/-- Geometric accounting over the whole run, including mass lost between restarts. -/
theorem Trace.mass_bound {r : ℝ≥0} {S₀ S : State G D L} {k q : ℕ}
    (h : Trace P r S₀ k q S) : r ^ k * S.mass ≤ S₀.mass := by
  induction h with
  | start => simp
  | @restart k q S h hbad ih =>
      calc
        r ^ (k + 1) * (S.selectedInstall P).mass = r ^ k * (r * (S.selectedInstall P).mass) := by ring
        _ ≤ r ^ k * S.mass := mul_le_mul_of_nonneg_left (S.selectedRestart_decreases P hbad).le zero_le
        _ ≤ S₀.mass := ih
  | @sample k q S h hready hpos p hp d hd ih =>
      exact (mul_le_mul_of_nonneg_left (S.round_mass_le p hp d hd) zero_le).trans ih

/-- Later cut rounds may reduce mass to zero; the last installation still
certifies the global installation bound. -/
theorem Trace.restart_power_le {r : ℝ≥0} {S₀ S : State G D L} {k q : ℕ}
    (h : Trace P r S₀ k q S) (hk : 0 < k) : r ^ k ≤ S₀.mass := by
  induction h with
  | start => omega
  | @restart k q S h hbad ih =>
      calc
        r ^ (k + 1) = r ^ (k + 1) * 1 := by simp
        _ ≤ r ^ (k + 1) * (S.selectedInstall P).mass :=
          mul_le_mul_of_nonneg_left (S.selectedRestart_mass_lower P hbad) zero_le
        _ ≤ S₀.mass := (Trace.restart h hbad).mass_bound
  | sample h hready hpos p hp d hd ih => exact ih hk

theorem Trace.scale_eq {r : ℝ≥0} {S₀ S : State G D L} {k q : ℕ}
    (h : Trace P r S₀ k q S) : S.scale = 4 ^ k * S₀.scale := by
  induction h with
  | start => simp
  | @restart k q S h hbad ih =>
      change 4 * S.scale = 4 ^ (k + 1) * S₀.scale
      rw [ih, pow_succ]
      ring
  | sample h hready hpos p hp d hd ih => exact ih

/-- A fixed geometric budget bounds every prefix, even after termination. -/
theorem Trace.installations_le {r : ℝ≥0} {S₀ S : State G D L} {k q J : ℕ}
    (h : Trace P r S₀ k q S) (hr : 1 < r)
    (hJ : S₀.mass < r ^ (J + 1)) : k ≤ J := by
  by_cases hk : k = 0
  · omega
  · have hpower := h.restart_power_le (Nat.pos_of_ne_zero hk)
    by_contra hnot
    have hJk : J + 1 ≤ k := by omega
    have hmono : r ^ (J + 1) ≤ r ^ k := pow_le_pow_right₀ hr.le hJk
    exact (not_le_of_gt hJ) (hmono.trans hpower)

theorem Trace.scale_le {r : ℝ≥0} {S₀ S : State G D L} {k q J : ℕ}
    (h : Trace P r S₀ k q S) (hr : 1 < r)
    (hJ : S₀.mass < r ^ (J + 1)) : S.scale ≤ 4 ^ J * S₀.scale := by
  rw [h.scale_eq]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) (h.installations_le hr hJ)) zero_le

theorem Trace.rounds_card {r : ℝ≥0} {S₀ S : State G D L} {k q : ℕ}
    (h : Trace P r S₀ k q S) : S.remaining.card + q = S₀.remaining.card := by
  induction h with
  | start => simp
  | restart h hbad ih => exact ih
  | @sample k q S h hready hpos p hp d hd ih =>
      have hc := S.round_card p hp d hd
      omega

theorem Trace.restart_log_le {r : ℝ≥0} {S₀ S : State G D L} {k q : ℕ}
    (h : Trace P r S₀ k q S) (hr : 1 < r) (hk : 0 < k) :
    (k : ℝ) ≤ Real.log (S₀.mass : ℝ) / Real.log (r : ℝ) := by
  have hrR : 1 < (r : ℝ) := by exact_mod_cast hr
  have hpow : (r : ℝ) ^ k ≤ (S₀.mass : ℝ) := by
    exact_mod_cast h.restart_power_le hk
  have hlog := Real.log_le_log (pow_pos (lt_trans zero_lt_one hrR) _) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos hrR)).mpr hlog

variable (P : FamilyProvider G D L)
/-- Every round in a scan is an actual legal round of the original control trace. -/
theorem run_trace {P : FamilyProvider G D L} (r M : ℝ≥0) (level : (V × V) → UnitLevel)
    (order : List (V × V)) {S₀ S : State G D L} {k q : ℕ}
    (hS : Trace P r S₀ k q S) :
    Trace P r S₀ k (q + (run r M level S order).rounds)
      (run r M level S order).state := by
  induction order generalizing S q with
  | nil => simpa using hS
  | cons p ps ih =>
      simp only [run]
      split_ifs with h
      · simpa only [Nat.add_assoc, Nat.add_comm 1] using
          ih (Trace.sample hS h.1.1 h.1.2.1 p h.2 (level p).val (level p).property)
      · simpa using hS

/-- Concatenating actual control traces adds the two global counters. -/
theorem trace_trans (r : ℝ≥0) {S₀ S T : State G D L} {k q j t : ℕ}
    (h₁ : Trace P r S₀ k q S) (h₂ : Trace P r S j t T) :
    Trace P r S₀ (k + j) (q + t) T := by
  induction h₂ with
  | start => simpa using h₁
  | restart h hbad ih => simpa only [Nat.add_assoc] using Trace.restart ih hbad
  | sample h hready hpos p hp d hd ih =>
      simpa only [Nat.add_assoc] using Trace.sample ih hready hpos p hp d hd


/-- Stabilization preserves the label set and cut and never increases mass. -/
theorem selectedStabilize_mass_le (r : ℝ≥0) (hr : 1 < r) (S : State G D L) :
    (S.selectedStabilize P r hr).mass ≤ S.mass := by
  have hpow : 1 ≤ r ^ S.selectedRestartCount P r hr := one_le_pow₀ hr.le
  calc
    _ = 1 * (S.selectedStabilize P r hr).mass := by simp
    _ ≤ r ^ S.selectedRestartCount P r hr * (S.selectedStabilize P r hr).mass :=
      mul_le_mul_of_nonneg_right hpow zero_le
    _ ≤ S.mass := S.selectedTrajectory_mass_bound P r hr le_rfl

@[simp] theorem selectedStabilize_remaining (r : ℝ≥0) (hr : 1 < r) (S : State G D L) :
    (S.selectedStabilize P r hr).remaining = S.remaining := S.selectedTrajectory_remaining P r _

@[simp] theorem selectedStabilize_cut (r : ℝ≥0) (hr : 1 < r) (S : State G D L) :
    (S.selectedStabilize P r hr).cut = S.cut := S.selectedTrajectory_cut P r _

/-- A failed stable gate forces at least one actual installation. -/
theorem selectedRestartCount_pos_of_not_ready (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    (hS : ¬S.Ready r) : 0 < S.selectedRestartCount P r hr := by
  apply Nat.pos_of_ne_zero
  intro hz
  apply hS
  simpa [State.selectedStabilize, hz] using S.selectedStabilize_ready P r hr

/-- If an epoch stops before a restart, that first installation supplies the
same factor-`r` mass loss as an analysis split. -/
theorem selectedStabilize_restart_mass (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    (hS : ¬S.Ready r) : r * (S.selectedStabilize P r hr).mass ≤ S.mass := by
  have hpos := selectedRestartCount_pos_of_not_ready P r hr S hS
  have hpow : r ≤ r ^ S.selectedRestartCount P r hr := by
    simpa using pow_le_pow_right₀ hr.le hpos
  exact (mul_le_mul_of_nonneg_right hpow zero_le).trans (S.selectedTrajectory_mass_bound P r hr le_rfl)

/-- At a nonterminal next start, either boundary reason gives the required
geometric decrease. No equality between current and starting mass is used. -/
theorem next_start_mass (r M : ℝ≥0) (hr : 1 < r) (S : State G D L)
    (hmass : S.mass ≤ M) (hstop : ¬Active r M S)
    (hnext : (S.selectedStabilize P r hr).optimum ≠ 0) :
    r * (S.selectedStabilize P r hr).mass ≤ M := by
  by_cases hready : S.Ready r
  · have hzero : S.optimum ≠ 0 := by
      intro hz
      have hc : S.selectedRestartCount P r hr = 0 :=
        Nat.eq_zero_of_le_zero (Nat.find_min' (S.selectedExists_ready P r hr)
          (show (S.selectedTrajectory P r 0).Ready r from Or.inl hz))
      exact hnext (by simpa [State.selectedStabilize, hc] using hz)
    have hsmall : r * S.mass < M := lt_of_not_ge (fun hM => hstop ⟨hready, hzero, hM⟩)
    exact (mul_le_mul_of_nonneg_left (selectedStabilize_mass_le P r hr S) zero_le).trans hsmall.le
  · exact (selectedStabilize_restart_mass P r hr S hready).trans hmass


end
end DirectedFlowCutGap.FlexibleCandidateSchedule
