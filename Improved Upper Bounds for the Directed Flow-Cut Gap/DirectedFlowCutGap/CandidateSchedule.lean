import DirectedFlowCutGap.EpochAccounting
import DirectedFlowCutGap.LevelCut
import DirectedFlowCutGap.WitnessSystem

/-!
# Attained candidates and the repaired deterministic restart schedule

Candidates are chosen from the proved compact minima, separately for each
remaining label. The deterministic trajectory installs them only when its
positive optimum fails the stable gate, and tests the enlarged cap again.
A first ready index is proved to exist, with an explicit geometric fuel bound.
This is a mathematical (noncomputable) finite schedule, not an LP runtime claim.

States retain original demand endpoints even if those endpoints belong to the
cut. A random-round adapter accepts every label and every closed-unit level;
it uses the actual `levelCut`, freezes weights, and preserves feasibility,
caps, and the internal-cut invariant for every processed demand. No equality
between current mass and analysis-epoch starting mass is used.
-/

namespace DirectedFlowCutGap.CandidateSchedule

noncomputable section
open scoped BigOperators NNReal ENNReal
open CandidateOptimization EpochAccounting
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The original label set is fixed. Feasibility is per remaining label. -/
structure State (G : Digraph V) (D : Finset (V × V)) (L : ℝ≥0) where
  remaining : Finset (V × V)
  cut : Finset V
  weight : (V × V) → V → ℝ≥0
  scale : ℝ≥0
  remaining_subset : remaining ⊆ D
  feasible : ∀ p ∈ remaining, IsFractionalCut G (weight p) {p}
  cap : ∀ p ∈ remaining, ∀ v ∉ cut, weight p v ≤ scale / L
  processed : ∀ p ∈ D, p ∉ remaining → CutsPair G cut p.1 p.2

namespace State
variable {G : Digraph V} {D : Finset (V × V)} {L : ℝ≥0}

def mass (S : State G D L) : ℝ≥0 := familyMass S.remaining S.cut S.weight

def AllCut (S : State G D L) : Prop :=
  ∀ p ∈ S.remaining, CutsPair G S.cut p.1 p.2

omit [Fintype V] in
theorem next_cap (S : State G D L) {p : V × V} (hp : p ∈ S.remaining)
    {v : V} (hv : v ∉ S.cut) : S.weight p v ≤ (4 * S.scale) / L := by
  apply (S.cap p hp v hv).trans
  exact div_le_div_of_nonneg_right (by nlinarith) zero_le

/-- A choice from an attained compact minimum; no optimization oracle is an input. -/
def candidate (S : State G D L) (p : V × V) : V → ℝ≥0 :=
  if hp : p ∈ S.remaining then
    Classical.choose (exists_minimum G {p} S.cut ((4 * S.scale) / L)
      (S.weight p) (S.feasible p hp) (fun _ hv => S.next_cap hp hv))
  else S.weight p

theorem candidate_spec (S : State G D L) {p : V × V} (hp : p ∈ S.remaining) :
    IsCandidate G {p} S.cut ((4 * S.scale) / L) (S.candidate p) ∧
      outsideMass S.cut (S.candidate p) ≤ outsideMass S.cut (S.weight p) ∧
      ∀ z, IsCandidate G {p} S.cut ((4 * S.scale) / L) z →
        outsideMass S.cut (S.candidate p) ≤ outsideMass S.cut z := by
  simpa only [candidate, dite_eq_left hp] using Classical.choose_spec
    (exists_minimum G {p} S.cut ((4 * S.scale) / L)
      (S.weight p) (S.feasible p hp) (fun _ hv => S.next_cap hp hv))

def optimum (S : State G D L) : ℝ≥0 := familyMass S.remaining S.cut S.candidate

theorem optimum_le_mass (S : State G D L) : S.optimum ≤ S.mass := by
  exact Finset.sum_le_sum fun p hp => (S.candidate_spec hp).2.1

/-- The candidate family attains the aggregate minimum as well. -/
theorem optimum_minimal (S : State G D L) (z : (V × V) → V → ℝ≥0)
    (hz : ∀ p ∈ S.remaining, IsCandidate G {p} S.cut ((4 * S.scale) / L) (z p)) :
    S.optimum ≤ familyMass S.remaining S.cut z := by
  exact Finset.sum_le_sum fun p hp => (S.candidate_spec hp).2.2 (z p) (hz p hp)

theorem one_le_mass_of_not_allCut (S : State G D L) (h : ¬S.AllCut) :
    1 ≤ S.mass := by
  classical
  change ¬∀ p ∈ S.remaining, CutsPair G S.cut p.1 p.2 at h
  push Not at h
  obtain ⟨p, hp, huncut⟩ := h
  have hlo := one_le_outsideMass_of_uncut G {p} S.cut (S.weight p)
    (S.feasible p hp) (Set.mem_singleton p) huncut
  exact hlo.trans (Finset.single_le_sum
    (f := fun q => outsideMass S.cut (S.weight q)) (fun _ _ => zero_le) hp)

omit [Fintype V] in
/-- Zero outside weights are feasible precisely when every actual path is cut.
Unreachable labels are covered vacuously; endpoints in the cut are not counted. -/
theorem zero_candidate_of_allCut (S : State G D L) (h : S.AllCut)
    {p : V × V} (hp : p ∈ S.remaining) :
    IsCandidate G {p} S.cut ((4 * S.scale) / L)
      (installCut S.cut (fun _ => 0)) := by
  refine ⟨?_, fun v hv => installCut_mem _ _ hv, fun v hv => ?_⟩
  · rw [isFractionalCut_iff]
    intro s t hst path
    have he : (s, t) = p := Set.mem_singleton_iff.mp hst
    subst p
    obtain ⟨v, hv, hvX⟩ := h (s, t) hp path
    calc
      1 = installCut S.cut (fun _ => 0) v := (installCut_mem _ _ hvX).symm
      _ ≤ path.weight (installCut S.cut (fun _ => 0)) :=
        Finset.single_le_sum (fun _ _ => zero_le) hv
  · simp only [installCut_not_mem _ _ hv]
    exact zero_le

theorem one_le_optimum_of_not_allCut (S : State G D L) (h : ¬S.AllCut) :
    1 ≤ S.optimum := by
  classical
  change ¬∀ p ∈ S.remaining, CutsPair G S.cut p.1 p.2 at h
  push Not at h
  obtain ⟨p, hp, huncut⟩ := h
  have hlo := one_le_outsideMass_of_uncut G {p} S.cut (S.candidate p)
    (S.candidate_spec hp).1.1 (Set.mem_singleton p) huncut
  exact hlo.trans (Finset.single_le_sum
    (f := fun q => outsideMass S.cut (S.candidate q)) (fun _ _ => zero_le) hp)

/-- Exact termination criterion, including disconnected and deleted-endpoint labels. -/
theorem optimum_eq_zero_iff (S : State G D L) : S.optimum = 0 ↔ S.AllCut := by
  constructor
  · intro hz
    by_contra h
    have := S.one_le_optimum_of_not_allCut h
    simp [hz] at this
  · intro h
    apply le_antisymm _ zero_le
    calc
      S.optimum ≤ familyMass S.remaining S.cut (fun _ => installCut S.cut (fun _ => 0)) :=
        S.optimum_minimal _ (fun _ hp => S.zero_candidate_of_allCut h hp)
      _ = 0 := by
        simp only [familyMass, outsideMass_installCut]
        simp [outsideMass]

theorem one_le_optimum (S : State G D L) (h : S.optimum ≠ 0) : 1 ≤ S.optimum :=
  S.one_le_optimum_of_not_allCut (fun hc => h (S.optimum_eq_zero_iff.mpr hc))

theorem integralCut_of_zero (S : State G D L) (h : S.optimum = 0) :
    IsIntegralCut G S.cut (D : Set (V × V)) := by
  intro s t hst
  by_cases hp : (s, t) ∈ S.remaining
  · exact (S.optimum_eq_zero_iff.mp h) _ hp
  · exact S.processed _ hst hp

/-- Install the actual minimizing weights and multiply the cap parameter by four. -/
def install (S : State G D L) : State G D L where
  remaining := S.remaining
  cut := S.cut
  weight := S.candidate
  scale := 4 * S.scale
  remaining_subset := S.remaining_subset
  feasible := fun _ hp => (S.candidate_spec hp).1.1
  cap := fun _ hp => (S.candidate_spec hp).1.2.2
  processed := S.processed

@[simp] theorem mass_install (S : State G D L) : S.install.mass = S.optimum := rfl

/-- Sampling is allowed only after a zero optimum or the current stable gate. -/
def Ready (r : ℝ≥0) (S : State G D L) : Prop :=
  S.optimum = 0 ∨ S.mass ≤ r * S.optimum

/-- A deterministic restart test. A successful installation is immediately retested. -/
def advance (r : ℝ≥0) (S : State G D L) : State G D L :=
  if S.Ready r then S else S.install

theorem advance_of_not_ready {r : ℝ≥0} (S : State G D L) (h : ¬S.Ready r) :
    S.advance r = S.install := by simp [advance, h]

theorem restart_decreases {r : ℝ≥0} (S : State G D L) (h : ¬S.Ready r) :
    r * S.install.mass < S.mass := by
  exact lt_of_not_ge (fun hs => h (Or.inr hs))

theorem restart_mass_lower {r : ℝ≥0} (S : State G D L) (h : ¬S.Ready r) :
    1 ≤ S.install.mass := S.one_le_optimum (fun hz => h (Or.inl hz))

/-- This trajectory becomes constant on reaching the first ready state. -/
def trajectory (r : ℝ≥0) (S : State G D L) : ℕ → State G D L
  | 0 => S
  | n + 1 => (S.trajectory r n).advance r

@[simp] theorem trajectory_zero (r : ℝ≥0) (S : State G D L) :
    S.trajectory r 0 = S := rfl

@[simp] theorem trajectory_succ (r : ℝ≥0) (S : State G D L) (n : ℕ) :
    S.trajectory r (n + 1) = (S.trajectory r n).advance r := rfl

theorem trajectory_remaining (r : ℝ≥0) (S : State G D L) (k : ℕ) :
    (S.trajectory r k).remaining = S.remaining := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [trajectory_succ]
      unfold advance
      split_ifs <;> exact ih

theorem trajectory_cut (r : ℝ≥0) (S : State G D L) (k : ℕ) :
    (S.trajectory r k).cut = S.cut := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [trajectory_succ]
      unfold advance
      split_ifs <;> exact ih

/-- Any fuel with `M_initial < r^fuel` suffices; the proof uses actual uncut paths. -/
theorem exists_ready_le (r : ℝ≥0) (S : State G D L) (N : ℕ)
    (hN : S.mass < r ^ N) : ∃ k ≤ N, (S.trajectory r k).Ready r := by
  by_contra h
  have hbad : ∀ i ≤ N, ¬(S.trajectory r i).Ready r := by
    intro i hi hr
    exact h ⟨i, hi, hr⟩
  have hstep : ∀ i < N, r * (S.trajectory r (i + 1)).mass ≤
      (S.trajectory r i).mass := by
    intro i hi
    rw [trajectory_succ, advance_of_not_ready _ (hbad i hi.le)]
    exact (restart_decreases _ (hbad i hi.le)).le
  have hlo : 1 ≤ (S.trajectory r N).mass := by
    apply (one_le_optimum _ (fun hz => hbad N le_rfl (Or.inl hz))).trans
    exact optimum_le_mass _
  have hpow := restart_power_le (fun i => (S.trajectory r i).mass) r S.mass N
    hstep hlo (by simp)
  exact (not_le_of_gt hN) hpow

theorem exists_ready (r : ℝ≥0) (hr : 1 < r) (S : State G D L) :
    ∃ k, (S.trajectory r k).Ready r := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt S.mass hr
  obtain ⟨k, _, hk⟩ := S.exists_ready_le r N hN
  exact ⟨k, hk⟩

/-- Number of actual installations before the first ready state. -/
def restartCount (r : ℝ≥0) (hr : 1 < r) (S : State G D L) : ℕ :=
  Nat.find (S.exists_ready r hr)

def stabilize (r : ℝ≥0) (hr : 1 < r) (S : State G D L) : State G D L :=
  S.trajectory r (S.restartCount r hr)

theorem stabilize_ready (r : ℝ≥0) (hr : 1 < r) (S : State G D L) :
    (S.stabilize r hr).Ready r := Nat.find_spec (S.exists_ready r hr)

theorem not_ready_before (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    {i : ℕ} (hi : i < S.restartCount r hr) : ¬(S.trajectory r i).Ready r :=
  Nat.find_min (S.exists_ready r hr) hi

theorem restartCount_le_fuel (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    (N : ℕ) (hN : S.mass < r ^ N) : S.restartCount r hr ≤ N := by
  obtain ⟨k, hk, hready⟩ := S.exists_ready_le r N hN
  exact (Nat.find_min' (S.exists_ready r hr) hready).trans hk

theorem trajectory_mass_bound (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    {k : ℕ} (hk : k ≤ S.restartCount r hr) :
    r ^ k * (S.trajectory r k).mass ≤ S.mass := by
  apply geometric_mass_bound (fun i => (S.trajectory r i).mass) r k
  intro i hi
  have hbad := S.not_ready_before r hr (hi.trans_le hk)
  rw [trajectory_succ, advance_of_not_ready _ hbad]
  exact (restart_decreases _ hbad).le

theorem trajectory_scale (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    {k : ℕ} (hk : k ≤ S.restartCount r hr) :
    (S.trajectory r k).scale = 4 ^ k * S.scale := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hbad := S.not_ready_before r hr (Nat.lt_of_succ_le hk)
      rw [trajectory_succ, advance_of_not_ready _ hbad]
      change 4 * (S.trajectory r k).scale = 4 ^ (k + 1) * S.scale
      rw [ih (Nat.le_of_succ_le hk), pow_succ]
      ring

theorem restartCount_power_le (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    (hpos : 0 < S.restartCount r hr) : r ^ S.restartCount r hr ≤ S.mass := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hlo : 1 ≤ (S.stabilize r hr).mass := by
    unfold stabilize
    rw [hk, trajectory_succ, advance_of_not_ready _ (S.not_ready_before r hr (by omega))]
    exact restart_mass_lower _ (S.not_ready_before r hr (by omega))
  calc
    _ = r ^ S.restartCount r hr * 1 := by simp
    _ ≤ r ^ S.restartCount r hr * (S.stabilize r hr).mass :=
      mul_le_mul_of_nonneg_left hlo zero_le
    _ ≤ S.mass := S.trajectory_mass_bound r hr le_rfl

theorem restartCount_log_le (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    (hpos : 0 < S.restartCount r hr) :
    (S.restartCount r hr : ℝ) ≤ Real.log (S.mass : ℝ) / Real.log (r : ℝ) := by
  have hrR : 1 < (r : ℝ) := by exact_mod_cast hr
  have hpow : (r : ℝ) ^ S.restartCount r hr ≤ (S.mass : ℝ) := by
    exact_mod_cast S.restartCount_power_le r hr hpos
  have hlog := Real.log_le_log (pow_pos (lt_trans zero_lt_one hrR) _) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos hrR)).mpr hlog

theorem stabilize_scale_le (r : ℝ≥0) (hr : 1 < r) (S : State G D L)
    {J : ℕ} (hJ : S.restartCount r hr ≤ J) :
    (S.stabilize r hr).scale ≤ 4 ^ J * S.scale := by
  unfold stabilize
  rw [S.trajectory_scale r hr le_rfl]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hJ) zero_le

/-- One genuine level-cut round. Remaining weights stay frozen. -/
def round (S : State G D L) (p : V × V) (hp : p ∈ S.remaining)
    (d : ℝ≥0) (hd : d ≤ 1) : State G D L where
  remaining := S.remaining.erase p
  cut := S.cut ∪ levelCut G (S.weight p) p.1 d
  weight := S.weight
  scale := S.scale
  remaining_subset := (Finset.erase_subset _ _).trans S.remaining_subset
  feasible := fun q hq => S.feasible q (Finset.mem_of_mem_erase hq)
  cap := by
    intro q hq v hv
    apply S.cap q (Finset.mem_of_mem_erase hq) v
    exact fun hvX => hv (Finset.mem_union_left _ hvX)
  processed := by
    intro q hq hgone
    by_cases heq : q = p
    · subst q
      exact cutsPair_mono Finset.subset_union_right
        ((S.feasible p hp).levelCut_cuts_selected_unit (Set.mem_singleton p) d hd)
    · apply cutsPair_mono Finset.subset_union_left
      apply S.processed q hq
      intro hrem
      exact hgone (Finset.mem_erase.mpr ⟨heq, hrem⟩)

theorem round_mass_le (S : State G D L) (p : V × V) (hp : p ∈ S.remaining)
    (d : ℝ≥0) (hd : d ≤ 1) : (S.round p hp d hd).mass ≤ S.mass :=
  familyMass_mono (Finset.erase_subset _ _) Finset.subset_union_left _

theorem round_card (S : State G D L) (p : V × V) (hp : p ∈ S.remaining)
    (d : ℝ≥0) (hd : d ≤ 1) :
    (S.round p hp d hd).remaining.card + 1 = S.remaining.card := by
  exact Finset.card_erase_add_one hp

/-- At a ready state with positive optimum, the actual weights and actual
attained candidates satisfy exactly the stable gate used by witness assembly. -/
theorem stable_gate (r : ℝ≥0) (S : State G D L)
    (hready : S.Ready r) (hpositive : S.optimum ≠ 0) :
    S.mass ≤ r * S.optimum := hready.resolve_left hpositive

/-- Complete deterministic control traces, with arbitrary legal samples.
The two counters count optimizer installations and actual cuts separately. -/
inductive Execution (r : ℝ≥0) (S₀ : State G D L) :
    ℕ → ℕ → State G D L → Prop
  | start : Execution r S₀ 0 0 S₀
  | restart {k q : ℕ} {S : State G D L} :
      Execution r S₀ k q S → ¬S.Ready r → Execution r S₀ (k + 1) q S.install
  | sample {k q : ℕ} {S : State G D L} :
      Execution r S₀ k q S → S.Ready r → S.optimum ≠ 0 →
      (p : V × V) → (hp : p ∈ S.remaining) →
      (d : ℝ≥0) → (hd : d ≤ 1) → Execution r S₀ k (q + 1) (S.round p hp d hd)

/-- The constructed first-ready schedule is a legal finite execution prefix. -/
theorem Execution.stabilize_prefix {r : ℝ≥0} {S₀ S : State G D L} {k q : ℕ}
    (h : Execution r S₀ k q S) (hr : 1 < r) {j : ℕ}
    (hj : j ≤ S.restartCount r hr) : Execution r S₀ (k + j) q (S.trajectory r j) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
      have hbad := S.not_ready_before r hr (Nat.lt_of_succ_le hj)
      rw [trajectory_succ, advance_of_not_ready _ hbad]
      exact Execution.restart (ih (Nat.le_of_succ_le hj)) hbad

/-- Geometric accounting over the whole run, including mass lost between restarts. -/
theorem Execution.mass_bound {r : ℝ≥0} {S₀ S : State G D L} {k q : ℕ}
    (h : Execution r S₀ k q S) : r ^ k * S.mass ≤ S₀.mass := by
  induction h with
  | start => simp
  | @restart k q S h hbad ih =>
      calc
        r ^ (k + 1) * S.install.mass = r ^ k * (r * S.install.mass) := by ring
        _ ≤ r ^ k * S.mass := mul_le_mul_of_nonneg_left (S.restart_decreases hbad).le zero_le
        _ ≤ S₀.mass := ih
  | @sample k q S h hready hpos p hp d hd ih =>
      exact (mul_le_mul_of_nonneg_left (S.round_mass_le p hp d hd) zero_le).trans ih

/-- Later cut rounds may reduce mass to zero; the last installation still
certifies the global installation bound. -/
theorem Execution.restart_power_le {r : ℝ≥0} {S₀ S : State G D L} {k q : ℕ}
    (h : Execution r S₀ k q S) (hk : 0 < k) : r ^ k ≤ S₀.mass := by
  induction h with
  | start => omega
  | @restart k q S h hbad ih =>
      calc
        r ^ (k + 1) = r ^ (k + 1) * 1 := by simp
        _ ≤ r ^ (k + 1) * S.install.mass :=
          mul_le_mul_of_nonneg_left (S.restart_mass_lower hbad) zero_le
        _ ≤ S₀.mass := (Execution.restart h hbad).mass_bound
  | sample h hready hpos p hp d hd ih => exact ih hk

theorem Execution.scale_eq {r : ℝ≥0} {S₀ S : State G D L} {k q : ℕ}
    (h : Execution r S₀ k q S) : S.scale = 4 ^ k * S₀.scale := by
  induction h with
  | start => simp
  | @restart k q S h hbad ih =>
      change 4 * S.scale = 4 ^ (k + 1) * S₀.scale
      rw [ih, pow_succ]
      ring
  | sample h hready hpos p hp d hd ih => exact ih

/-- A fixed geometric budget bounds every prefix, even after termination. -/
theorem Execution.installations_le {r : ℝ≥0} {S₀ S : State G D L} {k q J : ℕ}
    (h : Execution r S₀ k q S) (hr : 1 < r)
    (hJ : S₀.mass < r ^ (J + 1)) : k ≤ J := by
  by_cases hk : k = 0
  · omega
  · have hpower := h.restart_power_le (Nat.pos_of_ne_zero hk)
    by_contra hnot
    have hJk : J + 1 ≤ k := by omega
    have hmono : r ^ (J + 1) ≤ r ^ k := pow_le_pow_right₀ hr.le hJk
    exact (not_le_of_gt hJ) (hmono.trans hpower)

theorem Execution.scale_le {r : ℝ≥0} {S₀ S : State G D L} {k q J : ℕ}
    (h : Execution r S₀ k q S) (hr : 1 < r)
    (hJ : S₀.mass < r ^ (J + 1)) : S.scale ≤ 4 ^ J * S₀.scale := by
  rw [h.scale_eq]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) (h.installations_le hr hJ)) zero_le

theorem Execution.rounds_card {r : ℝ≥0} {S₀ S : State G D L} {k q : ℕ}
    (h : Execution r S₀ k q S) : S.remaining.card + q = S₀.remaining.card := by
  induction h with
  | start => simp
  | restart h hbad ih => exact ih
  | @sample k q S h hready hpos p hp d hd ih =>
      have hc := S.round_card p hp d hd
      omega

theorem Execution.restart_log_le {r : ℝ≥0} {S₀ S : State G D L} {k q : ℕ}
    (h : Execution r S₀ k q S) (hr : 1 < r) (hk : 0 < k) :
    (k : ℝ) ≤ Real.log (S₀.mass : ℝ) / Real.log (r : ℝ) := by
  have hrR : 1 < (r : ℝ) := by exact_mod_cast hr
  have hpow : (r : ℝ) ^ k ≤ (S₀.mass : ℝ) := by
    exact_mod_cast h.restart_power_le hk
  have hlog := Real.log_le_log (pow_pos (lt_trans zero_lt_one hrR) _) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos hrR)).mpr hlog

end State

/-- Actual unweighted internal-distance threshold demands, including infinity. -/
def unweightedDemands (G : Digraph V) (L : ℝ≥0) : Finset (V × V) :=
  Finset.univ.filter fun p => (L : ℝ≥0∞) ≤ vertexDistance G (fun _ => 1) p.1 p.2

theorem uniform_fractional (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L)
    {p : V × V} (hp : p ∈ unweightedDemands G L) :
    IsFractionalCut G (fun _ => 1 / L) {p} := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [isFractionalCut_iff]
  intro s t hst path
  have he : (s, t) = p := Set.mem_singleton_iff.mp hst
  subst p
  have hdist := (Finset.mem_filter.mp hp).2
  have hc : L ≤ (path.internalVertices.card : ℝ≥0) := by
    simpa using (coe_le_vertexDistance_iff G (fun _ => 1) s t L).mp hdist path
  have hw : path.weight (fun _ => 1 / L) = (path.internalVertices.card : ℝ≥0) / L := by
    simp [SimplePath.weight, div_eq_mul_inv]
  rw [hw]
  exact (le_div_iff₀ hLp).mpr (by simpa using hc)

/-- The genuine uniform initial state has scale one and no selected vertices. -/
def initial (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L) :
    State G (unweightedDemands G L) L where
  remaining := unweightedDemands G L
  cut := ∅
  weight := fun _ _ => 1 / L
  scale := 1
  remaining_subset := Finset.Subset.refl _
  feasible := fun _ hp => uniform_fractional G L hL hp
  cap := by intros; exact le_rfl
  processed := by intros p hp hnot; exact (hnot hp).elim

theorem initial_mass (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L) :
    (initial G L hL).mass =
      ((unweightedDemands G L).card : ℝ≥0) * (Fintype.card V : ℝ≥0) / L := by
  change familyMass (unweightedDemands G L) ∅ (fun _ _ => 1 / L) = _
  rw [familyMass_uniform]
  ring

theorem initial_mass_le_cube (G : Digraph V) (L : ℝ≥0) (hL : 1 ≤ L) :
    (initial G L hL).mass ≤ (Fintype.card V : ℝ≥0) ^ 3 := by
  have hcard : ((unweightedDemands G L).card : ℝ≥0) ≤
      (Fintype.card V : ℝ≥0) * (Fintype.card V : ℝ≥0) := by
    exact_mod_cast (show (unweightedDemands G L).card ≤ Fintype.card V * Fintype.card V by
      simpa [Fintype.card_prod] using (unweightedDemands G L).card_le_univ)
  rw [initial_mass]
  calc
    _ ≤ ((unweightedDemands G L).card : ℝ≥0) * (Fintype.card V : ℝ≥0) :=
      div_le_self zero_le hL
    _ ≤ ((Fintype.card V : ℝ≥0) * (Fintype.card V : ℝ≥0)) * (Fintype.card V : ℝ≥0) :=
      mul_le_mul_of_nonneg_right hcard zero_le
    _ = _ := by ring

end
end DirectedFlowCutGap.CandidateSchedule
