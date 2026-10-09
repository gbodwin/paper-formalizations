import DirectedFlowCutGap.CandidatePotentialSoundness

/-!
# Exact finite-grid single-pair candidate optimization

This module connects bounded common-shift rounding to the original candidate
problem through endpoint-safe port potentials. Its finite minimization theorem
is an existence/correctness result. It does not implement polynomial closure
optimization, max flow, bit complexity, or an executable CandidateSchedule.
-/

namespace DirectedFlowCutGap.CandidateGridOptimizer

noncomputable section
open scoped BigOperators NNReal ENNReal
open CandidateGridRounding.DifferenceSystem CandidatePotentialSoundness

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Point (V : Type*) := TerminalPorts.Vertex V × Bool

def before (p : Point V → ℝ) (v : TerminalPorts.Vertex V) : ℝ := p (v, false)
def after (p : Point V → ℝ) (v : TerminalPorts.Vertex V) : ℝ := p (v, true)

/-- Local integer difference constraints. Both endpoint gaps vanish because
all ports have zero gap. The selected source and sink are pinned exactly. -/
structure Feasible (G : Digraph V) (s t : V) (X : Finset V) (L B : ℕ)
    (p : Point V → ℝ) : Prop where
  bounded : ∀ i, 0 ≤ p i ∧ p i ≤ (L : ℝ)
  ordered : ∀ v, before p v ≤ after p v
  source : before p (TerminalPorts.source s) = 0
  sink : after p (TerminalPorts.sink t) = (L : ℝ)
  ports : ∀ a : V ⊕ V, after p (.inr a) = before p (.inr a)
  outsideCap : ∀ v ∉ X, after p (TerminalPorts.core v) - before p (TerminalPorts.core v) ≤ B
  edge : ∀ u v, (TerminalPorts.graph G).Adj u v → before p v ≤ after p u

omit [Fintype V] [DecidableEq V] in
/-- Elementary common-shift preservation is proved from the local constraints. -/
theorem Feasible.shiftFloor {G : Digraph V} {s t : V} {X : Finset V} {L B : ℕ}
    {p : Point V → ℝ} (hp : Feasible G s t X L B p)
    {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d < 1) :
    Feasible G s t X L B (shiftFloor p d) := by
  have hd : ⌊d⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hd₀, hd₁⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := (boxSystem (Point V) L).shiftFloor_feasible
      (feasible_boxSystem hp.bounded) hd₀ hd₁
    simpa [boxSystem] using h.1
  · intro v
    change (⌊before p v + d⌋ : ℝ) ≤ (⌊after p v + d⌋ : ℝ)
    have hf : ⌊before p v + d⌋ ≤ ⌊after p v + d⌋ :=
      Int.floor_mono (by linarith [hp.ordered v])
    exact_mod_cast hf
  · change (⌊before p (TerminalPorts.source s) + d⌋ : ℝ) = 0
    simp [hp.source, hd]
  · change (⌊after p (TerminalPorts.sink t) + d⌋ : ℝ) = (L : ℝ)
    simp [hp.sink, Int.floor_natCast_add, hd]
  · intro a
    change (⌊after p (.inr a) + d⌋ : ℝ) = (⌊before p (.inr a) + d⌋ : ℝ)
    rw [hp.ports a]
  · intro v hv
    change (⌊after p (TerminalPorts.core v) + d⌋ : ℝ) -
      (⌊before p (TerminalPorts.core v) + d⌋ : ℝ) ≤ (B : ℝ)
    exact_mod_cast floor_sub_floor_le (d := d) (by exact_mod_cast hp.outsideCap v hv)
  · intro u v huv
    change (⌊before p v + d⌋ : ℝ) ≤ (⌊after p u + d⌋ : ℝ)
    have hf : ⌊before p v + d⌋ ≤ ⌊after p u + d⌋ :=
      Int.floor_mono (by linarith [hp.edge u v huv])
    exact_mod_cast hf

/-- Clipping before converting to real preserves unreachable distances. -/
def clip (a : ℝ≥0∞) : ℝ := (min 1 a).toReal

theorem min_one_ne_top (a : ℝ≥0∞) : min 1 a ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (min_le_left _ _) ENNReal.one_lt_top)

theorem clip_nonneg (a : ℝ≥0∞) : 0 ≤ clip a := ENNReal.toReal_nonneg

theorem clip_le_one (a : ℝ≥0∞) : clip a ≤ 1 := by
  simpa [clip] using ENNReal.toReal_mono ENNReal.one_ne_top (min_le_left 1 a)

theorem clip_mono {a b : ℝ≥0∞} (h : a ≤ b) : clip a ≤ clip b :=
  ENNReal.toReal_mono (min_one_ne_top b) (min_le_min le_rfl h)

theorem clip_eq_one {a : ℝ≥0∞} (h : 1 ≤ a) : clip a = 1 := by
  simp [clip, min_eq_left h]

theorem clip_add_le (a : ℝ≥0∞) (b : ℝ≥0) : clip (a + b) ≤ clip a + b := by
  by_cases ha : a ≤ 1
  · have ha' : a ≠ ⊤ := ne_of_lt (lt_of_le_of_lt ha ENNReal.one_lt_top)
    have hb' : (b : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ha', hb'⟩)
      (min_le_right 1 (a + b))
    simpa [clip, min_eq_right ha, ENNReal.toReal_add ha' hb'] using h
  · have hclip : clip a = 1 := clip_eq_one (le_of_not_ge ha)
    have hb : (0 : ℝ) ≤ b := b.coe_nonneg
    rw [hclip]
    exact (clip_le_one _).trans (le_add_of_nonneg_right hb)

/-- Before and after potentials use the actual endpoint-excluding distance. -/
def distancePoint (G : Digraph V) (w : V → ℝ≥0) (s : V) (L : ℕ) : Point V → ℝ :=
  fun i => (L : ℝ) * clip
    (vertexDistance (TerminalPorts.graph G) (TerminalPorts.extend w)
      (TerminalPorts.source s) i.1 + if i.2 then (TerminalPorts.extend w i.1 : ℝ≥0∞) else 0)

omit [Fintype V] in
theorem distancePoint_gap_le (G : Digraph V) (w : V → ℝ≥0) (s : V) (L : ℕ)
    (v : TerminalPorts.Vertex V) :
    after (distancePoint G w s L) v - before (distancePoint G w s L) v ≤
      (L : ℝ) * (TerminalPorts.extend w v : ℝ) := by
  have h := mul_le_mul_of_nonneg_left
    (clip_add_le (vertexDistance (TerminalPorts.graph G) (TerminalPorts.extend w)
      (TerminalPorts.source s) v) (TerminalPorts.extend w v)) (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  simp only [after, before, distancePoint, Bool.false_eq_true, ite_false, ite_true, add_zero]
  nlinarith

/-- Every actual bounded candidate supplies feasible potentials at no greater
outside objective. Infinite and zero distances are handled by clipping. -/
theorem distancePoint_feasible (G : Digraph V) (w : V → ℝ≥0) (s t : V)
    (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (hw : CandidateOptimization.IsCandidate G {(s, t)} X ((B : ℝ≥0) / L) w) :
    Feasible G s t X L B (distancePoint G w s L) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp [distancePoint]
    exact ⟨mul_nonneg hLR.le (clip_nonneg _), by
      simpa using mul_le_mul_of_nonneg_left (clip_le_one _) hLR.le⟩
  · intro v
    simp only [before, after, distancePoint, Bool.false_eq_true, ite_false, ite_true, add_zero]
    exact mul_le_mul_of_nonneg_left (clip_mono (le_add_of_nonneg_right zero_le)) hLR.le
  · simp [before, distancePoint, clip]
  · have hd : (1 : ℝ≥0∞) ≤ vertexDistance (TerminalPorts.graph G) (TerminalPorts.extend w)
        (TerminalPorts.source s) (TerminalPorts.sink t) := by
      rw [TerminalPorts.vertexDistance_eq]
      exact hw.1 s t (Set.mem_singleton _)
    simp [after, distancePoint, TerminalPorts.extend_sink, clip_eq_one hd]
  · intro a
    simp [before, after, distancePoint, TerminalPorts.extend]
  · intro v hv
    have hgap := distancePoint_gap_le G w s L (TerminalPorts.core v)
    simp only [TerminalPorts.extend_core] at hgap
    have hcap : (w v : ℝ) ≤ (B : ℝ) / (L : ℝ) := by exact_mod_cast hw.2.2 v hv
    have hmul := (le_div_iff₀ hLR).mp hcap
    nlinarith
  · intro u v huv
    have hd := vertexDistance_triangle (TerminalPorts.graph G) (TerminalPorts.extend w)
      (TerminalPorts.source s) u v
    rw [vertexDistance_of_adj (TerminalPorts.extend w) huv, add_zero] at hd
    simpa [before, after, distancePoint] using
      mul_le_mul_of_nonneg_left (clip_mono hd) hLR.le


/-- Signed coefficients count only original cores outside the selected cut. -/
def costs (X : Finset V) : Point V → ℝ
  | (.inl v, b) => if v ∈ X then 0 else if b then 1 else -1
  | (.inr _, _) => 0

theorem objective_eq (X : Finset V) (p : Point V → ℝ) :
    objective (costs X) p = ∑ v ∈ Finset.univ.filter (fun v => v ∉ X),
      (after p (TerminalPorts.core v) - before p (TerminalPorts.core v)) := by
  unfold objective
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, costs, zero_mul, add_zero,
    Finset.sum_const_zero]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ X <;> simp [hv, before, after, sub_eq_add_neg]

omit [Fintype V] in
theorem Feasible.candidate {G : Digraph V} {s t : V} {X : Finset V} {L B : ℕ}
    {p : Point V → ℝ} (hp : Feasible G s t X L B p) (hL : 0 < L) :
    CandidateOptimization.IsCandidate G {(s, t)} X ((B : ℝ≥0) / L)
      (candidateWeight X L (before p) (after p) hp.ordered) := by
  apply candidateWeight_isCandidate G s t X L B hL _ _ hp.ordered
    hp.source hp.sink hp.ports ?_ hp.outsideCap hp.edge
  intro v _
  have ha := (hp.bounded (TerminalPorts.core v, true)).2
  have hb := (hp.bounded (TerminalPorts.core v, false)).1
  change after p (TerminalPorts.core v) ≤ (L : ℝ) at ha
  change 0 ≤ before p (TerminalPorts.core v) at hb
  linarith

theorem Feasible.candidate_mass {G : Digraph V} {s t : V} {X : Finset V} {L B : ℕ}
    {p : Point V → ℝ} (hp : Feasible G s t X L B p) :
    (CandidateOptimization.outsideMass X
      (candidateWeight X L (before p) (after p) hp.ordered) : ℝ) =
      objective (costs X) p / (L : ℝ) := by
  rw [outsideMass_candidateWeight, objective_eq]

theorem distancePoint_objective_le (G : Digraph V) (w : V → ℝ≥0) (s : V)
    (X : Finset V) (L : ℕ) :
    objective (costs X) (distancePoint G w s L) ≤
      (L : ℝ) * (CandidateOptimization.outsideMass X w : ℝ) := by
  rw [objective_eq, CandidateOptimization.outsideMass, NNReal.coe_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  exact distancePoint_gap_le G w s L (TerminalPorts.core v)

/-- The original single-pair candidate problem has an attained finite-grid
minimum with exactly the real optimum. The premise is an arbitrary feasible
candidate, not a minimizer. No polynomial running-time assertion is made. -/
theorem exists_candidate_grid_minimum (G : Digraph V) (s t : V)
    (X : Finset V) (L B : ℕ) (hL : 0 < L) (w₀ : V → ℝ≥0)
    (hw₀ : CandidateOptimization.IsCandidate G {(s, t)} X ((B : ℝ≥0) / L) w₀) :
    ∃ w : V → ℝ≥0,
      CandidateOptimization.IsCandidate G {(s, t)} X ((B : ℝ≥0) / L) w ∧
      (∀ v ∉ X, ∃ k : ℤ, 0 ≤ k ∧ (w v : ℝ) = (k : ℝ) / L) ∧
      ∀ z : V → ℝ≥0,
        CandidateOptimization.IsCandidate G {(s, t)} X ((B : ℝ≥0) / L) z →
        CandidateOptimization.outsideMass X w ≤ CandidateOptimization.outsideMass X z := by
  have hp₀ := distancePoint_feasible G w₀ s t X L B hL hw₀
  obtain ⟨q, hq, hmin⟩ := exists_grid_minimum_of_shift_closed
    (Feasible G s t X L B) (fun _ hp => hp.bounded)
    (fun _ hp _ hd₀ hd₁ => hp.shiftFloor hd₀ hd₁)
    (costs X) (distancePoint G w₀ s L) hp₀
  let p : Point V → ℝ := gridValue q
  let w := candidateWeight X L (before p) (after p) hq.ordered
  refine ⟨w, hq.candidate hL, ?_, ?_⟩
  · intro v hv
    apply candidateWeight_on_grid X L (before p) (after p) hq.ordered
    · intro u
      exact ⟨((q (TerminalPorts.core u, false) : ℕ) : ℤ), by simp [p, before, gridValue]⟩
    · intro u
      exact ⟨((q (TerminalPorts.core u, true) : ℕ) : ℤ), by simp [p, after, gridValue]⟩
    · exact hv
  · intro z hz
    have hpz := distancePoint_feasible G z s t X L B hL hz
    have hcost := (hmin (distancePoint G z s L) hpz).trans
      (distancePoint_objective_le G z s X L)
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    have hmass : (CandidateOptimization.outsideMass X w : ℝ) =
        objective (costs X) p / (L : ℝ) := hq.candidate_mass
    have hR : (CandidateOptimization.outsideMass X w : ℝ) ≤
        (CandidateOptimization.outsideMass X z : ℝ) := by
      rw [hmass]
      apply (div_le_iff₀ hLR).mpr
      simpa only [mul_comm] using hcost
    exact_mod_cast hR

/-- Independently minimizing each label attains the aggregate finite-family
minimum. No joint-family optimization oracle is assumed. -/
theorem exists_family_grid_minimum (G : Digraph V) (A : Finset (V × V))
    (X : Finset V) (L B : ℕ) (hL : 0 < L) (w₀ : (V × V) → V → ℝ≥0)
    (hw₀ : ∀ p ∈ A, CandidateOptimization.IsCandidate G {p} X ((B : ℝ≥0) / L) (w₀ p)) :
    ∃ w : (V × V) → V → ℝ≥0,
      (∀ p ∈ A, CandidateOptimization.IsCandidate G {p} X ((B : ℝ≥0) / L) (w p)) ∧
      (∀ p ∈ A, ∀ v ∉ X, ∃ k : ℤ, 0 ≤ k ∧ (w p v : ℝ) = (k : ℝ) / L) ∧
      ∀ z : (V × V) → V → ℝ≥0,
        (∀ p ∈ A, CandidateOptimization.IsCandidate G {p} X ((B : ℝ≥0) / L) (z p)) →
        (∑ p ∈ A, CandidateOptimization.outsideMass X (w p)) ≤
          ∑ p ∈ A, CandidateOptimization.outsideMass X (z p) := by
  classical
  have hex (p : V × V) : ∃ w : V → ℝ≥0, p ∈ A →
      CandidateOptimization.IsCandidate G {p} X ((B : ℝ≥0) / L) w ∧
      (∀ v ∉ X, ∃ k : ℤ, 0 ≤ k ∧ (w v : ℝ) = (k : ℝ) / L) ∧
      ∀ z : V → ℝ≥0, CandidateOptimization.IsCandidate G {p} X ((B : ℝ≥0) / L) z →
        CandidateOptimization.outsideMass X w ≤ CandidateOptimization.outsideMass X z := by
    by_cases hp : p ∈ A
    · obtain ⟨w, hw⟩ := exists_candidate_grid_minimum G p.1 p.2 X L B hL (w₀ p) (hw₀ p hp)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨w₀ p, fun h => (hp h).elim⟩
  choose w hw using hex
  refine ⟨w, fun p hp => (hw p hp).1, fun p hp => (hw p hp).2.1, ?_⟩
  intro z hz
  exact Finset.sum_le_sum (fun p hp => (hw p hp).2.2 (z p) (hz p hp))

end
end DirectedFlowCutGap.CandidateGridOptimizer
