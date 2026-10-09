import DirectedFlowCutGap.Basic

/-!
# Attained bounded candidate cuts

The candidate optimization in Algorithm 2 is a genuine finite-dimensional
minimum. Endpoints are excluded by the underlying actual-path constraints.
The objective counts only vertices outside the current integral cut. These
results prove existence and objective bounds, not an LP running time.
-/

namespace DirectedFlowCutGap.CandidateOptimization

noncomputable section
open scoped BigOperators NNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact candidate domain, including the cap only outside the cut. -/
def IsCandidate (G : Digraph V) (D : Set (V × V)) (X : Finset V)
    (cap : ℝ≥0) (w : V → ℝ≥0) : Prop :=
  IsFractionalCut G w D ∧ (∀ v ∈ X, w v = 1) ∧ (∀ v ∉ X, w v ≤ cap)

/-- The objective used by a candidate optimizer. -/
def outsideMass (X : Finset V) (w : V → ℝ≥0) : ℝ≥0 :=
  ∑ v ∈ Finset.univ.filter (fun v => v ∉ X), w v

/-- Set already cut vertices to one, preserving every other coordinate. -/
def installCut (X : Finset V) (w : V → ℝ≥0) (v : V) : ℝ≥0 :=
  if v ∈ X then 1 else w v

omit [Fintype V] in
@[simp] theorem installCut_mem (X : Finset V) (w : V → ℝ≥0) {v : V}
    (hv : v ∈ X) : installCut X w v = 1 := by simp [installCut, hv]

omit [Fintype V] in
@[simp] theorem installCut_not_mem (X : Finset V) (w : V → ℝ≥0) {v : V}
    (hv : v ∉ X) : installCut X w v = w v := by simp [installCut, hv]

@[simp] theorem outsideMass_installCut (X : Finset V) (w : V → ℝ≥0) :
    outsideMass X (installCut X w) = outsideMass X w := by
  apply Finset.sum_congr rfl
  intro v hv
  exact installCut_not_mem X w (Finset.mem_filter.mp hv).2

omit [Fintype V] in
/-- Raising a cut vertex to one is enough, even if its old weight exceeded one. -/
theorem installCut_fractional (G : Digraph V) (D : Set (V × V))
    (X : Finset V) (w : V → ℝ≥0) (hw : IsFractionalCut G w D) :
    IsFractionalCut G (installCut X w) D := by
  rw [isFractionalCut_iff] at hw ⊢
  intro s t hst p
  by_cases h : ∃ v ∈ p.internalVertices, v ∈ X
  · obtain ⟨v, hv, hvX⟩ := h
    calc
      1 = installCut X w v := (installCut_mem X w hvX).symm
      _ ≤ p.weight (installCut X w) := Finset.single_le_sum (fun _ _ => zero_le) hv
  · have he : p.weight (installCut X w) = p.weight w := by
      apply Finset.sum_congr rfl
      intro v hv
      exact installCut_not_mem X w (fun hvX => h ⟨v, hv, hvX⟩)
    rw [he]
    exact hw s t hst p

omit [Fintype V] in
theorem installCut_candidate (G : Digraph V) (D : Set (V × V))
    (X : Finset V) (cap : ℝ≥0) (w : V → ℝ≥0)
    (hw : IsFractionalCut G w D) (hcap : ∀ v ∉ X, w v ≤ cap) :
    IsCandidate G D X cap (installCut X w) := by
  refine ⟨installCut_fractional G D X w hw, ?_, ?_⟩
  · intro v hv
    exact installCut_mem X w hv
  · intro v hv
    simpa only [installCut_not_mem X w hv] using hcap v hv

omit [Fintype V] in
theorem isClosed_fractional (G : Digraph V) (D : Set (V × V)) :
    IsClosed {w : V → ℝ≥0 | IsFractionalCut G w D} := by
  simp only [isFractionalCut_iff, Set.ofPred_forall]
  refine isClosed_iInter fun s => isClosed_iInter fun t =>
    isClosed_iInter fun hst => isClosed_iInter fun p => ?_
  exact isClosed_le continuous_const (by unfold SimplePath.weight; fun_prop)

omit [Fintype V] in
theorem isClosed_candidate (G : Digraph V) (D : Set (V × V))
    (X : Finset V) (cap : ℝ≥0) :
    IsClosed {w : V → ℝ≥0 | IsCandidate G D X cap w} := by
  unfold IsCandidate
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply (isClosed_fractional G D).inter
  apply IsClosed.inter
  · exact isClosed_iInter fun v => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply v) continuous_const
  · exact isClosed_iInter fun v => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply v) continuous_const

omit [Fintype V] in
theorem isCompact_candidate (G : Digraph V) (D : Set (V × V))
    (X : Finset V) (cap : ℝ≥0) :
    IsCompact {w : V → ℝ≥0 | IsCandidate G D X cap w} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : V => (0 : ℝ≥0))
    (fun _ => max 1 cap))).of_isClosed_subset (isClosed_candidate G D X cap)
  intro w hw
  refine ⟨fun v => zero_le, fun v => ?_⟩
  by_cases hv : v ∈ X
  · rw [hw.2.1 v hv]
    exact le_max_left _ _
  · exact (hw.2.2 v hv).trans (le_max_right _ _)

/-- A candidate optimizer exists; an optimizer is not supplied as a premise. -/
theorem exists_minimum (G : Digraph V) (D : Set (V × V))
    (X : Finset V) (cap : ℝ≥0) (w₀ : V → ℝ≥0)
    (hfeas : IsFractionalCut G w₀ D) (hcap : ∀ v ∉ X, w₀ v ≤ cap) :
    ∃ w : V → ℝ≥0, IsCandidate G D X cap w ∧
      outsideMass X w ≤ outsideMass X w₀ ∧
      ∀ z, IsCandidate G D X cap z → outsideMass X w ≤ outsideMass X z := by
  have hnonempty : {w : V → ℝ≥0 | IsCandidate G D X cap w}.Nonempty :=
    ⟨installCut X w₀, installCut_candidate G D X cap w₀ hfeas hcap⟩
  obtain ⟨w, hw, hmin⟩ := (isCompact_candidate G D X cap).exists_isMinOn
    (f := outsideMass X) hnonempty (by unfold outsideMass; fun_prop)
  refine ⟨w, hw, ?_, fun z hz => hmin hz⟩
  simpa only [Set.mem_ofPred_eq, outsideMass_installCut] using
    hmin (installCut_candidate G D X cap w₀ hfeas hcap)

/-- An uncut demanded path forces at least one unit of remaining mass. -/
theorem one_le_outsideMass_of_uncut (G : Digraph V) (D : Set (V × V))
    (X : Finset V) (w : V → ℝ≥0) (hw : IsFractionalCut G w D)
    {s t : V} (hst : (s, t) ∈ D) (huncut : ¬CutsPair G X s t) :
    1 ≤ outsideMass X w := by
  obtain ⟨p, hp⟩ := (not_cutsPair_iff G X s t).mp huncut
  have hpath : 1 ≤ p.weight w := (isFractionalCut_iff G w D).mp hw s t hst p
  apply hpath.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp v hv⟩
  · intros
    exact zero_le

end
end DirectedFlowCutGap.CandidateOptimization
