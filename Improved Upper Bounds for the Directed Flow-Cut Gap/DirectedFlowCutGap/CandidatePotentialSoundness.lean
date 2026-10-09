import DirectedFlowCutGap.CandidateGridRounding

/-!
# Endpoint-safe soundness of candidate distance potentials

These lemmas turn local split-potential inequalities into the actual
endpoint-excluding path inequalities used by CandidateOptimization. Ports are
temporary subroutine vertices. This does not yet construct shortest-distance
potentials from a candidate, or identify the port constraints with the finite
integer system in CandidateGridRounding.
-/

namespace DirectedFlowCutGap.CandidatePotentialSoundness

noncomputable section
open scoped BigOperators NNReal

variable {V : Type*} [DecidableEq V]

/-- Edge inequalities telescope on the actual finite sequence of a simple path. -/
theorem path_potential_bound {G : Digraph V} {s t : V} (p : SimplePath G s t)
    (x y : V → ℝ)
    (hedge : ∀ u v, G.Adj u v → x v ≤ y u) :
    y t - x s ≤ ∑ v ∈ p.vertices, (y v - x v) := by
  have he : (∑ i : Fin p.edgeLength, x (p.vertex i.succ)) ≤
      ∑ i : Fin p.edgeLength, y (p.vertex i.castSucc) :=
    Finset.sum_le_sum (fun i _ => hedge _ _ (p.adjacent i))
  have hx := Fin.sum_univ_succ (fun i : Fin (p.edgeLength + 1) => x (p.vertex i))
  have hy := Fin.sum_univ_castSucc (fun i : Fin (p.edgeLength + 1) => y (p.vertex i))
  have hsum : (∑ v ∈ p.vertices, (y v - x v)) =
      (∑ i : Fin (p.edgeLength + 1), (y (p.vertex i) - x (p.vertex i))) := by
    rw [SimplePath.vertices, Finset.sum_image]
    exact fun _ _ _ _ h => p.injective h
  rw [hsum, Finset.sum_sub_distrib, hx, hy]
  simp only [p.source_eq, p.target_eq]
  linarith

/-- Zero endpoint gaps remove exactly the two excluded endpoints, even for a
length-zero path. No distinct-endpoint assumption is needed. -/
theorem path_internal_potential_bound {G : Digraph V} {s t : V}
    (p : SimplePath G s t) (x y : V → ℝ)
    (hedge : ∀ u v, G.Adj u v → x v ≤ y u)
    (hs : y s - x s = 0) (ht : y t - x t = 0) :
    y t - x s ≤ ∑ v ∈ p.internalVertices, (y v - x v) := by
  have heq : (∑ v ∈ p.internalVertices, (y v - x v)) =
      ∑ v ∈ p.vertices, (y v - x v) := by
    apply Finset.sum_subset (Finset.sdiff_subset : p.internalVertices ⊆ p.vertices)
    intro v hv hnot
    have hend : v = s ∨ v = t := by
      by_contra h
      apply hnot
      simp only [Finset.mem_sdiff]
      refine ⟨hv, ?_⟩
      simpa using h
    rcases hend with rfl | rfl
    · exact hs
    · exact ht
  rw [heq]
  exact path_potential_bound p x y hedge

/-- Local split-potential inequalities on permanent ports certify the original
endpoint-excluding fractional cut, including self and unreachable pairs. -/
theorem fractional_of_port_potentials (G : Digraph V) (w : V → ℝ≥0)
    (s t : V) (L : ℝ) (hL : 0 < L)
    (x y : TerminalPorts.Vertex V → ℝ)
    (hmono : ∀ v, x v ≤ y v)
    (hsource : x (TerminalPorts.source s) = 0)
    (hsink : y (TerminalPorts.sink t) = L)
    (hgap : ∀ v, y v - x v ≤ L * (TerminalPorts.extend w v : ℝ))
    (hedge : ∀ u v, (TerminalPorts.graph G).Adj u v → x v ≤ y u) :
    IsFractionalCut G w {(s, t)} := by
  rw [isFractionalCut_iff]
  intro a b hab p
  have hab' : (a, b) = (s, t) := Set.mem_singleton_iff.mp hab
  obtain ⟨ha, hb⟩ := Prod.mk.inj hab'
  subst a
  subst b
  obtain ⟨q, _, hweight⟩ := TerminalPorts.exists_lift_weight p w
  have hs : y (TerminalPorts.source s) - x (TerminalPorts.source s) = 0 := by
    have hg := hgap (TerminalPorts.source s)
    have hm := hmono (TerminalPorts.source s)
    simp only [TerminalPorts.extend_source, NNReal.coe_zero, mul_zero] at hg
    linarith
  have ht : y (TerminalPorts.sink t) - x (TerminalPorts.sink t) = 0 := by
    have hg := hgap (TerminalPorts.sink t)
    have hm := hmono (TerminalPorts.sink t)
    simp only [TerminalPorts.extend_sink, NNReal.coe_zero, mul_zero] at hg
    linarith
  have hpath := path_internal_potential_bound q x y hedge hs ht
  rw [hsource, hsink, sub_zero] at hpath
  have hsum : (∑ v ∈ q.internalVertices, (y v - x v)) ≤
      L * (q.weight (TerminalPorts.extend w) : ℝ) := by
    calc
      _ ≤ ∑ v ∈ q.internalVertices, L * (TerminalPorts.extend w v : ℝ) :=
        Finset.sum_le_sum (fun v _ => hgap v)
      _ = L * (q.weight (TerminalPorts.extend w) : ℝ) := by
        simp only [SimplePath.weight, NNReal.coe_sum, Finset.mul_sum]
  rw [hweight] at hsum
  have hone : (1 : ℝ) ≤ (p.weight w : ℝ) := by nlinarith
  exact_mod_cast hone


variable [Fintype V]

/-- Reconstruct exactly the candidate convention: one on X, potential gap/L
elsewhere. The nonnegative gap proof supplies the NNReal type. -/
def candidateWeight (X : Finset V) (L : ℕ)
    (x y : TerminalPorts.Vertex V → ℝ) (hmono : ∀ v, x v ≤ y v) : V → ℝ≥0 :=
  CandidateOptimization.installCut X (fun v =>
    NNReal.mk ((y (TerminalPorts.core v) - x (TerminalPorts.core v)) / (L : ℝ))
      (div_nonneg (sub_nonneg.mpr (hmono _)) (Nat.cast_nonneg _)))

/-- The objective conversion is exact, with no contribution from X or ports. -/
theorem outsideMass_candidateWeight (X : Finset V) (L : ℕ)
    (x y : TerminalPorts.Vertex V → ℝ) (hmono : ∀ v, x v ≤ y v) :
    (CandidateOptimization.outsideMass X (candidateWeight X L x y hmono) : ℝ) =
      (∑ v ∈ Finset.univ.filter (fun v => v ∉ X),
        (y (TerminalPorts.core v) - x (TerminalPorts.core v))) / (L : ℝ) := by
  rw [CandidateOptimization.outsideMass, NNReal.coe_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v hv
  simp [candidateWeight, CandidateOptimization.installCut,
    (Finset.mem_filter.mp hv).2]

omit [Fintype V] in
/-- Local potential constraints produce an actual bounded candidate with its
required weight one on X, even when the outside cap is below one. -/
theorem candidateWeight_isCandidate (G : Digraph V) (s t : V)
    (X : Finset V) (L B : ℕ) (hL : 0 < L)
    (x y : TerminalPorts.Vertex V → ℝ) (hmono : ∀ v, x v ≤ y v)
    (hsource : x (TerminalPorts.source s) = 0)
    (hsink : y (TerminalPorts.sink t) = (L : ℝ))
    (hports : ∀ a : V ⊕ V, y (.inr a) = x (.inr a))
    (hunit : ∀ v ∈ X, y (TerminalPorts.core v) - x (TerminalPorts.core v) ≤ L)
    (hcap : ∀ v ∉ X, y (TerminalPorts.core v) - x (TerminalPorts.core v) ≤ B)
    (hedge : ∀ u v, (TerminalPorts.graph G).Adj u v → x v ≤ y u) :
    CandidateOptimization.IsCandidate G {(s, t)} X ((B : ℝ≥0) / L)
      (candidateWeight X L x y hmono) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLR
  refine ⟨?_, ?_, ?_⟩
  · apply fractional_of_port_potentials G _ s t (L : ℝ) hLR x y hmono hsource hsink
    · intro a
      cases a with
      | inl v =>
        by_cases hv : v ∈ X
        · simpa [candidateWeight, CandidateOptimization.installCut, hv,
            TerminalPorts.extend] using hunit v hv
        · simp only [TerminalPorts.extend_core]
          change y (TerminalPorts.core v) - x (TerminalPorts.core v) ≤
            (L : ℝ) * (candidateWeight X L x y hmono v : ℝ)
          simp [candidateWeight, CandidateOptimization.installCut, hv,
            mul_div_cancel₀, hLne]
      | inr a => simp [TerminalPorts.extend, hports a]
    · exact hedge
  · intro v hv
    exact CandidateOptimization.installCut_mem X _ hv
  · intro v hv
    apply NNReal.coe_le_coe.mp
    have h := (div_le_div_iff_of_pos_right hLR).mpr (hcap v hv)
    simpa [candidateWeight, CandidateOptimization.installCut, hv] using h

omit [Fintype V] in
/-- Integer potentials give exact grid weights outside X. -/
theorem candidateWeight_on_grid (X : Finset V) (L : ℕ)
    (x y : TerminalPorts.Vertex V → ℝ) (hmono : ∀ v, x v ≤ y v)
    (hx : ∀ v, ∃ a : ℤ, x (TerminalPorts.core v) = a)
    (hy : ∀ v, ∃ b : ℤ, y (TerminalPorts.core v) = b)
    (v : V) (hv : v ∉ X) :
    ∃ k : ℤ, 0 ≤ k ∧ (candidateWeight X L x y hmono v : ℝ) = (k : ℝ) / L := by
  obtain ⟨a, ha⟩ := hx v
  obtain ⟨b, hb⟩ := hy v
  refine ⟨b - a, ?_, ?_⟩
  · have h := hmono (TerminalPorts.core v)
    rw [ha, hb] at h
    exact_mod_cast sub_nonneg.mpr h
  · simp [candidateWeight, CandidateOptimization.installCut, hv, ha, hb]

end
end DirectedFlowCutGap.CandidatePotentialSoundness
