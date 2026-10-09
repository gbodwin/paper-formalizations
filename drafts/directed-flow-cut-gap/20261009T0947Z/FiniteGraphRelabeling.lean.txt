import DirectedFlowCutGap.Basic

/-!
# Exact relabeling of the endpoint-excluding cut model

These proof-side bridges connect finite array indices to retained construction
labels. Paths, internal vertices, distances and actual cuts are transported
through a supplied equivalence. No equivalence is chosen or evaluated by an
algorithm in this file.
-/

namespace DirectedFlowCutGap.FiniteGraphRelabeling

variable {A B : Type*} [DecidableEq A] [DecidableEq B]
variable {G : Digraph A} {H : Digraph B}

def mapPath (e : A ≃ B) (h : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b))
    {s t : A} (p : SimplePath G s t) : SimplePath H (e s) (e t) where
  edgeLength := p.edgeLength
  vertex i := e (p.vertex i)
  source_eq := congrArg e p.source_eq
  target_eq := congrArg e p.target_eq
  injective := e.injective.comp p.injective
  adjacent i := (h _ _).mp (p.adjacent i)

omit [DecidableEq A] [DecidableEq B] in
theorem inverse_adj (e : A ≃ B) (h : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b))
    (a b : B) : H.Adj a b ↔ G.Adj (e.symm a) (e.symm b) := by
  simpa using (h (e.symm a) (e.symm b)).symm

theorem mapPath_internalVertices (e : A ≃ B)
    (h : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) {s t : A} (p : SimplePath G s t) :
    (mapPath e h p).internalVertices = p.internalVertices.image e := by
  ext b
  constructor
  · intro hb
    obtain ⟨⟨i,hi⟩,hs,ht⟩ := ((mapPath e h p).mem_internalVertices b).mp hb
    refine Finset.mem_image.mpr ⟨p.vertex i,(p.mem_internalVertices _).mpr ?_,hi⟩
    exact ⟨⟨i,rfl⟩,fun he => hs (hi.symm.trans (congrArg e he)),
      fun he => ht (hi.symm.trans (congrArg e he))⟩
  · intro hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨⟨i,hi⟩,hs,ht⟩ := (p.mem_internalVertices a).mp ha
    apply ((mapPath e h p).mem_internalVertices _).mpr
    exact ⟨⟨i,congrArg e hi⟩,fun he => hs (e.injective he),
      fun he => ht (e.injective he)⟩

open scoped NNReal ENNReal

theorem mapPath_weight (e : A ≃ B)
    (h : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) {s t : A}
    (p : SimplePath G s t) (w : B → ℝ≥0) :
    (mapPath e h p).weight w = p.weight (fun a => w (e a)) := by
  rw [SimplePath.weight,mapPath_internalVertices,Finset.sum_image]
  · rfl
  · intro a _ b _ he
    exact e.injective he

theorem vertexDistance_eq (e : A ≃ B)
    (h : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b))
    (w : B → ℝ≥0) (s t : A) :
    vertexDistance H w (e s) (e t) = vertexDistance G (fun a => w (e a)) s t := by
  apply le_antisymm
  · rw [le_vertexDistance_iff]
    intro p
    have hp := vertexDistance_le_weight w (mapPath e h p)
    rw [mapPath_weight] at hp
    exact hp
  · rw [le_vertexDistance_iff]
    intro p
    have hp := vertexDistance_le_weight (fun a => w (e a))
      (mapPath e.symm (inverse_adj e h) p)
    simpa only [Equiv.symm_apply_apply,mapPath_weight,Equiv.apply_symm_apply] using hp

/-- Pull back the actual finite cut, preserving endpoint exclusion. -/
theorem cutsPair_pullback (e : A ≃ B)
    (h : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) (X : Finset B) {s t : A}
    (hX : CutsPair H X (e s) (e t)) : CutsPair G (X.image e.symm) s t := by
  intro p
  obtain ⟨b,hb,hbX⟩ := hX (mapPath e h p)
  rw [mapPath_internalVertices] at hb
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  exact ⟨a,ha,Finset.mem_image.mpr ⟨e a,hbX,e.symm_apply_apply a⟩⟩

theorem threshold_cut_pullback (e : A ≃ B)
    (h : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) (w : B → ℝ≥0) (X : Finset B)
    (hX : IsIntegralCut H X (thresholdDemands H w)) :
    IsIntegralCut G (X.image e.symm) (thresholdDemands G (fun a => w (e a))) := by
  intro s t hst
  apply cutsPair_pullback e h X
  apply hX
  change 1 ≤ vertexDistance H w (e s) (e t)
  rw [vertexDistance_eq e h]
  exact hst

end DirectedFlowCutGap.FiniteGraphRelabeling
