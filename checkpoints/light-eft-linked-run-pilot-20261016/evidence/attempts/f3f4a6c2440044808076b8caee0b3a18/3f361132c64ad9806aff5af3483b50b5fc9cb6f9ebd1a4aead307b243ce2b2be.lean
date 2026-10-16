import LightEFTSpanners.NativeSeedPruning

namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- A retained loop is possible only below the uniform threshold 1. This uses
its actual original ID and includes zero edge weights. -/
theorem NativeWeightedGirthAbove.loop_threshold {G : Graph V E} {R : Finset E}
    {w : E → ℝ≥0} {b : ℝ≥0} (hg : NativeWeightedGirthAbove G R w b)
    {e : E} (he : e ∈ R) (u : G.vertexSet) (hl : G.IsLink e u.val u.val) : b < 1 := by
  let p : Walk G R ∅ u u := .cons e hl he (by simp) (.nil u)
  have h := hg u p (by simp [p,Walk.edgeList]) e (by simp [p,Walk.edgeList])
  simp only [p,Walk.weight,add_zero] at h
  by_contra hn
  have hb : 1 ≤ b := le_of_not_gt hn
  exact (not_lt_of_ge (by nlinarith)) h

/-- Two distinct retained parallel IDs force the threshold below 2. The two
cycle inequalities also rule out the case where both weights are zero. -/
theorem NativeWeightedGirthAbove.parallel_threshold [DecidableEq E]
    {G : Graph V E} {R : Finset E} {w : E → ℝ≥0} {b : ℝ≥0}
    (hg : NativeWeightedGirthAbove G R w b) {e d : E} (he : e ∈ R) (hd : d ∈ R)
    (hne : e ≠ d) (u v : G.vertexSet) (hel : G.IsLink e u.val v.val)
    (hdl : G.IsLink d u.val v.val) : b < 2 := by
  let p : Walk G R ∅ u u := .cons e hel he (by simp)
    (.cons d hdl.symm hd (by simp) (.nil u))
  have hn : p.edgeList.Nodup := by simp [p,Walk.edgeList,hne]
  have h1 := hg u p hn e (by simp [p,Walk.edgeList])
  have h2 := hg u p hn d (by simp [p,Walk.edgeList])
  simp only [p,Walk.weight,add_zero] at h1 h2
  by_contra h
  have hb : 2 ≤ b := le_of_not_gt h
  nlinarith

/-- At threshold at least 2 it is legitimate to forget edge identities, since
actual native simplicity (no loops or parallel IDs) has first been proved. -/
theorem NativeWeightedGirthAbove.simple [DecidableEq E] {G : Graph V E} {R : Finset E}
    {w : E → ℝ≥0} {b : ℝ≥0} (hg : NativeWeightedGirthAbove G R w b) (hb : 2 ≤ b) :
    (G.restrict (R : Set E)).Simple := by
  refine {not_isLoopAt := ?_,eq_of_isLink := ?_}
  · intro e u hl
    have h := hg.loop_threshold hl.1 ⟨u,hl.2.left_mem⟩ hl.2
    nlinarith
  · intro e d u v he hd
    by_contra hne
    have h := hg.parallel_threshold he.1 hd.1 hne ⟨u,he.2.left_mem⟩ ⟨v,he.2.right_mem⟩ he.2 hd.2
    exact (not_lt_of_ge hb) h

/-- A singleton/empty vertex host has no retained IDs once loops are excluded.
The actual-input premise prevents counting unused ambient IDs as edges. -/
theorem girth_subsingleton_empty [DecidableEq E] {G : Graph V E} {R : Finset E}
    {w : E → ℝ≥0} {b : ℝ≥0} (hg : NativeWeightedGirthAbove G R w b) (hb : 1 ≤ b)
    (hinput : ∀ e ∈ R, e ∈ G.edgeSet) [Subsingleton G.vertexSet] : R = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨u,v,hl⟩ := Graph.exists_isLink_of_mem_edgeSet (hinput e he)
  have huv : u = v := congrArg Subtype.val (Subsingleton.elim
    (⟨u,hl.left_mem⟩ : G.vertexSet) ⟨v,hl.right_mem⟩)
  subst v
  exact (not_lt_of_ge hb) (hg.loop_threshold he ⟨u,hl.left_mem⟩ hl)

end LightEFTSpanners.NativeWeighted
