import LightEFTSpanners.NativeTracedSampling

namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Fault-free reachability, retaining actual original edge IDs in its witness. -/
def NativeReach (G : Graph V E) (A : Finset E) (u v : G.vertexSet) : Prop :=
  Nonempty (Walk G A ∅ u v)

namespace NativeReach
variable {G : Graph V E} {A B : Finset E} {u v z : G.vertexSet}
theorem refl (u : G.vertexSet) : NativeReach G A u u := ⟨.nil u⟩
theorem symm (h : NativeReach G A u v) : NativeReach G A v u := by
  obtain ⟨p⟩ := h; exact ⟨p.reverse⟩
theorem trans (h : NativeReach G A u v) (h' : NativeReach G A v z) : NativeReach G A u z := by
  obtain ⟨p⟩ := h; obtain ⟨q⟩ := h'; exact ⟨p.append q⟩
theorem mono (h : NativeReach G A u v) (hAB : A ⊆ B) : NativeReach G B u v := by
  obtain ⟨p⟩ := h; exact ⟨p.mono hAB⟩
theorem single {e : E} (hl : G.IsLink e u.val v.val) (he : e ∈ A) : NativeReach G A u v :=
  ⟨.cons e hl he (by simp) (.nil _)⟩

/-- A replacement also works in the other endpoint orientation. -/
theorem same_link {e : E} (h : NativeReach G A u v) (hl : G.IsLink e u.val v.val)
    {x y : G.vertexSet} (hl' : G.IsLink e x.val y.val) : NativeReach G A x y := by
  rcases hl'.eq_and_eq_or_eq_and_eq hl with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · have hx' : x = u := Subtype.ext hx
    have hy' : y = v := Subtype.ext hy
    simpa only [hx',hy'] using h
  · have hx' : x = v := Subtype.ext hx
    have hy' : y = u := Subtype.ext hy
    simpa only [hx',hy'] using h.symm
end NativeReach

/-- A connected replacement for every input step replaces an entire walk. -/
theorem native_reach_replace {G : Graph V E} {A B : Finset E}
    (h : ∀ e ∈ A, ∀ u v : G.vertexSet, G.IsLink e u.val v.val → NativeReach G B u v)
    {u v : G.vertexSet} (hp : NativeReach G A u v) : NativeReach G B u v := by
  obtain ⟨p⟩ := hp
  induction p with
  | nil u => exact .refl u
  | cons e hl he hf p ih => exact (h e he _ _ hl).trans ih

/-- Replacing one deleted ID by a path restores every old connection. -/
theorem native_reach_replace_edge [DecidableEq E] {G : Graph V E} {A B : Finset E}
    {e : E} {x y : G.vertexSet} (hl : G.IsLink e x.val y.val)
    (hxy : NativeReach G B x y) (hAB : A.erase e ⊆ B)
    {u v : G.vertexSet} (hp : NativeReach G A u v) : NativeReach G B u v := by
  apply native_reach_replace (A:=A) (B:=B) ?_ hp
  intro d hd a b hab
  by_cases hde : d = e
  · subst d; exact hxy.same_link hl hab
  · exact .single hab (hAB (mem_erase.mpr ⟨hde,hd⟩))

/-- Spanning means equality of reachability on the original actual vertices.
No connectedness/nonemptiness hypothesis is imposed on the whole ambient graph. -/
def NativeSpans (G : Graph V E) (A K : Finset E) : Prop :=
  K ⊆ A ∧ ∀ u v : G.vertexSet, NativeReach G A u v → NativeReach G K u v

/-- Every retained original ID disconnects its endpoints when removed.
This excludes loops and parallel two-edge cycles rather than forgetting them. -/
def NativeForest [DecidableEq E] (G : Graph V E) (K : Finset E) : Prop :=
  ∀ e ∈ K, ∀ u v : G.vertexSet, G.IsLink e u.val v.val → ¬ NativeReach G (K.erase e) u v

/-- Minimize actual native weight, then cardinality among ties. The secondary
minimum is necessary because zero-weight cycles may occur. -/
theorem exists_native_minimum_forest [DecidableEq E] (G : Graph V E) (w : E → ℝ≥0)
    (A : Finset E) :
    ∃ K : Finset E, NativeSpans G A K ∧ NativeForest G K ∧
      ∀ J : Finset E, NativeSpans G A J → totalWeight w K ≤ totalWeight w J := by
  classical
  let S := A.powerset.filter (NativeSpans G A)
  have hAA : NativeSpans G A A := ⟨Subset.rfl,fun _ _ h => h⟩
  have hAS : A ∈ S := mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl,hAA⟩
  obtain ⟨M,hMS,hmin⟩ := S.exists_min_image (totalWeight w) ⟨A,hAS⟩
  let Z := S.filter fun K => totalWeight w K = totalWeight w M
  have hMZ : M ∈ Z := mem_filter.mpr ⟨hMS,rfl⟩
  obtain ⟨K,hKZ,hcard⟩ := Z.exists_min_image Finset.card ⟨M,hMZ⟩
  have hKS : K ∈ S := (mem_filter.mp hKZ).1
  have hK : NativeSpans G A K := (mem_filter.mp hKS).2
  have hKM : totalWeight w K = totalWeight w M := (mem_filter.mp hKZ).2
  have hopt : ∀ J, NativeSpans G A J → totalWeight w K ≤ totalWeight w J := by
    intro J hJ
    rw [hKM]
    exact hmin J (mem_filter.mpr ⟨mem_powerset.mpr hJ.1,hJ⟩)
  refine ⟨K,hK,?_,hopt⟩
  intro e he u v hl hconn
  have hdel : NativeSpans G A (K.erase e) := by
    refine ⟨(erase_subset _ _).trans hK.1,?_⟩
    intro a b hab
    exact native_reach_replace_edge hl hconn Subset.rfl (hK.2 a b hab)
  have hle : totalWeight w (K.erase e) ≤ totalWeight w K :=
    sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => by positivity)
  have heq : totalWeight w (K.erase e) = totalWeight w M :=
    (le_antisymm hle (hopt _ hdel)).trans hKM
  have hZ : K.erase e ∈ Z := mem_filter.mpr
    ⟨mem_filter.mpr ⟨mem_powerset.mpr hdel.1,hdel⟩,heq⟩
  have hc := hcard _ hZ
  have hlt := card_erase_lt_of_mem he
  omega

/-- The endpoint-disconnection certificate is the actual native bridge notion. -/
theorem NativeForest.bridges [DecidableEq E] {G : Graph V E} {K : Finset E}
    (h : NativeForest G K) : ∀ e ∈ (G.restrict (K : Set E)).edgeSet,
      (G.restrict (K : Set E)).IsBridge e := by
  intro e he
  obtain ⟨u,v,hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
  apply (MultigraphCuts.bridge_iff_not_reachable_delete (G.restrict (K : Set E)) hl).mpr
  intro hr
  have heq : ((G.restrict (K : Set E)).deleteEdges {e}).toSimpleGraph =
      (G.restrict ((K.erase e : Finset E) : Set E)).toSimpleGraph := by
    ext x y
    simp only [Graph.toSimpleGraph_adj,Graph.Adj,Graph.deleteEdges_isLink,
      Graph.restrict_isLink,mem_coe,mem_erase,Set.mem_singleton_iff]
    tauto
  rw [heq] at hr
  have hp := (walk_empty_iff_restrict G (K.erase e) ⟨u,hl.2.left_mem⟩ ⟨v,hl.2.right_mem⟩).mpr hr
  exact h e hl.1 ⟨u,hl.2.left_mem⟩ ⟨v,hl.2.right_mem⟩ hl.2 hp

end LightEFTSpanners.NativeWeighted
