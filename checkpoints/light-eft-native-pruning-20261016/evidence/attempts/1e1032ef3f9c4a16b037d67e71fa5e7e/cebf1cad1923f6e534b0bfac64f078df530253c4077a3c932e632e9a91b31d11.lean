import LightEFTSpanners.NativeMinimumForest

namespace LightEFTSpanners.NativeWeighted
open Finset
open scoped NNReal
variable {V E : Type*}
attribute [local instance] Classical.propDecidable

/-- Deleting one edge leaves every vertex connected to at least one endpoint
within its former component. The proof uses the original-ID walk directly. -/
theorem Walk.erase_sides [DecidableEq E] {G : Graph V E} {K : Finset E}
    {e : E} {a x y : G.vertexSet} (p : Walk G K ∅ a x) (hl : G.IsLink e x.val y.val) :
    NativeReach G (K.erase e) a x ∨ NativeReach G (K.erase e) a y := by
  induction p with
  | nil u => exact Or.inl (.refl u)
  | @cons a b x d hlink hd hf p ih =>
    by_cases hde : d = e
    · subst d
      rcases hlink.left_eq_or_eq hl with hx | hy
      · have hx' : a = x := Subtype.ext hx
        subst a; exact Or.inl (.refl _)
      · have hy' : a = y := Subtype.ext hy
        subst a; exact Or.inr (.refl _)
    · have hab : NativeReach G (K.erase e) a b := .single hlink (mem_erase.mpr ⟨hde,hd⟩)
      exact (ih hl).elim (fun h => Or.inl (hab.trans h)) (fun h => Or.inr (hab.trans h))

/-- A cut-crossing step, with suffix reachabilities retained for exchange. -/
theorem Walk.crossing_step {G : Graph V E} {A R : Finset E} {a b : G.vertexSet}
    (p : Walk G A ∅ a b) (hn : ¬ NativeReach G R a b) :
    ∃ d ∈ p.edgeList, ∃ u v : G.vertexSet, G.IsLink d u.val v.val ∧
      ¬ NativeReach G R u v ∧ NativeReach G A u b ∧ NativeReach G A v b := by
  induction p with
  | nil u => exact False.elim (hn (.refl u))
  | @cons a z b e hl he hf p ih =>
    by_cases haz : NativeReach G R a z
    · obtain ⟨d,hd,u,v,hl',hnot,hu,hv⟩ := ih (fun h => hn (haz.trans h))
      exact ⟨d,List.mem_cons_of_mem e hd,u,v,hl',hnot,hu,hv⟩
    · exact ⟨e,by simp [Walk.edgeList],a,z,hl,haz,⟨.cons e hl he hf p⟩,⟨p⟩⟩

/-- An edge crossing the deletion cut restores the deleted edge, provided both
its endpoints belong to the old component. This includes parallel replacements. -/
theorem restore_deleted_edge [DecidableEq E] {G : Graph V E} {K : Finset E}
    {e d : E} {x y u v : G.vertexSet} (he : G.IsLink e x.val y.val)
    (hd : G.IsLink d u.val v.val) (hu : NativeReach G K u x) (hv : NativeReach G K v x)
    (hcut : ¬ NativeReach G (K.erase e) u v) :
    NativeReach G (insert d (K.erase e)) x y := by
  obtain ⟨pu⟩ := hu
  obtain ⟨pv⟩ := hv
  have hsub : K.erase e ⊆ insert d (K.erase e) := subset_insert _ _
  have hdJ : NativeReach G (insert d (K.erase e)) u v := .single hd (mem_insert_self _ _)
  rcases pu.erase_sides he with hux | huy <;> rcases pv.erase_sides he with hvx | hvy
  · exact False.elim (hcut (hux.trans hvx.symm))
  · exact ((hux.symm.mono hsub).trans hdJ).trans (hvy.mono hsub)
  · exact ((hvx.symm.mono hsub).trans hdJ.symm).trans (huy.mono hsub)
  · exact False.elim (hcut (huy.trans hvy.symm))

/-- Cut-exchange optimality for original IDs, including equal/zero weights. -/
theorem native_exchange_weight [DecidableEq E] {G : Graph V E} {w : E → ℝ≥0}
    {A K : Finset E} (hK : NativeSpans G A K)
    (hopt : ∀ J, NativeSpans G A J → totalWeight w K ≤ totalWeight w J)
    {e d : E} (heK : e ∈ K) (hdA : d ∈ A) {x y u v : G.vertexSet}
    (he : G.IsLink e x.val y.val) (hd : G.IsLink d u.val v.val)
    (hu : NativeReach G K u x) (hv : NativeReach G K v x)
    (hcut : ¬ NativeReach G (K.erase e) u v) : w e ≤ w d := by
  classical
  let J := insert d (K.erase e)
  have hrestore : NativeReach G J x y := restore_deleted_edge he hd hu hv hcut
  have hJ : NativeSpans G A J := by
    refine ⟨insert_subset hdA ((erase_subset _ _).trans hK.1),?_⟩
    intro a b hab
    exact native_reach_replace_edge he hrestore (subset_insert _ _) (hK.2 a b hab)
  have hdnot : d ∉ K.erase e := fun h => hcut (.single hd h)
  have hsum : totalWeight w K = w e + totalWeight w (K.erase e) :=
    (Finset.add_sum_erase K w heK).symm
  have hsumJ : totalWeight w J = w d + totalWeight w (K.erase e) := by
    simp only [J,totalWeight,sum_insert hdnot]
  have h := hopt J hJ
  rw [hsum,hsumJ] at h
  exact (add_le_add_iff_right _).mp h

/-- The native bottleneck cycle property follows from a constructed minimum
forest: some maximum-weight cycle ID lies outside that forest, even with ties.
No simplification deletes a loop or merges parallel IDs before this proof. -/
theorem native_cycle_maximum_outside [DecidableEq E] {G : Graph V E} {w : E → ℝ≥0}
    {A K : Finset E} (hK : NativeSpans G A K) (hforest : NativeForest G K)
    (hopt : ∀ J, NativeSpans G A J → totalWeight w K ≤ totalWeight w J)
    {a : G.vertexSet} (p : Walk G A ∅ a a) (hp : p.edgeList.Nodup)
    (hne : p.edgeList ≠ []) :
    ∃ d ∈ p.edgeList, d ∉ K ∧ ∀ z ∈ p.edgeList, w z ≤ w d := by
  classical
  have hne' : p.edgeList.toFinset.Nonempty := by
    rcases List.exists_mem_of_ne_nil hne with ⟨d,hd⟩
    exact ⟨d,List.mem_toFinset.mpr hd⟩
  obtain ⟨e,he,hmax⟩ := exists_max_image p.edgeList.toFinset w hne'
  have hep : e ∈ p.edgeList := List.mem_toFinset.mp he
  have hmax' : ∀ z ∈ p.edgeList, w z ≤ w e := fun z hz => hmax z (List.mem_toFinset.mpr hz)
  by_cases heK : e ∈ K
  · obtain ⟨x,y,hl,r,_,hmem,_⟩ := p.cycle_complement w hp e hep
    have hcut : ¬ NativeReach G (K.erase e) y x := fun h => hforest e heK x y hl h.symm
    obtain ⟨d,hd,u,v,hdlink,hdcut,hu,hv⟩ := r.crossing_step hcut
    obtain ⟨hdp,hdne⟩ := (hmem d).mp hd
    have hdK : d ∉ K := fun h => hdcut (.single hdlink (mem_erase.mpr ⟨hdne,h⟩))
    have hwd := native_exchange_weight hK hopt heK (p.edgeList_selected d hdp)
      hl hdlink (hK.2 u x hu) (hK.2 v x hv) hdcut
    exact ⟨d,hdp,hdK,fun z hz => (hmax' z hz).trans hwd⟩
  · exact ⟨e,hep,heK,hmax'⟩

end LightEFTSpanners.NativeWeighted
