import LightEFTSpanners.NativeCoreTreeConstruction

namespace LightEFTSpanners.EvenSplitting
open MultigraphCuts
variable {V E : Type*} [Fintype V] [Fintype E]
attribute [local instance] Classical.propDecidable

/-- The minimal deficient core is filled by internally constructed disjoint
spanning trees. Any supplied quotient forest family then lifts to genuine
original-edge forests, preserving all connections of the quotient family. -/
theorem expand_native_minimal_core_forests (G : Graph V E) (K : Finset V) (k : ℕ)
    (hne : K.Nonempty) (hactual : (K:Set V)⊆G.vertexSet)
    (hsmall : (G.edgeCut (K:Set V)).toFinset.card≤2*k)
    (hmin : ∀ S : Finset V,S⊂K → S.Nonempty →
      2*k≤(G.edgeCut (S:Set V)).toFinset.card)
    (A : Fin k → Set E)
    (hA : ∀ c,A c⊆(G.map (collapseOutside (K:Set V)ᶜ)).edgeSet)
    (hforest : ∀ c e,e∈((G.map (collapseOutside (K:Set V)ᶜ)).restrict (A c)).edgeSet →
      ((G.map (collapseOutside (K:Set V)ᶜ)).restrict (A c)).IsBridge e)
    (hdis : Pairwise (fun c d => Disjoint (A c) (A d))) :
    ∃ B : Fin k → Set E,(∀ c,B c⊆G.edgeSet ∧
      ∀ e∈(G.restrict (B c)).edgeSet,(G.restrict (B c)).IsBridge e) ∧
      Pairwise (fun c d => Disjoint (B c) (B d)) ∧
      ∀ c (x y : G.vertexSet),
        EdgeSetJoins (G.map (collapseOutside (K:Set V)ᶜ)) (A c)
          (collapseOutside (K:Set V)ᶜ x.val) (collapseOutside (K:Set V)ᶜ y.val) →
        EdgeSetJoins G (B c) x.val y.val := by
  obtain ⟨T,hT,hd⟩ := exists_native_minimal_core_trees G K k hne hactual hsmall hmin
  have hinner (c : Fin k) (e : E) (he : e∈T c) :
      ∃ u v,G.IsLink e u v ∧ collapseOutside (K:Set V)ᶜ u=collapseOutside (K:Set V)ᶜ v := by
    obtain ⟨u,v,huv⟩ := Graph.exists_isLink_of_mem_edgeSet ((hT c).1 he)
    exact ⟨u,v,huv.1,by simp [collapseOutside,huv.2.1,huv.2.2]⟩
  obtain ⟨B,hB,hBd,hBj⟩ := lift_quotient_forest_family G (collapseOutside (K:Set V)ᶜ) A T
    hA hforest hdis hd hinner (fun c => core_tree_connects_collapse_fibers G _ hactual _ (hT c).2.2.1)
  exact ⟨B,fun c => (hB c).2,hBd,hBj⟩
end LightEFTSpanners.EvenSplitting
