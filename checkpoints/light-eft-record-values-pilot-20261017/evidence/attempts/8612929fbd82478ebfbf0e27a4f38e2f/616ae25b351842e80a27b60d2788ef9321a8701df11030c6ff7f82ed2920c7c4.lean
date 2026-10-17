import LightEFTSpanners.NativeContractionExpansion

namespace LightEFTSpanners.EvenSplitting
open SimpleGraph MultigraphCuts
variable {V W E I : Type*}

/-- A selected quotient forest cannot use an original edge whose endpoints
collapse together: that edge would be an actual native loop, not a bridge. -/
theorem quotient_forest_avoids_inner (G : Graph V E) (f : V → W) (A : Set E)
    (hb : ∀ e∈((G.map f).restrict A).edgeSet,((G.map f).restrict A).IsBridge e)
    {e : E} {u v : V} (he : e∈A) (hl : G.IsLink e u v) (hf : f u=f v) : False := by
  have hloop : ((G.map f).restrict A).IsLink e (f u) (f u) := by
    exact ⟨he,by simpa only [hf] using hl.map f⟩
  have hn := (bridge_iff_not_reachable_delete _ hloop).mp (hb e hloop.edge_mem)
  exact hn Reachable.rfl

/-- Combine actual quotient forests and disjoint internal fiber connectors,
then prune to original-edge forests. Mixed edge collisions are ruled out by
native loop/bridge semantics, rather than an extra disjointness assumption. -/
theorem lift_quotient_forest_family (G : Graph V E) (f : V → W)
    (A T : I → Set E) (hA : ∀ c,A c⊆(G.map f).edgeSet)
    (hforest : ∀ c e,e∈((G.map f).restrict (A c)).edgeSet →
      ((G.map f).restrict (A c)).IsBridge e)
    (hAd : Pairwise (fun c d => Disjoint (A c) (A d)))
    (hTd : Pairwise (fun c d => Disjoint (T c) (T d)))
    (hinner : ∀ c e,e∈T c → ∃ u v,G.IsLink e u v ∧ f u=f v)
    (hconn : ∀ c (x y : G.vertexSet),f x.val=f y.val →
      (G.restrict (T c)).toSimpleGraph.Reachable x y) :
    ∃ B : I → Set E,(∀ c,B c⊆A c∪T c ∧ B c⊆G.edgeSet ∧
      ∀ e∈(G.restrict (B c)).edgeSet,(G.restrict (B c)).IsBridge e) ∧
      Pairwise (fun c d => Disjoint (B c) (B d)) ∧
      ∀ c (x y : G.vertexSet),EdgeSetJoins (G.map f) (A c) (f x.val) (f y.val) →
        EdgeSetJoins G (B c) x.val y.val := by
  have mixed (c d : I) : Disjoint (A c) (T d) := by
    apply Set.disjoint_left.mpr
    intro e ha ht
    obtain ⟨u,v,hl,hf⟩ := hinner d e ht
    exact quotient_forest_avoids_inner G f (A c) (hforest c) ha hl hf
  have hsub (c : I) : A c∪T c⊆G.edgeSet := by
    rintro e (ha|ht)
    · exact hA c ha
    · obtain ⟨u,v,hl,_⟩ := hinner c e ht; exact hl.edge_mem
  have hd : Pairwise (fun c d => Disjoint (A c∪T c) (A d∪T d)) := by
    intro c d hcd
    apply Set.disjoint_left.mpr
    rintro e (ha|ht) (ha'|ht')
    · exact Set.disjoint_left.mp (hAd hcd) ha ha'
    · exact Set.disjoint_left.mp (mixed c d) ha ht'
    · exact Set.disjoint_left.mp (mixed d c) ha' ht
    · exact Set.disjoint_left.mp (hTd hcd) ht ht'
  obtain ⟨B,hB,hBd,hBj⟩ := prune_disjoint_native_family G (fun c => A c∪T c) hsub hd
  refine ⟨B,hB,hBd,?_⟩
  intro c x y ⟨_,_,hxy⟩
  apply hBj c x.val y.val
  exact ⟨x.property,y.property,reachable_map_expand G f (A c) (T c) (hconn c) hxy⟩
end LightEFTSpanners.EvenSplitting
