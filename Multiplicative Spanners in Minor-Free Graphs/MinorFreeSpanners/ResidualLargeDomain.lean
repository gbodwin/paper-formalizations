import MinorFreeSpanners.ResidualMassDichotomy
import MinorFreeSpanners.ConnectedComponentSlice

/-! Split one actual residual domain into whole short-path and long-path
components. The long domain has degree at most two, and its induced components
are exactly the original long components. No small total-mass premise is used. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem exists_residual_mass_domains {I : Type*} [Fintype I]
    (H : SimpleGraph I) (hH : H.IsAcyclic) (R : Finset I) (d : I → ℝ) (L : ℝ)
    (hd : ∀ i∈R,0≤d i)
    (hmax : ∀ W : Finset I,ConnectedWithin H W → W⊆R →
      (∃ x y,∃ p : H.Walk x y,p.IsPath ∧ (∀ i∈p.support,i∈W) ∧ L≤pathMass d p) →
        ∀ i∈W,((H.neighborFinset i)∩W).card≤2) :
    ∃ F : Finset (H.induce (R:Set I)).ConnectedComponent,
      let U := F.biUnion (ResidualComponents.block H R)
      let S := (Finset.univ\F).biUnion (ResidualComponents.block H R)
      U⊆R ∧ S⊆R ∧ Disjoint U S ∧ U∪S=R ∧
      (∀ i∈U,((H.neighborFinset i)∩U).card≤2) ∧
      (∀ t∈F,∃ x y,∃ p : H.Walk x y,p.IsPath ∧
        p.support.toFinset=ResidualComponents.block H R t ∧ L≤pathMass d p) ∧
      (∀ t∉F,∀ x y,∀ p : H.Walk x y,p.IsPath →
        (∀ i∈p.support,i∈ResidualComponents.block H R t) → pathMass d p<L) ∧
      (∀ q : (H.induce (U:Set I)).ConnectedComponent,
        ∃ t∈F,ResidualComponents.block H U q=ResidualComponents.block H R t) ∧
      (∀ q : (H.induce (S:Set I)).ConnectedComponent,
        ∃ t∉F,ResidualComponents.block H S q=ResidualComponents.block H R t) ∧
      (∀ i∈U,∀ j∈S,¬H.Adj i j) := by
  classical
  let F : Finset (H.induce (R:Set I)).ConnectedComponent :=
    Finset.univ.filter (LongResidualComponent H R d L)
  let U := F.biUnion (ResidualComponents.block H R)
  let S := (Finset.univ\F).biUnion (ResidualComponents.block H R)
  have hf (t : (H.induce (R:Set I)).ConnectedComponent) :
      t∈F ↔ LongResidualComponent H R d L t := by simp [F]
  have hUR : U⊆R := by
    intro i hi
    obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hi
    exact ResidualComponents.subset H R t ht
  have hSR : S⊆R := by
    intro i hi
    obtain ⟨t,_,ht⟩ := Finset.mem_biUnion.mp hi
    exact ResidualComponents.subset H R t ht
  have hdis : Disjoint U S := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨t,ht,hit⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨q,hq,hiq⟩ := Finset.mem_biUnion.mp hj
    exact Finset.disjoint_left.mp (ResidualComponents.disjoint H R t q
      (fun he => (Finset.mem_sdiff.mp hq).2 (he ▸ ht))) hit hiq
  have hcover : U∪S=R := by
    apply Finset.Subset.antisymm (Finset.union_subset hUR hSR)
    intro i hi
    obtain ⟨t,hit⟩ := ResidualComponents.covers H R hi
    by_cases ht : t∈F
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨t,ht,hit⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t,Finset.mem_sdiff.mpr ⟨mem_univ _,ht⟩,hit⟩)
  refine ⟨F,hUR,hSR,hdis,hcover,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    obtain ⟨t,ht,hit⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.card_le_card (Finset.inter_subset_inter_left hUR)).trans
      (long_residual_component_degree H R d L hmax t ((hf t).mp ht) i hit)
  · intro t ht
    exact long_residual_component_spanning_path H hH R d L hd hmax t ((hf t).mp ht)
  · intro t ht x y p hp hs
    exact short_residual_component H R d L t (fun h => ht ((hf t).mpr h)) p hp hs
  · exact (chosen_slices_are_components H R F (ResidualComponents.block H R)
      (by intros;exact Finset.Subset.refl _) (fun t _ => ResidualComponents.nonempty H R t)
      (fun t _ => ResidualComponents.connected H R t)).2
  · intro q
    obtain ⟨t,ht,he⟩ := (chosen_slices_are_components H R (Finset.univ\F) (ResidualComponents.block H R)
      (by intros;exact Finset.Subset.refl _) (fun t _ => ResidualComponents.nonempty H R t)
      (fun t _ => ResidualComponents.connected H R t)).2 q
    exact ⟨t,(Finset.mem_sdiff.mp ht).2,he⟩

  · intro i hi j hj hadj
    obtain ⟨t,ht,hit⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨q,hq,hjq⟩ := Finset.mem_biUnion.mp hj
    have hjt := ResidualComponents.closed_adj H R t hit (hSR (Finset.mem_biUnion.mpr ⟨q,hq,hjq⟩)) hadj
    exact Finset.disjoint_left.mp (ResidualComponents.disjoint H R t q
      (fun he => (Finset.mem_sdiff.mp hq).2 (he ▸ ht))) hjt hjq

end MinorFreeSpanners
