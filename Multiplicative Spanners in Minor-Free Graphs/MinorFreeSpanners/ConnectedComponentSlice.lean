import MinorFreeSpanners.RootedResidualGraph

/-! A nonempty connected slice of an actual residual component is exactly a
component of the smaller induced union, provided the union contains no other
vertices from that original component. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem residual_connected_slice {I : Type*} (H : SimpleGraph I)
    (R U S : Finset I) (hUR : U⊆R)
    (t : (H.induce (R:Set I)).ConnectedComponent)
    (hS : S=U∩ResidualComponents.block H R t)
    (hne : S.Nonempty) (hconn : ConnectedWithin H S) :
    ∃ q : (H.induce (U:Set I)).ConnectedComponent,ResidualComponents.block H U q=S := by
  classical
  obtain ⟨x,hx⟩ := hne
  have hSU : S⊆U := by rw [hS];exact Finset.inter_subset_left
  have hSt : S⊆ResidualComponents.block H R t := by rw [hS];exact Finset.inter_subset_right
  obtain ⟨q,hxq⟩ := ResidualComponents.covers H U (hSU hx)
  refine ⟨q,Finset.Subset.antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨p,hp⟩ := ResidualComponents.connected H U q x hxq y hy
    have hm := residual_walk_in_block H R t p (hSt hx)
      (fun i hi => hUR (ResidualComponents.subset H U q (hp i hi)))
    rw [hS]
    exact Finset.mem_inter.mpr ⟨ResidualComponents.subset H U q hy,hm y p.end_mem_support⟩
  · intro y hy
    obtain ⟨p,hp⟩ := hconn x hx y hy
    exact residual_walk_in_block H U q p hxq (fun i hi => hSU (hp i hi)) y p.end_mem_support

 theorem chosen_component_slice_inter {I : Type*} (H : SimpleGraph I)
    (R : Finset I) (F : Finset (H.induce (R:Set I)).ConnectedComponent)
    (A : (H.induce (R:Set I)).ConnectedComponent → Finset I)
    (hA : ∀ t∈F,A t⊆ResidualComponents.block H R t)
    (t : (H.induce (R:Set I)).ConnectedComponent) (ht : t∈F) :
    (F.biUnion A)∩ResidualComponents.block H R t=A t := by
  classical
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨hiU,hit⟩ := Finset.mem_inter.mp hi
    obtain ⟨q,hq,hiq⟩ := Finset.mem_biUnion.mp hiU
    have he : q=t := by
      by_contra hne
      exact Finset.disjoint_left.mp (ResidualComponents.disjoint H R q t hne) (hA q hq hiq) hit
    exact he ▸ hiq
  · intro i hi
    exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨t,ht,hi⟩,hA t ht hi⟩

 theorem chosen_slices_are_components {I : Type*} (H : SimpleGraph I)
    (R : Finset I) (F : Finset (H.induce (R:Set I)).ConnectedComponent)
    (A : (H.induce (R:Set I)).ConnectedComponent → Finset I)
    (hA : ∀ t∈F,A t⊆ResidualComponents.block H R t)
    (hne : ∀ t∈F,(A t).Nonempty) (hconn : ∀ t∈F,ConnectedWithin H (A t)) :
    let U := F.biUnion A
    (∀ t∈F,∃ q : (H.induce (U:Set I)).ConnectedComponent,ResidualComponents.block H U q=A t) ∧
    (∀ q : (H.induce (U:Set I)).ConnectedComponent,∃ t∈F,ResidualComponents.block H U q=A t) := by
  classical
  dsimp
  let U := F.biUnion A
  have hUR : U⊆R := by
    intro i hi
    obtain ⟨t,ht,hi⟩ := Finset.mem_biUnion.mp hi
    exact ResidualComponents.subset H R t (hA t ht hi)
  have hf : ∀ t∈F,∃ q : (H.induce (U:Set I)).ConnectedComponent,ResidualComponents.block H U q=A t := by
    intro t ht
    exact residual_connected_slice H R U (A t) hUR t
      (chosen_component_slice_inter H R F A hA t ht).symm (hne t ht) (hconn t ht)
  refine ⟨hf,?_⟩
  intro q
  obtain ⟨i,hi⟩ := ResidualComponents.nonempty H U q
  obtain ⟨t,ht,hit⟩ := Finset.mem_biUnion.mp (ResidualComponents.subset H U q hi)
  obtain ⟨q',he⟩ := hf t ht
  have heq : q=q' := by
    by_contra hne
    exact Finset.disjoint_left.mp (ResidualComponents.disjoint H U q q' hne) hi (by rwa [he])
  exact ⟨t,ht,by simpa only [heq] using he⟩

end MinorFreeSpanners
