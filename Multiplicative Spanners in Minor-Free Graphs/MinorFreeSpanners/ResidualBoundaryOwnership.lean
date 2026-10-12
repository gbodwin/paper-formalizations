import MinorFreeSpanners.ResidualComponents

/-! Every actual residual component of a connected host has an original
boundary edge to a selected nonempty union. Its owner is chosen from that
edge, retaining whole components rather than splitting their vertices. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem residual_component_boundary {I : Type*} [Fintype I]
    (H : SimpleGraph I) (hH : ConnectedWithin H Finset.univ)
    (U : Finset I) (hU : U.Nonempty)
    (Q : (H.induce ((Finset.univ\U : Finset I):Set I)).ConnectedComponent) :
    ∃ x∈ResidualComponents.block H (Finset.univ\U) Q,∃ y∈U,H.Adj x y := by
  classical
  let S := ResidualComponents.block H (Finset.univ\U) Q
  have hsub : S⊆Finset.univ := Finset.subset_univ _
  have hlt : S.card<(Finset.univ : Finset I).card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩
    intro he
    obtain ⟨u,hu⟩ := hU
    have hus : u∈S := he.symm ▸ Finset.mem_univ u
    exact (Finset.mem_sdiff.mp (ResidualComponents.subset H (Finset.univ\U) Q hus)).2 hu
  obtain ⟨x,hx,y,_,hy,hxy⟩ := hH.boundary hsub (ResidualComponents.nonempty H _ Q) hlt
  have hyU : y∈U := by
    by_contra hn
    have hyr : y∈Finset.univ\U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hn⟩
    exact hy (ResidualComponents.closed_adj H _ Q hx hyr hxy)
  exact ⟨x,hx,y,hyU,hxy⟩

 theorem exists_residual_component_owners {I : Type*} [Fintype I]
    (H : SimpleGraph I) (hH : ConnectedWithin H Finset.univ)
    (P : Finset (Finset I)) (hne : (P.biUnion id).Nonempty) :
    ∃ owner : (H.induce ((Finset.univ\P.biUnion id : Finset I):Set I)).ConnectedComponent → {S // S∈P},
      ∀ Q,∃ x∈ResidualComponents.block H (Finset.univ\P.biUnion id) Q,
        ∃ y∈(owner Q).val,H.Adj x y := by
  classical
  have hchoose (Q : (H.induce ((Finset.univ\P.biUnion id : Finset I):Set I)).ConnectedComponent) :
      ∃ S : {S // S∈P},∃ x∈ResidualComponents.block H (Finset.univ\P.biUnion id) Q,
        ∃ y∈S.val,H.Adj x y := by
    obtain ⟨x,hx,y,hy,hxy⟩ := residual_component_boundary H hH (P.biUnion id) hne Q
    obtain ⟨S,hS,hyS⟩ := Finset.mem_biUnion.mp hy
    exact ⟨⟨S,hS⟩,x,hx,y,hyS,hxy⟩
  choose owner howner using hchoose
  exact ⟨owner,howner⟩

end MinorFreeSpanners
