import MinorFreeSpanners.InteriorPathBlock

/-! Every vertex of a small non-endpoint block lies in the weighted interior
of the same actual component spanning path retained by the segmentation. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem ResidualAttachmentPartition.interior_path {I : Type*}
    {H : SimpleGraph I} (hH : H.IsAcyclic) {R : Finset I}
    {t : (H.induce (R:Set I)).ConnectedComponent} {d : I → ℝ}
    {M L : ℝ} {N : ℕ} {port : I} {P : Finset (Finset I)} {A ends : Finset I}
    (hpart : ResidualAttachmentPartition H R t d M L N port P A ends)
    (hd : ∀ i∈R,0≤d i) :
    ∃ a b,∃ p : H.Walk a b,p.IsPath ∧
      p.support.toFinset=ResidualComponents.block H R t ∧
      ∀ B∈P,B.card≤N → ∀ x∈B,x∉ends → WeightedInterior d L p x := by
  classical
  obtain ⟨a,b,p,hp,hps,hends⟩ := hpart.actual_ends
  refine ⟨a,b,p,hp,hps,?_⟩
  intro B hB hBN x hx hxE
  have hex : a∉B ∧ b∉B := by
    constructor <;> intro he
    all_goals
      apply hxE
      rw [hends]
      apply Finset.mem_biUnion.mpr
      refine ⟨B,Finset.mem_filter.mpr ⟨hB,?_,hBN⟩,hx⟩
    · exact Or.inl he
    · exact Or.inr he
  have hconn : ∀ S∈P,ConnectedWithin H S := by
    intro S hS
    obtain ⟨u,v,q,_,he,_,_⟩ := hpart.good S hS
    exact he ▸ forest_walk_support_connected q
  have hm : ∀ S∈P,L≤∑ i∈S,d i := by
    intro S hS
    obtain ⟨u,v,q,_,he,hlo,_⟩ := hpart.good S hS
    simpa only [pathMass,he] using hlo
  exact interior_of_nonendpoint_block H hH p hp P (hpart.cover.trans hps.symm)
    hpart.disjoint hconn d L (fun i hi => hd i (ResidualComponents.subset H R t
      (hps ▸ List.mem_toFinset.mpr hi))) hm B hB hex.1 hex.2 x hx

end MinorFreeSpanners
