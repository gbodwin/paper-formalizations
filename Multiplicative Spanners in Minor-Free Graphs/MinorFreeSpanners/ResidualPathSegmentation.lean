import MinorFreeSpanners.WeightedPathBlockFamily
import MinorFreeSpanners.ResidualForestPaths

/-! The actual degree-two residual forest supplies its own spanning path;
segmentation therefore needs no externally supplied component path. An actual
boundary port internally selects a long block from the resulting partition. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem exists_residual_attachment_partition {I : Type*} [Fintype I]
    (H : SimpleGraph I) (hH : H.IsAcyclic) (R : Finset I)
    (t : (H.induce (R:Set I)).ConnectedComponent)
    (d : I → ℝ) (D L : ℝ) (hD : 0≤D) (hL : 0<L)
    (hdeg : ∀ i∈R,((H.neighborFinset i)∩R).card≤2)
    (hd : ∀ i∈R,d i≤D) (hm : L≤∑ i∈ResidualComponents.block H R t,d i)
    (port : I) (hport : port∈ResidualComponents.block H R t) (N : ℕ) :
    ∃ x y,∃ p : H.Walk x y,p.IsPath ∧ p.support.toFinset=ResidualComponents.block H R t ∧
      ∃ P : Finset (Finset I),∃ S∈P,
        (∀ A∈P,∀ B∈P,A≠B → Disjoint A B) ∧
        P.biUnion id=ResidualComponents.block H R t ∧ port∈S ∧
        ConnectedWithin H S ∧
        (∀ A∈P,∃ u v,∃ q : H.Walk u v,q.IsPath ∧ q.support.toFinset=A ∧
          L≤pathMass d q ∧ pathMass d q<2*L+D) ∧
        ((P.filter (fun A => (x∈A ∨ y∈A) ∧ A.card≤N)).biUnion id).card≤2*N := by
  classical
  have htR := ResidualComponents.subset H R t
  obtain ⟨x,_,y,_,p,hp,hps⟩ := connected_forest_degree_two_path H hH
    (ResidualComponents.block H R t) (ResidualComponents.connected H R t)
    (ResidualComponents.nonempty H R t) (fun i hi =>
      (Finset.card_le_card (show H.neighborFinset i∩ResidualComponents.block H R t⊆H.neighborFinset i∩R from fun z hz => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hz).1,htR (Finset.mem_inter.mp hz).2⟩)).trans (hdeg i (htR hi)))
  have hpR : ∀ i∈p.support,i∈R := fun i hi => htR (hps ▸ List.mem_toFinset.mpr hi)
  have hpm : L≤pathMass d p := by simpa only [pathMass,hps] using hm
  have hpp : port∈p.support := by
    apply List.mem_toFinset.mp
    rwa [hps]
  obtain ⟨P,S,hS,hdis,hcover,hpS,hgood,hend⟩ :=
    exists_attached_path_blocks d D L hD hL p hp (fun i hi => hd i (hpR i hi)) hpm port hpp N
  obtain ⟨u,v,q,_,hq,_,_⟩ := hgood S hS
  have hconn : ConnectedWithin H S := hq ▸ forest_walk_support_connected q
  exact ⟨x,y,p,hp,hps,P,S,hS,hdis,hcover.trans hps,hpS,hconn,hgood,hend⟩

end MinorFreeSpanners
