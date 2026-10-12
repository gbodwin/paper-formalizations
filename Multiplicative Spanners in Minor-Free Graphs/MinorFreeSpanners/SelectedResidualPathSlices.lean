import MinorFreeSpanners.ConnectedComponentSlice
import MinorFreeSpanners.ResidualPathSegmentation

/-! Actual degree-two residual components are segmented internally. Their
attachment blocks form exactly the components of the selected induced union;
every one has a genuine long spanning path and bounded total mass. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

structure ResidualAttachmentPartition {I : Type*} (H : SimpleGraph I)
    (R : Finset I) (t : (H.induce (R:Set I)).ConnectedComponent)
    (d : I → ℝ) (D L : ℝ) (N : ℕ) (port : I)
    (P : Finset (Finset I)) (A ends : Finset I) : Prop where
  member : A∈P
  port_mem : port∈A
  connected : ConnectedWithin H A
  disjoint : ∀ B∈P,∀ C∈P,B≠C → Disjoint B C
  cover : P.biUnion id=ResidualComponents.block H R t
  good : ∀ B∈P,∃ x y,∃ p : H.Walk x y,p.IsPath ∧ p.support.toFinset=B ∧
    L≤pathMass d p ∧ pathMass d p<2*L+D
  ends_card : ends.card≤2*N
  actual_ends : ∃ x y,∃ p : H.Walk x y,p.IsPath ∧
    p.support.toFinset=ResidualComponents.block H R t ∧
    ends=(P.filter (fun B => (x∈B ∨ y∈B) ∧ B.card≤N)).biUnion id

 theorem exists_selected_residual_path_slices {I : Type*} [Fintype I]
    (H : SimpleGraph I) (hH : H.IsAcyclic) (R : Finset I)
    (F : Finset (H.induce (R:Set I)).ConnectedComponent)
    (d : I → ℝ) (D L : ℝ) (hD : 0≤D) (hL : 0<L)
    (hdeg : ∀ i∈R,((H.neighborFinset i)∩R).card≤2)
    (hd : ∀ i∈R,d i≤D)
    (hm : ∀ t∈F,L≤∑ i∈ResidualComponents.block H R t,d i)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (hport : ∀ t∈F,port t∈ResidualComponents.block H R t) (N : ℕ) :
    ∃ P : (H.induce (R:Set I)).ConnectedComponent → Finset (Finset I),
    ∃ A ends : (H.induce (R:Set I)).ConnectedComponent → Finset I,
      (∀ t∈F,ResidualAttachmentPartition H R t d D L N (port t) (P t) (A t) (ends t)) ∧
      let U := F.biUnion A
      U⊆R ∧
      (∀ t∈F,∃ q : (H.induce (U:Set I)).ConnectedComponent,ResidualComponents.block H U q=A t) ∧
      (∀ q : (H.induce (U:Set I)).ConnectedComponent,∃ t∈F,ResidualComponents.block H U q=A t) := by
  classical
  have hw : ∀ t∈F,∃ (P : Finset (Finset I)) (A ends : Finset I),
      ResidualAttachmentPartition H R t d D L N (port t) P A ends := by
    intro t ht
    obtain ⟨x,y,p,hp,hps,P,A,hAP,hdis,hcover,hpa,hconn,hgood,hends⟩ :=
      exists_residual_attachment_partition H hH R t d D L hD hL hdeg hd
        (hm t ht) (port t) (hport t ht) N
    refine ⟨P,A,(P.filter (fun B => (x∈B ∨ y∈B) ∧ B.card≤N)).biUnion id,?_⟩
    refine { member := hAP
             port_mem := hpa
             connected := hconn
             disjoint := hdis
             cover := hcover
             good := hgood
             ends_card := ?_
             actual_ends := ?_ }
    · exact hends
    · exact ⟨x,y,p,hp,hps,rfl⟩
  choose! P A ends hpart using hw
  have hA : ∀ t∈F,A t⊆ResidualComponents.block H R t := by
    intro t ht i hi
    rw [←(hpart t ht).cover]
    exact Finset.mem_biUnion.mpr ⟨A t,(hpart t ht).member,hi⟩
  have hUR : F.biUnion A⊆R := by
    intro i hi
    obtain ⟨t,ht,hit⟩ := Finset.mem_biUnion.mp hi
    exact ResidualComponents.subset H R t (hA t ht hit)
  have hcomp := chosen_slices_are_components H R F A hA
    (fun t ht => ⟨port t,(hpart t ht).port_mem⟩) (fun t ht => (hpart t ht).connected)
  exact ⟨P,A,ends,hpart,hUR,hcomp⟩

end MinorFreeSpanners
