import MinorFreeSpanners.SelectedResidualPathSlices
import MinorFreeSpanners.SelectedComponentOwner
import MinorFreeSpanners.WeightedDonorAbsorption

/-! Degree-two residual components supply their actual spanning paths and
attachment blocks internally. Every selected block is an actual component of
the selected induced union. The same original component's short endpoint
pieces are paid exactly once, with no supplied long-path or donor premise. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem weighted_selected_donor_absorption {I V : Type*} [Fintype I]
    {B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
    (C : ClusterFamily (I:=I) B w D₀) (hB : B≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    (hforest : H.IsAcyclic) (R : Finset I) (root : I) (hr : root∉R)
    (F : Finset (H.induce (R:Set I)).ConnectedComponent)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (hport : ∀ t∈F,port t∈ResidualComponents.block H R t)
    (hbridge : ∀ t∈F,(C.graph T).Adj root (port t))
    (d credit : I → ℝ) (M L c b a spare future : ℝ) (N : ℕ)
    (hM : 0≤M) (hL : 0<L) (hroot : 1≤d root) (hc : 0≤c) (ha : 0≤a)
    (hdeg : ∀ i∈R,((H.neighborFinset i)∩R).card≤2)
    (hd : ∀ i∈R,2≤d i) (hdM : ∀ i∈R,d i≤M)
    (hm : ∀ t∈F,L≤∑ i∈ResidualComponents.block H R t,d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : B.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i-1)
    (hcredit : ∀ i∈R,c*(d i-1)≤credit i) (hbase : ∀ i∈R,c*b≤credit i)
    (hsize : 2*(2*L+M)≤N*b) (hhalf : 2*a≤c*b)
    (hdonor : 2*(N:ℝ)*a≤c*L/4) (hbudget : 5*(N:ℝ)*a+future≤spare) :
    ∃ P : (H.induce (R:Set I)).ConnectedComponent → Finset (Finset I),
    ∃ selected ends : (H.induce (R:Set I)).ConnectedComponent → Finset I,
      (∀ t∈F,ResidualAttachmentPartition H R t d M L N (port t) (P t) (selected t) (ends t)) ∧
      let U := F.biUnion selected
      let S := insert root U
      let carrier := {x | ∃ i∈S,x∈C.branch i}
      U⊆R ∧ ∃ J : SimpleGraph I,∃ hJ : J≤C.graph T,∃ radius : ℝ,
        d root-1≤radius ∧ radius≤d root-1+2*(2*L+M) ∧
        (∀ x∈carrier,∀ y∈carrier,∃ p : G.Walk x y,
          (∀ z∈p.support,z∈carrier) ∧ walkWeight w p≤radius) ∧
        c*radius+a*U.card+(∑ t∈F,a*(ends t).card)+future≤
          c*(d root-1)+spare+(∑ i∈U,credit i)+
            c*(∑ e∈C.connectorEdges hB hT J hJ S,w e) := by
  classical
  obtain ⟨P,A,ends,hpart,hUR,hforward,hback⟩ :=
    exists_selected_residual_path_slices H hforest R F d M L hM hL hdeg hdM hm port hport N
  let U := F.biUnion A
  have hAsub : ∀ t∈F,A t⊆ResidualComponents.block H R t := by
    intro t ht i hi
    rw [←(hpart t ht).cover]
    exact Finset.mem_biUnion.mpr ⟨A t,(hpart t ht).member,hi⟩
  obtain ⟨owner,howner,hinj,hsurj⟩ := exists_selected_component_owner H R U F A hAsub
    (fun t ht => ⟨port t,(hpart t ht).port_mem⟩) hforward hback
  have hport' : ∀ q,port (owner q)∈ResidualComponents.block H U q := by
    intro q
    rw [(howner q).2]
    exact (hpart _ (howner q).1).port_mem
  have hcomponent : ∀ q : (H.induce (U:Set I)).ConnectedComponent,
      ∀ x y,∀ p : H.Walk x y,p.IsPath →
      (∀ i∈p.support,i∈ResidualComponents.block H U q) → pathMass d p≤2*L+M := by
    intro q x y p _ hp
    obtain ⟨u,v,s,_,hs,_,hhi⟩ := (hpart _ (howner q).1).good _ (hpart _ (howner q).1).member
    have hps : p.support.toFinset⊆A (owner q) := by
      intro i hi
      rw [←(howner q).2]
      exact hp i (List.mem_toFinset.mp hi)
    have hnonneg : ∀ i∈A (owner q),0≤d i := by
      intro i hi
      have hh := hd i (ResidualComponents.subset H R _ (hAsub _ (howner q).1 hi))
      linarith
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hps (fun i hi _ => hnonneg i hi)
    change (∑ i∈p.support.toFinset,d i)≤2*L+M
    change (∑ i∈s.support.toFinset,d i)<2*L+M at hhi
    rw [hs] at hhi
    exact hh.trans hhi.le
  have hlong : ∀ q : (H.induce (U:Set I)).ConnectedComponent,
      ∃ x y,∃ p : H.Walk x y,p.IsPath ∧
      (∀ i∈p.support,i∈ResidualComponents.block H U q) ∧ L≤pathMass d p := by
    intro q
    obtain ⟨x,y,p,hp,he,hlo,_⟩ := (hpart _ (howner q).1).good _ (hpart _ (howner q).1).member
    refine ⟨x,y,p,hp,?_,hlo⟩
    intro i hi
    rw [(howner q).2,←he]
    exact List.mem_toFinset.mpr hi
  obtain ⟨J,hJ,radius,hlo,hhi,hpaths,hpaid⟩ := weighted_donor_absorption C hB hT hunit H hH U root
    (fun h => hr (hUR h)) (fun q => port (owner q)) hport'
    (fun q => hbridge _ (howner q).1) Finset.univ (fun q => ends (owner q))
    d credit (2*L+M) L c b a spare future N hroot (by linarith) hc ha
    (fun i hi => hd i (hUR hi)) hdiam hcomponent (fun q _ => hlong q)
    (fun q _ => (hpart _ (howner q).1).ends_card)
    (fun i hi => hcredit i (hUR hi)) (fun i hi => hbase i (hUR hi)) hsize hhalf hdonor hbudget
  have hsum := component_owner_sum F owner (fun q => (howner q).1) hinj hsurj
    (fun t => a*(ends t).card)
  rw [hsum] at hpaid
  exact ⟨P,A,ends,hpart,hUR,J,hJ,radius,hlo,hhi,hpaths,hpaid⟩

end MinorFreeSpanners
