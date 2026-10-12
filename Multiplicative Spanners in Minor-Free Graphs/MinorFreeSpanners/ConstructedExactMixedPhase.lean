import MinorFreeSpanners.ExactMixedPriorPayment

/-! Large roots are actual unions of the original old clusters. The final
mixed phase constructs all ownership and path data internally and pays every
remaining residual-incident original edge using original, pre-collapse degree
bounds. Prior paid root endpoints cannot become heavy owners. Their previous
expenditure, the common forest and numerical scales remain explicit. Exact
fresh unit-connector identities are retained for the later global potential. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace AssembledPathFamilies
variable {I V : Type*} [Fintype I] [Fintype V]
variable {A T E G : SimpleGraph V} {w : Sym2 V → ℝ} {D D₁ : ℝ}
variable (C : ClusterFamily (I:=I) A w D) (hA : A≤G) {hT : T≤G}
variable (P : Finset (Finset I)) (F : ClusterFamily (I:={S // S∈P}) G w D₁)
variable (hbranch : ∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i})
variable {H : SimpleGraph (SelectedResidualIndex P)} {hH : H≤(C.selectedResidual hA P F hbranch).graph T}
variable {d credit : SelectedResidualIndex P → ℝ} {M L c b a : ℝ}
variable {spare reserve : {r // r∈(selectedRoots P)} → ℝ} {N : ℕ}


attribute [-instance] instDecidableEqSum in
 theorem exists_constructed_mixed_prior_phase_exact (hcover : ∀ x,∃ i,x∈C.branch i) (hunit : ∀ e∈T.edgeSet,w e=1) (hE : E≤G)
    (hforest : H.IsAcyclic) (hconn : ConnectedWithin H Finset.univ)
    (hP : P.Nonempty) (W U prior eligible : Finset (SelectedResidualIndex P))
    (hprevious : selectedRoots P\eligible⊆prior)
    (hRW : Finset.univ\(selectedRoots P)⊆W) (hRU : Disjoint (Finset.univ\(selectedRoots P)) U)
    (hmax : ∀ S : Finset (SelectedResidualIndex P),S⊆W → Disjoint S U →
      ¬(C.selectedResidual hA P F hbranch).ShortCycleCore H d L E S ∧ ¬(C.selectedResidual hA P F hbranch).FourArmCore H d L E S)
    (edgeMax : ℝ) (future : {r // r∈(selectedRoots P)} → ℝ)
    (hM : 0≤M) (hL : 0<L) (hK : 1≤2*L+M) (hMax : 0≤edgeMax) (hc : 0≤c) (ha : 0≤a)
    (hroot0 : ∀ r∈(selectedRoots P),0≤d r) (hd0 : ∀ i∈W,0≤d i+1) (hdD : ∀ i∈W,d i≤max D D₁)
    (hd : ∀ i∉(selectedRoots P),1≤d i) (hdM : ∀ i∉(selectedRoots P),d i+1≤M)
    (hdeg2 : ∀ i∉(selectedRoots P),((H.neighborFinset i)\(selectedRoots P)).card≤2)
    (hm : ∀ t : (H.induce ((Finset.univ\(selectedRoots P) : Finset (SelectedResidualIndex P)):Set (SelectedResidualIndex P))).ConnectedComponent,
      L≤∑ i∈ResidualComponents.block H (Finset.univ\(selectedRoots P)) t,(d i+1))
    (hdiam : ∀ i x,x∈(C.selectedResidual hA P F hbranch).branch i → ∀ y,y∈(C.selectedResidual hA P F hbranch).branch i →
      ∃ q : G.Walk x y,(∀ z∈q.support,z∈(C.selectedResidual hA P F hbranch).branch i) ∧ walkWeight w q≤d i)
    (hcredit : ∀ i∉(selectedRoots P),c*d i≤credit i) (hbase : ∀ i∉(selectedRoots P),c*b≤credit i)
    (hcredit0 : ∀ i,0≤credit i)
    (hrootcredit : ∀ r,c*d r.val+spare r≤credit r.val)
    (hweight : ∀ e∈E.edgeSet,w e≤edgeMax)
    (hfuture : ∀ r,future r≤reserve r)
    (hbudget : ∀ r,r.val∈eligible → 2*c*edgeMax+2*(N:ℝ)*a+future r≤reserve r)
    (hsize : 2*(2*L+M)≤N*b) (hhalf : 2*a≤c*b)
    (hdonor : 2*(N:ℝ)*a≤c*L/4) (hrootbudget : ∀ r,5*(N:ℝ)*a+reserve r≤spare r)
    (hcost : (N+1:ℕ)*a≤c*b/2)
    (q : ℕ) (hqa : (q:ℝ)*edgeMax≤a)
    (hdeg : ∀ i,i∉P.biUnion id → (C.graph E).degree i≤q)
    (hw0 : ∀ e∈E.edgeSet,0≤w e)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬E.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → E.Adj x y → E.Adj u v → s(x,y)=s(u,v)) :
    (∀ i∉(selectedRoots P),∀ x∈(C.selectedResidual hA P F hbranch).branch i,∀ y,E.Adj x y →
      s(x,y)∉(C.selectedResidual hA P F hbranch).touchingEdges E prior →
      s(x,y)∈(C.selectedResidual hA P F hbranch).unpaidTouchingEdges E (Finset.univ\(selectedRoots P)) prior) ∧
    ∃ O : ResidualOwnership H (selectedRoots P),
    ∃ Q : (r : {r // r∈(selectedRoots P)}) → RootedPathAssemblyResult (C.selectedResidual hA P F hbranch) le_rfl hT H hH
    (Finset.univ\(selectedRoots P)) r.val (O.components r) O.port (fun i => d i+1) credit M L c b a (spare r) (reserve r) N,
    ExactPriorPaidHeavyPhaseOutput O Q E prior eligible edgeMax future := by
  have hroots : (selectedRoots P).Nonempty := by
    obtain ⟨S,hS⟩ := hP
    exact ⟨Sum.inl ⟨S,hS⟩,by simp [selectedRoots]⟩
  refine ⟨fun i hi x hx y hxy hnot => Finset.mem_sdiff.mpr
    ⟨incident_residual_edge_mem_touching E (C.selectedResidual_covers hA P F hbranch hcover) hi hx hxy,hnot⟩,?_⟩
  obtain ⟨O,Q,_⟩ := exists_multi_root_path_assembly (C.selectedResidual hA P F hbranch) le_rfl hT hunit H hH hforest hconn (selectedRoots P) hroots
    (fun i => d i+1) credit M L c b a spare reserve N hM hL
    (fun r hr => by have hh := hroot0 r hr;linarith) hc ha hdeg2
    (fun i hi => by have hh := hd i hi;linarith) hdM hm
    (by simpa only [add_sub_cancel_right] using hdiam)
    (by simpa only [add_sub_cancel_right] using hcredit) hbase hsize hhalf hdonor hrootbudget hcost
  refine ⟨O,Q,?_⟩
  exact mixed_prior_paid_heavy_phase_exact C hA P F hbranch O Q hcover hunit hE hforest W U prior eligible hprevious hRW hRU hmax edgeMax future
    hL hK hMax hc ha hroot0 hd0 hdD (fun i hi => le_trans (by norm_num) (hd i hi)) hdiam
    hcredit (fun i hi => by have hh := hbase i hi;linarith) hcredit0 hrootcredit hweight hfuture hbudget
    q hqa hdeg hw0 hloop hsingle

end AssembledPathFamilies
end MinorFreeSpanners
