import MinorFreeSpanners.AssembledPriorPaidPayment

/-! The actual residual heavy phase constructs its ownership, ports and
all root-fiber path partitions internally before paying original residual
edges after subtracting actual prior-paid incidences. Only eligible roots carry
the heavy-scale reserve; every other root retains its future. The earlier
connected forest, prior root payment, root selection and numerical budgets
remain explicit, but no compatible path assembly is supplied as an input. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable
namespace AssembledPathFamilies
variable {I V : Type*} [Fintype I] [Fintype V] {A T E G : SimpleGraph V} {w : Sym2 V → ℝ} {D₀ : ℝ}
variable {C : ClusterFamily (I:=I) A w D₀} {hA : A≤G} {hT : T≤G}
variable {H : SimpleGraph I} {hH : H≤C.graph T} {roots : Finset I}
variable {d credit : I → ℝ} {M L c b a : ℝ} {spare reserve : {r // r∈roots} → ℝ} {N : ℕ}

 theorem exists_constructed_prior_paid_phase (hcover : ∀ x,∃ i,x∈C.branch i) (hunit : ∀ e∈T.edgeSet,w e=1) (hE : E≤G)
    (hforest : H.IsAcyclic) (hconn : ConnectedWithin H Finset.univ)
    (hroots : roots.Nonempty) (W U prior eligible : Finset I)
    (hprevious : roots\eligible⊆prior)
    (hRW : Finset.univ\roots⊆W) (hRU : Disjoint (Finset.univ\roots) U)
    (hmax : ∀ S : Finset I,S⊆W → Disjoint S U →
      ¬C.ShortCycleCore H d L E S ∧ ¬C.FourArmCore H d L E S)
    (edgeMax : ℝ) (future : {r // r∈roots} → ℝ)
    (hM : 0≤M) (hL : 0<L) (hK : 1≤2*L+M) (hMax : 0≤edgeMax) (hc : 0≤c) (ha : 0≤a)
    (hroot0 : ∀ r∈roots,0≤d r) (hd0 : ∀ i∈W,0≤d i+1) (hdD : ∀ i∈W,d i≤D₀)
    (hd : ∀ i∉roots,1≤d i) (hdM : ∀ i∉roots,d i+1≤M)
    (hdeg2 : ∀ i∉roots,((H.neighborFinset i)\roots).card≤2)
    (hm : ∀ t : (H.induce ((Finset.univ\roots : Finset I):Set I)).ConnectedComponent,
      L≤∑ i∈ResidualComponents.block H (Finset.univ\roots) t,(d i+1))
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ q : A.Walk x y,(∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i)
    (hcredit : ∀ i∉roots,c*d i≤credit i) (hbase : ∀ i∉roots,c*b≤credit i)
    (hcredit0 : ∀ i,0≤credit i)
    (hrootcredit : ∀ r,c*d r.val+spare r≤credit r.val)
    (hweight : ∀ e∈E.edgeSet,w e≤edgeMax)
    (hfuture : ∀ r,future r≤reserve r)
    (hbudget : ∀ r,r.val∈eligible → 2*c*edgeMax+2*(N:ℝ)*a+future r≤reserve r)
    (hsize : 2*(2*L+M)≤N*b) (hhalf : 2*a≤c*b)
    (hdonor : 2*(N:ℝ)*a≤c*L/4) (hrootbudget : ∀ r,5*(N:ℝ)*a+reserve r≤spare r)
    (hcost : (N+1:ℕ)*a≤c*b/2)
    (q : ℕ) (hqa : (q:ℝ)*edgeMax≤a)
    (hdeg : ∀ i∉roots,(C.graph E).degree i≤q)
    (hw0 : ∀ e∈E.edgeSet,0≤w e)
    (hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬E.Adj x y)
    (hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j → E.Adj x y → E.Adj u v → s(x,y)=s(u,v)) :
    (∀ i∉roots,∀ x∈C.branch i,∀ y,E.Adj x y →
      s(x,y)∉C.touchingEdges E prior → s(x,y)∈C.unpaidTouchingEdges E (Finset.univ\roots) prior) ∧
    ∃ O : ResidualOwnership H roots,
    ∃ Q : (r : {r // r∈roots}) → RootedPathAssemblyResult C hA hT H hH
    (Finset.univ\roots) r.val (O.components r) O.port (fun i => d i+1) credit M L c b a (spare r) (reserve r) N,
    PriorPaidHeavyPhaseOutput O Q E prior eligible edgeMax future := by
  refine ⟨fun i hi x hx y hxy hnot => Finset.mem_sdiff.mpr
    ⟨incident_residual_edge_mem_touching E hcover hi hx hxy,hnot⟩,?_⟩
  obtain ⟨O,Q,_⟩ := exists_multi_root_path_assembly C hA hT hunit H hH hforest hconn roots hroots
    (fun i => d i+1) credit M L c b a spare reserve N hM hL
    (fun r hr => by have hh := hroot0 r hr;linarith) hc ha hdeg2
    (fun i hi => by have hh := hd i hi;linarith) hdM hm
    (by simpa only [add_sub_cancel_right] using hdiam)
    (by simpa only [add_sub_cancel_right] using hcredit) hbase hsize hhalf hdonor hrootbudget hcost
  refine ⟨O,Q,?_⟩
  exact prior_paid_weighted_heavy_phase O Q hunit hE hforest W U prior eligible hprevious hRW hRU hmax edgeMax future
    hL hK hMax hc ha hroot0 hd0 hdD (fun i hi => le_trans (by norm_num) (hd i hi)) hdiam
    hcredit (fun i hi => by have hh := hbase i hi;linarith) hcredit0 hrootcredit hweight hfuture hbudget
    q hqa hdeg hw0 hloop hsingle

end AssembledPathFamilies
end MinorFreeSpanners
