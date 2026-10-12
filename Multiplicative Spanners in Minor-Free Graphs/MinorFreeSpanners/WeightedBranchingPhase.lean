import MinorFreeSpanners.ResidualClusterForest
import MinorFreeSpanners.FiniteReservePayment
import MinorFreeSpanners.BranchingConnectorBudget
import MinorFreeSpanners.TouchingClusterEdges

/-! Actual low-degree branching phase. The forest and disjoint cores are
chosen internally; all charged heavy and connector edges retain their original
host identities. Half a surplus baseline is saved for later absorption. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem exists_weighted_branching_phase {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I := I) A w D) (hcover : ∀ x,∃ i,x∈C.branch i) (hA : A≤G) (hB : B≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (R : Finset I) (d credit : I → ℝ)
    (hd1 : ∀ i,1≤d i) (hdD : ∀ i,d i≤D)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (L c b M : ℝ) (q s : ℕ) (hD : 0≤D) (hc : 0≤c) (hM : 0≤M)
    (hLD : 3*(D+1)<L) (hsize : L+D≤s*b)
    (hcost : (s+1:ℕ)*((q:ℝ)*M)≤c*b/2)
    (hcred : ∀ i∈R,c*d i≤credit i) (hbase : ∀ i∈R,c*b≤credit i)
    (hdeg : ∀ i∈R,(C.graph B).degree i≤q)
    (hweight : ∀ e∈B.edgeSet,w e≤M)
    (g ell : ℝ) (hG : WeightedGirthAbove G w g)
    (hw : ∀ e∈G.edgeSet,0≤w e) (hell : 0<ell) (hg : 2≤g)
    (hlight : ∀ e∈A.edgeSet,w e<ell) (hheavy : ∀ e∈B.edgeSet,ell≤w e)
    (hbudget : 2*D≤(g-2)*ell) :
    ∃ H : SimpleGraph I,∃ hH : H≤C.graph T,
    ∃ P : Finset (Finset I),∃ F : ClusterFamily (I := {S // S∈P}) G w (L+D),
    ∃ radius : {S // S∈P} → ℝ,
      H.IsAcyclic ∧ H.Reachable=(withinVertices (C.graph T) (R:Set I)).Reachable ∧
      (∀ S∈P,S⊆R) ∧
      (∀ S U,S∈P → U∈P → S≠U → Disjoint S U) ∧
      (∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i}) ∧
      (∀ S,0≤radius S ∧ L-1≤radius S ∧ radius S≤L+D) ∧
      (∀ S x,x∈F.branch S → ∀ y,y∈F.branch S →
        ∃ p : G.Walk x y,(∀ z∈p.support,z∈F.branch S) ∧ walkWeight w p≤radius S) ∧
      (∀ S x,x∈F.branch S → ∀ y,B.Adj x y → s(x,y)∈C.touchingEdges B S.val) ∧
      (∀ S,c*radius S+(∑ e∈C.touchingEdges B S.val,w e)+c*b/2≤
        (∑ i∈S.val,credit i)+c*(∑ e∈C.connectorEdges hA hT H hH S.val,w e)) ∧
      (∀ S U : {S // S∈P},S≠U →
        Disjoint (C.connectorEdges hA hT H hH S.val) (C.connectorEdges hA hT H hH U.val)) ∧
      (∀ W : Finset I,ConnectedWithin H W → Disjoint W (P.biUnion id) →
        (∃ i j,∃ p : H.Walk i j,p.IsPath ∧ (∀ v∈p.support,v∈W) ∧
          L≤pathMass (fun i => d i+1) p) →
        ∀ i∈W,((H.neighborFinset i)∩W).card≤2) := by
  classical
  have hbudget1 : D≤(g-1)*ell := by nlinarith only [hD,hell.le,hbudget]
  have hloop : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i → ¬B.Adj x y := by
    intro i x hx y hy hxy
    exact C.no_heavy_loop hA hG hw hlight (by linarith) hbudget1 i hx hy
      (hB hxy) (hheavy _ hxy)
  have hsingle : ∀ i j x,x∈C.branch i → ∀ y,y∈C.branch j →
      ∀ u,u∈C.branch i → ∀ v,v∈C.branch j →
      B.Adj x y → B.Adj u v → s(x,y)=s(u,v) := by
    intro i j x hx y hy u hu v hv hxy huv
    rcases le_total (w s(x,y)) (w s(u,v)) with hle|hle
    · exact C.heavy_edge_unique hA hG hw hlight hg hbudget i j hx hy hu hv
        (hB hxy) (hB huv) (hheavy _ huv) hle
    · exact (C.heavy_edge_unique hA hG hw hlight hg hbudget i j hu hv hx hy
        (hB huv) (hB hxy) (hheavy _ hxy) hle).symm
  obtain ⟨H,hH,hacyc,hreach,hinside,hbridge⟩ := C.exists_residual_unit_forest (R:Set I) hT hunit
  obtain ⟨P,F,hcore,hdis,hbranch,hres⟩ :=
    exists_weighted_branching_clusters C hA H hacyc d hd1 hdD hdiam hbridge L hD hLD
  have hsub : ∀ S∈P,S⊆R := fun S hS =>
    branchingCore_subset_residual H (R:Set I) hinside _ _ _ S (hcore S hS)
  have hcredit (S : {S // S∈P}) := branching_core_credit H hacyc d credit S.val L D c b
    ((q:ℝ)*M) s (hcore S.val S.property) hc (mul_nonneg (Nat.cast_nonneg q) hM)
    (fun i _ => hd1 i) (fun i hi => hcred i (hsub S.val S.property hi))
    (fun i hi => hbase i (hsub S.val S.property hi)) hsize hcost
  choose radius hrad0 hradL hradD hpaths hpaid using hcredit
  refine ⟨H,hH,P,F,radius,hacyc,hreach,hsub,hdis,hbranch,
    (fun S => ⟨hrad0 S,hradL S,hradD S⟩),?_,?_,?_,?_,hres⟩
  · intro S x hx y hy
    rw [hbranch S] at hx hy
    obtain ⟨i,hi,hxi⟩ := hx
    obtain ⟨j,hj,hyj⟩ := hy
    obtain ⟨p,hp⟩ := (hcore S.val S.property).1 i hi j hj
    let r := p.toPath
    have hrs : ∀ k∈r.val.support,k∈S.val :=
      fun k hk => hp k (p.support_toPath_subset_support hk)
    obtain ⟨t,ht,htw⟩ := C.lift_path_variable hA H d hdiam hbridge r.val r.property
      (F.branch S) (fun k hk v hv => by rw [hbranch S]; exact ⟨k,hrs k hk,hv⟩) hxi hyj
    exact ⟨t,ht,htw.trans (hpaths S i j r.val r.property hrs)⟩
  · intro S x hx y hxy
    rw [hbranch S] at hx
    obtain ⟨i,hi,hxi⟩ := hx
    obtain ⟨j,hyj⟩ := hcover y
    exact Finset.mem_filter.mpr ⟨mem_edgeFinset.mpr hxy,i,hi,j,x,hxi,y,hyj,rfl⟩
  · intro S
    have hwgt := C.touching_edges_weight_le hA hB S.val q M hM
      (fun i hi => hdeg i (hsub S.val S.property hi)) hweight hloop hsingle
    rw [C.connectorEdges_unit_weight hA hT H hH S.val hunit]
    linarith [hpaid S]
  · intro S U hne
    exact C.connectorEdges_disjoint hA hT H hH S.val U.val
      (hdis S.val U.val S.property U.property (fun h => hne (Subtype.ext h)))

end MinorFreeSpanners
