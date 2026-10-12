import MinorFreeSpanners.ShortCycleCorePacking
import MinorFreeSpanners.WeightedFourArmPhase

/-! Actual short-cycle phase with an internally selected finite packing.
Weighted girth supplies its credit surplus; each chosen original heavy edge
supplies its own intrinsic radius certificate. All incident heavy edges are
paid from the same old credits and distinct original unit connectors. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem exists_weighted_short_cycle_phase {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I := I) A w D) (hcover : ∀ x,∃ i,x∈C.branch i)
    (hA : A≤G) (hB : B≤G) (hT : T≤G)
    (H : SimpleGraph I) (hH : H≤C.graph T) (hunit : ∀ e∈T.edgeSet,w e=1)
    (R : Finset I) (d credit : I → ℝ) (hd1 : ∀ i,1≤d i) (hdD : ∀ i,d i≤D)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (L c b M : ℝ) (q N : ℕ) (hD : 0≤D) (hc : 0≤c) (hM : 0≤M)
    (hcred : ∀ i∈R,c*d i≤credit i) (hbase : ∀ i∈R,c*b≤credit i)
    (hdeg : ∀ i∈R,(C.graph B).degree i≤q) (hweight : ∀ e∈B.edgeSet,w e≤M)
    (g ell : ℝ) (hG : WeightedGirthAbove G w g) (hw : ∀ e∈G.edgeSet,0≤w e)
    (hell : 1<ell) (hg : 2≤g) (hlight : ∀ e∈A.edgeSet,w e<ell)
    (hheavy : ∀ e∈B.edgeSet,ell≤w e) (hbudget : 2*D≤(g-2)*ell)
    (hsmall : ((q:ℝ)*M)*N+c*b/2≤c*((g-2)*ell-6*D-4))
    (hlarge : 2*c*(2*(L+2*D+1)+M)+c*b≤N*(c*b))
    (hpay : 2*((q:ℝ)*M)≤c*b) :
    ∃ P : Finset (Finset I),
    ∃ F : ClusterFamily (I := {S // S∈P}) G w (2*(L+2*D+1)+M),
    ∃ radius : {S // S∈P} → ℝ,
      (∀ S∈P,S⊆R ∧ C.ShortCycleCore H d L B S) ∧
      (∀ S U,S∈P → U∈P → S≠U → Disjoint S U) ∧
      (∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i}) ∧
      (∀ S,2*(L+2*D+1)+ell≤radius S ∧ radius S≤2*(L+2*D+1)+M) ∧
      (∀ S x,x∈F.branch S → ∀ y,y∈F.branch S →
        ∃ p : G.Walk x y,(∀ z∈p.support,z∈F.branch S) ∧ walkWeight w p≤radius S) ∧
      (∀ S x,x∈F.branch S → ∀ y,B.Adj x y → s(x,y)∈C.touchingEdges B S.val) ∧
      (∀ S : {S // S∈P},c*radius S+(∑ e∈C.touchingEdges B S.val,w e)+c*b/2≤
        (∑ i∈S.val,credit i)+c*(∑ e∈C.connectorEdges hA hT H hH S.val,w e)) ∧
      (∀ S U : {S // S∈P},S≠U →
        Disjoint (C.connectorEdges hA hT H hH S.val) (C.connectorEdges hA hT H hH U.val)) ∧
      ∀ S : Finset I,S⊆R → Disjoint S (P.biUnion id) → ¬C.ShortCycleCore H d L B S := by
  classical
  have hbudget1 : D≤(g-1)*ell := by nlinarith only [hD,hell,hbudget]
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
  obtain ⟨P,hcore,hdis,hmax⟩ := C.exists_short_cycle_packing (B:=B) H d L R
  have hpaid (S : {S // S∈P}) := (hcore S.val S.property).2.paid C hA hB hT H hH
    d credit L c b ((q:ℝ)*M) M g ell N hD hc (mul_nonneg (Nat.cast_nonneg _) hM)
    hd1 hdD hdiam hG hw hlight hunit hell hg hheavy hweight
    (fun i hi => hcred i ((hcore S.val S.property).1 hi))
    (fun i hi => hbase i ((hcore S.val S.property).1 hi)) hsmall hlarge hpay
  choose radius hradL hradD hwalks hcredit using hpaid
  let F : ClusterFamily (I := {S // S∈P}) G w (2*(L+2*D+1)+M) := {
    branch := fun S => {x | ∃ i∈S.val,x∈C.branch i}
    nonempty := by
      intro S
      obtain ⟨i,hi⟩ := (hcore S.val S.property).2.nonempty C
      obtain ⟨x,hx⟩ := C.nonempty i
      exact ⟨x,i,hi,hx⟩
    disjoint := by
      intro S U hSU
      apply Set.disjoint_left.mpr
      rintro x ⟨i,hi,hxi⟩ ⟨j,hj,hxj⟩
      have he : i=j := by
        by_contra hn
        exact Set.disjoint_left.mp (C.disjoint i j hn) hxi hxj
      subst j
      exact Finset.disjoint_left.mp (hdis S.val S.property U.val U.property
        (fun h => hSU (Subtype.ext h))) hi hj
    connected := by
      intro S x hx y hy
      obtain ⟨p,hp,hw⟩ := hwalks S x hx y hy
      exact ⟨p,hp,hw.trans (hradD S)⟩ }
  refine ⟨P,F,radius,hcore,fun S U hS hU hne => hdis S hS U hU hne,
    fun _ => rfl,(fun S => ⟨hradL S,hradD S⟩),hwalks,?_,?_,?_,hmax⟩
  · intro S x hx y hxy
    obtain ⟨i,hi,hxi⟩ := hx
    obtain ⟨j,hyj⟩ := hcover y
    exact Finset.mem_filter.mpr ⟨mem_edgeFinset.mpr hxy,i,hi,j,x,hxi,y,hyj,rfl⟩
  · intro S
    have hp := hcredit S
    have he := C.touching_edges_weight_le hA hB S.val q M hM
      (fun i hi => hdeg i ((hcore S.val S.property).1 hi)) hweight hloop hsingle
    rw [C.connectorEdges_unit_weight hA hT H hH S.val hunit]
    linarith
  · intro S U hne
    exact C.connectorEdges_disjoint hA hT H hH S.val U.val
      (hdis S.val S.property U.val U.property (fun h => hne (Subtype.ext h)))

end MinorFreeSpanners
