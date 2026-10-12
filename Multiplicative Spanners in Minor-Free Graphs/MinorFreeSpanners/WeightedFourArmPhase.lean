import MinorFreeSpanners.FourArmCorePacking

/-! Actual four-arm path phase. Internally maximize disjoint witnessed
carriers, lift their original graph paths, and pay every incident heavy edge.
The residual excludes all still-eligible disjoint far-endpoint path pairs.
Short-cycle path cases and absorption are separate. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem exists_weighted_four_arm_phase {I V : Type*} [Fintype I] [Fintype V]
    {A B T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I := I) A w D) (hcover : ∀ x,∃ i,x∈C.branch i)
    (hA : A≤G) (hB : B≤G) (hT : T≤G)
    (H : SimpleGraph I) (hH : H≤C.graph T) (hunit : ∀ e∈T.edgeSet,w e=1)
    (R : Finset I) (d credit : I → ℝ) (hd1 : ∀ i,1≤d i) (hdD : ∀ i,d i≤D)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i)
    (L c b M : ℝ) (q : ℕ) (hD : 0≤D) (hc : 0≤c) (hM : 0≤M)
    (hcost : 8*((q:ℝ)*M)≤c*b) (hroom : 15*D+4*M+15+2*b≤6*L)
    (hcred : ∀ i∈R,c*d i≤credit i) (hbase : ∀ i∈R,c*b≤credit i)
    (hdeg : ∀ i∈R,(C.graph B).degree i≤q) (hweight : ∀ e∈B.edgeSet,w e≤M)
    (g ell : ℝ) (hG : WeightedGirthAbove G w g) (hw : ∀ e∈G.edgeSet,0≤w e)
    (hell : 0<ell) (hg : 2≤g) (hlight : ∀ e∈A.edgeSet,w e<ell)
    (hheavy : ∀ e∈B.edgeSet,ell≤w e) (hbudget : 2*D≤(g-2)*ell) :
    ∃ P : Finset (Finset I),
    ∃ F : ClusterFamily (I := {S // S∈P}) G w (2*(L+D)+M),
      (∀ S∈P,S⊆R ∧ C.FourArmCore H d L B S) ∧
      (∀ S U,S∈P → U∈P → S≠U → Disjoint S U) ∧
      (∀ S,F.branch S={x | ∃ i∈S.val,x∈C.branch i}) ∧
      (∀ S x,x∈F.branch S → ∀ y,B.Adj x y → s(x,y)∈C.touchingEdges B S.val) ∧
      (∀ S : {S // S∈P},c*(2*(L+D)+M)+(∑ e∈C.touchingEdges B S.val,w e)+c*b/2≤
        (∑ i∈S.val,credit i)+c*(∑ e∈C.connectorEdges hA hT H hH S.val,w e)) ∧
      (∀ S U : {S // S∈P},S≠U →
        Disjoint (C.connectorEdges hA hT H hH S.val) (C.connectorEdges hA hT H hH U.val)) ∧
      ∀ S : Finset I,S⊆R → Disjoint S (P.biUnion id) → ¬C.FourArmCore H d L B S := by
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
  have hbridge : ∀ i j,H.Adj i j → ∃ x∈C.branch i,∃ y∈C.branch j,
      ∃ _hxy : G.Adj x y,w s(x,y)≤1 := by
    intro i j hij
    obtain ⟨_,x,hx,y,hy,hxy⟩ := hH hij
    exact ⟨x,hx,y,hy,hT hxy,(hunit _ hxy).le⟩
  obtain ⟨P,hcore,hdis,hmax⟩ := C.exists_four_arm_packing (B:=B) H d L R
  let F : ClusterFamily (I := {S // S∈P}) G w (2*(L+D)+M) := {
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
      intro S
      exact (hcore S.val S.property).2.walks C hA H d L M B hB
        (fun i _ => by have h:=hd1 i;linarith) hdiam hbridge hM hweight }
  refine ⟨P,F,hcore,fun S U hS hU hne => hdis S hS U hU hne,fun _ => rfl,?_,?_,?_,hmax⟩
  · intro S x hx y hxy
    obtain ⟨i,hi,hxi⟩ := hx
    obtain ⟨j,hyj⟩ := hcover y
    exact Finset.mem_filter.mpr ⟨mem_edgeFinset.mpr hxy,i,hi,j,x,hxi,y,hyj,rfl⟩
  · intro S
    have hp := (hcore S.val S.property).2.credit C H d credit L M c b ((q:ℝ)*M) hc
      (fun i _ => hdD i) (fun i hi => hcred i ((hcore S.val S.property).1 hi))
      (fun i hi => hbase i ((hcore S.val S.property).1 hi)) hcost hroom
    have he := C.touching_edges_weight_le hA hB S.val q M hM
      (fun i hi => hdeg i ((hcore S.val S.property).1 hi)) hweight hloop hsingle
    rw [C.connectorEdges_unit_weight hA hT H hH S.val hunit]
    linarith
  · intro S U hne
    exact C.connectorEdges_disjoint hA hT H hH S.val U.val
      (hdis S.val S.property U.val U.property (fun h => hne (Subtype.ext h)))

end MinorFreeSpanners
