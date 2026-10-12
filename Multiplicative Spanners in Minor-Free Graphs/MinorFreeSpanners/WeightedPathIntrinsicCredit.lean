import MinorFreeSpanners.WeightedLargePathBlock

/-! Every actual segmented path block, including small blocks, can keep its
intrinsic diameter using its original old-vertex credits and unit connectors.
The bound is realized by confined original-host walks. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem weighted_path_intrinsic_credit {I V : Type*} [Fintype I]
    {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    {x y : I} (p : H.Walk x y) (hp : p.IsPath) (d credit : I → ℝ)
    (L K c : ℝ) (hc : 0≤c) (hd : ∀ i∈p.support,1≤d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ q : A.Walk x y,(∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i-1)
    (hL : L≤pathMass d p) (hK : pathMass d p≤K)
    (hcredit : ∀ i∈p.support,c*(d i-1)≤credit i) :
    let S := p.support.toFinset
    let radius := pathMass d p-1
    0≤radius ∧ L-1≤radius ∧ radius≤K-1 ∧
      (∀ x∈{x | ∃ i∈S,x∈C.branch i},∀ y∈{x | ∃ i∈S,x∈C.branch i},
        ∃ q : G.Walk x y,(∀ z∈q.support,∃ i∈S,z∈C.branch i) ∧ walkWeight w q≤radius) ∧
      c*radius≤(∑ i∈S,credit i)+c*(∑ e∈C.connectorEdges hA hT H hH S,w e) := by
  classical
  let S := p.support.toFinset
  have hmass : 1≤pathMass d p := by
    have hh := Finset.single_le_sum (s:=S) (f:=d)
      (fun i hi => (show (0:ℝ)≤1 by norm_num).trans (hd i (List.mem_toFinset.mp hi)))
      (List.mem_toFinset.mpr p.start_mem_support)
    exact (hd x p.start_mem_support).trans hh
  have hconn : ConnectedWithin H S := forest_walk_support_connected p
  have hbridge : ∀ i j,H.Adj i j → ∃ x∈C.branch i,∃ y∈C.branch j,
      ∃ _hxy : G.Adj x y,w s(x,y)≤1 := by
    intro i j hij
    obtain ⟨_,x,hx,y,hy,hxy⟩ := hH hij
    exact ⟨x,hx,y,hy,hT hxy,(hunit _ hxy).le⟩
  refine ⟨by linarith,by linarith,by linarith,?_,?_⟩
  · rintro a ⟨i,hi,hai⟩ b ⟨j,hj,hbj⟩
    obtain ⟨q,hq⟩ := hconn i hi j hj
    let r := q.toPath
    have hrS : ∀ k∈r.val.support,k∈S := fun k hk => hq k (q.support_toPath_subset_support hk)
    obtain ⟨s,hs,hw⟩ := C.lift_path_variable hA H (fun i => d i-1) hdiam hbridge
      r.val r.property {x | ∃ k∈S,x∈C.branch k}
      (fun k hk z hz => ⟨k,hrS k hk,hz⟩) hai hbj
    have hm := pathMass_add_one (fun i => d i-1) r.val r.property
    have he : pathMass (fun i => (d i-1)+1) r.val=pathMass d r.val := by
      congr 1;funext i;ring
    rw [he] at hm
    have hsub : r.val.support.toFinset⊆S := fun k hk => hrS k (List.mem_toFinset.mp hk)
    have hle : pathMass d r.val≤pathMass d p := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k hk _ => (show (0:ℝ)≤1 by norm_num).trans (hd k (List.mem_toFinset.mp hk)))
    exact ⟨s,hs,by linarith⟩
  · rw [C.connectorEdges_unit_weight hA hT H hH S hunit]
    have hcard : S.card=p.length+1 := by
      simp only [S,List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support]
    have hedge := internalEdges_card_lower H S hconn ⟨x,List.mem_toFinset.mpr p.start_mem_support⟩
    have hlen : (p.length:ℝ)≤(internalEdges H S).card := by exact_mod_cast (show p.length≤(internalEdges H S).card by omega)
    have hsum : c*pathMass (fun i => d i-1) p≤∑ i∈S,credit i := by
      rw [pathMass,Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi => hcredit i (List.mem_toFinset.mp hi)
    have hm := pathMass_add_one (fun i => d i-1) p hp
    have he : pathMass (fun i => (d i-1)+1) p=pathMass d p := by congr 1;funext i;ring
    rw [he] at hm
    nlinarith [mul_le_mul_of_nonneg_left hlen hc]

end MinorFreeSpanners
