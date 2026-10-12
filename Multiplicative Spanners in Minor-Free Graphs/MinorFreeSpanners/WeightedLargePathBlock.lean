import MinorFreeSpanners.LargePathBlockPayment
import MinorFreeSpanners.VariableClusterWalkLift
import MinorFreeSpanners.BranchingConnectorBudget

/-! A large actual path block is realized in the original weighted host,
with confined paths and payment using its original unit connector identities. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem weighted_large_path_block {I V : Type*} [Fintype I]
    {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    {x y : I} (p : H.Walk x y) (hp : p.IsPath) (d credit : I → ℝ)
    (L K c b a : ℝ) (N : ℕ) (hc : 0≤c) (ha : 0≤a)
    (hd : ∀ i∈p.support,1≤d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ q : A.Walk x y,(∀ z∈q.support,z∈C.branch i) ∧ walkWeight w q≤d i-1)
    (hL : L≤pathMass d p) (hK : pathMass d p≤K)
    (hbase : ∀ i∈p.support,c*b≤credit i) (hlarge : N<p.length+1)
    (hsize : K-1≤N*b) (hcost : (N+1:ℕ)*a≤c*b/2) :
    let S := p.support.toFinset
    let carrier := {x | ∃ i∈S,x∈C.branch i}
    ∃ radius : ℝ,0≤radius ∧ L-1≤radius ∧ radius≤K-1 ∧
      (∀ x∈carrier,∀ y∈carrier,∃ q : G.Walk x y,
        (∀ z∈q.support,z∈carrier) ∧ walkWeight w q≤radius) ∧
      c*radius+a*S.card+c*b/2≤(∑ i∈S,credit i)+
        c*(∑ e∈C.connectorEdges hA hT H hH S,w e) := by
  classical
  obtain ⟨radius,hr,hlo,hhi,hpaths,hpaid⟩ := large_path_block_payment p hp d credit
    L K c b a N hc ha hd hL hK hbase hlarge hsize hcost
  let S := p.support.toFinset
  have hconn : ConnectedWithin H S := forest_walk_support_connected p
  have hbridge : ∀ i j,H.Adj i j → ∃ x∈C.branch i,∃ y∈C.branch j,
      ∃ _hxy : G.Adj x y,w s(x,y)≤1 := by
    intro i j hij
    obtain ⟨_,x,hx,y,hy,hxy⟩ := hH hij
    exact ⟨x,hx,y,hy,hT hxy,(hunit _ hxy).le⟩
  refine ⟨radius,hr,hlo,hhi,?_,?_⟩
  · rintro x ⟨i,hi,hxi⟩ y ⟨j,hj,hyj⟩
    obtain ⟨q,hq⟩ := hconn i hi j hj
    let r := q.toPath
    have hrS : ∀ k∈r.val.support,k∈S := fun k hk => hq k (q.support_toPath_subset_support hk)
    obtain ⟨s,hs,hw⟩ := C.lift_path_variable hA H (fun i => d i-1) hdiam hbridge
      r.val r.property {x | ∃ k∈S,x∈C.branch k}
      (fun k hk z hz => ⟨k,hrS k hk,hz⟩) hxi hyj
    have hm := pathMass_add_one (fun i => d i-1) r.val r.property
    have he : pathMass (fun i => (d i-1)+1) r.val=pathMass d r.val := by
      congr 1;funext i;ring
    rw [he] at hm
    have hb := hpaths i j r.val r.property (fun k hk => List.mem_toFinset.mp (hrS k hk))
    exact ⟨s,hs,by linarith⟩
  · rw [C.connectorEdges_unit_weight hA hT H hH S hunit]
    exact hpaid

end MinorFreeSpanners
