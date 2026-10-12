import MinorFreeSpanners.OwnedResidualAbsorption
import MinorFreeSpanners.VariableClusterWalkLift
import MinorFreeSpanners.BranchingConnectorBudget

/-! Actual host walks and original unit connector credit for rooted
whole-component absorption. The root's saved reserve pays the bounded
critical-path vertices; every other absorbed vertex releases its allocation. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem weighted_rooted_absorption {I V : Type*} [Fintype I]
    {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    (R : Finset I) (root : I) (hr : root∉R)
    (Q : Finset (H.induce (R:Set I)).ConnectedComponent)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (hport : ∀ t∈Q,port t∈ResidualComponents.block H R t)
    (hbridge : ∀ t∈Q,(C.graph T).Adj root (port t))
    (d credit : I → ℝ) (K c b a spare future : ℝ) (N : ℕ)
    (hroot : 1≤d root) (hK : 0≤K) (hc : 0≤c) (ha : 0≤a)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i-1)
    (hsmall : ∀ t∈Q,∀ x y,∀ p : H.Walk x y,p.IsPath →
      (∀ i∈p.support,i∈ResidualComponents.block H R t) → pathMass d p≤K)
    (hcredit : ∀ i∈R,c*(d i-1)≤credit i) (hbase : ∀ i∈R,c*b≤credit i)
    (hsize : 2*K≤N*b) (hrelease : a≤c*b) (hbudget : N*a+future≤spare) :
    let U := Q.biUnion (ResidualComponents.block H R)
    let S := insert root U
    let B := {x | ∃ i∈S,x∈C.branch i}
    ∃ J : SimpleGraph I,∃ hJ : J≤C.graph T,∃ radius : ℝ,
      d root-1≤radius ∧ radius≤d root-1+2*K ∧
      (∀ x∈B,∀ y∈B,∃ p : G.Walk x y,(∀ z∈p.support,z∈B) ∧ walkWeight w p≤radius) ∧
      c*radius+a*U.card+future≤c*(d root-1)+spare+(∑ i∈U,credit i)+
        c*(∑ e∈C.connectorEdges hA hT J hJ S,w e) := by
  classical
  dsimp
  let U := Q.biUnion (ResidualComponents.block H R)
  let S := insert root U
  obtain ⟨J,radius,hJ,hconn,hlo,hhi,hpaths,hpaid⟩ :=
    owned_component_absorption H (C.graph T) hH R root hr Q port hport hbridge
      d credit K c b a spare future N hroot hK hc ha hsmall hcredit hbase hsize hrelease hbudget
  have hjbridge : ∀ i j,J.Adj i j → ∃ x∈C.branch i,∃ y∈C.branch j,
      ∃ _hxy : G.Adj x y,w s(x,y)≤1 := by
    intro i j hij
    obtain ⟨_,x,hx,y,hy,hxy⟩ := hJ hij
    exact ⟨x,hx,y,hy,hT hxy,(hunit _ hxy).le⟩
  refine ⟨J,hJ,radius,hlo,hhi,?_,?_⟩
  · rintro x ⟨i,hi,hxi⟩ y ⟨j,hj,hyj⟩
    obtain ⟨p,hp⟩ := hconn i hi j hj
    let q := p.toPath
    have hqS : ∀ k∈q.val.support,k∈S := fun k hk => hp k (p.support_toPath_subset_support hk)
    obtain ⟨r,hr,hw⟩ := C.lift_path_variable hA J (fun i => d i-1) hdiam hjbridge
      q.val q.property {x | ∃ i∈S,x∈C.branch i}
      (fun k hk z hz => ⟨k,hqS k hk,hz⟩) hxi hyj
    have hm := pathMass_add_one (fun i => d i-1) q.val q.property
    have he : pathMass (fun i => (d i-1)+1) q.val=pathMass d q.val := by
      congr 1;funext i;ring
    rw [he] at hm
    have hb := hpaths i j q.val q.property hqS
    exact ⟨r,hr,by linarith⟩
  · rw [C.connectorEdges_unit_weight hA hT J hJ S hunit]
    exact hpaid

end MinorFreeSpanners
