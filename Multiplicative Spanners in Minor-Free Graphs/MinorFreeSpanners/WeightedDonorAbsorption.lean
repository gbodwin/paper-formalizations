import MinorFreeSpanners.RootedDonorPayment
import MinorFreeSpanners.WeightedRootedAbsorption

/-! The donor payment is realized on the same original weighted host: actual
component ports construct the connected coarse graph, actual original unit
connectors pay its reserve, and confined host walks realize the chosen radius.
The endpoint vertex sets and their size bounds remain explicit. -/
namespace MinorFreeSpanners
open SimpleGraph LightSpanners Finset
attribute [local instance] Classical.propDecidable

 theorem weighted_donor_absorption {I V : Type*} [Fintype I]
    {A T G : SimpleGraph V} {w : Sym2 V → ℝ} {D : ℝ}
    (C : ClusterFamily (I:=I) A w D) (hA : A≤G) (hT : T≤G)
    (hunit : ∀ e∈T.edgeSet,w e=1) (H : SimpleGraph I) (hH : H≤C.graph T)
    (U : Finset I) (root : I) (hr : root∉U)
    (port : (H.induce (U:Set I)).ConnectedComponent → I)
    (hport : ∀ t,port t∈ResidualComponents.block H U t)
    (hbridge : ∀ t,(C.graph T).Adj root (port t))
    (F : Finset (H.induce (U:Set I)).ConnectedComponent)
    (ends : (H.induce (U:Set I)).ConnectedComponent → Finset I)
    (d credit : I → ℝ) (K L c b a spare future : ℝ) (N : ℕ)
    (hroot : 1≤d root) (hK : 0≤K) (hc : 0≤c) (ha : 0≤a)
    (hd : ∀ i∈U,2≤d i)
    (hdiam : ∀ i x,x∈C.branch i → ∀ y,y∈C.branch i →
      ∃ p : A.Walk x y,(∀ z∈p.support,z∈C.branch i) ∧ walkWeight w p≤d i-1)
    (hcomponent : ∀ t,∀ x y,∀ p : H.Walk x y,p.IsPath →
      (∀ i∈p.support,i∈ResidualComponents.block H U t) → pathMass d p≤K)
    (hlong : ∀ t∈F,∃ x y,∃ p : H.Walk x y,p.IsPath ∧
      (∀ i∈p.support,i∈ResidualComponents.block H U t) ∧ L≤pathMass d p)
    (hends : ∀ t∈F,(ends t).card≤2*N)
    (hcredit : ∀ i∈U,c*(d i-1)≤credit i) (hbase : ∀ i∈U,c*b≤credit i)
    (hsize : 2*K≤N*b) (hhalf : 2*a≤c*b) (hdonor : 2*(N:ℝ)*a≤c*L/4)
    (hbudget : 5*(N:ℝ)*a+future≤spare) :
    let S := insert root U
    let B := {x | ∃ i∈S,x∈C.branch i}
    ∃ J : SimpleGraph I,∃ hJ : J≤C.graph T,∃ radius : ℝ,
      d root-1≤radius ∧ radius≤d root-1+2*K ∧
      (∀ x∈B,∀ y∈B,∃ p : G.Walk x y,(∀ z∈p.support,z∈B) ∧ walkWeight w p≤radius) ∧
      c*radius+a*U.card+(∑ t∈F,a*(ends t).card)+future≤
        c*(d root-1)+spare+(∑ i∈U,credit i)+
          c*(∑ e∈C.connectorEdges hA hT J hJ S,w e) := by
  classical
  dsimp
  let ports : Finset I := Finset.univ.image port
  let J := rootedResidualGraph H U root ports
  let S := insert root U
  have hports : ports⊆U := by
    intro i hi
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hi
    exact ResidualComponents.subset H U t (hport t)
  have hreach : ∀ i∈U,∃ j∈ports,∃ p : H.Walk i j,∀ z∈p.support,z∈U := by
    intro i hi
    obtain ⟨t,hit⟩ := ResidualComponents.covers H U hi
    obtain ⟨p,hp⟩ := ResidualComponents.connected H U t i hit (port t) (hport t)
    exact ⟨port t,Finset.mem_image.mpr ⟨t,by simp,rfl⟩,p,
      fun z hz => ResidualComponents.subset H U t (hp z hz)⟩
  have hconn : ConnectedWithin J S := rooted_residual_connected H U root hr ports hports hreach
  have hJ : J≤C.graph T := by
    rintro i j ⟨_,hh | hh | hh⟩
    · exact hH hh.1
    · obtain ⟨t,_,he⟩ := Finset.mem_image.mp hh.2
      simpa only [hh.1,←he] using hbridge t
    · obtain ⟨t,_,he⟩ := Finset.mem_image.mp hh.2
      simpa only [hh.1,←he] using (hbridge t).symm
  obtain ⟨radius,hlo,hhi,hpaths,hpaid⟩ := rooted_long_donor_payment H U root ports hr hconn
    F ends d credit K L c b a spare future N hroot hK hc ha hd hcomponent hlong hends
    hcredit hbase hsize hhalf hdonor hbudget
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
