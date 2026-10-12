import MinorFreeSpanners.RootedResidualConnectivity
import MinorFreeSpanners.AbsorptionCreditPayment

/-! Absorb whole actual residual components through selected original ports.
The radius and its paid reserve are chosen from a longest actual path, rather
than supplied as a numerical certificate. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem owned_component_absorption {I : Type*} [Fintype I]
    (H H0 : SimpleGraph I) (hH : H≤H0) (R : Finset I) (root : I) (hr : root∉R)
    (Q : Finset (H.induce (R:Set I)).ConnectedComponent)
    (port : (H.induce (R:Set I)).ConnectedComponent → I)
    (hport : ∀ t∈Q,port t∈ResidualComponents.block H R t)
    (hbridge : ∀ t∈Q,H0.Adj root (port t))
    (d credit : I → ℝ) (K c b a spare future : ℝ) (N : ℕ)
    (hroot : 1≤d root) (hK : 0≤K) (hc : 0≤c) (ha : 0≤a)
    (hsmall : ∀ t∈Q,∀ x y,∀ p : H.Walk x y,p.IsPath →
      (∀ i∈p.support,i∈ResidualComponents.block H R t) → pathMass d p≤K)
    (hcredit : ∀ i∈R,c*(d i-1)≤credit i) (hbase : ∀ i∈R,c*b≤credit i)
    (hsize : 2*K≤N*b) (hrelease : a≤c*b) (hbudget : N*a+future≤spare) :
    let U := Q.biUnion (ResidualComponents.block H R)
    ∃ J : SimpleGraph I,∃ radius : ℝ,J≤H0 ∧
      ConnectedWithin J (insert root U) ∧ d root-1≤radius ∧ radius≤d root-1+2*K ∧
      (∀ x y,∀ p : J.Walk x y,p.IsPath → (∀ i∈p.support,i∈insert root U) →
        pathMass d p-1≤radius) ∧
      c*radius+a*U.card+future≤c*(d root-1)+spare+(∑ i∈U,credit i)+
        c*(internalEdges J (insert root U)).card := by
  classical
  dsimp
  let U := Q.biUnion (ResidualComponents.block H R)
  let P := Q.image port
  let J := rootedResidualGraph H U root P
  have hUR : U⊆R := by
    intro i hi
    obtain ⟨t,_,hi⟩ := Finset.mem_biUnion.mp hi
    exact ResidualComponents.subset H R t hi
  have hrU : root∉U := fun h => hr (hUR h)
  obtain ⟨hPU,hreach⟩ := components_reach_chosen_ports H R Q port hport
  have hconn : ConnectedWithin J (insert root U) :=
    rooted_residual_connected H U root hrU P hPU hreach
  have hJ : J≤H0 := by
    rintro x y ⟨_,hh | hh | hh⟩
    · exact hH hh.1
    · obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hh.2
      simpa only [hh.1,←he] using hbridge t ht
    · obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hh.2
      simpa only [hh.1,←he] using (hbridge t ht).symm
  have havoid : ∀ x y,∀ p : J.Walk x y,p.IsPath →
      (∀ i∈p.support,i∈insert root U) → root∉p.support → pathMass d p≤K := by
    intro x y p hp hps hn
    obtain ⟨q,hq,hqp⟩ := root_avoiding_transfer H U root P p hn
    have hqU : ∀ i∈q.support,i∈U := by
      intro i hi
      have hi' : i∈p.support := hq ▸ hi
      rcases Finset.mem_insert.mp (hps i hi') with he | he
      · exact (hn (he ▸ hi')).elim
      · exact he
    obtain ⟨t,ht,hxt⟩ := Finset.mem_biUnion.mp (hqU x q.start_mem_support)
    have hqt := residual_walk_in_block H R t q hxt (fun i hi => hUR (hqU i hi))
    simpa only [pathMass,hq] using hsmall t ht x y q (hqp hp) hqt
  obtain ⟨radius,hlo,hhi,hpaths,hpaid⟩ := rooted_absorption_payment J (insert root U) hconn
    root (Finset.mem_insert_self _ _) d credit K c b a spare future N hroot hK hc ha havoid
    (fun i hi hn => hcredit i (hUR (by simpa [hn] using hi)))
    (fun i hi hn => hbase i (hUR (by simpa [hn] using hi))) hsize hrelease hbudget
  refine ⟨J,radius,hJ,hconn,hlo,hhi,hpaths,?_⟩
  simpa only [Finset.erase_insert hrU] using hpaid

end MinorFreeSpanners
