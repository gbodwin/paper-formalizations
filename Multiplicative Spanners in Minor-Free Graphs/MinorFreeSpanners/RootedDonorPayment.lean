import MinorFreeSpanners.ResidualPathDonorCredit

/-! Actual long-path donors pay at most two short endpoint pieces per
component. Only the at-most-two components touched by the actual diameter
reserve draw on the old root's spare credit. No donor-payment premise is used. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem finite_two_exception_charge {I J : Type*} (F Q : Finset J)
    (ends : J → Finset I) (N : ℕ) (a donor released : ℝ)
    (ha : 0≤a) (hQ : Q.card≤2) (hends : ∀ t∈F,(ends t).card≤2*N)
    (hdonor : 2*(N:ℝ)*a≤donor)
    (hrel : donor*(F\Q).card≤released) :
    (∑ t∈F,a*(ends t).card)≤released+4*N*a := by
  classical
  have hsub : F⊆(F\Q)∪Q := by intro t ht;by_cases h : t∈Q <;> simp [ht,h]
  have hcard : F.card≤(F\Q).card+2 :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
  have hcardR : (F.card:ℝ)≤(F\Q).card+2 := by exact_mod_cast hcard
  have hsum : (∑ t∈F,a*(ends t).card)≤(F.card:ℝ)*(2*N*a) := by
    calc
      _ ≤ ∑ _t∈F,2*N*a := Finset.sum_le_sum fun t ht => by
        have hh : ((ends t).card:ℝ)≤2*N := by exact_mod_cast hends t ht
        nlinarith [mul_le_mul_of_nonneg_right hh ha]
      _ = _ := by simp
  have hscale := mul_le_mul_of_nonneg_right hcardR (show 0≤2*(N:ℝ)*a by positivity)
  have hdscale := mul_le_mul_of_nonneg_right hdonor (Nat.cast_nonneg (F\Q).card)
  nlinarith

 theorem rooted_long_donor_payment {I : Type*} [Fintype I]
    (H : SimpleGraph I) (U : Finset I) (root : I) (ports : Finset I)
    (hrU : root∉U)
    (hconn : ConnectedWithin (rootedResidualGraph H U root ports) (insert root U))
    (F : Finset (H.induce (U:Set I)).ConnectedComponent)
    (ends : (H.induce (U:Set I)).ConnectedComponent → Finset I)
    (d credit : I → ℝ) (K L c b a spare future : ℝ) (N : ℕ)
    (hroot : 1≤d root) (hK : 0≤K) (hc : 0≤c) (ha : 0≤a)
    (hd : ∀ i∈U,2≤d i)
    (hcomponent : ∀ Q : (H.induce (U:Set I)).ConnectedComponent,
      ∀ x y,∀ p : H.Walk x y,p.IsPath →
      (∀ i∈p.support,i∈ResidualComponents.block H U Q) → pathMass d p≤K)
    (hlong : ∀ t∈F,∃ x y,∃ p : H.Walk x y,p.IsPath ∧
      (∀ i∈p.support,i∈ResidualComponents.block H U t) ∧ L≤pathMass d p)
    (hends : ∀ t∈F,(ends t).card≤2*N)
    (hcredit : ∀ i∈U,c*(d i-1)≤credit i)
    (hbase : ∀ i∈U,c*b≤credit i) (hsize : 2*K≤N*b)
    (hhalf : 2*a≤c*b) (hdonor : 2*(N:ℝ)*a≤c*L/4)
    (hbudget : 5*(N:ℝ)*a+future≤spare) :
    ∃ radius : ℝ,d root-1≤radius ∧ radius≤d root-1+2*K ∧
      (∀ x y,∀ p : (rootedResidualGraph H U root ports).Walk x y,p.IsPath →
        (∀ i∈p.support,i∈insert root U) → pathMass d p-1≤radius) ∧
      c*radius+a*U.card+(∑ t∈F,a*(ends t).card)+future≤
        c*(d root-1)+spare+(∑ i∈U,credit i)+
          c*(internalEdges (rootedResidualGraph H U root ports) (insert root U)).card := by
  classical
  obtain ⟨R,Q,radius,hRU,hRcard,hQ,hcover,hlo,hhi,hpaths,hreserve⟩ :=
    rooted_reserve_two_components H U root ports hrU hconn d credit K c b N
      hroot hK hc hcomponent hcredit hbase hsize
  have hreleased := residual_path_donor_credit H U R Q F d credit L c a hc ha hcover
    hd hcredit (fun i hi => hhalf.trans (hbase i hi)) hlong
  have hcharges := finite_two_exception_charge F Q ends N a (c*L/4)
    (∑ i∈U\R,(credit i-a)) ha hQ hends hdonor hreleased
  have hsum := Finset.sum_sdiff (f:=credit) hRU
  have hcount : (U.card:ℝ)=(U\R).card+R.card := by
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card hRU).symm
  have hRc : (R.card:ℝ)≤N := by exact_mod_cast hRcard
  have hRa := mul_le_mul_of_nonneg_right hRc ha
  have hexcess : (∑ i∈U\R,(credit i-a))=(∑ i∈U\R,credit i)-(U\R).card*a := by
    rw [Finset.sum_sub_distrib]
    simp
  refine ⟨radius,hlo,hhi,hpaths,?_⟩
  nlinarith

end MinorFreeSpanners
