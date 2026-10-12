import MinorFreeSpanners.RootedAbsorptionReserve

/-! Pay every absorbed vertex from the actual bounded diameter reserve and
released credits, counting the root's old reserve exactly once. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem finite_external_reserve_payment {I : Type*} (S R : Finset I)
    (credit : I → ℝ) (old spare future reserve a bridge : ℝ) (N : ℕ)
    (hRS : R⊆S) (hcard : R.card≤N) (ha : 0≤a)
    (hcredit : ∀ i∈S,a≤credit i) (hbudget : N*a+future≤spare)
    (hreserve : reserve≤old+(∑ i∈R,credit i)+bridge) :
    reserve+a*S.card+future≤old+spare+(∑ i∈S,credit i)+bridge := by
  classical
  have hrel : ((S\R).card:ℝ)*a≤∑ i∈S\R,credit i := by
    calc
      _ = ∑ _i∈S\R,a := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi => hcredit i (Finset.mem_sdiff.mp hi).1
  have hsum := Finset.sum_sdiff (f:=credit) hRS
  have hn : (S.card:ℝ)=(S\R).card+R.card := by exact_mod_cast (Finset.card_sdiff_add_card_eq_card hRS).symm
  have hRc : (R.card:ℝ)≤N := by exact_mod_cast hcard
  have hcharge := mul_le_mul_of_nonneg_right hRc ha
  nlinarith

 theorem rooted_absorption_payment {I : Type*} [Fintype I]
    (H : SimpleGraph I) (S : Finset I) (hconn : ConnectedWithin H S)
    (root : I) (hrootS : root∈S) (d credit : I → ℝ)
    (K c b a spare future : ℝ) (N : ℕ)
    (hroot : 1≤d root) (hK : 0≤K) (hc : 0≤c) (ha : 0≤a)
    (havoid : ∀ u v,∀ q : H.Walk u v,q.IsPath → (∀ i∈q.support,i∈S) →
      root∉q.support → pathMass d q≤K)
    (hcredit : ∀ i∈S,i≠root → c*(d i-1)≤credit i)
    (hbase : ∀ i∈S,i≠root → c*b≤credit i) (hsize : 2*K≤N*b)
    (hrelease : a≤c*b) (hbudget : N*a+future≤spare) :
    ∃ radius : ℝ,d root-1≤radius ∧ radius≤d root-1+2*K ∧
      (∀ u v,∀ p : H.Walk u v,p.IsPath → (∀ i∈p.support,i∈S) → pathMass d p-1≤radius) ∧
      c*radius+a*(S.erase root).card+future≤c*(d root-1)+spare+
        (∑ i∈S.erase root,credit i)+c*(internalEdges H S).card := by
  classical
  obtain ⟨R,radius,hRS,hcard,hlo,hhi,hpaths,hreserve⟩ :=
    rooted_absorption_reserve H S hconn root hrootS d credit K c b N hroot hK hc havoid hcredit hbase hsize
  refine ⟨radius,hlo,hhi,hpaths,?_⟩
  exact finite_external_reserve_payment (S.erase root) R credit (c*(d root-1)) spare future
    (c*radius) a (c*(internalEdges H S).card) N hRS hcard ha
    (fun i hi => hrelease.trans (hbase i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1))
    hbudget hreserve

end MinorFreeSpanners
