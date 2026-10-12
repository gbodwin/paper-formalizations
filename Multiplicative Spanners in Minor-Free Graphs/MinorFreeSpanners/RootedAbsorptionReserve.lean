import MinorFreeSpanners.RootedPathDiameter
import MinorFreeSpanners.FiniteReservePayment

/-! A bounded reserve of actual non-root vertices pays the intrinsic radius
of a rooted absorption. The root's old diameter credit is counted once. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem rooted_absorption_reserve {I : Type*} [Fintype I]
    (H : SimpleGraph I) (S : Finset I) (hconn : ConnectedWithin H S)
    (root : I) (hrootS : root∈S) (d credit : I → ℝ) (K c b : ℝ) (N : ℕ)
    (hroot : 1≤d root) (hK : 0≤K) (hc : 0≤c)
    (havoid : ∀ a b,∀ q : H.Walk a b,q.IsPath → (∀ i∈q.support,i∈S) →
      root∉q.support → pathMass d q≤K)
    (hcredit : ∀ i∈S,i≠root → c*(d i-1)≤credit i)
    (hbase : ∀ i∈S,i≠root → c*b≤credit i) (hsize : 2*K≤N*b) :
    ∃ R : Finset I,∃ radius : ℝ,R⊆S.erase root ∧ R.card≤N ∧
      d root-1≤radius ∧ radius≤d root-1+2*K ∧
      (∀ a b,∀ p : H.Walk a b,p.IsPath → (∀ i∈p.support,i∈S) → pathMass d p-1≤radius) ∧
      c*radius≤c*(d root-1)+(∑ i∈R,credit i)+c*(internalEdges H S).card := by
  classical
  obtain ⟨x,_,y,_,p,hp,hps,hlo,hhi,hmax⟩ := exists_rooted_diameter_path H d S root hrootS K hroot hK havoid
  let P := p.support.toFinset.erase root
  have hPS : P⊆S.erase root := by
    intro i hi
    obtain ⟨hne,hi⟩ := Finset.mem_erase.mp hi
    exact Finset.mem_erase.mpr ⟨hne,hps i (List.mem_toFinset.mp hi)⟩
  have hbridge : 0≤c*(internalEdges H S).card := mul_nonneg hc (Nat.cast_nonneg _)
  by_cases hsmall : P.card≤N
  · refine ⟨P,pathMass d p-1,hPS,hsmall,hlo,hhi,hmax,?_⟩
    have hedge := internalEdges_card_lower H S hconn ⟨root,hrootS⟩
    have hpcard := Finset.card_le_card (show p.support.toFinset⊆S from
      fun i hi => hps i (List.mem_toFinset.mp hi))
    rw [List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support] at hpcard
    have hlen : (p.length:ℝ)≤(internalEdges H S).card := by exact_mod_cast (show p.length≤(internalEdges H S).card by omega)
    have hlenC := mul_le_mul_of_nonneg_left hlen hc
    have hsum : c*(∑ i∈P,(d i-1))≤∑ i∈P,credit i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi => hcredit i
        (Finset.mem_erase.mp (hPS hi)).2 (Finset.mem_erase.mp hi).1
    have hmass : pathMass d p-1≤(d root-1)+(∑ i∈P,(d i-1))+p.length := by
      have hnode := pathMass_add_one (fun i => d i-1) p hp
      have he : pathMass (fun i => (d i-1)+1) p=pathMass d p := by congr 1;funext i;ring
      rw [he] at hnode
      by_cases hr : root∈p.support.toFinset
      · have hs := Finset.sum_erase_add p.support.toFinset (fun i => d i-1) hr
        change (∑ i∈P,(d i-1))+(d root-1)=pathMass (fun i => d i-1) p at hs
        linarith
      · have heP : P=p.support.toFinset := Finset.erase_eq_of_notMem hr
        rw [heP]
        change pathMass d p-1≤d root-1+pathMass (fun i => d i-1) p+p.length
        linarith
    have hm := mul_le_mul_of_nonneg_left hmass hc
    nlinarith
  · obtain ⟨R,hRP,hcard⟩ := Finset.exists_subset_card_eq (show N≤P.card by omega)
    refine ⟨R,pathMass d p-1,hRP.trans hPS,by omega,hlo,hhi,hmax,?_⟩
    have hsum : (R.card:ℝ)*(c*b)≤∑ i∈R,credit i := by
      calc
        _ = ∑ _i∈R,c*b := by simp
        _ ≤ _ := Finset.sum_le_sum fun i hi => hbase i
          (Finset.mem_erase.mp (hPS (hRP hi))).2 (Finset.mem_erase.mp (hRP hi)).1
    rw [hcard] at hsum
    have hm := mul_le_mul_of_nonneg_left (show pathMass d p-1≤d root-1+N*b by linarith) hc
    nlinarith

end MinorFreeSpanners
