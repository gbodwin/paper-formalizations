import MinorFreeSpanners.FiniteReservePayment
import MinorFreeSpanners.WeightedPathBlockFamily

/-! A segmented path block with more than N actual old clusters internally
selects N reserve vertices and a distinct surplus donor. It pays its own
incident-edge allocation while retaining half a baseline for later use. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

 theorem large_path_block_payment {I : Type*} [Fintype I] {H : SimpleGraph I}
    {x y : I} (p : H.Walk x y) (hp : p.IsPath) (d credit : I → ℝ)
    (L K c b a : ℝ) (N : ℕ) (hc : 0≤c) (ha : 0≤a)
    (hd : ∀ i∈p.support,1≤d i)
    (hL : L≤pathMass d p) (hK : pathMass d p≤K)
    (hbase : ∀ i∈p.support,c*b≤credit i)
    (hlarge : N<p.length+1)
    (hsize : K-1≤N*b) (hcost : (N+1:ℕ)*a≤c*b/2) :
    ∃ radius : ℝ,0≤radius ∧ L-1≤radius ∧ radius≤K-1 ∧
      (∀ u v,∀ q : H.Walk u v,q.IsPath →
        (∀ i∈q.support,i∈p.support) → pathMass d q-1≤radius) ∧
      c*radius+a*p.support.toFinset.card+c*b/2≤
        (∑ i∈p.support.toFinset,credit i)+c*(internalEdges H p.support.toFinset).card := by
  classical
  let S := p.support.toFinset
  have hScard : S.card=p.length+1 := by
    simp only [S,List.toFinset_card_of_nodup hp.support_nodup,Walk.length_support]
  obtain ⟨R,hRS,hRcard⟩ := Finset.exists_subset_card_eq (show N≤S.card by omega)
  have hdiff : (S\R).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_sdiff_of_subset hRS,hRcard]
    omega)
  obtain ⟨z,hz⟩ := hdiff
  have hzS := (Finset.mem_sdiff.mp hz).1
  have hzR := (Finset.mem_sdiff.mp hz).2
  have hsum : (N:ℝ)*(c*b)≤∑ i∈R,credit i := by
    calc
      _ = ∑ _i∈R,c*b := by simp [hRcard]
      _ ≤ _ := Finset.sum_le_sum fun i hi => hbase i (List.mem_toFinset.mp (hRS hi))
  have hmass : 1≤pathMass d p := by
    have hh := Finset.single_le_sum (s:=S) (f:=d)
      (fun i hi => (show (0:ℝ)≤1 by norm_num).trans (hd i (List.mem_toFinset.mp hi)))
      (List.mem_toFinset.mpr p.start_mem_support)
    exact (hd x p.start_mem_support).trans hh
  have hreserve : c*(pathMass d p-1)≤(∑ i∈R,credit i)+c*(internalEdges H S).card := by
    have hh := mul_le_mul_of_nonneg_left (show pathMass d p-1≤N*b by linarith) hc
    have hb := mul_nonneg hc (Nat.cast_nonneg (internalEdges H S).card)
    nlinarith
  refine ⟨pathMass d p-1,by linarith,by linarith,by linarith,?_,?_⟩
  · intro u v q _ hq
    have hs : q.support.toFinset⊆S := fun i hi => List.mem_toFinset.mpr (hq i (List.mem_toFinset.mp hi))
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun i hi _ => (show (0:ℝ)≤1 by norm_num).trans (hd i (List.mem_toFinset.mp hi)))
    exact sub_le_sub_right hh 1
  · exact finite_reserve_payment S R z credit c b a _ _ N hRS (by omega) hzS hzR ha
      (fun i hi => hbase i (List.mem_toFinset.mp hi)) hcost hreserve

end MinorFreeSpanners
