import MinorFreeSpanners.FiniteReservePayment

/-! A proved geometric surplus pays all incident edges, including when the
number of old clusters is large. The large case uses actual baseline credits;
the small case uses the surplus. No upper bound on carrier size is assumed. -/
namespace MinorFreeSpanners
open Finset

 theorem bounded_surplus_payment {I : Type*} (S : Finset I) (credit : I → ℝ)
    (c radius bridge delta b a : ℝ) (N : ℕ)
    (hc : 0≤c) (ha : 0≤a) (hbridge : 0≤bridge)
    (hbase : ∀ i∈S,c*b≤credit i)
    (hgap : c*radius+c*delta≤(∑ i∈S,credit i)+c*bridge)
    (hsmall : a*N+c*b/2≤c*delta)
    (hlarge : 2*c*radius+c*b≤N*(c*b)) (hpay : 2*a≤c*b) :
    c*radius+a*S.card+c*b/2≤(∑ i∈S,credit i)+c*bridge := by
  have hcb : 0≤c*b := le_trans (by linarith) hpay
  by_cases hn : S.card≤N
  · have hnR : (S.card:ℝ)≤N := by exact_mod_cast hn
    have hm := mul_le_mul_of_nonneg_left hnR ha
    linarith
  · have hnR : (N:ℝ)≤S.card := by exact_mod_cast (show N≤S.card by omega)
    have hsum : (S.card:ℝ)*(c*b)≤∑ i∈S,credit i := by
      calc
        _ = ∑ _i∈S,c*b := by simp
        _ ≤ _ := Finset.sum_le_sum fun i hi => hbase i hi
    have hnr := mul_le_mul_of_nonneg_right hnR hcb
    have hap := mul_le_mul_of_nonneg_right hpay (Nat.cast_nonneg S.card : (0:ℝ)≤S.card)
    have he := mul_nonneg hc hbridge
    nlinarith

end MinorFreeSpanners
