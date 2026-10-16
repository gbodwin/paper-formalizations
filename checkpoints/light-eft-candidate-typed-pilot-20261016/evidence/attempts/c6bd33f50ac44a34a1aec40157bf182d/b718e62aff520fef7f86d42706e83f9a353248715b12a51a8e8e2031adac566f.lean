import LightEFTSpanners.StoredWeightSort

namespace LightEFTSpanners.StoredWeightSort

def bound (bank : StoredOriginalWeightLookup.Bank) (xs : List StoredEdges.Edge) : ℕ :=
  (4*bank.length+60)*(xs.length+1)^2

theorem split_budget (m a b : ℕ) (ha : 1≤a) (hb : 1≤b) :
    (4*m+60)*(a+1)^2+(4*m+60)*(b+1)^2+(a+b)*(2*m+12)+11≤
      (4*m+60)*(a+b+1)^2 := by
  have hp : a+b≤2*a*b := by
    have h1 := Nat.mul_le_mul_left a hb
    have h2 := Nat.mul_le_mul_left b ha
    nlinarith
  have hn : 2≤a+b := by omega
  have hid : a+b-1+1=a+b := by omega
  have hgap : (a+1)^2+(b+1)^2+(a+b-1)≤(a+b+1)^2 := by nlinarith
  have hmul := Nat.mul_le_mul_left (4*m+60) hgap
  have hpos : 1≤a+b-1 := by omega
  have hm := Nat.mul_le_mul_left (2*m) hpos
  nlinarith
end LightEFTSpanners.StoredWeightSort
