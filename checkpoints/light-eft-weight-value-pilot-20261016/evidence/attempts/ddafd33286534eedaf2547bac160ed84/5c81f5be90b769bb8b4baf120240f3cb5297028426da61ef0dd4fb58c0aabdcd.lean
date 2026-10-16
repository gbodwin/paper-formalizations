import LightEFTSpanners.StoredOriginalWeightLookup

namespace LightEFTSpanners.StoredOriginalWeightLookup
abbrev TypedBank (n : ℕ) := List ((Fin n × Fin n) × ℚ)

def encode {n : ℕ} (bank : TypedBank n) : Bank :=
  bank.map fun r => ((r.1.1.val,r.1.2.val),r.2)

def weight {n : ℕ} (e : Sym2 (Fin n)) : TypedBank n → ℚ
  | [] => 0
  | (p,c)::rs => if e=s(p.1,p.2) then c else weight e rs

theorem value_encoded {n : ℕ} (u v : Fin n) (bank : TypedBank n) :
    value (u.val,v.val) (encode bank)=weight s(u,v) bank := by
  induction bank with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨⟨a,b⟩,c⟩
    have he := StoredEdges.same_encode u v a b
    simp only [encode] at ih
    simp [encode,value_cons,weight,he,ih]

theorem weight_nonnegative {n : ℕ} (bank : TypedBank n) (h : ∀ r∈bank,0≤r.2)
    (e : Sym2 (Fin n)) : 0≤weight e bank := by
  induction bank with
  | nil => simp [weight]
  | cons r rs ih =>
    simp only [weight]
    split
    · exact h r (by simp)
    · exact ih (fun x hx => h x (by simp [hx]))
end LightEFTSpanners.StoredOriginalWeightLookup
