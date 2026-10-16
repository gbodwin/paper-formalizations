import LightEFTSpanners.StoredOriginalWeightEncoding
namespace LightEFTSpanners.StoredOriginalWeightLookup.WeightTypedComparison
def weight {n : ℕ} (e : Sym2 (Fin n)) : TypedBank n → ℚ :=
  List.rec (motive := fun _ => ℚ) 0
    (fun r _ rest => if e=s(r.1.1,r.1.2) then r.2 else rest)
theorem weight_eq_prior {n : ℕ} (e : Sym2 (Fin n)) (bank : TypedBank n) :
    weight e bank = LightEFTSpanners.StoredOriginalWeightLookup.weight e bank := by
  induction bank with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨p,q⟩
    exact congrArg (fun rest => if e=s(p.1,p.2) then q else rest) ih
#print axioms weight_eq_prior
end LightEFTSpanners.StoredOriginalWeightLookup.WeightTypedComparison
