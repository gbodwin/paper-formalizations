import LightEFTSpanners.StoredDrawLookupEncoding
namespace LightEFTSpanners.StoredDrawLookup.DrawPilotComparison
def typedValue {n : ℕ} (key : ℕ) : TypedBank n → List (List (Fin n × Fin n)) :=
  List.rec (motive := fun _ => List (List (Fin n × Fin n))) []
    (fun r _ rest => if key=r.1 then r.2 else rest)
theorem typedValue_eq_prior {n : ℕ} (key : ℕ) (bank : TypedBank n) :
    typedValue key bank = LightEFTSpanners.StoredDrawLookup.typedValue key bank := by
  induction bank with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨i,ds⟩
    exact congrArg (fun rest => if key=i then ds else rest) ih
#print axioms typedValue_eq_prior
end LightEFTSpanners.StoredDrawLookup.DrawPilotComparison
