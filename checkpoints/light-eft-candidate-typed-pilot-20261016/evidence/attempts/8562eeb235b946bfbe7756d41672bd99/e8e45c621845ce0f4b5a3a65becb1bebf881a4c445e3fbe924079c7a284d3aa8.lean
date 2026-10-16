import LightEFTSpanners.StoredCandidateDrawEncoding
namespace LightEFTSpanners.StoredCandidateDrawLookup.TypedPilotComparison
def typedValue {n : ℕ} (e : Sym2 (Fin n)) : TypedBank n → StoredDrawLookup.TypedBank n :=
  List.rec (motive := fun _ => StoredDrawLookup.TypedBank n) []
    (fun r _ rest => if e=s(r.1.1,r.1.2) then r.2 else rest)
theorem typedValue_eq_prior {n : ℕ} (e : Sym2 (Fin n)) (bank : TypedBank n) :
    typedValue e bank = LightEFTSpanners.StoredCandidateDrawLookup.typedValue e bank := by
  induction bank with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨p,ds⟩
    exact congrArg (fun rest => if e=s(p.1,p.2) then ds else rest) ih
#print axioms typedValue_eq_prior
end LightEFTSpanners.StoredCandidateDrawLookup.TypedPilotComparison
