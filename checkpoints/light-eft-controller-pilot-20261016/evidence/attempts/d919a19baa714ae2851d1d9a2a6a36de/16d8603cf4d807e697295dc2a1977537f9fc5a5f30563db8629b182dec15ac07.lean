import LightEFTSpanners.StoredForestInputTrace

namespace LightEFTSpanners.StoredDrawLookup
abbrev TypedBank (n : ℕ) := List (ℕ × List (List (Fin n × Fin n)))

def encode {n : ℕ} (bank : TypedBank n) : Bank :=
  bank.map fun r => (r.1,StoredVote.encodeDraws r.2)

def typedValue {n : ℕ} (key : ℕ) : TypedBank n → List (List (Fin n × Fin n))
  | [] => []
  | (i,ds)::xs => if key=i then ds else typedValue key xs

theorem value_encoded {n : ℕ} (key : ℕ) (bank : TypedBank n) :
    value key (encode bank)=StoredVote.encodeDraws (typedValue key bank) := by
  induction bank with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨i,ds⟩
    by_cases h : key=i <;> simp [encode,value,typedValue,h] at *
    exact ih
end LightEFTSpanners.StoredDrawLookup

namespace LightEFTSpanners.StoredForestInput

def typedInputs {n : ℕ} (bank : StoredDrawLookup.TypedBank n) :
    ℕ → List (List (Fin n × Fin n)) → List (StoredComponentRecord.TypedInput n)
  | _,[] => []
  | i,es::rest => (StoredCanonicalComponents.roots es).map (fun root =>
      ⟨StoredForestHosts.label n i root.val,StoredEdgeComponent.vertices es root,
        ⟨StoredDiscoveredHosts.typedHost es root,
          StoredDrawLookup.typedValue (StoredForestHosts.label n i root.val) bank⟩⟩)++typedInputs bank (i+1) rest
end LightEFTSpanners.StoredForestInput
