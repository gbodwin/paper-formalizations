import LightEFTSpanners.StoredForestInputTrace

namespace LightEFTSpanners.StoredDrawLookup
abbrev TypedBank (n : ℕ) := List (ℕ × List (List (Fin n × Fin n)))

def encode {n : ℕ} (bank : TypedBank n) : Bank :=
  bank.map fun r => (r.1,StoredVote.encodeDraws r.2)

def typedValue {n : ℕ} (key : ℕ) : TypedBank n → List (List (Fin n × Fin n)) :=
  List.rec (motive := fun _ => List (List (Fin n × Fin n))) []
    (fun r _ rest => if key=r.1 then r.2 else rest)

theorem typedValue_nil {n : ℕ} (key : ℕ) : typedValue (n:=n) key [] = [] := rfl

theorem typedValue_cons {n : ℕ} (key i : ℕ) (ds : List (List (Fin n × Fin n)))
    (xs : TypedBank n) : typedValue key ((i,ds)::xs) = if key=i then ds else typedValue key xs := rfl

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
    ℕ → List (List (Fin n × Fin n)) → List (StoredComponentRecord.TypedInput n) :=
  fun i fs => List.rec (motive := fun _ => ℕ → List (StoredComponentRecord.TypedInput n))
    (fun _ => [])
    (fun es _ next j => (StoredCanonicalComponents.roots es).map (fun root =>
      ⟨StoredForestHosts.label n j root.val,StoredEdgeComponent.vertices es root,
        ⟨StoredDiscoveredHosts.typedHost es root,
          StoredDrawLookup.typedValue (StoredForestHosts.label n j root.val) bank⟩⟩) ++ next (j+1)) fs i

theorem typedInputs_nil {n : ℕ} (bank : StoredDrawLookup.TypedBank n) (i : ℕ) :
    typedInputs bank i [] = [] := rfl

theorem typedInputs_cons {n : ℕ} (bank : StoredDrawLookup.TypedBank n) (i : ℕ)
    (es : List (Fin n × Fin n)) (rest : List (List (Fin n × Fin n))) :
    typedInputs bank i (es::rest) = (StoredCanonicalComponents.roots es).map (fun root =>
      ⟨StoredForestHosts.label n i root.val,StoredEdgeComponent.vertices es root,
        ⟨StoredDiscoveredHosts.typedHost es root,
          StoredDrawLookup.typedValue (StoredForestHosts.label n i root.val) bank⟩⟩) ++ typedInputs bank (i+1) rest := rfl

end LightEFTSpanners.StoredForestInput
