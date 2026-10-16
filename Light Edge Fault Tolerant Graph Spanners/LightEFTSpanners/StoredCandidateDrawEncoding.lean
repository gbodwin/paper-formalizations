import LightEFTSpanners.StoredOriginalCandidateTrace

namespace LightEFTSpanners.StoredCandidateDrawLookup
abbrev TypedBank (n : ℕ) := List ((Fin n × Fin n) × StoredDrawLookup.TypedBank n)

def encode {n : ℕ} (bank : TypedBank n) : Bank :=
  bank.map fun r => ((r.1.1.val,r.1.2.val),StoredDrawLookup.encode r.2)

def typedValue {n : ℕ} (e : Sym2 (Fin n)) : TypedBank n → StoredDrawLookup.TypedBank n :=
  List.rec (motive := fun _ => StoredDrawLookup.TypedBank n) []
    (fun r _ rest => if e=s(r.1.1,r.1.2) then r.2 else rest)

theorem typedValue_nil {n : ℕ} (e : Sym2 (Fin n)) : typedValue e [] = [] := rfl

theorem typedValue_cons {n : ℕ} (e : Sym2 (Fin n)) (p : Fin n × Fin n)
    (ds : StoredDrawLookup.TypedBank n) (rs : TypedBank n) :
    typedValue e ((p,ds)::rs) = if e=s(p.1,p.2) then ds else typedValue e rs := rfl

theorem value_encoded {n : ℕ} (u v : Fin n) (bank : TypedBank n) :
    value (u.val,v.val) (encode bank)=StoredDrawLookup.encode (typedValue s(u,v) bank) := by
  induction bank with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨⟨a,b⟩,ds⟩
    have he := StoredEdges.same_encode u v a b
    simp only [encode] at ih
    by_cases h : s(u,v)=s(a,b) <;> simp [encode,value,typedValue,he,h,ih]
end LightEFTSpanners.StoredCandidateDrawLookup

namespace LightEFTSpanners.StoredOriginalCandidateRecords

def typedValue {n : ℕ} (Q : List (Fin n × Fin n)) (bank : StoredCandidateDrawLookup.TypedBank n) :
    List (Fin n × Fin n) → List (StoredForestBank.TypedInput n) :=
  List.rec (motive := fun _ => List (StoredForestBank.TypedInput n)) []
    (fun x _ rest => if s(x.1,x.2)∈StoredSample.edgeSet Q then rest
      else ⟨x,StoredCandidateDrawLookup.typedValue s(x.1,x.2) bank⟩::rest)

theorem typedValue_nil {n : ℕ} (Q : List (Fin n × Fin n))
    (bank : StoredCandidateDrawLookup.TypedBank n) : typedValue Q bank [] = [] := rfl

theorem typedValue_cons {n : ℕ} (Q : List (Fin n × Fin n))
    (bank : StoredCandidateDrawLookup.TypedBank n) (x : Fin n × Fin n)
    (xs : List (Fin n × Fin n)) :
    typedValue Q bank (x::xs) = if s(x.1,x.2)∈StoredSample.edgeSet Q then typedValue Q bank xs
      else ⟨x,StoredCandidateDrawLookup.typedValue s(x.1,x.2) bank⟩::typedValue Q bank xs := rfl

theorem value_encoded {n : ℕ} (Q : List (Fin n × Fin n)) (bank : StoredCandidateDrawLookup.TypedBank n)
    (xs : List (Fin n × Fin n)) :
    value (StoredEdges.encode Q) (StoredCandidateDrawLookup.encode bank) (StoredEdges.encode xs)=
      (typedValue Q bank xs).map StoredForestBank.encode := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hm : StoredEdges.contains (x.1.val,x.2.val) (StoredEdges.encode Q)=true ↔ s(x.1,x.2)∈StoredSample.edgeSet Q := by
      simpa only [StoredSample.edgeSet,List.mem_toFinset] using StoredEdges.contains_encode x.1 x.2 Q
    cases hr : StoredEdges.contains (x.1.val,x.2.val) (StoredEdges.encode Q) with
    | true =>
      have h := hm.mp hr
      simp only [StoredEdges.encode] at hr
      simpa [StoredEdges.encode,value,typedValue,hr,h] using ih
    | false =>
      have h : s(x.1,x.2)∉StoredSample.edgeSet Q := by intro h;have ht := hm.mpr h;rw [hr] at ht;cases ht
      simp only [StoredEdges.encode] at hr
      simpa [StoredEdges.encode,value,typedValue,hr,h,StoredForestBank.encode,StoredCandidateDrawLookup.value_encoded] using
        congrArg (List.cons (StoredForestBank.encode (⟨x,StoredCandidateDrawLookup.typedValue s(x.1,x.2) bank⟩ : StoredForestBank.TypedInput n))) ih
end LightEFTSpanners.StoredOriginalCandidateRecords
