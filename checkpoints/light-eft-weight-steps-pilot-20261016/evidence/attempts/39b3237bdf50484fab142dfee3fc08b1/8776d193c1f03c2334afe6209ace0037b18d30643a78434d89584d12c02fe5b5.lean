import LightEFTSpanners.StoredForestCandidatesExecutable

namespace LightEFTSpanners.StoredOriginalWeightLookup
open Controller
abbrev Bank := List (StoredEdges.Edge × ℚ)
inductive State where
  | scan : Bank → State
  | halt : ℚ → State
  deriving DecidableEq, Repr

def transition (key : StoredEdges.Edge) : State → Option State
  | .scan [] => some (.halt 0)
  | .scan ((i,ds)::xs) => if StoredEdges.same key i then some (.halt ds) else some (.scan xs)
  | .halt _ => none

def value (key : StoredEdges.Edge) : Bank → ℚ
  | [] => 0
  | (i,ds)::xs => if StoredEdges.same key i then ds else value key xs

def steps (key : StoredEdges.Edge) : Bank → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun r _ rest => if StoredEdges.same key r.1 then 1 else 1+rest)

theorem steps_nil (key : StoredEdges.Edge) : steps key [] = 1 := rfl

theorem steps_cons (key i : StoredEdges.Edge) (ds : ℚ) (xs : Bank) :
    steps key ((i,ds)::xs) = if StoredEdges.same key i then 1 else 1+steps key xs := rfl


theorem lookup_trace (key : StoredEdges.Edge) (bank : Bank) :
    Trace (transition key) (steps key bank) (.scan bank) (.halt (value key bank)) := by
  induction bank with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    rcases r with ⟨i,ds⟩
    by_cases h : StoredEdges.same key i=true
    · simpa [steps,value,h] using Trace.one
        (show transition key (.scan ((i,ds)::rs))=some (.halt ds) by simp [transition,h])
    · simpa [steps,value,h,Nat.add_comm] using Trace.cons
        (show transition key (.scan ((i,ds)::rs))=some (.scan rs) by simp [transition,h]) ih

theorem steps_le (key : StoredEdges.Edge) (bank : Bank) : steps key bank≤bank.length+1 := by
  induction bank with
  | nil => simp [steps]
  | cons r rs ih =>
    rcases r with ⟨i,ds⟩
    simp only [steps,List.length_cons]
    split <;> omega
end LightEFTSpanners.StoredOriginalWeightLookup
