import LightEFTSpanners.StoredForestHostsCoverage

namespace LightEFTSpanners.StoredDrawLookup
open Controller
abbrev Bank := List (ℕ × StoredVote.Draws)
inductive State where
  | scan : Bank → State
  | halt : StoredVote.Draws → State
  deriving DecidableEq, Repr

def transition (key : ℕ) : State → Option State
  | .scan [] => some (.halt [])
  | .scan ((i,ds)::xs) => if key=i then some (.halt ds) else some (.scan xs)
  | .halt _ => none

def value (key : ℕ) : Bank → StoredVote.Draws :=
  List.rec (motive := fun _ => StoredVote.Draws) []
    (fun r _ rest => if key=r.1 then r.2 else rest)

theorem value_nil (key : ℕ) : value key [] = [] := rfl

theorem value_cons (key i : ℕ) (ds : StoredVote.Draws) (xs : Bank) :
    value key ((i,ds)::xs) = if key=i then ds else value key xs := rfl

def steps (key : ℕ) : Bank → ℕ
  | [] => 1
  | (i,_)::xs => if key=i then 1 else 1+steps key xs

theorem lookup_trace (key : ℕ) (bank : Bank) :
    Trace (transition key) (steps key bank) (.scan bank) (.halt (value key bank)) := by
  induction bank with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    rcases r with ⟨i,ds⟩
    by_cases h : key=i
    · simpa [steps,value_cons,h] using Trace.one
        (show transition key (.scan ((i,ds)::rs))=some (.halt ds) by simp [transition,h])
    · simpa [steps,value_cons,h,Nat.add_comm] using Trace.cons
        (show transition key (.scan ((i,ds)::rs))=some (.scan rs) by simp [transition,h]) ih

theorem steps_le (key : ℕ) (bank : Bank) : steps key bank≤bank.length+1 := by
  induction bank with
  | nil => simp [steps]
  | cons r rs ih =>
    rcases r with ⟨i,ds⟩
    simp only [steps,List.length_cons]
    split <;> omega
end LightEFTSpanners.StoredDrawLookup
