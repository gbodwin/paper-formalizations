import LightEFTSpanners.StoredCanonicalIndices

namespace LightEFTSpanners.StoredVertexMembership
open Controller
inductive State where
  | scan : ℕ → List ℕ → State
  | halt : Bool → State
  deriving DecidableEq, Repr

def transition : State → Option State
  | .scan _ [] => some (.halt false)
  | .scan v (x::xs) => if v=x then some (.halt true) else some (.scan v xs)
  | .halt _ => none

def contains (v : ℕ) : List ℕ → Bool
  | [] => false
  | x::xs => if v=x then true else contains v xs

def steps (v : ℕ) : List ℕ → ℕ
  | [] => 1
  | x::xs => if v=x then 1 else steps v xs+1

theorem scan_trace (v : ℕ) (xs : List ℕ) :
    Trace transition (steps v xs) (.scan v xs) (.halt (contains v xs)) := by
  induction xs with
  | nil => exact Trace.one rfl
  | cons x xs ih =>
    by_cases h : v=x
    · simpa [steps,contains,h] using Trace.one (show transition (.scan v (x::xs))=some (.halt true) by simp [transition,h])
    · simpa [steps,contains,h] using Trace.cons (show transition (.scan v (x::xs))=some (.scan v xs) by simp [transition,h]) ih

theorem steps_le (v : ℕ) (xs : List ℕ) : steps v xs≤xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [steps,List.length_cons];split <;> omega

theorem contains_iff (v : ℕ) (xs : List ℕ) : contains v xs=true ↔ v∈xs := by
  induction xs with
  | nil => simp [contains]
  | cons x xs ih => by_cases h : v=x <;> simp [contains,h,ih]
end LightEFTSpanners.StoredVertexMembership
