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

def contains (v : ℕ) : List ℕ → Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x _ rest => if v=x then true else rest)

theorem contains_nil (v : ℕ) : contains v [] = false := rfl

theorem contains_cons (v x : ℕ) (xs : List ℕ) :
    contains v (x::xs) = (if v=x then true else contains v xs) := rfl

def steps (v : ℕ) : List ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ) 1
    (fun x _ rest => if v=x then 1 else rest+1)

theorem steps_nil (v : ℕ) : steps v [] = 1 := rfl

theorem steps_cons (v x : ℕ) (xs : List ℕ) :
    steps v (x::xs) = (if v=x then 1 else steps v xs+1) := rfl

theorem scan_trace (v : ℕ) (xs : List ℕ) :
    Trace transition (steps v xs) (.scan v xs) (.halt (contains v xs)) := by
  induction xs with
  | nil => exact Trace.one rfl
  | cons x xs ih =>
    by_cases h : v=x
    · simpa [steps_cons,contains_cons,h] using Trace.one (show transition (.scan v (x::xs))=some (.halt true) by simp [transition,h])
    · simpa [steps_cons,contains_cons,h] using Trace.cons (show transition (.scan v (x::xs))=some (.scan v xs) by simp [transition,h]) ih

theorem steps_le (v : ℕ) (xs : List ℕ) : steps v xs≤xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [steps_cons,List.length_cons];split <;> omega

theorem contains_iff (v : ℕ) (xs : List ℕ) : contains v xs=true ↔ v∈xs := by
  induction xs with
  | nil => simp [contains_nil]
  | cons x xs ih => by_cases h : v=x <;> simp [contains_cons,h,ih]
end LightEFTSpanners.StoredVertexMembership
