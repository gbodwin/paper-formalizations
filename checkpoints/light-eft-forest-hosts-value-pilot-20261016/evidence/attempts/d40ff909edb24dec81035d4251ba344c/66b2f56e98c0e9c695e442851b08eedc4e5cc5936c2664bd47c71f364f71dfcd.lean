import LightEFTSpanners.StoredWeightMergeEncoding

namespace LightEFTSpanners.StoredSortSplit
open Controller
inductive State where
  | count : List StoredEdges.Edge → ℕ → State
  | split : ℕ → List StoredEdges.Edge → List StoredEdges.Edge → State
  | reverse : List StoredEdges.Edge → List StoredEdges.Edge → List StoredEdges.Edge → State
  | halt : List StoredEdges.Edge → List StoredEdges.Edge → State
  deriving DecidableEq, Repr

def transition (original : List StoredEdges.Edge) : State → Option State
  | .count [] n => some (.split ((n+1)/2) original [])
  | .count (_::xs) n => some (.count xs (n+1))
  | .split 0 xs acc => some (.reverse acc xs [])
  | .split (_+1) [] acc => some (.reverse acc [] [])
  | .split (k+1) (x::xs) acc => some (.split k xs (x::acc))
  | .reverse [] right left => some (.halt left right)
  | .reverse (x::xs) right left => some (.reverse xs right (x::left))
  | .halt _ _ => none

theorem count_trace (original xs : List StoredEdges.Edge) (n : ℕ) :
    Trace (transition original) (xs.length+1) (.count xs n)
      (.split ((n+xs.length+1)/2) original []) := by
  induction xs generalizing n with
  | nil => exact Trace.one rfl
  | cons x xs ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition original (.count (x::xs) n)=some (.count xs (n+1)) from rfl) (ih (n+1))

theorem split_trace (original xs acc : List StoredEdges.Edge) (k : ℕ) :
    Trace (transition original) (min k xs.length+1) (.split k xs acc)
      (.reverse ((xs.take k).reverse++acc) (xs.drop k) []) := by
  induction k generalizing xs acc with
  | zero => exact Trace.one rfl
  | succ k ih =>
    cases xs with
    | nil => simpa using Trace.one (show transition original (.split (k+1) [] acc)=some (.reverse acc [] []) from rfl)
    | cons x xs =>
      simpa [List.take_succ_cons,List.drop_succ_cons,List.reverse_cons,List.append_assoc,
        Nat.add_comm,Nat.add_left_comm] using
        Trace.cons (show transition original (.split (k+1) (x::xs) acc)=some (.split k xs (x::acc)) from rfl) (ih xs (x::acc))

theorem reverse_trace (original xs right left : List StoredEdges.Edge) :
    Trace (transition original) (xs.length+1) (.reverse xs right left) (.halt (xs.reverse++left) right) := by
  induction xs generalizing left with
  | nil => exact Trace.one rfl
  | cons x xs ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition original (.reverse (x::xs) right left)=some (.reverse xs right (x::left)) from rfl) (ih (x::left))
end LightEFTSpanners.StoredSortSplit
