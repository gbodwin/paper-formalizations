import LightEFTSpanners.ControllerTrace
import LightEFTSpanners.StoredEdgeMembership

namespace LightEFTSpanners.StoredFlagSample
open Controller
abbrev Input := List (StoredEdges.Edge × Bool)
inductive State where
  | scan : Input → List StoredEdges.Edge → State
  | reverse : List StoredEdges.Edge → List StoredEdges.Edge → State
  | halt : List StoredEdges.Edge → State
  deriving DecidableEq, Repr

def transition : State → Option State
  | .scan [] acc => some (.reverse acc [])
  | .scan ((e,b)::xs) acc => some (.scan xs (if b then e::acc else acc))
  | .reverse [] acc => some (.halt acc)
  | .reverse (x::xs) acc => some (.reverse xs (x::acc))
  | .halt _ => none

def value : Input → List StoredEdges.Edge :=
  List.rec (motive := fun _ => List StoredEdges.Edge) []
    (fun x _ rest => if x.2 then x.1::rest else rest)

theorem value_nil : value [] = [] := rfl

theorem value_cons (e : StoredEdges.Edge) (b : Bool) (xs : Input) :
    value ((e,b)::xs) = if b then e::value xs else value xs := rfl

theorem scan_trace (xs : Input) (acc : List StoredEdges.Edge) :
    Trace transition (xs.length+1) (.scan xs acc) (.reverse ((value xs).reverse++acc) []) := by
  induction xs generalizing acc with
  | nil => exact Trace.one rfl
  | cons x xs ih =>
    rcases x with ⟨e,b⟩
    cases b with
    | false =>
      simpa [value,Nat.add_assoc] using
        Trace.cons (show transition (.scan ((e,false)::xs) acc)=some (.scan xs acc) from rfl) (ih acc)
    | true =>
      simpa [value,Nat.add_assoc] using
        Trace.cons (show transition (.scan ((e,true)::xs) acc)=some (.scan xs (e::acc)) from rfl) (ih (e::acc))

theorem reverse_trace (xs acc : List StoredEdges.Edge) :
    Trace transition (xs.length+1) (.reverse xs acc) (.halt (xs.reverse++acc)) := by
  induction xs generalizing acc with
  | nil => exact Trace.one rfl
  | cons x xs ih =>
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
      Trace.cons (show transition (.reverse (x::xs) acc)=some (.reverse xs (x::acc)) from rfl) (ih (x::acc))

theorem value_length (xs : Input) : (value xs).length≤xs.length := by
  induction xs with
  | nil => simp [value]
  | cons x xs ih => rcases x with ⟨e,b⟩;cases b <;> simp [value] <;> omega
end LightEFTSpanners.StoredFlagSample
