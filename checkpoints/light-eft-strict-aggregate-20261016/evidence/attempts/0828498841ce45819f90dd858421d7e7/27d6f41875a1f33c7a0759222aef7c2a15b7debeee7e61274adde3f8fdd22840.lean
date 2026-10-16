import LightEFTSpanners.StoredCandidatePreparationEncoding

namespace LightEFTSpanners.StoredVertexPairs
open Controller

def pairs (xs ys : List ℕ) : List StoredEdges.Edge := xs.flatMap fun x => ys.map fun y => (x,y)
inductive State where
  | rows : List ℕ → List ℕ → List StoredEdges.Edge → State
  | cells : ℕ → List ℕ → List ℕ → List ℕ → List StoredEdges.Edge → State
  | reverse : List StoredEdges.Edge → List StoredEdges.Edge → State
  | halt : List StoredEdges.Edge → State
  deriving DecidableEq, Repr

def transition : State → Option State
  | .rows [] _ acc => some (.reverse acc [])
  | .rows (x::xs) ys acc => some (.cells x ys xs ys acc)
  | .cells _ [] xs ys acc => some (.rows xs ys acc)
  | .cells x (y::ys) xs original acc => some (.cells x ys xs original ((x,y)::acc))
  | .reverse [] out => some (.halt out)
  | .reverse (e::es) out => some (.reverse es (e::out))
  | .halt _ => none

theorem cells_trace (x : ℕ) (ys xs original : List ℕ) (acc : List StoredEdges.Edge) :
    Trace transition (ys.length+1) (.cells x ys xs original acc)
      (.rows xs original ((ys.map fun y => (x,y)).reverse++acc)) := by
  induction ys generalizing acc with
  | nil => exact Trace.one rfl
  | cons y ys ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition (.cells x (y::ys) xs original acc)=
        some (.cells x ys xs original ((x,y)::acc)) from rfl) (ih ((x,y)::acc))

theorem rows_trace (xs ys : List ℕ) (acc : List StoredEdges.Edge) :
    Trace transition (xs.length*(ys.length+2)+1) (.rows xs ys acc)
      (.reverse ((pairs xs ys).reverse++acc) []) := by
  induction xs generalizing acc with
  | nil => simpa [pairs] using (Trace.one (show transition (.rows [] ys acc)=some (.reverse acc []) from rfl))
  | cons x xs ih =>
    have a := Trace.one (show transition (.rows (x::xs) ys acc)=some (.cells x ys xs ys acc) from rfl)
    have b := cells_trace x ys xs ys acc
    have c := ih ((ys.map fun y => (x,y)).reverse++acc)
    convert a.trans (b.trans c) using 1 <;>
      simp [pairs,List.reverse_append,List.append_assoc,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    omega

theorem reverse_trace (es out : List StoredEdges.Edge) :
    Trace transition (es.length+1) (.reverse es out) (.halt (es.reverse++out)) := by
  induction es generalizing out with
  | nil => exact Trace.one rfl
  | cons e es ih =>
    simpa [List.reverse_cons,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      Trace.cons (show transition (.reverse (e::es) out)=some (.reverse es (e::out)) from rfl) (ih (e::out))

@[simp] theorem pairs_length (xs ys : List ℕ) : (pairs xs ys).length=xs.length*ys.length := by
  induction xs with
  | nil => simp [pairs]
  | cons x xs ih => simp [pairs,List.length_flatMap,Nat.add_mul,Nat.add_comm] at *

def steps (xs ys : List ℕ) : ℕ := xs.length*(ys.length+2)+xs.length*ys.length+2

theorem pairs_trace (xs ys : List ℕ) :
    Trace transition (steps xs ys) (.rows xs ys []) (.halt (pairs xs ys)) := by
  have a := rows_trace xs ys []
  simp only [List.append_nil] at a
  have b := reverse_trace (pairs xs ys).reverse []
  convert a.trans b using 1 <;> simp [steps]
  omega
end LightEFTSpanners.StoredVertexPairs
