import LightEFTSpanners.ControllerTrace
import LightEFTSpanners.ExecutableVoting

/-! Literal stored sample records. Each input cell contains its weight and
four membership bits. Graph-to-record encoding is a representation contract;
the controller itself will inspect only these records and natural indices. -/
namespace LightEFTSpanners.SampleRecords
open LinkedDistance
structure Entry where
  weight : ℚ
  seed : Bool
  selected : Bool
  host : Bool
  drawn : Bool
  deriving DecidableEq, Repr
abbrev Records := List (List Entry)
 def value (i j : ℕ) (a : Entry) : Cell :=
  if i=j then none else if a.host || (a.drawn && a.selected && !a.seed)
    then some a.weight else none
 def rowValues (i : ℕ) : ℕ → List Entry → List Cell
  | _,[] => []
  | j,a::as => value i j a :: rowValues i (j+1) as
 def values : ℕ → Records → Matrix
  | _,[] => []
  | i,r::rs => rowValues i 0 r :: values (i+1) rs
 @[simp] theorem rowValues_length (i j : ℕ) (r : List Entry) :
    (rowValues i j r).length=r.length := by
  induction r generalizing j with
  | nil => rfl
  | cons a as ih => simp [rowValues,ih]
 @[simp] theorem values_length (i : ℕ) (R : Records) : (values i R).length=R.length := by
  induction R generalizing i with
  | nil => rfl
  | cons r rs ih => simp [values,ih]
 def encode {n : ℕ} (Q E T S : Finset (Sym2 (Fin n))) (w : Sym2 (Fin n) → ℚ) : Records :=
  List.ofFn fun u : Fin n => List.ofFn fun v : Fin n =>
    ⟨w s(u,v),decide (s(u,v)∈Q),decide (s(u,v)∈E),decide (s(u,v)∈T),decide (s(u,v)∈S)⟩
end LightEFTSpanners.SampleRecords
