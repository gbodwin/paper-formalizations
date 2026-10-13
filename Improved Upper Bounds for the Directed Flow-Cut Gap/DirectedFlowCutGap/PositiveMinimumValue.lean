import DirectedFlowCutGap.PositiveMinimumCalls

namespace DirectedFlowCutGap.PositiveMinimum
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

def choose (x y : Bits × Fraction) : Bits × Fraction := if (BinaryRational.le x.2 y.2).1 then x else y

def minFrom : Bits × Fraction → List (Bits × Fraction) → Bits × Fraction
  | x,[] => x
  | x,y::ys => minFrom (choose x y) ys

def select : List (Bits × Fraction) → Option (Bits × Fraction)
  | [] => none
  | x::xs => some (minFrom x xs)

def Encoded (heap : NaturalHeap) (x : Bits × Fraction) (y : RetainedArgminProgram.Item) : Prop :=
  y.score=x.2 ∧ BoolList heap y.payload x.1

def Result (heap : NaturalHeap) (root : ℕ) : Option (Bits × Fraction) → Prop
  | none => heap[root]?=some .nil
  | some x => ∃ y,RetainedArgminProgram.StoredItem heap root y ∧ Encoded heap x y

theorem from_related {heap : NaturalHeap} {xs : List (Bits × Fraction)} {ys : List RetainedArgminProgram.Item}
    (rel : List.Forall₂ (Encoded heap) xs ys) (x : Bits × Fraction) (y : RetainedArgminProgram.Item)
    (head : Encoded heap x y) : Encoded heap (minFrom x xs) (RetainedArgminProgram.selectFrom y ys) := by
  induction rel generalizing x y with
  | nil => exact head
  | @cons a b xs ys hab _ ih =>
    simp only [minFrom,RetainedArgminProgram.selectFrom]
    apply ih
    unfold choose RetainedArgminProgram.choose RetainedArgminProgram.keep
    rw [head.1,hab.1]
    split <;> assumption

theorem selected_related {heap : NaturalHeap} {root : ℕ} {xs : List (Bits × Fraction)}
    {ys : List RetainedArgminProgram.Item} (rel : List.Forall₂ (Encoded heap) xs ys)
    (h : RetainedArgminProgram.Selected heap root (RetainedArgminProgram.select ys)) :
    Result heap root (select xs) := by
  cases rel with
  | nil => exact h
  | @cons a b xs ys hab tail =>
    exact ⟨RetainedArgminProgram.selectFrom b ys,h,from_related tail a b hab⟩
end DirectedFlowCutGap.PositiveMinimum
