import DirectedFlowCutGap.PositiveInventoryProgram

namespace DirectedFlowCutGap.PositiveInventory
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor

inductive Inventory (heap : NaturalHeap) : ℕ → List (Bits × Fraction) → Prop
  | nil {root : ℕ} : heap[root]?=some .nil → Inventory heap root []
  | cons {root item tail cost word : ℕ} {u : Bits} {q : Fraction} {xs : List (Bits × Fraction)} :
      heap[root]?=some (.pair item tail) → heap[item]?=some (.pair cost word) →
      RationalComparisonProgram.Stored heap cost q → BoolList heap word u → Inventory heap tail xs →
      Inventory heap root ((u,q)::xs)

theorem inventory_extend {heap : NaturalHeap} {root : ℕ} {xs : List (Bits × Fraction)}
    (h : Inventory heap root xs) (extra : NaturalHeap) : Inventory (heap++extra) root xs := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp extra)
  | cons hp hi hq hu _ ih =>
      exact .cons (lookup_extend hp extra) (lookup_extend hi extra)
        (RationalComparisonProgram.stored_extend hq extra) (boolList_extend hu extra) ih

def selected (xs : List (Bits × Fraction)) : List (Bits × Fraction) :=
  xs.filter fun x => !(BinaryArithmetic.isZero x.2.num).1

def steps : List Fraction → ℕ
  | [] => 3
  | q::qs => BinaryZeroProgram.steps q.num+8+
      (if (BinaryArithmetic.isZero q.num).1 then 6 else 13)+steps qs

def cells : List Fraction → ℕ
  | [] => 1
  | q::qs => 2+(if (BinaryArithmetic.isZero q.num).1 then 0 else 2)+cells qs

/-- Every retained record carries exactly the original rational fields and
original index-word payload. Addresses are the actual allocated record roots. -/
theorem inventory_items {heap : NaturalHeap} {root : ℕ} {xs : List (Bits × Fraction)}
    (h : Inventory heap root xs) :
    ∃ items,RetainedArgminProgram.ItemList heap root items ∧
      List.Forall₂ (fun x y => y.score=x.2 ∧ BoolList heap y.payload x.1) xs items := by
  induction h with
  | nil hp => exact ⟨[],.nil hp,.nil⟩
  | @cons root item tail cost word u q xs hp hi hq hu _ ih =>
    obtain ⟨items,hr,rel⟩ := ih
    exact ⟨⟨q,word,item⟩::items,.cons hp ⟨rfl,cost,hi,hq⟩ hr,.cons ⟨rfl,hu⟩ rel⟩
end DirectedFlowCutGap.PositiveInventory
