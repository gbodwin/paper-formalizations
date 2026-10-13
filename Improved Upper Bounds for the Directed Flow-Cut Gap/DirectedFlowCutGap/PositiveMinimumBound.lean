import DirectedFlowCutGap.PositiveMinimumRefinement

namespace DirectedFlowCutGap.PositiveMinimum
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def inputSteps (rows : List Fraction) (W : ℕ) : ℕ :=
  4*SourceRowTableProgram.bits (IndexedRationalRead.fields rows)+(6400*(W+1)^2+36)*rows.length+16

theorem related_extend {heap : NaturalHeap} {xs : List (Bits × Fraction)} {ys : List RetainedArgminProgram.Item}
    (h : List.Forall₂ (Encoded heap) xs ys) (ext : NaturalHeap) :
    List.Forall₂ (Encoded (heap++ext)) xs ys := by
  induction h with
  | nil => exact .nil
  | cons head _ ih => exact .cons ⟨head.1,boolList_extend head.2 ext⟩ ih

theorem items_fit {heap : NaturalHeap} {xs : List (Bits × Fraction)} {ys : List RetainedArgminProgram.Item}
    (h : List.Forall₂ (Encoded heap) xs ys) {W : ℕ}
    (size : ∀ x∈xs,x.2.num.length≤W ∧ x.2.den.length≤W) :
    ∀ y∈ys,RetainedArgminProgram.Fits W y := by
  induction h with
  | nil => simp
  | @cons x y xs ys head _ ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · unfold RetainedArgminProgram.Fits
      rw [head.1]
      exact size x (by simp)
    · exact ih (by intro a ha;exact size a (by simp [ha])) z hz

theorem total_bound {heap : NaturalHeap} (rows : List Fraction) (words : List Bits)
    (items : List RetainedArgminProgram.Item) (W : ℕ)
    (rel : List.Forall₂ (Encoded heap) (PositiveInventory.selected (words.zip rows)) items)
    (size : ∀ q∈rows,q.num.length≤W ∧ q.den.length≤W) :
    PositiveInventory.steps rows+RetainedArgminProgram.steps items+8≤ inputSteps rows W := by
  have fit : ∀ y∈items,RetainedArgminProgram.Fits W y := items_fit rel (by
    intro x hx
    exact size x.2 (List.of_mem_zip (List.mem_of_mem_filter hx)).2)
  have cmp := RetainedArgminProgram.steps_bound items fit
  have inv := PositiveInventory.steps_bound rows
  have filtered := List.length_filter_le (fun x : Bits × Fraction => !(BinaryArithmetic.isZero x.2.num).1) (words.zip rows)
  have same := rel.length_eq
  have len : items.length≤rows.length := by
    simp only [PositiveInventory.selected,List.length_zip] at filtered same
    omega
  have mul := Nat.mul_le_mul_left (6400*(W+1)^2+12) len
  unfold inputSteps
  nlinarith
end DirectedFlowCutGap.PositiveMinimum
