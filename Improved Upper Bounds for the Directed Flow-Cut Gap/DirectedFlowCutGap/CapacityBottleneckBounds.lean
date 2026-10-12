import DirectedFlowCutGap.CapacityBottleneckRefinement

namespace DirectedFlowCutGap.CapacityBottleneck
open BinaryArithmetic BinaryRational BinaryFractionalRows

theorem steps_le (xs : List Slot) : steps xs ≤ 24*xs.length+3 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [steps,List.length_cons]
    split <;> omega

theorem items_length (xs : List Slot) (next : ℕ) : (items next xs).length ≤ xs.length := by
  induction xs generalizing next with
  | nil => rfl
  | cons x xs ih =>
    have h := ih (next+2)
    simp only [items,List.length_cons]
    split
    · simp only [List.length_cons];omega
    · omega

theorem items_fits (xs : List Slot) (next W : ℕ)
    (hw : ∀ x∈xs,x.score.num.length≤W ∧ x.score.den.length≤W) :
    ∀ z∈items next xs,RetainedArgminProgram.Fits W z := by
  induction xs generalizing next with
  | nil => simp [items]
  | cons x xs ih =>
    have hx := hw x (by simp)
    have ht := ih (next+2) (fun y h => hw y (by simp [h]))
    simp only [items]
    split
    · intro z hz
      rcases List.mem_cons.mp hz with rfl|hz
      · exact hx
      · exact ht z hz
    · exact ht

def instructionBound (n W : ℕ) : ℕ := (6400*(W+1)^2+36)*n+10

theorem selected_steps_le (xs : List Slot) (next W : ℕ)
    (hw : ∀ x∈xs,x.score.num.length≤W ∧ x.score.den.length≤W) :
    selectedSteps next xs ≤ instructionBound xs.length W := by
  have hc := steps_le xs
  have hs := RetainedArgminProgram.steps_bound (items next xs) (items_fits xs next W hw)
  have hl := Nat.mul_le_mul_left (6400*(W+1)^2+12) (items_length xs next)
  unfold selectedSteps instructionBound
  nlinarith

theorem encoded_widths {n W : ℕ} {label : Fin n → Bits} {capacity : Row n} {mask : Vector Bool n}
    {xs : List Slot} {is : List (Fin n)} (encoded : List.Forall₂ (EncodesSlot label capacity mask) xs is)
    (hw : ∀ i,(get capacity i).num.length≤W ∧ (get capacity i).den.length≤W) :
    ∀ x∈xs,x.score.num.length≤W ∧ x.score.den.length≤W := by
  induction encoded with
  | nil => simp
  | @cons x i xs is hx _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl|hy
    · simpa [hx.2.1] using hw i
    · exact ih y hy

end DirectedFlowCutGap.CapacityBottleneck
