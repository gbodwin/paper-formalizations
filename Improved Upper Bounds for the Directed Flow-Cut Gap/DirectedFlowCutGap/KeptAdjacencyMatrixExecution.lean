import DirectedFlowCutGap.KeptAdjacencyMatrixTrace

namespace DirectedFlowCutGap.KeptAdjacencyMatrix
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

def rowCells (rows : List Bits) : ℕ := (rows.map List.length).sum
def inputSteps (rows : List Bits) : ℕ := 24*rowCells rows+28*rows.length+4

theorem steps_bound (kept : Bits) (rows : List Bits) (remaining : Bits) :
    steps kept rows remaining+1 ≤ inputSteps rows := by
  induction rows generalizing remaining with
  | nil => cases remaining <;> simp [steps,inputSteps,rowCells]
  | cons u us ih =>
    cases remaining with
    | nil => simp [steps,inputSteps,rowCells]
    | cons z zs =>
      have h := ih zs
      have hr := KeptAdjacencyRow.steps_bound z u kept
      simp only [steps,inputSteps,rowCells,List.map_cons,List.sum_cons,List.length_cons,
        Nat.mul_add,Nat.mul_one] at *
      omega

theorem scan {heap : NaturalHeap} {a b : ℕ} {kept : Bits} {rows : List Bits} {remaining : Bits}
    (ha : Matrix heap a rows) (hc : Context heap b remaining kept)
    (aligned : rows.length=remaining.length) (widths : ∀ u∈rows,u.length=kept.length)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 84)) (source : Bits) :
    ∃ ext root,ext.length=cells kept rows remaining ∧ NaturalRun program (steps kept rows remaining+1)
      (state heap next a b c d stack source 82) []
      (state (heap++ext) (next+ext.length) a b c root stack source 83) ∧
      Matrix (heap++ext) root (matrix kept rows remaining) := by
  obtain ⟨ext,root,len,run,rep⟩ := matrix_return ha hc aligned widths next c d hn ⟨a,b,c,d⟩ 83 stack source
  have call : tickNatural program (state heap next a b c d stack source 82)=
      some ⟨state heap next a b c d (⟨83,.r3,⟨a,b,c,d⟩⟩::stack) source 40,[],0⟩ := by rfl
  exact ⟨ext,root,len,by simpa [Nat.add_comm] using NaturalRun.step call run,rep⟩

theorem matrix_zip (kept : Bits) (rows : List Bits) (remaining : Bits) :
    matrix kept rows remaining=List.zipWith (fun row k => List.zipWith (fun a v => a && k && v) row kept) rows remaining := by
  induction rows generalizing remaining with
  | nil => cases remaining <;> rfl
  | cons u us ih => cases remaining <;> simp [matrix,ih,KeptAdjacencyRow.row_zip]
end DirectedFlowCutGap.KeptAdjacencyMatrix
