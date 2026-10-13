import DirectedFlowCutGap.OriginalRowMinimumTrace

namespace DirectedFlowCutGap.OriginalRowMinimum
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem compute {heap : NaturalHeap} {rows : List Fraction} {a : ℕ}
    (table : WordPairTableRead.Table heap a (IndexedRationalRead.fields rows))
    (next b c d : ℕ) (dense : next=heap.length) (stack : List (Frame ℕ 320)) (source : Bits) :
    ∃ k ext root,k≤ inputSteps rows ∧
      NaturalRun program k (state heap next a b c d stack source 318) []
        (state (heap++ext) (next+ext.length) a b c root stack source 319) ∧
      PositiveMinimum.Result (heap++ext) root (result rows) := by
  obtain ⟨k,ext,root,bound,body,rep⟩ := minimum_return table next b c d dense
    ⟨a,b,c,d⟩ 319 stack source
  have first : tickNatural program (state heap next a b c d stack source 318)=
      some ⟨state heap next a b c d (⟨319,.r3,⟨a,b,c,d⟩⟩::stack) source 300,[],0⟩ := by rfl
  exact ⟨k+1,ext,root,bound,by simpa [Nat.add_comm] using NaturalRun.step first body,rep⟩

theorem result_original {n : ℕ} (costs : BinaryFractionalRows.Row n) :
    result costs.toList=(BinaryFractionalDispatch.minimumPositive costs).1.map
      (fun i => (RowVertices.vertexLabel i,BinaryFractionalRows.get costs i)) := by
  unfold result
  simp only [Vector.length_toList]
  rw [← RowVertices.labels_exact n]
  exact PositiveMinimum.original_value costs RowVertices.vertexLabel
end DirectedFlowCutGap.OriginalRowMinimum
