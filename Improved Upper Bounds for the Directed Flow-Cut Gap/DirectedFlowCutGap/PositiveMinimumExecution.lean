import DirectedFlowCutGap.PositiveMinimumTrace

namespace DirectedFlowCutGap.PositiveMinimum
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem minimum (rows : List Fraction) (words : List Bits) (aligned : words.length=rows.length)
    {heap : NaturalHeap} {a b : ℕ} (verts : GraphDiscoveryProgram.Vertices heap a words)
    (table : WordPairTableRead.Table heap b (IndexedRationalRead.fields rows))
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 256)) (source : Bits) (W : ℕ)
    (size : ∀ q∈rows,q.num.length≤W ∧ q.den.length≤W) :
    ∃ k ext root,k≤ inputSteps rows W ∧
      NaturalRun program k (state heap next a b c d stack source 254) []
        (state (heap++ext) (next+ext.length) a b c root stack source 255) ∧
      Result (heap++ext) root (select (PositiveInventory.selected (words.zip rows))) := by
  obtain ⟨k,ext,root,bound,run,result⟩ := minimum_return rows words aligned verts table next c d hn
    ⟨a,b,c,d⟩ 255 stack source W size
  have call : tickNatural program (state heap next a b c d stack source 254)=
      some ⟨state heap next a b c d (⟨255,.r3,⟨a,b,c,d⟩⟩::stack) source 248,[],0⟩ := by rfl
  exact ⟨k+1,ext,root,bound,by simpa [Nat.add_comm] using NaturalRun.step call run,result⟩
end DirectedFlowCutGap.PositiveMinimum
