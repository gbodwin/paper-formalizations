import DirectedFlowCutGap.ActualPositiveMinimum

namespace DirectedFlowCutGap.PositiveMinimum
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal

/-- The exact original minimum-positive index word and rational fields are
returned by the same physical run that constructs and selects its inventory. -/
theorem minimum_original_bit {n H A : ℕ} (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits)
    (W : ℕ) (size : ∀ q∈costs.toList,q.num.length≤W ∧ q.den.length≤W)
    (initial : BitState 256) (bounded : initial.Bounded H A) (pc0 : initial.pc=254)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (verts : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a
      ((List.finRange n).map label))
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.b
      (IndexedRationalRead.fields costs.toList)) :
    ∃ k charge out,k≤ inputSteps costs.toList W ∧ Run program k charge initial [] out ∧
      Result (eraseState out).heap (eraseState out).registers.d
        ((BinaryFractionalDispatch.minimumPositive costs).1.map
          (fun i => (label i,BinaryFractionalRows.get costs i))) ∧
      GraphDiscoveryProgram.Vertices (eraseState out).heap (eraseState initial).registers.a
        ((List.finRange n).map label) ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.b
        (IndexedRationalRead.fields costs.toList) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=255 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 256 H A (inputSteps costs.toList W) := by
  obtain ⟨k,charge,out,hk,run,rep,vs,cs,src,stack,pc,ext,halt,bound⟩ :=
    minimum_bit (by simp) W size initial bounded pc0 dense empty verts table
  rw [original_value] at rep
  exact ⟨k,charge,out,hk,run,rep,vs,cs,src,stack,pc,ext,halt,bound⟩

theorem original_size (rows : List BinaryRational.Fraction) :
    ∀ q∈rows,q.num.length≤SourceRowTableProgram.bits (IndexedRationalRead.fields rows) ∧
      q.den.length≤SourceRowTableProgram.bits (IndexedRationalRead.fields rows) := by
  induction rows with
  | nil => simp
  | cons x xs ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · simp only [IndexedRationalRead.fields,List.map_cons,SourceRowTableProgram.bits]
      constructor <;> omega
    · obtain ⟨hn,hd⟩ := ih q hq
      simp only [IndexedRationalRead.fields] at hn hd
      simp only [IndexedRationalRead.fields,List.map_cons,SourceRowTableProgram.bits]
      constructor <;> omega

theorem minimum_original_input_bit {n H A : ℕ} (costs : BinaryFractionalRows.Row n) (label : Fin n → Bits)
    (initial : BitState 256) (bounded : initial.Bounded H A) (pc0 : initial.pc=254)
    (dense : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (verts : GraphDiscoveryProgram.Vertices (eraseState initial).heap (eraseState initial).registers.a
      ((List.finRange n).map label))
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.b
      (IndexedRationalRead.fields costs.toList)) :
    ∃ k charge out,k≤ inputSteps costs.toList (SourceRowTableProgram.bits (IndexedRationalRead.fields costs.toList)) ∧ Run program k charge initial [] out ∧
      Result (eraseState out).heap (eraseState out).registers.d
        ((BinaryFractionalDispatch.minimumPositive costs).1.map
          (fun i => (label i,BinaryFractionalRows.get costs i))) ∧
      GraphDiscoveryProgram.Vertices (eraseState out).heap (eraseState initial).registers.a
        ((List.finRange n).map label) ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState initial).registers.b
        (IndexedRationalRead.fields costs.toList) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=255 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 256 H A (inputSteps costs.toList (SourceRowTableProgram.bits (IndexedRationalRead.fields costs.toList))) := by
  exact minimum_original_bit costs label
    (SourceRowTableProgram.bits (IndexedRationalRead.fields costs.toList))
    (original_size costs.toList) initial bounded pc0 dense empty verts table
end DirectedFlowCutGap.PositiveMinimum
