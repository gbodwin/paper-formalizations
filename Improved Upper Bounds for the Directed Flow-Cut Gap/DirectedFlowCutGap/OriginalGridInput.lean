import DirectedFlowCutGap.ActualGridInput

namespace DirectedFlowCutGap.GridInputProgram
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation
open BooleanTableRead PackedBooleanConstructor

theorem prepared_extend {heap : NaturalHeap} {root : ℕ} {rows : List Fraction}
    (h : Prepared heap root rows) (ext : NaturalHeap) : Prepared (heap++ext) root rows := by
  obtain ⟨pair,dim,wid,fuel,hp,hq,hd,hw,hf⟩ := h
  exact ⟨pair,dim,wid,fuel,lookup_extend hp ext,lookup_extend hq ext,
    boolList_extend hd ext,boolList_extend hw ext,boolList_extend hf ext⟩

theorem dimension_exact {n : ℕ} (c : Row n) : dimension c.toList=(BinaryFractionalCore.dimension c).1 := by
  have h := PackingParameters.dimension_lengthBits (c.toList.map fun _ => false)
  simpa only [dimension,PackingParameters.dimensionWord,List.length_map,BinaryFractionalCore.dimension] using h

theorem original_fields {n : ℕ} (c : Row n) {heap : NaturalHeap} {root : ℕ}
    (h : Prepared heap root c.toList) :
    ∃ pair dim wid fuel,heap[root]?=some (.pair pair fuel) ∧ heap[pair]?=some (.pair dim wid) ∧
      BoolList heap dim (BinaryFractionalCore.dimension c).1 ∧
      BoolList heap wid (BinaryFractionalGuesses.inputWidth c).1 ∧
      BoolList heap fuel (BinaryFractionalGuesses.gridFuel (BinaryFractionalCore.dimension c).1
        (BinaryFractionalGuesses.inputWidth c).1).1 := by
  simpa only [Prepared,dimension_exact,width,BinaryFractionalGuesses.inputWidth] using h
end DirectedFlowCutGap.GridInputProgram
