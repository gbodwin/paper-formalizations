import DirectedFlowCutGap.MaterializedPathSum
import DirectedFlowCutGap.CanonicalPathCost
import DirectedFlowCutGap.BinaryFractionalGraphOracle

/-! Actual outgoing graph-cost traversal and accumulation. The heap supplies
edge-tail index words, a row table and the source word; no cost list or cost
result is a premise. Path discovery and the edge-list representation remain
separate from this literal cost computation. -/
namespace DirectedFlowCutGap.MaterializedGraphPath
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal
open RationalComparisonProgram BinaryFractionalRows

/-- Padding is allowed in every index. The relation only describes the stored
edge-tail words, not the costs that the program will read or construct. -/
def Encodes {n : ℕ} (words : List Bits) (es : List (BinaryFractionalWalkOracle.Pair n)) : Prop :=
  List.Forall₂ (fun w e => value w=e.1.val) words es

theorem lookup_get {n : ℕ} (y : Row n) (i : Fin n) (word : Bits) (hw : value word=i.val) :
    IndexedRationalRead.lookup y.toList word=get y i := by
  simp [IndexedRationalRead.lookup,hw,BinaryFractionalRows.get]

theorem outgoing_eq {n : ℕ} (y : Row n) (s : Fin n) (e : BinaryFractionalWalkOracle.Pair n)
    (sw word : Bits) (hs : value sw=s.val) (hw : value word=e.1.val) :
    OutgoingCostProgram.result y.toList sw word=(BinaryFractionalGraphOracle.outgoing y s e).1 := by
  by_cases he : e.1=s
  · have same : OutgoingCostProgram.same word sw=true :=
      (OutgoingCostProgram.same_spec word sw).2 (by simpa [hs,hw] using congrArg Fin.val he)
    simp [OutgoingCostProgram.result,same,BinaryFractionalGraphOracle.outgoing,he]
  · have same : OutgoingCostProgram.same word sw=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      have hv := (OutgoingCostProgram.same_spec word sw).1 h
      exact he (Fin.ext (by simpa [hs,hw] using hv))
    simp [OutgoingCostProgram.result,same,BinaryFractionalGraphOracle.outgoing,he,lookup_get y e.1 word hw]

theorem costs_eq {n : ℕ} (y : Row n) (s : Fin n) (sw : Bits) (hs : value sw=s.val)
    {words : List Bits} {es : List (BinaryFractionalWalkOracle.Pair n)} (encoding : Encodes words es) :
    PathCostMaterialization.costs y.toList sw words=
      (BinaryFractionalWalkOracle.costList (BinaryFractionalGraphOracle.outgoing y s) es).1 := by
  induction encoding with
  | nil => rfl
  | @cons w e ws es hw _ ih =>
    simp [PathCostMaterialization.costs,BinaryFractionalWalkOracle.costList,outgoing_eq y s e sw w hs hw] at *
    exact ih

theorem result_eq {n : ℕ} (y : Row n) (s : Fin n) (sw : Bits) (hs : value sw=s.val)
    {words : List Bits} {es : List (BinaryFractionalWalkOracle.Pair n)} (encoding : Encodes words es) :
    MaterializedPathSum.result y.toList sw words=
      (CanonicalPathCost.candidate (BinaryFractionalGraphOracle.outgoing y s) es).cost := by
  rw [CanonicalPathCost.candidate_cost]
  exact congrArg (fun xs => (BinaryFractionalRows.sum xs).1) (costs_eq y s sw hs encoding)

theorem indices_valid {n : ℕ} {words : List Bits} {es : List (BinaryFractionalWalkOracle.Pair n)}
    (encoding : Encodes words es) : ∀ w∈words,value w<n := by
  induction encoding with
  | nil => simp
  | @cons w e ws es hw _ ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl|hv
    · simp [hw]
    · exact ih v hv

/-- The returned record is the literal old graph-extension cost, including its
source-zero convention. The cost list was constructed by this same run. -/
theorem path_cost_bit {n H A : ℕ} (y : Row n) (s : Fin n)
    (es : List (BinaryFractionalWalkOracle.Pair n)) (words : List Bits) (sw : Bits)
    (encoding : Encodes words es) (hs : value sw=s.val) (initial : BitState 284)
    (bounded : initial.Bounded H A) (pc0 : initial.pc=282)
    (hn : value initial.next=initial.heap.length) (empty : initial.stack=[])
    (input : PathCostMaterialization.WordList (eraseState initial).heap (eraseState initial).registers.a words)
    (context : OutgoingCostProgram.Context (eraseState initial).heap (eraseState initial).registers.b y.toList sw)
    (B : ℕ) (hB : 1 ≤ B) (rowWidths : ∀ x∈y.toList,StoredBounded x B)
    (wordWidths : ∀ w∈words,w.length ≤ B) :
    ∃ charge out,Run MaterializedPathSum.program (MaterializedPathSum.steps y.toList sw words+1) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d
        (CanonicalPathCost.candidate (BinaryFractionalGraphOracle.outgoing y s) es).cost ∧
      PathCostMaterialization.WordList (eraseState out).heap (eraseState initial).registers.a words ∧
      OutgoingCostProgram.Context (eraseState out).heap (eraseState initial).registers.b y.toList sw ∧
      (∃ costRoot,CanonicalRationalSum.StoredList (eraseState out).heap costRoot
        (BinaryFractionalWalkOracle.costList (BinaryFractionalGraphOracle.outgoing y s) es).1) ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=283 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=MaterializedPathSum.cells y.toList sw words) ∧
      (attempt MaterializedPathSum.program out).result=none ∧
      charge+(attempt MaterializedPathSum.program out).operations ≤
        completeBound 284 H A (MaterializedPathSum.instructionBound words.length B n sw.length) := by
  have valid := indices_valid encoding
  have result := MaterializedPathSum.sum_bit initial bounded pc0 hn empty input context
    (by simpa using valid) B n hB rowWidths wordWidths (fun w hw => (valid w hw).le)
  simpa only [result_eq y s sw hs encoding,costs_eq y s sw hs encoding] using result

end DirectedFlowCutGap.MaterializedGraphPath
