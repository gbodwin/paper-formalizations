import DirectedFlowCutGap.CanonicalRationalSum
import DirectedFlowCutGap.BinaryFractionalWalkOracle

/-! Source-shaped path-cost refinement. The supplied list contains the exact
edge-cost records obtained by the existing graph oracle's costList operation.
The machine constructs their canonical accumulated cost. Graph traversal,
materializing this record list and path metadata construction remain separate. -/
namespace DirectedFlowCutGap.CanonicalPathCost
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal
open RationalComparisonProgram CanonicalRationalSum

/-- The existing graph candidate extension, iterated in literal path order. -/
def candidate {n : ℕ} (cost : BinaryFractionalWalkOracle.Cost n) :
    List (BinaryFractionalWalkOracle.Pair n) → BinaryFractionalWalkOracle.Candidate n
  | [] => BinaryFractionalWalkOracle.zero
  | (u,v)::es => (BinaryFractionalWalkOracle.extend cost u v (candidate cost es)).1

theorem candidate_edges {n : ℕ} (cost : BinaryFractionalWalkOracle.Cost n)
    (es : List (BinaryFractionalWalkOracle.Pair n)) : (candidate cost es).edges=es := by
  induction es with
  | nil => rfl
  | cons e es ih => rcases e with ⟨u,v⟩;simpa [candidate,BinaryFractionalWalkOracle.extend] using ih

theorem candidate_cost {n : ℕ} (cost : BinaryFractionalWalkOracle.Cost n)
    (es : List (BinaryFractionalWalkOracle.Pair n)) :
    (candidate cost es).cost=(BinaryFractionalRows.sum (BinaryFractionalWalkOracle.costList cost es).1).1 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨u,v⟩
    simp [candidate,BinaryFractionalWalkOracle.extend,BinaryFractionalWalkOracle.costList,
      BinaryFractionalRows.sum,ih]

/-- The exact cost field of the original graph extension is returned in the
same lower heap, with the same retained records, source and complete charge. -/
theorem path_cost_bit {n H A : ℕ} (cost : BinaryFractionalWalkOracle.Cost n)
    (es : List (BinaryFractionalWalkOracle.Pair n)) (initial : BitState 158)
    (bounded : initial.Bounded H A) (pc0 : initial.pc=156)
    (hn : value initial.next=initial.heap.length)
    (input : StoredList (eraseState initial).heap (eraseState initial).registers.a
      (BinaryFractionalWalkOracle.costList cost es).1)
    (empty : initial.stack=[]) (B : ℕ)
    (widths : ∀ x ∈ (BinaryFractionalWalkOracle.costList cost es).1, StoredBounded x B) :
    ∃ charge out, Run CanonicalRationalSum.program
        (1+steps (BinaryFractionalWalkOracle.costList cost es).1) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (candidate cost es).cost ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a
        (BinaryFractionalWalkOracle.costList cost es).1 ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=157 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=cells (BinaryFractionalWalkOracle.costList cost es).1) ∧
      (attempt CanonicalRationalSum.program out).result=none ∧
      charge+(attempt CanonicalRationalSum.program out).operations ≤
        completeBound 158 H A (instructionBound (BinaryFractionalWalkOracle.costList cost es).1.length B) := by
  rw [candidate_cost]
  exact sum_bit initial bounded pc0 hn input empty B widths

end DirectedFlowCutGap.CanonicalPathCost
