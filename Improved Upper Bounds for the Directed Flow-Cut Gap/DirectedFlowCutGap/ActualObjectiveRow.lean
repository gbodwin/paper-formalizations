import DirectedFlowCutGap.ObjectiveRowExecution

namespace DirectedFlowCutGap.ObjectiveRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

/-- Exact old field representation, not merely rational-value equality. -/
theorem result_eq_objective {m : ℕ} (c y : BinaryFractionalRows.Row m) :
    result c.toList y.toList=(BinaryFractionalRows.objective c y).1 := by
  have hv : Vector.zipWith (fun x y : Fraction => (BinaryRational.mul x y).1) c y=
      Vector.ofFn (fun i : Fin m => (BinaryRational.mul (BinaryFractionalRows.get c i)
        (BinaryFractionalRows.get y i)).1) := by
    ext i hi
    simp [BinaryFractionalRows.get]
  unfold result BinaryFractionalRows.objective
  dsimp only
  rw [EncodedRoundingInput.tabulate_value,←hv]
  simp [ObjectiveProductList.products]

/-- Same lower run constructs every product and accumulates that actual list.
Original row and address bounds remain input premises; one terminal attempt is
included in the physical charge. -/
theorem objective_bit {xs ys : List Fraction} {H A : ℕ} (initial : BitState 312)
    (bounded : initial.Bounded H A) (pc0 : initial.pc=308)
    (hn : value initial.next=initial.heap.length)
    (left : StoredList (eraseState initial).heap (eraseState initial).registers.a xs)
    (right : StoredList (eraseState initial).heap (eraseState initial).registers.b ys)
    (aligned : xs.length=ys.length) (empty : initial.stack=[]) (B : ℕ)
    (hx : ∀ x∈xs,StoredBounded x B) (hy : ∀ y∈ys,StoredBounded y B) :
    ∃ charge out,Run program (steps xs ys) charge initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (result xs ys) ∧
      StoredList (eraseState out).heap (eraseState out).registers.a (ObjectiveProductList.products xs ys) ∧
      StoredList (eraseState out).heap (eraseState initial).registers.a xs ∧
      StoredList (eraseState out).heap (eraseState initial).registers.b ys ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=311 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=cells xs ys) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 312 H A (instructionBound xs.length B) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have hs : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,rp,root,len,high,rep,products⟩ := objective_high (eraseState initial) pc0 hn' left right aligned hs
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have hh : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          rp (eraseState initial).registers.b (eraseState initial).registers.c root []
          (eraseState initial).source 311)=none := rfl
    rw [hh] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb := steps_bound xs ys B aligned hx hy
  have hm : completeBound 312 H A (steps xs ys)≤completeBound 312 H A (instructionBound xs.length B) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,?_,source,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact products
  · rw [erase];exact list_extend left ext
  · rw [erase];exact list_extend right ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=311 := by rw [erase];rfl
    exact h
  · rw [erase];rfl
end DirectedFlowCutGap.ObjectiveRow
