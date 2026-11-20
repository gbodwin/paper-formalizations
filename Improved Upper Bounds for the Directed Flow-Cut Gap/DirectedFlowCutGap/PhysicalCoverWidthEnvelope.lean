import DirectedFlowCutGap.PhysicalSourceReadback

/-! Each realized fractional row is read from two Boolean-list fields in
the terminal physical heap. Its raw operand width follows from that heap. -/

namespace DirectedFlowCutGap.PhysicalCoverWidthEnvelope

open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open FractionalCoverRawCore PhysicalCoverReader BinaryArithmetic BinaryRational

private theorem word_length {H : NaturalHeap} {root : ℕ} {bs : Bits} (h : BoolList H root bs) :
    bs.length ≤ H.length := by
  have spine : IndexSpine H root bs.length := by
    induction h with
    | nil hp => exact .nil hp
    | cons hp _ _ ih => exact .cons hp ih
  exact (spine_short spine).le

private theorem fraction_width {H : NaturalHeap} {root : ℕ} {q : Fraction}
    (h : RationalComparisonProgram.Stored H root q) : StoredBounded q H.length := by
  obtain ⟨_,_,_,num,den⟩ := h
  exact ⟨word_length num,word_length den⟩

private theorem list_width {H : NaturalHeap} {root : ℕ} {xs : List Fraction}
    (h : CanonicalRationalSum.StoredList H root xs) : ∀ q ∈ xs, StoredBounded q H.length := by
  induction h with
  | nil _ => simp
  | cons _ head _ ih =>
    intro q hq
    obtain rfl | rest := List.mem_cons.mp hq
    · exact fraction_width head
    · exact ih q rest

private theorem best_stored {n : ℕ} {H : NaturalHeap} {root : ℕ} {s : BinaryFractionalCore.State n}
    (h : MinimumGuess.Result H root (some s)) (i : Fin n) :
    StoredBounded (BinaryFractionalRows.get s.best i) H.length := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,row,_⟩ := h
  have member : BinaryFractionalRows.get s.best i ∈ s.best.toList := by
    change s.best[i.val] ∈ s.best.toList
    have atIndex : i.val < s.best.toList.length := by simp only [Vector.length_toList,i.isLt]
    simpa only [Vector.getElem_toList] using List.getElem_mem atIndex
  exact list_width row _ member

private theorem states_stored {n : ℕ} {H : NaturalHeap} {root : ℕ}
    {xs : List (Option (BinaryFractionalCore.State n))} (h : GridFamily.StateList H root xs)
    {s : BinaryFractionalCore.State n} (member : some s ∈ xs) (i : Fin n) :
    StoredBounded (BinaryFractionalRows.get s.best i) H.length := by
  induction h with
  | nil _ => simp at member
  | cons _ head _ ih =>
    obtain equal | member := List.mem_cons.mp member
    · rw [← equal] at head
      exact best_stored head i
    · exact ih member

private theorem stateSpine {n : ℕ} {H : NaturalHeap} {root : ℕ}
    {xs : List (Option (BinaryFractionalCore.State n))} (h : GridFamily.StateList H root xs) :
    IndexSpine H root xs.length := by
  induction h with
  | nil found => exact .nil found
  | cons found _ _ ih => exact .cons found ih

theorem output_stored {n : ℕ} {H : NaturalHeap} {root : ℕ} {out : BinaryFractionalGuesses.Output n}
    (h : FinalDispatch.Output H root out) :
    match out with
    | .covers found => found.length ≤ H.length ∧
        ∀ row ∈ found, ∀ i, StoredBounded (BinaryFractionalRows.get row.state.best i) H.length
    | _ => True := by
  cases out with
  | invalid | infeasible _ | zero _ => trivial
  | covers found =>
    obtain ⟨_,_,_,_,states⟩ := h
    have count := (spine_short (stateSpine states)).le
    rw [List.length_map] at count
    exact ⟨count,fun row mem i => states_stored states (List.mem_map.mpr ⟨row,mem,rfl⟩) i⟩

def RowsFit {n : ℕ} (p : Plan n) (B : ℕ) : Prop :=
  ∀ rows, p=.covers rows → ∀ row ∈ rows, ∀ i, (get row i).Bounded B

theorem output_width {n : ℕ} {H : NaturalHeap} {root : ℕ} {out : BinaryFractionalGuesses.Output n}
    (h : FinalDispatch.Output H root out) : RowsFit (plan out) H.length := by
  cases out with
  | invalid | infeasible _ | zero _ => simp [RowsFit,plan]
  | covers results =>
    intro rows equal row member i
    simp only [plan,Plan.covers.injEq] at equal
    rw [← equal] at member
    obtain ⟨r,mem,rfl⟩ := List.mem_map.mp member
    rw [BinaryFractionalRows.decode_get]
    exact BinaryFractionalRows.stored_raw_bound ((output_stored h).2 r mem i)

private theorem solve_heap {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    ∃ H root, FinalDispatch.Output H root (BinaryFractionalGuesses.solveInput D).1 ∧
      H.length ≤ 1+PhysicalSourceDispatch.instructionPolynomial.eval (PhysicalSourceDispatch.input D).length := by
  obtain ⟨k,charge,out,hk,trace,_,_,_,stored⟩ := PhysicalSourceDispatch.bit_trace D
  have hstart : (PhysicalSourceDispatch.initial (PhysicalSourceDispatch.input D)).Bounded 1 0 := by
    simp [PhysicalSourceDispatch.initial,State.Bounded,State.records,Registers.All,Heap.Bounded]
  have live := reached_bounded trace hstart (hk.trans (PhysicalSourceDispatch.steps_polynomial D))
  have h := live.1
  unfold State.records at h
  have size : (eraseState out).heap.length ≤ 1+PhysicalSourceDispatch.instructionPolynomial.eval
      (PhysicalSourceDispatch.input D).length := by
    change (out.heap.map (Cell.map value)).length ≤ _
    rw [List.length_map]
    omega
  exact ⟨_,_,stored,size⟩

theorem solveInput_stored {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    let cap := 1+PhysicalSourceDispatch.instructionPolynomial.eval (PhysicalSourceDispatch.input D).length
    match (BinaryFractionalGuesses.solveInput D).1 with
    | .covers found => found.length≤cap ∧
        ∀ row ∈ found, ∀ i, StoredBounded (BinaryFractionalRows.get row.state.best i) cap
    | _ => True := by
  obtain ⟨_,_,stored,cap⟩ := solve_heap D
  generalize (BinaryFractionalGuesses.solveInput D).1 = out at stored ⊢
  cases out with
  | invalid | infeasible _ | zero _ => trivial
  | covers found =>
    have h := output_stored stored
    exact ⟨h.1.trans cap,fun row mem i => ⟨(h.2 row mem i).1.trans cap,(h.2 row mem i).2.trans cap⟩⟩

theorem rows_width {n : ℕ} (D : BinaryFractionalGuesses.Input n) :
    RowsFit (plan (BinaryFractionalGuesses.solveInput D).1)
      (1+PhysicalSourceDispatch.instructionPolynomial.eval (PhysicalSourceDispatch.input D).length) := by
  obtain ⟨_,_,stored,cap⟩ := solve_heap D
  intro rs eq row member i
  exact RawNonnegativeRational.Code.bounded_mono (output_width stored rs eq row member i) cap

theorem returned_rows_width {n : ℕ} (D : BinaryFractionalGuesses.Input n) {p : Plan n} {first second : ℕ}
    (run : PhysicalSourceReadback.run D=some (p,first,second)) :
    RowsFit p (1+PhysicalSourceDispatch.instructionPolynomial.eval (PhysicalSourceDispatch.input D).length) := by
  obtain ⟨a,b,source,_,_⟩ := PhysicalSourceReadback.run_eq D
  rw [run] at source
  have equal := congrArg Prod.fst (Option.some.inj source)
  change p=plan (BinaryFractionalGuesses.solveInput D).1 at equal
  rw [equal]
  exact rows_width D

end DirectedFlowCutGap.PhysicalCoverWidthEnvelope
