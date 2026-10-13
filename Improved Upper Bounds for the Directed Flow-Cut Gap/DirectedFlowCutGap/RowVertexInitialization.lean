import DirectedFlowCutGap.RowVertexScan

namespace DirectedFlowCutGap.RowVertexScan
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation PackedBooleanConstructor
open BooleanTableRead (BoolList)
open CanonicalRationalSum (StoredList list_extend)
open GraphDiscoveryProgram (Vertices vertices_extend)

theorem steps_bound (n : ℕ) (acc : Bits) :
    steps n acc ≤ (8*(acc.length+n)+15)*n+1 := by
  induction n generalizing acc with
  | zero => simp [steps]
  | succ n ih =>
    have hi := (increment_spec true acc).2.1
    have hs := BinaryIncrementProgram.steps_bound acc
    have h := ih (increment true acc).1
    have hm : (8*((increment true acc).1.length+n)+15)*n ≤
        (8*(acc.length+(n+1))+15)*n := Nat.mul_le_mul_right n (by omega)
    simp only [steps]
    nlinarith

theorem words_length (n : ℕ) (acc : Bits) : (words n acc).length=n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simp [words,ih]

/-- The two initial nils are allocated by the same executed program. -/
theorem enumerate_reverse {xs : List Fraction} (initial : NaturalState 32)
    (pc0 : initial.pc=16) (dense : initial.next=initial.heap.length)
    (input : StoredList initial.heap initial.registers.a xs) (empty : initial.stack=[]) :
    ∃ out ext, NaturalRun program (steps xs.length []+2) initial [] out ∧
      Vertices out.heap out.registers.d (words xs.length []).reverse ∧
      out.heap=initial.heap++ext ∧ out.next=out.heap.length ∧ out.stack=[] ∧
      out.source=initial.source ∧ out.pc=31 := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 dense input empty
      subst pc
      subst stack
      let ext : NaturalHeap := [.nil,.nil]
      have counter : BoolList (heap++ext) next [] := .nil (by simp [ext,dense])
      have acc : Vertices (heap++ext) (next+1) [] := .nil (by simp [ext,dense])
      have dn : next+2=(heap++ext).length := by simp [ext,dense]
      obtain ⟨out,more,run,rep,he,nd,st,src,pc⟩ :=
        scan (list_extend input ext) counter acc (next+2) c dn source
      have t16 : tickNatural program (state heap next a b c d source 16)=
          some ⟨state (heap++[.nil]) (next+1) a next c d source 25,[],0⟩ := by
        simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set]
      have t25 : tickNatural program (state (heap++[.nil]) (next+1) a next c d source 25)=
          some ⟨state (heap++ext) (next+2) a next c (next+1) source 17,[],0⟩ := by
        simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,ext,List.append_assoc,Nat.add_assoc]
      refine ⟨out,ext++more,?_,?_,?_,nd,st,src,pc⟩
      · simpa [state,Nat.add_assoc] using NaturalRun.step t16 (.step t25 run)
      · simpa using rep
      · simpa [List.append_assoc] using he
end DirectedFlowCutGap.RowVertexScan
