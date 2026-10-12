import DirectedFlowCutGap.NormalizedRowProgram

namespace DirectedFlowCutGap.NormalizedRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def alpha (xs : List Fraction) (mask : List Bool) : Fraction :=
  (BinaryFractionalRows.sum (MaskedRationalRow.result xs mask)).1
def result (xs : List Fraction) (mask : List Bool) : List Fraction :=
  ScalarQuotientRow.result false (alpha xs mask) xs
def steps (xs : List Fraction) (mask : List Bool) : ℕ :=
  MaskedRationalRow.steps mask+CanonicalRationalSum.steps (MaskedRationalRow.result xs mask)+
    ScalarQuotientRow.steps false (alpha xs mask) xs+13
def cells (xs : List Fraction) (mask : List Bool) : ℕ :=
  1+MaskedRationalRow.cells mask+CanonicalRationalSum.cells (MaskedRationalRow.result xs mask)+
    ScalarQuotientRow.cells false (alpha xs mask) xs

theorem normalized_high {xs : List Fraction} {mask : List Bool} (initial : NaturalState 372)
    (pc0 : initial.pc=364) (hn : initial.next=initial.heap.length)
    (row : StoredList initial.heap initial.registers.a xs)
    (flags : BoolList initial.heap initial.registers.b mask)
    (aligned : xs.length=mask.length) (empty : initial.stack=[]) :
    ∃ ext maskedRoot alphaRoot root,ext.length=cells xs mask ∧
      NaturalRun program (steps xs mask) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
          alphaRoot initial.next root [] initial.source 371) ∧
      StoredList (initial.heap++ext) root (result xs mask) ∧
      Stored (initial.heap++ext) alphaRoot (alpha xs mask) ∧
      StoredList (initial.heap++ext) maskedRoot (MaskedRationalRow.result xs mask) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn row flags empty
      subst pc;subst stack
      let e0 : NaturalHeap := [.pair a b]
      let h0 := heap++e0
      let n0 := next+1
      have dense0 : n0=h0.length := by simp [n0,h0,e0,hn]
      obtain ⟨em,rm,lm,maskRun,maskRep⟩ := mask_return (list_extend row e0) (boolList_extend flags e0)
        aligned n0 next d dense0 ⟨a,b,next,d⟩ 366 [] source
      let h1 := h0++em
      let n1 := n0+em.length
      have dense1 : n1=h1.length := by simp [n1,h1,dense0]
      obtain ⟨es,rs,ls,sumRun,sumRep⟩ := sum_return (b:=b) maskRep n1 next rm dense1
        ⟨rm,b,next,rm⟩ 368 [] source
      let h2 := h1++es
      let n2 := n1+es.length
      have dense2 : n2=h2.length := by simp [n2,h2,dense1]
      have row2 : StoredList h2 a xs := list_extend (list_extend (list_extend row e0) em) es
      obtain ⟨ed,rd,ld,divideRun,divideRep⟩ := divide_return (alpha xs mask) row2 sumRep n2 next rs dense2
        ⟨a,rs,next,rs⟩ 371 [] source
      let h3 := h2++ed
      let n3 := n2+ed.length
      have context2 : h2[next]?=some (.pair a b) := by
        apply lookup_extend (h:=h1)
        apply lookup_extend (h:=h0)
        simp [h0,e0,hn]
      have t364 : tickNatural program (state heap next a b c d [] source 364)=
          some ⟨state h0 n0 a b next d [] source 365,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h0,e0,n0]
      have t365 : tickNatural program (state h0 n0 a b next d [] source 365)=
          some ⟨state h0 n0 a b next d [⟨366,.r3,⟨a,b,next,d⟩⟩] source 22,[],0⟩ := by
        simp [tickNatural,program,state]
      have t366 : tickNatural program (state h1 n1 a b next rm [] source 366)=
          some ⟨state h1 n1 rm b next rm [] source 367,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t367 : tickNatural program (state h1 n1 rm b next rm [] source 367)=
          some ⟨state h1 n1 rm b next rm [⟨368,.r3,⟨rm,b,next,rm⟩⟩] source 180,[],0⟩ := by
        simp [tickNatural,program,state]
      have t368 : tickNatural program (state h2 n2 rm b next rs [] source 368)=
          some ⟨state h2 n2 rm rs next rs [] source 369,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t369 : tickNatural program (state h2 n2 rm rs next rs [] source 369)=
          some ⟨state h2 n2 a rs next rs [] source 370,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,context2]
      have t370 : tickNatural program (state h2 n2 a rs next rs [] source 370)=
          some ⟨state h2 n2 a rs next rs [⟨371,.r3,⟨a,rs,next,rs⟩⟩] source 362,[],0⟩ := by
        simp [tickNatural,program,state]
      have whole := NaturalRun.step t364 (.step t365 (run_append maskRun (.step t366 (.step t367
        (run_append sumRun (.step t368 (.step t369 (.step t370 divideRun))))))))
      let ext := e0++em++es++ed
      have heaps : heap++ext=h3 := by simp [ext,h3,h2,h1,h0,List.append_assoc]
      have sizes : next+ext.length=n3 := by simp [ext,e0,n3,n2,n1,n0];omega
      refine ⟨ext,rm,rs,rd,?_,?_,?_,?_,?_⟩
      · simp [ext,e0,cells,lm,ls,ld];omega
      · rw [heaps,sizes]
        convert whole using 1 <;> simp only [steps,state,List.nil_append]
        omega
      · rw [heaps];exact divideRep
      · rw [heaps];exact stored_extend sumRep ed
      · rw [heaps];exact list_extend (list_extend maskRep es) ed
end DirectedFlowCutGap.NormalizedRow
