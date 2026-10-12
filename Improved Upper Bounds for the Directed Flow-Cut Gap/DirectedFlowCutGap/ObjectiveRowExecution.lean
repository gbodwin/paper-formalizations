import DirectedFlowCutGap.ObjectiveRowProgram

namespace DirectedFlowCutGap.ObjectiveRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def result (xs ys : List Fraction) : Fraction :=
  (BinaryFractionalRows.sum (ObjectiveProductList.products xs ys)).1

def steps (xs ys : List Fraction) : ℕ :=
  ObjectiveProductList.steps xs ys+CanonicalRationalSum.steps (ObjectiveProductList.products xs ys)+7

def cells (xs ys : List Fraction) : ℕ :=
  ObjectiveProductList.cells xs ys+CanonicalRationalSum.cells (ObjectiveProductList.products xs ys)

theorem objective_high {xs ys : List Fraction} (initial : NaturalState 312)
    (pc0 : initial.pc=308) (hn : initial.next=initial.heap.length)
    (left : StoredList initial.heap initial.registers.a xs)
    (right : StoredList initial.heap initial.registers.b ys) (aligned : xs.length=ys.length)
    (empty : initial.stack=[]) :
    ∃ ext productsRoot root,ext.length=cells xs ys ∧
      NaturalRun program (steps xs ys) initial []
        (state (initial.heap++ext) (initial.next+ext.length) productsRoot
          initial.registers.b initial.registers.c root [] initial.source 311) ∧
      Stored (initial.heap++ext) root (result xs ys) ∧
      StoredList (initial.heap++ext) productsRoot (ObjectiveProductList.products xs ys) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn left right empty
      subst pc;subst stack
      obtain ⟨ep,rp,lp,productRun,productRep⟩ := products_return left right aligned next c d hn
        ⟨a,b,c,d⟩ 309 [] source
      let h1 := heap++ep
      let n1 := next+ep.length
      have dense1 : n1=h1.length := by simp [n1,h1,hn]
      obtain ⟨es,rs,ls,sumRun,sumRep⟩ := sum_return productRep n1 b c rp dense1
        ⟨rp,b,c,rp⟩ 311 [] source
      let h2 := h1++es
      let n2 := n1+es.length
      have t308 : tickNatural program (state heap next a b c d [] source 308)=
          some ⟨state heap next a b c d [⟨309,.r3,⟨a,b,c,d⟩⟩] source 148,[],0⟩ := by
        simp [tickNatural,program,state]
      have t309 : tickNatural program (state h1 n1 a b c rp [] source 309)=
          some ⟨state h1 n1 rp b c rp [] source 310,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t310 : tickNatural program (state h1 n1 rp b c rp [] source 310)=
          some ⟨state h1 n1 rp b c rp [⟨311,.r3,⟨rp,b,c,rp⟩⟩] source 306,[],0⟩ := by
        simp [tickNatural,program,state]
      have whole := NaturalRun.step t308 (run_append productRun (.step t309 (.step t310 sumRun)))
      refine ⟨ep++es,rp,rs,by simp [cells,lp,ls],?_,?_,?_⟩
      · convert whole using 1 <;> simp [steps,state,n1,List.append_assoc,Nat.add_assoc]
        omega
      · simpa [result,List.append_assoc] using sumRep
      · simpa [List.append_assoc] using list_extend productRep es

def instructionBound (n B : ℕ) : ℕ :=
  ObjectiveProductList.instructionBound n B+CanonicalRationalSum.instructionBound n (B+B+1)+5

theorem steps_bound (xs ys : List Fraction) (B : ℕ)
    (aligned : xs.length=ys.length)
    (hx : ∀ x∈xs,StoredBounded x B) (hy : ∀ y∈ys,StoredBounded y B) :
    steps xs ys ≤ instructionBound xs.length B := by
  have hp := ObjectiveProductList.steps_bound xs ys B aligned hx hy
  have hs := CanonicalRationalSum.steps_bound (ObjectiveProductList.products xs ys) (B+B+1)
    (ObjectiveProductList.products_width xs ys B hx hy)
  rw [ObjectiveProductList.products_length xs ys aligned] at hs
  dsimp [steps,instructionBound]
  omega
end DirectedFlowCutGap.ObjectiveRow
