import DirectedFlowCutGap.PackingGuardComparison

namespace DirectedFlowCutGap.PackingGuard
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def Context (heap : NaturalHeap) (root capacity original input : ℕ) : Prop :=
  ∃ base,heap[root]?=some (.pair original base) ∧ heap[base]?=some (.pair capacity input)

def steps (capacity weights : List Fraction) : ℕ :=
  ObjectiveRow.steps capacity weights+
    RationalComparisonProgram.instructions one (ObjectiveRow.result capacity weights)+12

def cells (capacity weights : List Fraction) : ℕ :=
  ObjectiveRow.cells capacity weights+
    RationalComparisonProgram.cells one (ObjectiveRow.result capacity weights)+6

theorem guard_high {xs ys : List Fraction} {heap : NaturalHeap} {a b weights k : ℕ}
    (row : StoredList heap a xs) (current : heap[b]?=some (.pair weights k))
    (values : StoredList heap weights ys) (aligned : xs.length=ys.length)
    (next c d : ℕ) (hn : next=heap.length) (source : Bits) :
    ∃ ext oneRoot objectiveRoot flagRoot,
      ext.length=cells xs ys ∧
      NaturalRun program (steps xs ys) (state heap next a b c d [] source 470) []
        (state (heap++ext) (next+ext.length) oneRoot objectiveRoot (next+1) flagRoot [] source 480) ∧
      (heap++ext)[flagRoot]?=some (.flag (BinaryRational.le one (ObjectiveRow.result xs ys)).1) ∧
      Context (heap++ext) (next+1) a b c ∧
      Stored (heap++ext) objectiveRoot (ObjectiveRow.result xs ys) := by
  let e0 : NaturalHeap := [.pair a c,.pair b next]
  let h0 := heap++e0
  let n0 := next+2
  have dense0 : n0=h0.length := by simp [n0,h0,e0,hn]
  obtain ⟨eo,ro,lo,objectiveRun,objectiveRep⟩ := objective_return
    (list_extend row e0) (list_extend values e0) aligned n0 (next+1) d dense0
    ⟨a,weights,next+1,d⟩ 474 [] source
  let h1 := h0++eo
  let n1 := n0+eo.length
  have dense1 : n1=h1.length := by simp [n1,h1,dense0]
  let e1 : NaturalHeap := [.nil,.flag true,.pair (n1+1) n1,.pair (n1+2) (n1+2)]
  let h2 := h1++e1
  let n2 := n1+4
  have dense2 : n2=h2.length := by simp [n2,h2,e1,dense1]
  have empty : h2[n1]?=some .nil := by simp [h2,e1,dense1]
  have bit : h2[n1+1]?=some (.flag true) := by simp [h2,e1,dense1]
  have word : h2[n1+2]?=some (.pair (n1+1) n1) := by simp [h2,e1,dense1]
  have oneRep : Stored h2 (n1+3) one := by
    refine ⟨n1+2,n1+2,?_,?_,?_⟩
    · simp [h2,e1,dense1]
    · exact .cons word bit (.nil empty)
    · exact .cons word bit (.nil empty)
  obtain ⟨ec,rc,lc,compareRun,flag⟩ := comparison_return one (ObjectiveRow.result xs ys)
    oneRep (stored_extend objectiveRep e1) n2 (next+1) (n1+1) dense2
    ⟨n1+3,ro,next+1,n1+1⟩ 480 [] source
  let ext := e0++eo++e1++ec
  have heaps : heap++ext=h2++ec := by simp [ext,h2,h1,h0,List.append_assoc]
  have sizes : next+ext.length=n2+ec.length := by simp [ext,n2,n1,n0,e0,e1];omega
  have original : h0[b]?=
      some (.pair weights k) := lookup_extend current _
  have t470 : tickNatural program (state heap next a b c d [] source 470)=
      some ⟨state (heap++[.pair a c]) (next+1) a b next d [] source 471,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
  have t471 : tickNatural program (state (heap++[.pair a c]) (next+1) a b next d [] source 471)=
      some ⟨state h0 n0 a b (next+1) d [] source 472,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,h0,n0,e0,List.append_assoc]
  have t472 : tickNatural program (state h0 n0 a b (next+1) d [] source 472)=
      some ⟨state h0 n0 a weights (next+1) d [] source 473,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,original]
  have t473 : tickNatural program (state h0 n0 a weights (next+1) d [] source 473)=
      some ⟨state h0 n0 a weights (next+1) d [⟨474,.r3,⟨a,weights,next+1,d⟩⟩] source 308,[],0⟩ := by
    simp [tickNatural,program,state]
  have t474 : tickNatural program (state h1 n1 a weights (next+1) ro [] source 474)=
      some ⟨state h1 n1 a ro (next+1) ro [] source 475,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t475 : tickNatural program (state h1 n1 a ro (next+1) ro [] source 475)=
      some ⟨state (h1++[.nil]) (n1+1) n1 ro (next+1) ro [] source 476,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
  have t476 : tickNatural program (state (h1++[.nil]) (n1+1) n1 ro (next+1) ro [] source 476)=
      some ⟨state (h1++[.nil,.flag true]) (n1+2) n1 ro (next+1) (n1+1) [] source 477,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,List.append_assoc,Nat.add_assoc]
  have t477 : tickNatural program (state (h1++[.nil,.flag true]) (n1+2) n1 ro (next+1) (n1+1) [] source 477)=
      some ⟨state (h1++[.nil,.flag true,.pair (n1+1) n1]) (n1+3) (n1+2) ro (next+1) (n1+1) [] source 478,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,List.append_assoc,Nat.add_assoc]
  have t478 : tickNatural program (state (h1++[.nil,.flag true,.pair (n1+1) n1]) (n1+3) (n1+2) ro (next+1) (n1+1) [] source 478)=
      some ⟨state h2 n2 (n1+3) ro (next+1) (n1+1) [] source 479,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,h2,n2,e1,List.append_assoc,Nat.add_assoc]
  have t479 : tickNatural program (state h2 n2 (n1+3) ro (next+1) (n1+1) [] source 479)=
      some ⟨state h2 n2 (n1+3) ro (next+1) (n1+1) [⟨480,.r3,⟨n1+3,ro,next+1,n1+1⟩⟩] source 456,[],0⟩ := by
    simp [tickNatural,program,state]
  have tailRun := NaturalRun.step t474 (.step t475 (.step t476 (.step t477 (.step t478 (.step t479 compareRun)))))
  have whole := NaturalRun.step t470 (.step t471 (.step t472 (.step t473 (run_append objectiveRun tailRun))))
  refine ⟨ext,n1+3,ro,rc,?_,?_,?_,?_,?_⟩
  · simp [ext,e0,e1,cells,lo,lc];omega
  · rw [heaps,sizes]
    convert whole using 1
    · simp only [steps];omega
    · rfl
  · rw [heaps];exact flag
  · rw [heaps]
    refine ⟨next,?_,?_⟩
    · exact lookup_extend (lookup_extend (lookup_extend (by simp [h0,e0,hn]) eo) e1) ec
    · exact lookup_extend (lookup_extend (lookup_extend (by simp [h0,e0,hn]) eo) e1) ec
  · rw [heaps];exact stored_extend (stored_extend objectiveRep e1) ec
end DirectedFlowCutGap.PackingGuard
