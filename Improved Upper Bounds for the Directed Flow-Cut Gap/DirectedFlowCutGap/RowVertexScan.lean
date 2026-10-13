import DirectedFlowCutGap.ActualPreparedPacking

namespace DirectedFlowCutGap.RowVertexScan
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation PackedBooleanConstructor
open BooleanTableRead (BoolList)
open CanonicalRationalSum (StoredList list_extend)
open GraphDiscoveryProgram (Vertices vertices_extend)

def label (pc : Fin 16) : Fin 32 := ⟨pc.val,by omega⟩
def program : Program 32 := fun pc =>
  if pc.val=14 then .move .r0 .r2 22
  else if h : pc.val<16 then
    ReferenceProgramLabels.instruction label (BinaryIncrementProgram.program ⟨pc.val,h⟩)
  else match pc.val with
  | 16 => .make .r1 .nil 25
  | 25 => .make .r3 .nil 17
  | 17 => .branch .r0 31 31 31 18
  | 18 => .field .r2 .r0 true 19
  | 19 => .move .r0 .r1 20
  | 20 => .make .r1 (.pair .r0 .r3) 21
  | 21 => .call 0 14 .r3
  | 22 => .move .r2 .r1 23
  | 23 => .move .r1 .r3 24
  | 24 => .move .r3 .r2 17
  | _ => .halt

theorem agree (pc : Fin 16) (h : BinaryIncrementProgram.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (BinaryIncrementProgram.program pc) := by
  fin_cases pc <;> simp_all [program,label,BinaryIncrementProgram.program]

def state (heap : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 32) : NaturalState 32 :=
  ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩
def words : ℕ → Bits → List Bits
  | 0,_ => []
  | n+1,acc => acc::words n (increment true acc).1
def steps : ℕ → Bits → ℕ
  | 0,_ => 1
  | n+1,acc => BinaryIncrementProgram.steps acc+9+steps n (increment true acc).1

theorem run_append {s u v : NaturalState 32} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- Every capacity-list cell saves its actual current counter word, then runs
binary increment. No vertex word or integer-value primitive is supplied. -/
theorem scan {xs : List Fraction} {acc : Bits} {rev : List Bits}
    {heap : NaturalHeap} {a b d : ℕ}
    (input : StoredList heap a xs) (counter : BoolList heap b acc) (old : Vertices heap d rev)
    (next c : ℕ) (dense : next=heap.length) (source : Bits) :
    ∃ out ext, NaturalRun program (steps xs.length acc)
      (state heap next a b c d source 17) [] out ∧
      Vertices out.heap out.registers.d ((words xs.length acc).reverse++rev) ∧
      out.heap=heap++ext ∧ out.next=out.heap.length ∧ out.stack=[] ∧ out.source=source ∧ out.pc=31 := by
  induction xs generalizing acc rev heap a b d next c with
  | nil =>
    cases input with
    | nil hp =>
      refine ⟨state heap next a b c d source 31,[],?_,?_,by simp [state],dense,rfl,rfl,rfl⟩
      · have t : tickNatural program (state heap next a b c d source 17)=
          some ⟨state heap next a b c d source 31,[],0⟩ := by
          simp [program,tickNatural,state,Registers.get,hp,tagBranch]
        exact .step t (.done _)
      · simpa [state,words] using old
  | cons x xs ih =>
    cases input with
    | @cons a head tail x xs hp hf ht =>
      let h1 := heap++[Cell.pair b d]
      have node : h1[next]?=some (.pair b d) := by simp [h1,dense]
      have old' : Vertices h1 next (acc::rev) :=
        .cons node (boolList_extend counter _) (vertices_extend old _)
      have dense1 : next+1=h1.length := by simp [h1,dense]
      obtain ⟨ei,root,len,inc,stored⟩ := BinaryIncrementProgram.increment_return
        (boolList_extend counter [Cell.pair b d]) (next+1) next tail d dense1
        ⟨b,next,tail,d⟩ 14 [] source
      have inc' := ReferenceProgramLabels.run label BinaryIncrementProgram.program program agree inc
      have dense2 : next+1+BinaryIncrementProgram.cells acc=(h1++ei).length := by simp [dense1,len]
      obtain ⟨out,er,rest,represented,he,nd,st,src,pc⟩ :=
        ih (list_extend (list_extend ht [Cell.pair b d]) ei) stored (vertices_extend old' ei)
          (next+1+BinaryIncrementProgram.cells acc) next dense2
      have t17 : tickNatural program (state heap next a b c d source 17)=
          some ⟨state heap next a b c d source 18,[],0⟩ := by
        simp [program,tickNatural,state,Registers.get,hp,tagBranch]
      have t18 : tickNatural program (state heap next a b c d source 18)=
          some ⟨state heap next a b tail d source 19,[],0⟩ := by
        simp [program,tickNatural,state,Registers.get,Registers.set,hp]
      have t19 : tickNatural program (state heap next a b tail d source 19)=
          some ⟨state heap next b b tail d source 20,[],0⟩ := by
        simp [program,tickNatural,state,Registers.get,Registers.set]
      have t20 : tickNatural program (state heap next b b tail d source 20)=
          some ⟨state h1 (next+1) b next tail d source 21,[],0⟩ := by
        simp [program,tickNatural,state,Registers.get,Registers.set,allocateNatural,Recipe.cell,h1]
      have t21 : tickNatural program (state h1 (next+1) b next tail d source 21)=
          some ⟨ReferenceProgramLabels.state label
            (BinaryIncrementProgram.state h1 (next+1) b next tail d
              [⟨14,.r3,⟨b,next,tail,d⟩⟩] source 0),[],0⟩ := by
        simp [program,tickNatural,state,ReferenceProgramLabels.state,ReferenceProgramLabels.frame,label,BinaryIncrementProgram.state]
      have t14 : tickNatural program (ReferenceProgramLabels.state label
            (BinaryIncrementProgram.state (h1++ei) (next+1+BinaryIncrementProgram.cells acc)
              b next tail root [] source 14))=
          some ⟨state (h1++ei) (next+1+BinaryIncrementProgram.cells acc) tail next tail root source 22,[],0⟩ := by
        simp [program,tickNatural,state,ReferenceProgramLabels.state,label,BinaryIncrementProgram.state,Registers.get,Registers.set]
      have t22 : tickNatural program (state (h1++ei) (next+1+BinaryIncrementProgram.cells acc) tail next tail root source 22)=
          some ⟨state (h1++ei) (next+1+BinaryIncrementProgram.cells acc) tail next next root source 23,[],0⟩ := by
        simp [program,tickNatural,state,Registers.get,Registers.set]
      have t23 : tickNatural program (state (h1++ei) (next+1+BinaryIncrementProgram.cells acc) tail next next root source 23)=
          some ⟨state (h1++ei) (next+1+BinaryIncrementProgram.cells acc) tail root next root source 24,[],0⟩ := by
        simp [program,tickNatural,state,Registers.get,Registers.set]
      have t24 : tickNatural program (state (h1++ei) (next+1+BinaryIncrementProgram.cells acc) tail root next root source 24)=
          some ⟨state (h1++ei) (next+1+BinaryIncrementProgram.cells acc) tail root next next source 17,[],0⟩ := by
        simp [program,tickNatural,state,Registers.get,Registers.set]
      refine ⟨out,[Cell.pair b d]++ei++er,?_,?_,?_,nd,st,src,pc⟩
      · have joined := run_append inc' (.step t14 (.step t22 (.step t23 (.step t24 rest))))
        convert NaturalRun.step t17 (.step t18 (.step t19 (.step t20 (.step t21 joined)))) using 1 <;>
          simp [steps,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        omega
      · simpa [words,List.reverse_cons,List.append_assoc] using represented
      · simpa [h1,List.append_assoc] using he
end DirectedFlowCutGap.RowVertexScan
