import DirectedFlowCutGap.ActualRationalQuotient
import DirectedFlowCutGap.BinaryFractionalCore

namespace DirectedFlowCutGap.NaturalFractionProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

def program : Program 8 := fun pc => match pc.val with
  | 0 => .make .r2 .nil 1
  | 1 => .make .r3 (.flag true) 2
  | 2 => .make .r3 (.pair .r3 .r2) 3
  | 3 => .make .r3 (.pair .r0 .r3) 4
  | 4 => .ret .r3
  | 6 => .call 0 7 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 8)) (source : Bits) (pc : Fin 8) : NaturalState 8 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def extension (next a : ℕ) : NaturalHeap :=
  [.nil,.flag true,.pair (next+1) next,.pair a (next+2)]

theorem fraction_return {heap : NaturalHeap} {word : Bits} {a : ℕ}
    (rep : BoolList heap a word) (next b c d : ℕ) (dense : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 8) (stack : List (Frame ℕ 8)) (source : Bits) :
    NaturalRun program 5 (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
      (state (heap++extension next a) (next+4) saved.a saved.b saved.c (next+3) stack source pc) ∧
    Stored (heap++extension next a) (next+3) (BinaryFractionalCore.naturalFraction word) := by
  let frames := ⟨pc,.r3,saved⟩::stack
  have t0 : tickNatural program (state heap next a b c d frames source 0)=
      some ⟨state (heap++[.nil]) (next+1) a b next d frames source 1,[],0⟩ := by rfl
  have t1 : tickNatural program (state (heap++[.nil]) (next+1) a b next d frames source 1)=
      some ⟨state (heap++[.nil,.flag true]) (next+2) a b next (next+1) frames source 2,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,List.append_assoc,Nat.add_assoc]
  have t2 : tickNatural program (state (heap++[.nil,.flag true]) (next+2) a b next (next+1) frames source 2)=
      some ⟨state (heap++[.nil,.flag true,.pair (next+1) next]) (next+3)
        a b next (next+2) frames source 3,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,List.append_assoc,Nat.add_assoc]
  have t3 : tickNatural program (state (heap++[.nil,.flag true,.pair (next+1) next])
      (next+3) a b next (next+2) frames source 3)=
      some ⟨state (heap++extension next a) (next+4) a b next (next+3) frames source 4,[],0⟩ := by
    simp [program,tickNatural,state,extension,allocateNatural,Recipe.cell,Registers.get,Registers.set,List.append_assoc,Nat.add_assoc]
  have t4 : tickNatural program (state (heap++extension next a) (next+4) a b next (next+3) frames source 4)=
      some ⟨state (heap++extension next a) (next+4) saved.a saved.b saved.c (next+3) stack source pc,[],0⟩ := by
    simp [program,tickNatural,state,frames,Registers.get,Registers.set]
  refine ⟨.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.done _))))),a,next+2,?_,?_,?_⟩
  · simp [extension,dense]
  · exact boolList_extend rep _
  · exact .cons (head:=next+1) (tail:=next) (by simp [extension,dense])
      (by simp [extension,dense]) (.nil (by simp [extension,dense]))
end DirectedFlowCutGap.NaturalFractionProgram
