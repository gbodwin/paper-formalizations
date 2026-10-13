import DirectedFlowCutGap.GridFamilyControlCalls
import DirectedFlowCutGap.GridFamilyData

namespace DirectedFlowCutGap.GridFamily
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead
set_option maxRecDepth 32768

theorem guard_prefix {heap : NaturalHeap} {c : ℕ} {fuel : Bits}
    (input : BoolList heap c fuel) (next a b d : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 10180)) (source : Bits) :
    NaturalRun program (BinaryZeroProgram.steps fuel+6)
      (state heap next a b c d stack source 10130) []
      (state (heap++[.flag (isZero fuel).1]) (next+1) a b c next stack source 10131) := by
  have first : tickNatural program (state heap next a b c d stack source 10130)=
      some ⟨state heap next a b c d (⟨10131,.r3,⟨a,b,c,d⟩⟩::stack) source 10100,[],0⟩ := by rfl
  have run := zero_helper input next a b d dense ⟨a,b,c,d⟩ 10131 stack source
  simpa [Nat.add_assoc] using NaturalRun.step first run

theorem empty_return (n : ℕ) {heap : NaturalHeap} {c : ℕ} {fuel : Bits}
    (input : BoolList heap c fuel) (zero : (isZero fuel).1=true)
    (next a b d : ℕ) (dense : next=heap.length) (saved : Registers ℕ)
    (destination : Reg) (pc : Fin 10180) (stack : List (Frame ℕ 10180)) (source : Bits) :
    NaturalRun program (BinaryZeroProgram.steps fuel+9)
      (state heap next a b c d (⟨pc,destination,saved⟩::stack) source 10130) []
      ⟨heap++[.flag true,.nil],next+2,saved.set destination (next+1),stack,pc,source⟩ ∧
      StateList (n:=n) (heap++[.flag true,.nil]) (next+1) [] := by
  let frame : Frame ℕ 10180 := ⟨pc,destination,saved⟩
  have front : NaturalRun program (BinaryZeroProgram.steps fuel+6)
      (state heap next a b c d (frame::stack) source 10130) []
      (state (heap++[.flag true]) (next+1) a b c next (frame::stack) source 10131) := by
    simpa [zero] using guard_prefix input next a b d dense (frame::stack) source
  have t1 : tickNatural program
      (state (heap++[.flag true]) (next+1) a b c next (frame::stack) source 10131)=
      some ⟨state (heap++[.flag true]) (next+1) a b c next (frame::stack) source 10150,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,tagBranch,dense]
  have t2 : tickNatural program
      (state (heap++[.flag true]) (next+1) a b c next (frame::stack) source 10150)=
      some ⟨state (heap++[.flag true,.nil]) (next+2) a b c (next+1) (frame::stack) source 10151,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,List.append_assoc,Nat.add_assoc]
  have t3 : tickNatural program
      (state (heap++[.flag true,.nil]) (next+2) a b c (next+1) (frame::stack) source 10151)=
      some ⟨⟨heap++[.flag true,.nil],next+2,saved.set destination (next+1),stack,pc,source⟩,[],0⟩ := by
    simp [tickNatural,program,state,frame,Registers.get]
  constructor
  · simpa [frame,Nat.add_assoc] using run_append front (.step t1 (.step t2 (.step t3 (.done _))))
  · exact .nil (by simp [dense])
end DirectedFlowCutGap.GridFamily
