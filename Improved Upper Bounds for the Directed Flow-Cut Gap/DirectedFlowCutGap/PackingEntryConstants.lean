import DirectedFlowCutGap.PackingEntryCalls
namespace DirectedFlowCutGap.PackingEntry
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

def constants (next a b c : ℕ) : NaturalHeap := [.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false,.pair (next+6) (next+4),.pair (next+7) (next+4),.pair (next+5) (next+1)]

theorem constants_run (heap : NaturalHeap) (next a b c d : ℕ) (hn : next=heap.length) (source : Bits) :
    NaturalRun program 13 (state heap next a b c d [] source 440) []
      (state (heap++constants next a b c) (next+10) (next+8) a (next+9) (next+4) [] source 453) := by
  have t440 : tickNatural program (state heap next a b c d [] source 440)=
      some ⟨state (heap++[.pair b c]) (next+1) a b next d [] source 441,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,hn]
  have t441 : tickNatural program (state (heap++[.pair b c]) (next+1) a b next d [] source 441)=
      some ⟨state (heap++[.pair b c,.pair a next]) (next+2) a b (next+1) d [] source 442,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,hn,List.append_assoc,Nat.add_assoc]
  have t442 : tickNatural program (state (heap++[.pair b c,.pair a next]) (next+2) a b (next+1) d [] source 442)=
      some ⟨state (heap++[.pair b c,.pair a next,.nil]) (next+3) (next+2) b (next+1) d [] source 443,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,hn,List.append_assoc,Nat.add_assoc]
  have t443 : tickNatural program (state (heap++[.pair b c,.pair a next,.nil]) (next+3) (next+2) b (next+1) d [] source 443)=
      some ⟨state (heap++[.pair b c,.pair a next,.nil,.flag true]) (next+4) (next+2) (next+3) (next+1) d [] source 444,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,hn,List.append_assoc,Nat.add_assoc]
  have t444 : tickNatural program (state (heap++[.pair b c,.pair a next,.nil,.flag true]) (next+4) (next+2) (next+3) (next+1) d [] source 444)=
      some ⟨state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2)]) (next+5) (next+4) (next+3) (next+1) d [] source 445,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,hn,List.append_assoc,Nat.add_assoc]
  have t445 : tickNatural program (state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2)]) (next+5) (next+4) (next+3) (next+1) d [] source 445)=
      some ⟨state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4)]) (next+6) (next+4) (next+5) (next+1) d [] source 446,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,hn,List.append_assoc,Nat.add_assoc]
  have t446 : tickNatural program (state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4)]) (next+6) (next+4) (next+5) (next+1) d [] source 446)=
      some ⟨state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false]) (next+7) (next+4) (next+5) (next+1) (next+6) [] source 447,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set,hn,List.append_assoc,Nat.add_assoc]
  have t447 : tickNatural program (state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false]) (next+7) (next+4) (next+5) (next+1) (next+6) [] source 447)=
      some ⟨state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false,.pair (next+6) (next+4)]) (next+8) (next+7) (next+5) (next+1) (next+6) [] source 448,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,hn,List.append_assoc,Nat.add_assoc]
  have t448 : tickNatural program (state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false,.pair (next+6) (next+4)]) (next+8) (next+7) (next+5) (next+1) (next+6) [] source 448)=
      some ⟨state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false,.pair (next+6) (next+4)]) (next+8) (next+7) (next+5) (next+1) (next+4) [] source 449,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hn]
  have t449 : tickNatural program (state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false,.pair (next+6) (next+4)]) (next+8) (next+7) (next+5) (next+1) (next+4) [] source 449)=
      some ⟨state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false,.pair (next+6) (next+4),.pair (next+7) (next+4)]) (next+9) (next+8) (next+5) (next+1) (next+4) [] source 450,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,hn,List.append_assoc,Nat.add_assoc]
  have t450 : tickNatural program (state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false,.pair (next+6) (next+4),.pair (next+7) (next+4)]) (next+9) (next+8) (next+5) (next+1) (next+4) [] source 450)=
      some ⟨state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false,.pair (next+6) (next+4),.pair (next+7) (next+4),.pair (next+5) (next+1)]) (next+10) (next+8) (next+5) (next+9) (next+4) [] source 451,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,hn,List.append_assoc,Nat.add_assoc]
  have t451 : tickNatural program (state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false,.pair (next+6) (next+4),.pair (next+7) (next+4),.pair (next+5) (next+1)]) (next+10) (next+8) (next+5) (next+9) (next+4) [] source 451)=
      some ⟨state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false,.pair (next+6) (next+4),.pair (next+7) (next+4),.pair (next+5) (next+1)]) (next+10) (next+8) (next+1) (next+9) (next+4) [] source 452,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hn]
  have t452 : tickNatural program (state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false,.pair (next+6) (next+4),.pair (next+7) (next+4),.pair (next+5) (next+1)]) (next+10) (next+8) (next+1) (next+9) (next+4) [] source 452)=
      some ⟨state (heap++[.pair b c,.pair a next,.nil,.flag true,.pair (next+3) (next+2),.pair (next+4) (next+4),.flag false,.pair (next+6) (next+4),.pair (next+7) (next+4),.pair (next+5) (next+1)]) (next+10) (next+8) a (next+9) (next+4) [] source 453,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hn]
  simpa [constants] using (show NaturalRun program 13 _ [] _ from .step t440 (.step t441 (.step t442 (.step t443 (.step t444 (.step t445 (.step t446 (.step t447 (.step t448 (.step t449 (.step t450 (.step t451 (.step t452 (.done _))))))))))))))

theorem constants_rep (heap : NaturalHeap) (next a b c : ℕ) (hn : next=heap.length) :
    Stored (heap++constants next a b c) (next+5) one ∧
    Stored (heap++constants next a b c) (next+8) two := by
  let h := heap++constants next a b c
  have nil : h[next+2]?=some .nil := by simp [h,constants,hn]
  have bt : h[next+3]?=some (.flag true) := by simp [h,constants,hn]
  have bf : h[next+6]?=some (.flag false) := by simp [h,constants,hn]
  have ow : BoolList h (next+4) [true] := .cons (by simp [h,constants,hn]) bt (.nil nil)
  have tw : BoolList h (next+7) [false,true] := .cons (by simp [h,constants,hn]) bf ow
  exact ⟨⟨next+4,next+4,by simp [constants,hn],ow,ow⟩,
    ⟨next+7,next+4,by simp [constants,hn],tw,ow⟩⟩
end DirectedFlowCutGap.PackingEntry
