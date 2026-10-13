import DirectedFlowCutGap.PackingParametersQuotientCall

namespace DirectedFlowCutGap.PackingParameters
open BinaryArithmetic BinaryRational BinaryFractionalRows ImmutableReferenceSimulation PackedBooleanConstructor
open BooleanTableRead (BoolList)
open RationalComparisonProgram (Stored)

set_option maxRecDepth 10000 in
theorem three_prefix (heap : NaturalHeap) (next a b c d : ℕ) (dense : next=heap.length) (source : Bits) :
    let ext : NaturalHeap := [.nil,.flag true,.pair (next+1) next,.pair (next+1) (next+2)]
    NaturalRun program 4 (state heap next a b c d [] source 313) []
      (state (heap++ext) (next+4) (next+3) b c (next+1) [] source 317) ∧
    BoolList (heap++ext) (next+3) [true,true] := by
  dsimp only
  constructor
  · have t0 : tickNatural program (state heap next a b c d [] source 313)=
        some ⟨state (heap++[.nil]) (next+1) next b c d [] source 314,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set]
    have t1 : tickNatural program (state (heap++[.nil]) (next+1) next b c d [] source 314)=
        some ⟨state (heap++[.nil,.flag true]) (next+2) next b c (next+1) [] source 315,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,List.append_assoc,Nat.add_assoc]
    have t2 : tickNatural program (state (heap++[.nil,.flag true]) (next+2) next b c (next+1) [] source 315)=
        some ⟨state (heap++[.nil,.flag true,.pair (next+1) next]) (next+3) (next+2) b c (next+1) [] source 316,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,List.append_assoc,Nat.add_assoc]
    have t3 : tickNatural program (state (heap++[.nil,.flag true,.pair (next+1) next]) (next+3) (next+2) b c (next+1) [] source 316)=
        some ⟨state (heap++[.nil,.flag true,.pair (next+1) next,.pair (next+1) (next+2)]) (next+4) (next+3) b c (next+1) [] source 317,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,List.append_assoc,Nat.add_assoc]
    exact .step t0 (.step t1 (.step t2 (.step t3 (.done _))))
  · exact .cons (head:=next+1) (tail:=next+2) (by simp [dense]) (by simp [dense])
      (.cons (head:=next+1) (tail:=next) (by simp [dense]) (by simp [dense]) (.nil (by simp [dense])))

set_option maxRecDepth 10000 in
theorem two_prefix {heap : NaturalHeap} {fuelRoot : ℕ} {fuel : Bits} (stored : BoolList heap fuelRoot fuel)
    (next a b c : ℕ) (dense : next=heap.length) (source : Bits) :
    let ext : NaturalHeap := [.nil,.flag true,.pair (next+1) next,.pair fuelRoot (next+2),
      .flag false,.pair (next+4) (next+2),.pair (next+5) (next+2)]
    NaturalRun program 8 (state heap next a b c fuelRoot [] source 318) []
      (state (heap++ext) (next+7) (next+6) (next+3) fuelRoot (next+5) [] source 326) ∧
    Stored (heap++ext) (next+6) two ∧ Stored (heap++ext) (next+3) (BinaryFractionalCore.naturalFraction fuel) := by
  let e : NaturalHeap := [.nil,.flag true,.pair (next+1) next,.pair fuelRoot (next+2),
      .flag false,.pair (next+4) (next+2),.pair (next+5) (next+2)]
  change NaturalRun program 8 _ [] _ ∧ Stored (heap++e) (next+6) two ∧ Stored (heap++e) (next+3) _
  have oneBits : BoolList (heap++e) (next+2) [true] :=
    .cons (head:=next+1) (tail:=next) (by simp [e,dense]) (by simp [e,dense]) (.nil (by simp [e,dense]))
  have twoBits : BoolList (heap++e) (next+5) [false,true] :=
    .cons (head:=next+4) (tail:=next+2) (by simp [e,dense]) (by simp [e,dense]) oneBits
  refine ⟨?_,⟨next+5,next+2,by simp [e,dense],twoBits,oneBits⟩,
    ⟨fuelRoot,next+2,by simp [e,dense],boolList_extend stored e,oneBits⟩⟩
  have t0 : tickNatural program (state heap next a b c fuelRoot [] source 318)=
      some ⟨state (heap++e.take 1) (next+1) next b c fuelRoot [] source 319,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,e]
  have t1 : tickNatural program (state (heap++e.take 1) (next+1) next b c fuelRoot [] source 319)=
      some ⟨state (heap++e.take 2) (next+2) next (next+1) c fuelRoot [] source 320,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,e,List.append_assoc,Nat.add_assoc]
  have t2 : tickNatural program (state (heap++e.take 2) (next+2) next (next+1) c fuelRoot [] source 320)=
      some ⟨state (heap++e.take 3) (next+3) (next+2) (next+1) c fuelRoot [] source 321,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,e,List.append_assoc,Nat.add_assoc]
  have t3 : tickNatural program (state (heap++e.take 3) (next+3) (next+2) (next+1) c fuelRoot [] source 321)=
      some ⟨state (heap++e.take 4) (next+4) (next+2) (next+3) c fuelRoot [] source 322,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,e,List.append_assoc,Nat.add_assoc]
  have t4 : tickNatural program (state (heap++e.take 4) (next+4) (next+2) (next+3) c fuelRoot [] source 322)=
      some ⟨state (heap++e.take 4) (next+4) (next+2) (next+3) fuelRoot fuelRoot [] source 323,[],0⟩ := by
    simp [program,tickNatural,state,Registers.set,Registers.get]
  have t5 : tickNatural program (state (heap++e.take 4) (next+4) (next+2) (next+3) fuelRoot fuelRoot [] source 323)=
      some ⟨state (heap++e.take 5) (next+5) (next+2) (next+3) fuelRoot (next+4) [] source 324,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,e,List.append_assoc,Nat.add_assoc]
  have t6 : tickNatural program (state (heap++e.take 5) (next+5) (next+2) (next+3) fuelRoot (next+4) [] source 324)=
      some ⟨state (heap++e.take 6) (next+6) (next+2) (next+3) fuelRoot (next+5) [] source 325,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,e,List.append_assoc,Nat.add_assoc]
  have t7 : tickNatural program (state (heap++e.take 6) (next+6) (next+2) (next+3) fuelRoot (next+5) [] source 325)=
      some ⟨state (heap++e) (next+7) (next+6) (next+3) fuelRoot (next+5) [] source 326,[],0⟩ := by
    simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,e,List.append_assoc,Nat.add_assoc]
  exact .step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.done _))))))))
end DirectedFlowCutGap.PackingParameters
