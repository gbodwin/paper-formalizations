import DirectedFlowCutGap.GridFuelCalls

namespace DirectedFlowCutGap.GridFuelProgram
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead

def twoCells (next : ℕ) : NaturalHeap :=
  [.nil,.flag true,.pair (next+1) next,.flag false,.pair (next+3) (next+2)]
def threeCells (next : ℕ) : NaturalHeap :=
  [.nil,.flag true,.pair (next+1) next,.pair (next+1) (next+2)]

set_option maxRecDepth 10000 in
theorem two_prefix (heap : NaturalHeap) (next a b c d : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 256)) (source : Bits) :
    NaturalRun program 5 (state heap next a b c d stack source 203) []
      (state (heap++twoCells next) (next+5) (next+4) b c (next+3) stack source 208) ∧
    BoolList (heap++twoCells next) (next+4) [false,true] := by
  constructor
  · have t0 : tickNatural program (state heap next a b c d stack source 203)=
        some ⟨state (heap++(twoCells next).take 1) (next+1) next b c d stack source 204,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,twoCells]
    have t1 : tickNatural program (state (heap++(twoCells next).take 1) (next+1) next b c d stack source 204)=
        some ⟨state (heap++(twoCells next).take 2) (next+2) next b c (next+1) stack source 205,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,twoCells,List.append_assoc,Nat.add_assoc]
    have t2 : tickNatural program (state (heap++(twoCells next).take 2) (next+2) next b c (next+1) stack source 205)=
        some ⟨state (heap++(twoCells next).take 3) (next+3) (next+2) b c (next+1) stack source 206,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,twoCells,List.append_assoc,Nat.add_assoc]
    have t3 : tickNatural program (state (heap++(twoCells next).take 3) (next+3) (next+2) b c (next+1) stack source 206)=
        some ⟨state (heap++(twoCells next).take 4) (next+4) (next+2) b c (next+3) stack source 207,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,twoCells,List.append_assoc,Nat.add_assoc]
    have t4 : tickNatural program (state (heap++(twoCells next).take 4) (next+4) (next+2) b c (next+3) stack source 207)=
        some ⟨state (heap++twoCells next) (next+5) (next+4) b c (next+3) stack source 208,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,twoCells,List.append_assoc,Nat.add_assoc]
    exact .step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.done _)))))
  · exact .cons (head:=next+3) (tail:=next+2) (by simp [twoCells,dense]) (by simp [twoCells,dense])
      (.cons (head:=next+1) (tail:=next) (by simp [twoCells,dense]) (by simp [twoCells,dense]) (.nil (by simp [twoCells,dense])))

set_option maxRecDepth 10000 in
theorem three_prefix (heap : NaturalHeap) (next a b c d : ℕ) (dense : next=heap.length)
    (stack : List (Frame ℕ 256)) (source : Bits) :
    NaturalRun program 4 (state heap next a b c d stack source 216) []
      (state (heap++threeCells next) (next+4) a (next+3) c (next+1) stack source 220) ∧
    BoolList (heap++threeCells next) (next+3) [true,true] := by
  constructor
  · have t0 : tickNatural program (state heap next a b c d stack source 216)=
        some ⟨state (heap++(threeCells next).take 1) (next+1) a next c d stack source 217,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,threeCells]
    have t1 : tickNatural program (state (heap++(threeCells next).take 1) (next+1) a next c d stack source 217)=
        some ⟨state (heap++(threeCells next).take 2) (next+2) a next c (next+1) stack source 218,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,threeCells,List.append_assoc,Nat.add_assoc]
    have t2 : tickNatural program (state (heap++(threeCells next).take 2) (next+2) a next c (next+1) stack source 218)=
        some ⟨state (heap++(threeCells next).take 3) (next+3) a (next+2) c (next+1) stack source 219,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,threeCells,List.append_assoc,Nat.add_assoc]
    have t3 : tickNatural program (state (heap++(threeCells next).take 3) (next+3) a (next+2) c (next+1) stack source 219)=
        some ⟨state (heap++threeCells next) (next+4) a (next+3) c (next+1) stack source 220,[],0⟩ := by
      simp [program,tickNatural,state,allocateNatural,Recipe.cell,Registers.set,Registers.get,threeCells,List.append_assoc,Nat.add_assoc]
    exact .step t0 (.step t1 (.step t2 (.step t3 (.done _))))
  · exact .cons (head:=next+1) (tail:=next+2) (by simp [threeCells,dense]) (by simp [threeCells,dense])
      (.cons (head:=next+1) (tail:=next) (by simp [threeCells,dense]) (by simp [threeCells,dense]) (.nil (by simp [threeCells,dense])))
end DirectedFlowCutGap.GridFuelProgram
