import DirectedFlowCutGap.KeptAdjacencyRowProgram

namespace DirectedFlowCutGap.KeptAdjacencyRow
open BinaryArithmetic ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor

def flagSteps (a keep : Bool) : ℕ := if a then if keep then 10 else 7 else 5

theorem flag_trace {heap : NaturalHeap} {a b ap tail kp ks kv kt : ℕ} {av ku vv : Bool}
    (ha : heap[a]?=some (.pair ap tail)) (hav : heap[ap]?=some (.flag av))
    (hb : heap[b]?=some (.pair kp ks)) (hku : heap[kp]?=some (.flag ku))
    (hks : heap[ks]?=some (.pair kv kt)) (hvv : heap[kv]?=some (.flag vv))
    (next c d : ℕ) (_hn : next=heap.length) (stack : List (Frame ℕ 36)) (source : Bits) :
    NaturalRun program (flagSteps av ku)
      (state heap next a b c d stack source 0) []
      (state (heap++[.pair a b,.flag (av && ku && vv)]) (next+2) a b next (next+1) stack source 17) := by
  have ha1 := lookup_extend ha [Cell.pair a b]
  have hav1 := lookup_extend hav [Cell.pair a b]
  have hb1 := lookup_extend hb [Cell.pair a b]
  have hku1 := lookup_extend hku [Cell.pair a b]
  have hks1 := lookup_extend hks [Cell.pair a b]
  have hvv1 := lookup_extend hvv [Cell.pair a b]
  cases av with
  | false =>
    have t0 : tickNatural program (state heap next a b c d stack source 0)=
        some ⟨(state heap next a b c d stack source 3),[],0⟩ := by simp [tickNatural,program,state,Registers.get,ha,tagBranch]
    have t3 : tickNatural program (state heap next a b c d stack source 3)=
        some ⟨(state (heap++[.pair a b]) (next+1) a b next d stack source 4),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
    have t4 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next d stack source 4)=
        some ⟨(state (heap++[.pair a b]) (next+1) a b next ap stack source 5),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,ha1]
    have t5 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next ap stack source 5)=
        some ⟨(state (heap++[.pair a b]) (next+1) a b next ap stack source 16),[],0⟩ := by simp [tickNatural,program,state,Registers.get,hav1,tagBranch]
    have t16 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next ap stack source 16)=
        some ⟨(state (heap++[.pair a b,.flag false]) (next+2) a b next (next+1) stack source 17),[],0⟩ := by simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell,List.append_assoc,Nat.add_assoc]
    exact (.step t0 (.step t3 (.step t4 (.step t5 (.step t16 (.done _))))))
  | true =>
    cases ku with
    | false =>
      have t0 : tickNatural program (state heap next a b c d stack source 0)=
          some ⟨(state heap next a b c d stack source 3),[],0⟩ := by simp [tickNatural,program,state,Registers.get,ha,tagBranch]
      have t3 : tickNatural program (state heap next a b c d stack source 3)=
          some ⟨(state (heap++[.pair a b]) (next+1) a b next d stack source 4),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
      have t4 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next d stack source 4)=
          some ⟨(state (heap++[.pair a b]) (next+1) a b next ap stack source 5),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,ha1]
      have t5 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next ap stack source 5)=
          some ⟨(state (heap++[.pair a b]) (next+1) a b next ap stack source 6),[],0⟩ := by simp [tickNatural,program,state,Registers.get,hav1,tagBranch]
      have t6 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next ap stack source 6)=
          some ⟨(state (heap++[.pair a b]) (next+1) a b next kp stack source 7),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
      have t7 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next kp stack source 7)=
          some ⟨(state (heap++[.pair a b]) (next+1) a b next kp stack source 16),[],0⟩ := by simp [tickNatural,program,state,Registers.get,hku1,tagBranch]
      have t16 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next kp stack source 16)=
          some ⟨(state (heap++[.pair a b,.flag false]) (next+2) a b next (next+1) stack source 17),[],0⟩ := by simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell,List.append_assoc,Nat.add_assoc]
      exact (.step t0 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t16 (.done _))))))))
    | true =>
      cases vv with
      | false =>
        have t0 : tickNatural program (state heap next a b c d stack source 0)=
            some ⟨(state heap next a b c d stack source 3),[],0⟩ := by simp [tickNatural,program,state,Registers.get,ha,tagBranch]
        have t3 : tickNatural program (state heap next a b c d stack source 3)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next d stack source 4),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
        have t4 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next d stack source 4)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next ap stack source 5),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,ha1]
        have t5 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next ap stack source 5)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next ap stack source 6),[],0⟩ := by simp [tickNatural,program,state,Registers.get,hav1,tagBranch]
        have t6 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next ap stack source 6)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next kp stack source 7),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
        have t7 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next kp stack source 7)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next kp stack source 8),[],0⟩ := by simp [tickNatural,program,state,Registers.get,hku1,tagBranch]
        have t8 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next kp stack source 8)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next ks stack source 9),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
        have t9 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next ks stack source 9)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next kv stack source 10),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hks1]
        have t10 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next kv stack source 10)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next kv stack source 16),[],0⟩ := by simp [tickNatural,program,state,Registers.get,hvv1,tagBranch]
        have t16 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next kv stack source 16)=
            some ⟨(state (heap++[.pair a b,.flag false]) (next+2) a b next (next+1) stack source 17),[],0⟩ := by simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell,List.append_assoc,Nat.add_assoc]
        exact (.step t0 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t16 (.done _)))))))))))
      | true =>
        have t0 : tickNatural program (state heap next a b c d stack source 0)=
            some ⟨(state heap next a b c d stack source 3),[],0⟩ := by simp [tickNatural,program,state,Registers.get,ha,tagBranch]
        have t3 : tickNatural program (state heap next a b c d stack source 3)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next d stack source 4),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
        have t4 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next d stack source 4)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next ap stack source 5),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,ha1]
        have t5 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next ap stack source 5)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next ap stack source 6),[],0⟩ := by simp [tickNatural,program,state,Registers.get,hav1,tagBranch]
        have t6 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next ap stack source 6)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next kp stack source 7),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
        have t7 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next kp stack source 7)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next kp stack source 8),[],0⟩ := by simp [tickNatural,program,state,Registers.get,hku1,tagBranch]
        have t8 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next kp stack source 8)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next ks stack source 9),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hb1]
        have t9 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next ks stack source 9)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next kv stack source 10),[],0⟩ := by simp [tickNatural,program,state,Registers.get,Registers.set,hks1]
        have t10 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next kv stack source 10)=
            some ⟨(state (heap++[.pair a b]) (next+1) a b next kv stack source 14),[],0⟩ := by simp [tickNatural,program,state,Registers.get,hvv1,tagBranch]
        have t14 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next kv stack source 14)=
            some ⟨(state (heap++[.pair a b,.flag true]) (next+2) a b next (next+1) stack source 17),[],0⟩ := by simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell,List.append_assoc,Nat.add_assoc]
        exact (.step t0 (.step t3 (.step t4 (.step t5 (.step t6 (.step t7 (.step t8 (.step t9 (.step t10 (.step t14 (.done _)))))))))))
end DirectedFlowCutGap.KeptAdjacencyRow
