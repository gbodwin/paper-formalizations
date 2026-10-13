import DirectedFlowCutGap.AvoidingZeroContextTrace

namespace DirectedFlowCutGap.AvoidingZeroContext
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

def inputSteps (vs : List Bits) : ℕ := 5*vs.length+38

theorem construct {heap : NaturalHeap} {a b : ℕ} {vs adjacency : List Bits} {sw target : Bits}
    (vertices : GraphDiscoveryProgram.Vertices heap a vs) (metadata : Static heap b adjacency sw target)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 64)) (source : Bits) :
    ∃ ext root,ext.length=vs.length+14 ∧ NaturalRun program (inputSteps vs)
      (state heap next a b c d stack source 62) []
      (state (heap++ext) (next+ext.length) a b c root stack source 63) ∧
      GraphDiscoveryProgram.GlobalContext (heap++ext) root vs adjacency
        (List.replicate vs.length BinaryRational.zero) sw target := by
  obtain ⟨ext,root,len,run,rep⟩ := construct_return vertices metadata next c d hn ⟨a,b,c,d⟩ 63 stack source
  have call : tickNatural program (state heap next a b c d stack source 62)=
      some ⟨state heap next a b c d (⟨63,.r3,⟨a,b,c,d⟩⟩::stack) source 40,[],0⟩ := rfl
  exact ⟨ext,root,len,by simpa [inputSteps,Nat.add_assoc] using NaturalRun.step call run,rep⟩
end DirectedFlowCutGap.AvoidingZeroContext
