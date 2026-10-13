import DirectedFlowCutGap.AvoidingGraphContextTrace

namespace DirectedFlowCutGap.AvoidingGraphContext
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead

theorem construct {heap : NaturalHeap} {a b : ℕ} {vs adjacency : List Bits}
    {rows : List Fraction} {sw target : Bits}
    (vertices : GraphDiscoveryProgram.Vertices heap a vs) (context : Input heap b adjacency rows sw target)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 20)) (source : Bits) :
    ∃ ext root,ext.length=5 ∧ NaturalRun program 16
      (state heap next a b c d stack source 18) []
      (state (heap++ext) (next+ext.length) a b c root stack source 19) ∧
      GraphDiscoveryProgram.GlobalContext (heap++ext) root vs adjacency rows sw target := by
  obtain ⟨ext,root,len,run,rep⟩ := construct_return vertices context next c d hn ⟨a,b,c,d⟩ 19 stack source
  have call : tickNatural program (state heap next a b c d stack source 18)=
      some ⟨state heap next a b c d (⟨19,.r3,⟨a,b,c,d⟩⟩::stack) source 0,[],0⟩ := rfl
  exact ⟨ext,root,len,.step call run,rep⟩
end DirectedFlowCutGap.AvoidingGraphContext
