import DirectedFlowCutGap.SupportEdgeMembership

namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem support_return {heap : NaturalHeap} {a b : ℕ} {u v : Bits}
    {adjacency : List Bits} {es : List (Bits × Bits)}
    (query : Edge heap a (u,v)) (context : SupportContext heap b adjacency es)
    (hi : value u<adjacency.length) (hj : value v<(adjacency[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=supportCells adjacency es u v ∧
      NaturalRun program (supportSteps adjacency es u v)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 120) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.flag (support adjacency es u v)) := by
  obtain ⟨ur,vr,hq,hu,hv⟩ := query
  obtain ⟨matrix,edges,hctx,hm,he⟩ := context
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e0 : NaturalHeap := [.pair a b,.pair matrix vr]
  let h0 := heap++e0
  let n0 := next+2
  have dense : n0=h0.length := by simp [n0,h0,e0,hn]
  have readctx : GraphAdjacencyProgram.Context h0 (next+1) adjacency v :=
    ⟨matrix,vr,by simp [h0,e0,hn],GraphAdjacencyProgram.matrix_extend hm e0,boolList_extend hv e0⟩
  obtain ⟨e1,flag,len1,read,htag⟩ := adjacency_return (boolList_extend hu e0) readctx hi hj
    n0 next vr dense ⟨ur,next+1,next,vr⟩ 126 frames source
  simp only [List.append_assoc] at htag
  have t120 : tickNatural program (state heap next a b c d frames source 120)=
      some ⟨state (heap++[.pair a b]) (next+1) a b next d frames source 121,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
  have t121 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next d frames source 121)=
      some ⟨state (heap++[.pair a b]) (next+1) a b next vr frames source 122,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hq [.pair a b]]
  have t122 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next vr frames source 122)=
      some ⟨state (heap++[.pair a b]) (next+1) ur b next vr frames source 123,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hq [.pair a b]]
  have t123 : tickNatural program (state (heap++[.pair a b]) (next+1) ur b next vr frames source 123)=
      some ⟨state (heap++[.pair a b]) (next+1) ur matrix next vr frames source 124,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hctx [.pair a b]]
  have t124 : tickNatural program (state (heap++[.pair a b]) (next+1) ur matrix next vr frames source 124)=
      some ⟨state h0 n0 ur (next+1) next vr frames source 125,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,h0,n0,e0,List.append_assoc]
  have t125 : tickNatural program (state h0 n0 ur (next+1) next vr frames source 125)=
      some ⟨state h0 n0 ur (next+1) next vr
        (⟨126,.r3,⟨ur,next+1,next,vr⟩⟩::frames) source 34,[],0⟩ := by
    simp [tickNatural,program,state]
  have preRun := NaturalRun.step t120 (.step t121 (.step t122 (.step t123 (.step t124 (.step t125 read)))))
  have branch : tickNatural program (state (h0++e1) (n0+e1.length) ur (next+1) next flag frames source 126)=
      some ⟨state (h0++e1) (n0+e1.length) ur (next+1) next flag frames source
        (if GraphRelaxationProgram.adjacent adjacency u v then 127 else 139),[],0⟩ := by
    cases ha : GraphRelaxationProgram.adjacent adjacency u v <;>
      simp [tickNatural,program,state,Registers.get,h0,htag,ha,tagBranch]
  by_cases ha : GraphRelaxationProgram.adjacent adjacency u v=true
  · have dense1 : n0+e1.length=(h0++e1).length := by simp [dense]
    obtain ⟨e2,root,len2,body,out⟩ := member_return
      (edgeList_extend (edgeList_extend he e0) e1)
      (edge_extend (edge_extend (show Edge heap a (u,v) from ⟨ur,vr,hq,hu,hv⟩) e0) e1)
      (n0+e1.length) next flag dense1 ⟨edges,a,next,flag⟩ 139 frames source
    have scratch : (h0++e1)[next]?=some (.pair a b) := by simp [h0,e0,hn]
    have storedctx : (h0++e1)[b]?=some (.pair matrix edges) := lookup_extend (lookup_extend hctx e0) e1
    have t127 : tickNatural program (state (h0++e1) (n0+e1.length) ur (next+1) next flag frames source 127)=
        some ⟨state (h0++e1) (n0+e1.length) b (next+1) next flag frames source 128,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t128 : tickNatural program (state (h0++e1) (n0+e1.length) b (next+1) next flag frames source 128)=
        some ⟨state (h0++e1) (n0+e1.length) edges (next+1) next flag frames source 129,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,storedctx]
    have t129 : tickNatural program (state (h0++e1) (n0+e1.length) edges (next+1) next flag frames source 129)=
        some ⟨state (h0++e1) (n0+e1.length) edges a next flag frames source 130,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
    have t130 : tickNatural program (state (h0++e1) (n0+e1.length) edges a next flag frames source 130)=
        some ⟨state (h0++e1) (n0+e1.length) edges a next flag
          (⟨139,.r3,⟨edges,a,next,flag⟩⟩::frames) source 90,[],0⟩ := by
      simp [tickNatural,program,state]
    have t139 : tickNatural program
        (state ((h0++e1)++e2) (n0+e1.length+e2.length) edges a next root frames source 139)=
        some ⟨state ((h0++e1)++e2) (n0+e1.length+e2.length)
          saved.a saved.b saved.c root stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    simp only [ha,ite_true] at branch
    refine ⟨e0++e1++e2,root,by simp [supportCells,ha,e0,len1,len2];omega,?_,?_⟩
    · convert run_append preRun (.step branch (.step t127 (.step t128 (.step t129 (.step t130
        (run_append body (.step t139 (.done _)))))))) using 1 <;>
        simp [supportSteps,ha,h0,n0,e0,List.append_assoc,state]
      all_goals omega
    · simpa [support,ha,h0,List.append_assoc] using out
  · have ret : tickNatural program (state (h0++e1) (n0+e1.length) ur (next+1) next flag frames source 139)=
        some ⟨state (h0++e1) (n0+e1.length) saved.a saved.b saved.c flag stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    simp only [ha] at branch
    refine ⟨e0++e1,flag,by simp [supportCells,ha,e0,len1],?_,?_⟩
    · convert run_append preRun (.step branch (.step ret (.done _))) using 1 <;>
        simp [supportSteps,ha,h0,n0,e0,List.append_assoc,state]
      all_goals omega
    · simpa [support,ha,h0,List.append_assoc] using htag

end DirectedFlowCutGap.SupportRecoveryProgram
