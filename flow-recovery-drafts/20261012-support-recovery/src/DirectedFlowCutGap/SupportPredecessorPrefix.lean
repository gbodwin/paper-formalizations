import DirectedFlowCutGap.SupportAdjacencyTest

namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

/-- The nonempty predecessor branch allocates a literal query edge and calls
the actual adjacency-plus-membership program on the same retained heap. -/
theorem predecessor_prefix {heap : NaturalHeap} {a b head tail : ℕ} {x : Code} {u : Bits}
    {adjacency : List Bits} {es : List (Bits × Bits)}
    (hp : heap[a]?=some (.pair head tail)) (entry : StoredCode heap head x)
    (context : StoredPredContext heap b adjacency es u)
    (hi : value u<adjacency.length) (hj : value x.1<(adjacency[value u]).length)
    (next c d : ℕ) (hn : next=heap.length) (frames : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext flag contextRoot,ext.length=2+supportCells adjacency es u x.1 ∧
      NaturalRun program (supportSteps adjacency es u x.1+8)
        (state heap next a b c d frames source 170) []
        (state (heap++ext) (next+ext.length) (next+1) contextRoot next flag frames source 178) ∧
      (heap++ext)[next]?=some (.pair a b) ∧
      (heap++ext)[flag]?=some (.flag (support adjacency es u x.1)) := by
  obtain ⟨vertex,edges,he,hv,_⟩ := entry
  obtain ⟨ur,ctx,hctx,hu,hc⟩ := context
  let e0 : NaturalHeap := [.pair a b,.pair ur vertex]
  let h0 := heap++e0
  let n0 := next+2
  have dense : n0=h0.length := by simp [h0,n0,e0,hn]
  have query : Edge h0 (next+1) (u,x.1) :=
    ⟨ur,vertex,by simp [h0,e0,hn],boolList_extend hu e0,boolList_extend hv e0⟩
  obtain ⟨ext,flag,len,body,out⟩ := support_return query (supportContext_extend hc e0) hi hj
    n0 next ur dense ⟨next+1,ctx,next,ur⟩ 178 frames source
  have t170 : tickNatural program (state heap next a b c d frames source 170)=
      some ⟨state heap next a b c d frames source 171,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,hp,tagBranch]
  have t171 : tickNatural program (state heap next a b c d frames source 171)=
      some ⟨state (heap++[.pair a b]) (next+1) a b next d frames source 172,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
  have t172 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next d frames source 172)=
      some ⟨state (heap++[.pair a b]) (next+1) head b next d frames source 173,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp [.pair a b]]
  have t173 : tickNatural program (state (heap++[.pair a b]) (next+1) head b next d frames source 173)=
      some ⟨state (heap++[.pair a b]) (next+1) vertex b next d frames source 174,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend he [.pair a b]]
  have t174 : tickNatural program (state (heap++[.pair a b]) (next+1) vertex b next d frames source 174)=
      some ⟨state (heap++[.pair a b]) (next+1) vertex b next ur frames source 175,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hctx [.pair a b]]
  have t175 : tickNatural program (state (heap++[.pair a b]) (next+1) vertex b next ur frames source 175)=
      some ⟨state h0 n0 (next+1) b next ur frames source 176,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,h0,n0,e0,List.append_assoc]
  have t176 : tickNatural program (state h0 n0 (next+1) b next ur frames source 176)=
      some ⟨state h0 n0 (next+1) ctx next ur frames source 177,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,h0,lookup_extend hctx e0]
  have t177 : tickNatural program (state h0 n0 (next+1) ctx next ur frames source 177)=
      some ⟨state h0 n0 (next+1) ctx next ur
        (⟨178,.r3,⟨next+1,ctx,next,ur⟩⟩::frames) source 120,[],0⟩ := by
    simp [tickNatural,program,state]
  refine ⟨e0++ext,flag,ctx,by simp [e0,len];omega,?_,by simp [e0,hn],?_⟩
  · convert NaturalRun.step t170 (.step t171 (.step t172 (.step t173 (.step t174
      (.step t175 (.step t176 (.step t177 body))))))) using 1 <;>
      simp [h0,n0,e0,List.append_assoc,state]
    all_goals omega
  · simpa [h0,List.append_assoc] using out

end DirectedFlowCutGap.SupportRecoveryProgram
