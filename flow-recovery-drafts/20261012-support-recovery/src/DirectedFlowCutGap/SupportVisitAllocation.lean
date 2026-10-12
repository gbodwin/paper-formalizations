import DirectedFlowCutGap.SupportPredecessorScan
import DirectedFlowCutGap.SupportCodeLookup

namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem keep_return {heap : NaturalHeap} {p ur ctx : ℕ} {adjacency : List Bits}
    {es : List (Bits × Bits)} {xs : List Code}
    (scratch : heap[p]?=some (.pair ur ctx)) (context : StoredVisitContext heap ctx adjacency es xs)
    (next a b d : ℕ) (saved : Registers ℕ) (pc : Fin 280) (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ root,NaturalRun program 3 (state heap next a b p d (⟨pc,.r3,saved⟩::stack) source 215) []
      (state heap next saved.a saved.b saved.c root stack source pc) ∧ Codes heap root xs := by
  obtain ⟨table,support,hctx,ht,_⟩ := context
  let frames := (⟨pc,.r3,saved⟩::stack)
  have t215 : tickNatural program (state heap next a b p d frames source 215)=
      some ⟨state heap next a b p ctx frames source 216,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
  have t216 : tickNatural program (state heap next a b p ctx frames source 216)=
      some ⟨state heap next a b p table frames source 217,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hctx]
  have t217 : tickNatural program (state heap next a b p table frames source 217)=
      some ⟨state heap next saved.a saved.b saved.c table stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  exact ⟨table,.step t215 (.step t216 (.step t217 (.done _))),ht⟩

theorem prepend_return {heap : NaturalHeap} {p ur ctx pred : ℕ} {adjacency : List Bits}
    {es : List (Bits × Bits)} {u : Bits} {xs : List Code} {x : Code}
    (scratch : heap[p]?=some (.pair ur ctx)) (word : BoolList heap ur u)
    (context : StoredVisitContext heap ctx adjacency es xs) (predecessor : StoredCode heap pred x)
    (next a b : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=4 ∧ NaturalRun program 10
      (state heap next a b p pred (⟨pc,.r3,saved⟩::stack) source 203) []
      (state (heap++ext) (next+4) saved.a saved.b saved.c root stack source pc) ∧
      Codes (heap++ext) root ((u,(u,x.1)::x.2)::xs) := by
  obtain ⟨table,support,hctx,ht,_⟩ := context
  obtain ⟨xv,xe,hpred,hxv,hxe⟩ := predecessor
  let frames := (⟨pc,.r3,saved⟩::stack)
  let e1 : NaturalHeap := [.pair ur xv]
  let e2 : NaturalHeap := e1++[.pair next xe]
  let e3 : NaturalHeap := e2++[.pair ur (next+1)]
  let ext : NaturalHeap := e3++[.pair (next+2) table]
  have t203 : tickNatural program (state heap next a b p pred frames source 203)=
      some ⟨state heap next ur b p pred frames source 204,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,scratch]
  have t204 : tickNatural program (state heap next ur b p pred frames source 204)=
      some ⟨state heap next ur xv p pred frames source 205,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hpred]
  have t205 : tickNatural program (state heap next ur xv p pred frames source 205)=
      some ⟨state (heap++e1) (next+1) ur next p pred frames source 206,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,e1]
  have t206 : tickNatural program (state (heap++e1) (next+1) ur next p pred frames source 206)=
      some ⟨state (heap++e1) (next+1) ur next p xe frames source 207,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hpred e1]
  have t207 : tickNatural program (state (heap++e1) (next+1) ur next p xe frames source 207)=
      some ⟨state (heap++e2) (next+2) ur next p (next+1) frames source 208,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,e2,List.append_assoc]
  have t208 : tickNatural program (state (heap++e2) (next+2) ur next p (next+1) frames source 208)=
      some ⟨state (heap++e3) (next+3) (next+2) next p (next+1) frames source 209,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,e3,List.append_assoc]
  have t209 : tickNatural program (state (heap++e3) (next+3) (next+2) next p (next+1) frames source 209)=
      some ⟨state (heap++e3) (next+3) (next+2) ctx p (next+1) frames source 210,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend scratch e3]
  have t210 : tickNatural program (state (heap++e3) (next+3) (next+2) ctx p (next+1) frames source 210)=
      some ⟨state (heap++e3) (next+3) (next+2) table p (next+1) frames source 211,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hctx e3]
  have t211 : tickNatural program (state (heap++e3) (next+3) (next+2) table p (next+1) frames source 211)=
      some ⟨state (heap++ext) (next+4) (next+2) table p (next+3) frames source 212,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,ext,List.append_assoc]
  have t212 : tickNatural program (state (heap++ext) (next+4) (next+2) table p (next+3) frames source 212)=
      some ⟨state (heap++ext) (next+4) saved.a saved.b saved.c (next+3) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨ext,next+3,by simp [ext,e3,e2,e1],?_,?_⟩
  · exact .step t203 (.step t204 (.step t205 (.step t206 (.step t207 (.step t208
      (.step t209 (.step t210 (.step t211 (.step t212 (.done _))))))))))
  · refine .cons (head:=next+2) (tail:=table) ?_
      ⟨ur,next+1,?_,boolList_extend word ext,.cons (head:=next) (tail:=xe) ?_
        ⟨ur,xv,?_,boolList_extend word ext,boolList_extend hxv ext⟩ (edgeList_extend hxe ext)⟩
      (codes_extend ht ext) <;> simp [ext,e3,e2,e1,hn]

end DirectedFlowCutGap.SupportRecoveryProgram
