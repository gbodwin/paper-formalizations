import DirectedFlowCutGap.SupportForwardPass

namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

theorem initial_return {heap : NaturalHeap} {a b : ℕ} {vs adjacency : List Bits}
    {es : List (Bits × Bits)} {target : Bits} (nil : heap[a]?=some .nil)
    (context : StoredGlobalContext heap b vs adjacency es target)
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=3 ∧ NaturalRun program 6
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 240) []
      (state (heap++ext) (next+3) saved.a saved.b saved.c root stack source pc) ∧
      Codes (heap++ext) root [(target,[])] := by
  obtain ⟨tr,bundle,vertices,ctx,hb,_,ht,_,_⟩ := context
  let ext : NaturalHeap := [.nil,.pair tr next,.pair (next+1) next]
  let frames := (⟨pc,.r3,saved⟩::stack)
  have t240 : tickNatural program (state heap next a b c d frames source 240)=
      some ⟨state heap next a b c d frames source 241,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,nil,tagBranch]
  have t241 : tickNatural program (state heap next a b c d frames source 241)=
      some ⟨state (heap++[.nil]) (next+1) a b c next frames source 242,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
  have t242 : tickNatural program (state (heap++[.nil]) (next+1) a b c next frames source 242)=
      some ⟨state (heap++[.nil]) (next+1) tr b c next frames source 243,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hb [.nil]]
  have t243 : tickNatural program (state (heap++[.nil]) (next+1) tr b c next frames source 243)=
      some ⟨state (heap++[.nil,.pair tr next]) (next+2) (next+1) b c next frames source 244,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,List.append_assoc]
  have t244 : tickNatural program (state (heap++[.nil,.pair tr next]) (next+2) (next+1) b c next frames source 244)=
      some ⟨state (heap++ext) (next+3) (next+1) b c (next+2) frames source 245,[],0⟩ := by
    simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,List.append_assoc,ext]
  have t245 : tickNatural program (state (heap++ext) (next+3) (next+1) b c (next+2) frames source 245)=
      some ⟨state (heap++ext) (next+3) saved.a saved.b saved.c (next+2) stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  refine ⟨ext,next+2,rfl,.step t240 (.step t241 (.step t242 (.step t243 (.step t244 (.step t245 (.done _)))))),?_⟩
  exact .cons (head:=next+1) (tail:=next) (by simp [ext,hn]) ⟨tr,next,by simp [ext,hn],boolList_extend ht ext,.nil (by simp [ext,hn])⟩
    (.nil (by simp [ext,hn]))

end DirectedFlowCutGap.SupportRecoveryProgram
