import DirectedFlowCutGap.CostedSupportCalls

namespace DirectedFlowCutGap.CostedSupportProgram
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead PackedBooleanConstructor
open GraphWalkExtension RationalComparisonProgram

theorem cost_return {heap : NaturalHeap} {b edgeRoot : ℕ} {vs adjacency : List Bits}
    {support es : List (Bits×Bits)} {target sw : Bits} {rows : List Fraction}
    (context : Context heap b vs adjacency support target rows sw)
    (input : EdgeList heap edgeRoot es) (valid : ∀ w∈es.map Prod.fst,value w<rows.length)
    (next a c : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 592)
    (stack : List (Frame ℕ 592)) (source : Bits) :
    ∃ ext root,ext.length=es.length+MaterializedPathSum.cells rows sw (es.map Prod.fst)+2 ∧
      NaturalRun program (7*es.length+MaterializedPathSum.steps rows sw (es.map Prod.fst)+17)
        (state heap next a b c edgeRoot (⟨pc,.r3,saved⟩::stack) source 577) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      StoredWalk (heap++ext) root ⟨es,MaterializedPathSum.result rows sw (es.map Prod.fst)⟩ := by
  obtain ⟨searchRoot,costRoot,hctx,_,hcost⟩ := context
  let frames := (⟨pc,.r3,saved⟩::stack)
  let scratch : NaturalHeap := [.pair edgeRoot b]
  let h1 := heap++scratch
  let n1 := next+1
  have dense1 : n1=h1.length := by simp [n1,h1,scratch,hn]
  obtain ⟨ep,words,lp,proj,wordsRep⟩ := project_call (edgeList_extend input scratch)
    n1 b next edgeRoot dense1 ⟨edgeRoot,b,next,edgeRoot⟩ 583 frames source
  let h2 := h1++ep
  let n2 := n1+ep.length
  have dense2 : n2=h2.length := by simp [n2,h2,dense1]
  have costRep : OutgoingCostProgram.Context h2 costRoot rows sw :=
    PathCostMaterialization.context_extend (PathCostMaterialization.context_extend hcost scratch) ep
  obtain ⟨et,cost,lt,sum,sumRep⟩ := sum_call wordsRep costRep valid n2 next words dense2
    ⟨words,costRoot,next,words⟩ 587 frames source
  let h3 := h2++et
  let n3 := n2+et.length
  have dense3 : n3=h3.length := by simp [n3,h3,dense2]
  have hs1 : h1[next]?=some (.pair edgeRoot b) := by simp [h1,scratch,hn]
  have hs2 : h2[next]?=some (.pair edgeRoot b) := lookup_extend hs1 ep
  have hs3 : h3[next]?=some (.pair edgeRoot b) := lookup_extend hs2 et
  have hc2 : h2[b]?=some (.pair searchRoot costRoot) :=
    lookup_extend (lookup_extend hctx scratch) ep
  have t577 : tickNatural program (state heap next a b c edgeRoot frames source 577)=
      some ⟨state h1 n1 a b next edgeRoot frames source 578,[],0⟩ := by
    simp [tickNatural,program,state,h1,n1,scratch,allocateNatural,Recipe.cell,Registers.get,Registers.set]
  have t578 : tickNatural program (state h1 n1 a b next edgeRoot frames source 578)=
      some ⟨state h1 n1 edgeRoot b next edgeRoot frames source 579,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t579 : tickNatural program (state h1 n1 edgeRoot b next edgeRoot frames source 579)=
      some ⟨state h1 n1 edgeRoot b next edgeRoot (⟨583,.r3,⟨edgeRoot,b,next,edgeRoot⟩⟩::frames) source 290,[],0⟩ := by
    simp [tickNatural,program,state]
  have t583 : tickNatural program (state h2 n2 edgeRoot b next words frames source 583)=
      some ⟨state h2 n2 words b next words frames source 584,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t584 : tickNatural program (state h2 n2 words b next words frames source 584)=
      some ⟨state h2 n2 words b next words frames source 585,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hs2]
  have t585 : tickNatural program (state h2 n2 words b next words frames source 585)=
      some ⟨state h2 n2 words costRoot next words frames source 586,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hc2]
  have t586 : tickNatural program (state h2 n2 words costRoot next words frames source 586)=
      some ⟨state h2 n2 words costRoot next words (⟨587,.r3,⟨words,costRoot,next,words⟩⟩::frames) source 574,[],0⟩ := by
    simp [tickNatural,program,state]
  have t587 : tickNatural program (state h3 n3 words costRoot next cost frames source 587)=
      some ⟨state h3 n3 edgeRoot costRoot next cost frames source 588,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hs3]
  have t588 : tickNatural program (state h3 n3 edgeRoot costRoot next cost frames source 588)=
      some ⟨state (h3++[.pair edgeRoot cost]) (n3+1) edgeRoot costRoot next n3 frames source 589,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,allocateNatural,Recipe.cell]
  have t589 : tickNatural program (state (h3++[.pair edgeRoot cost]) (n3+1) edgeRoot costRoot next n3 frames source 589)=
      some ⟨state (h3++[.pair edgeRoot cost]) (n3+1) saved.a saved.b saved.c n3 stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,frames,Registers.get,Registers.set]
  have headRun : NaturalRun program 3 (state heap next a b c edgeRoot frames source 577) []
      (state h1 n1 edgeRoot b next edgeRoot (⟨583,.r3,⟨edgeRoot,b,next,edgeRoot⟩⟩::frames) source 290) :=
    .step t577 (.step t578 (.step t579 (.done _)))
  have middleRun : NaturalRun program 4 (state h2 n2 edgeRoot b next words frames source 583) []
      (state h2 n2 words costRoot next words (⟨587,.r3,⟨words,costRoot,next,words⟩⟩::frames) source 574) :=
    .step t583 (.step t584 (.step t585 (.step t586 (.done _))))
  have endRun : NaturalRun program 3 (state h3 n3 words costRoot next cost frames source 587) []
      (state (h3++[.pair edgeRoot cost]) (n3+1) saved.a saved.b saved.c n3 stack source pc) :=
    .step t587 (.step t588 (.step t589 (.done _)))
  let ext := scratch++ep++et++[.pair edgeRoot cost]
  refine ⟨ext,n3,by simp [ext,scratch,lp,lt];omega,?_,?_⟩
  · have all := run_append headRun (run_append proj (run_append middleRun (run_append sum endRun)))
    convert all using 1 <;> simp [ext,h3,h2,h1,n3,n2,n1,scratch,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm];omega
  · have cell : (h3++[.pair edgeRoot cost])[n3]?=some (.pair edgeRoot cost) := by rw [dense3];simp
    refine ⟨edgeRoot,cost,?_,edgeList_extend input ext,?_⟩
    · simpa only [ext,h3,h2,h1,List.append_assoc] using cell
    · simpa only [ext,h3,h2,h1,List.append_assoc] using stored_extend sumRep [.pair edgeRoot cost]

end DirectedFlowCutGap.CostedSupportProgram
