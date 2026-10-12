import DirectedFlowCutGap.SupportRounds

namespace DirectedFlowCutGap.SupportRecoveryProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor GraphWalkExtension

def foundEdges : Option Code → List (Bits×Bits) | none => [] | some x => x.2

theorem extract_return {heap : NaturalHeap} {d : ℕ} {x : Option Code}
    (rep : StoredOption heap d x) (next a b c : ℕ) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ root,NaturalRun program (extractSteps x)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 264) []
      (state heap next saved.a saved.b saved.c root stack source pc) ∧
      EdgeList heap root (foundEdges x) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  cases x with
  | none =>
    change heap[d]?=some .nil at rep
    have t264 : tickNatural program (state heap next a b c d frames source 264)=
        some ⟨state heap next a b c d frames source 265,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,rep,tagBranch]
    have t265 : tickNatural program (state heap next a b c d frames source 265)=
        some ⟨state heap next saved.a saved.b saved.c d stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    exact ⟨d,.step t264 (.step t265 (.done _)),.nil rep⟩
  | some x =>
    obtain ⟨vertex,edges,hp,_,he⟩ := rep
    have t264 : tickNatural program (state heap next a b c d frames source 264)=
        some ⟨state heap next a b c d frames source 267,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hp,tagBranch]
    have t267 : tickNatural program (state heap next a b c d frames source 267)=
        some ⟨state heap next a b c edges frames source 268,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hp]
    have t268 : tickNatural program (state heap next a b c edges frames source 268)=
        some ⟨state heap next saved.a saved.b saved.c edges stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    exact ⟨edges,.step t264 (.step t267 (.step t268 (.done _))),he⟩

theorem search_return {heap : NaturalHeap} {a b c : ℕ} {vs adjacency : List Bits}
    {es : List (Bits×Bits)} {sw target : Bits} (N : ℕ)
    (vertices : Vertices heap a vs) (context : StoredGlobalContext heap b vs adjacency es target)
    (sourceWord : BoolList heap c sw) (rows : N≤adjacency.length)
    (cols : ∀ (i : ℕ) (hi : i<N), N≤(adjacency[i]'(lt_of_lt_of_le hi rows)).length)
    (hv : ∀ u∈vs,value u<N) (ht : value target<N)
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 280)
    (stack : List (Frame ℕ 280)) (source : Bits) :
    ∃ ext root,ext.length=searchCells vs adjacency es sw target ∧
      NaturalRun program (searchSteps vs adjacency es sw target)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 260) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      EdgeList (heap++ext) root (search vs adjacency es sw target) := by
  let frames := (⟨pc,.r3,saved⟩::stack)
  obtain ⟨e1,table,len1,roundRun,tableRep⟩ := rounds_return N vertices context rows cols hv ht
    next c d hn ⟨a,b,c,d⟩ 261 frames source
  obtain ⟨e2,found,len2,lookRun,foundRep⟩ := lookup_return tableRep (boolList_extend sourceWord e1)
    (next+e1.length) c table (by simp [hn]) ⟨table,c,c,table⟩ 264 frames source
  obtain ⟨root,tail,rep⟩ := extract_return foundRep (next+e1.length+e2.length)
    table c c saved pc stack source
  have t260 : tickNatural program (state heap next a b c d frames source 260)=
      some ⟨state heap next a b c d (⟨261,.r3,⟨a,b,c,d⟩⟩::frames) source 240,[],0⟩ := by
    simp [tickNatural,program,state]
  have t261 : tickNatural program (state (heap++e1) (next+e1.length) a b c table frames source 261)=
      some ⟨state (heap++e1) (next+e1.length) table b c table frames source 262,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t262 : tickNatural program (state (heap++e1) (next+e1.length) table b c table frames source 262)=
      some ⟨state (heap++e1) (next+e1.length) table c c table frames source 263,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t263 : tickNatural program (state (heap++e1) (next+e1.length) table c c table frames source 263)=
      some ⟨state (heap++e1) (next+e1.length) table c c table
        (⟨264,.r3,⟨table,c,c,table⟩⟩::frames) source 150,[],0⟩ := by
    simp [tickNatural,program,state]
  refine ⟨e1++e2,root,by simp [searchCells,len1,len2],?_,?_⟩
  · convert (NaturalRun.step t260 (run_append roundRun (.step t261 (.step t262 (.step t263
      (run_append lookRun tail)))))) using 1 <;>
      simp [searchSteps,List.append_assoc,state]
    all_goals omega
  · cases pick : lookup sw (rounds vs adjacency es target vs) <;>
      simpa [search,foundEdges,pick,List.append_assoc] using rep

end DirectedFlowCutGap.SupportRecoveryProgram
