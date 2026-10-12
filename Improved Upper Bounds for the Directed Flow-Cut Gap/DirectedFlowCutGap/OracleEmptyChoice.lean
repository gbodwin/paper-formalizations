import DirectedFlowCutGap.OracleDefaultMask

namespace DirectedFlowCutGap.OracleChoice
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

/-- The actual no-selected-record branch traverses the stored enumeration and
constructs the whole singleton mask, retaining its first stored vertex word. -/
theorem empty_choice_return {heap : NaturalHeap} {a b vertices capacities : ℕ}
    {zero : Bits} {vs : List Bits} (ha : heap[a]?=some .nil)
    (hb : heap[b]?=some (.pair vertices capacities))
    (hv : GraphDiscoveryProgram.Vertices heap vertices (zero::vs))
    (next c d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 484) (stack : List (Frame ℕ 484)) (source : Bits) :
    ∃ ext root maskRoot wordRoot,ext.length=2*vs.length+5 ∧
      NaturalRun program (6*vs.length+14)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 410) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      (heap++ext)[root]?=some (.pair maskRoot wordRoot) ∧
      BoolList (heap++ext) maskRoot (true::List.replicate vs.length false) ∧
      BoolList (heap++ext) wordRoot zero := by
  cases hv with
  | @cons _ head tail _ _ hp hz ht =>
    let frame : Cell ℕ := .pair a b
    let h1 := heap++[frame]
    let frames := (⟨pc,.r3,saved⟩::stack)
    have hn1 : next+1=h1.length := by simp [h1,hn]
    have ht1 := GraphDiscoveryProgram.vertices_extend ht [frame]
    obtain ⟨et,rt,lt,body,rep⟩ := false_mask_return ht1 (next+1) head next d hn1
      ⟨tail,head,next,d⟩ 455 frames source
    let n1 := next+1+et.length
    have t410 : tickNatural program (state heap next a b c d frames source 410)=
        some ⟨state h1 (next+1) a b next d frames source 411,[],0⟩ := by
      simp [tickNatural,program,state,h1,frame,allocateNatural,Recipe.cell,Registers.get,Registers.set]
    have t411 : tickNatural program (state h1 (next+1) a b next d frames source 411)=
        some ⟨state h1 (next+1) a b next d frames source 450,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,lookup_extend ha [frame],h1]
    have t450 : tickNatural program (state h1 (next+1) a b next d frames source 450)=
        some ⟨state h1 (next+1) b b next d frames source 451,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,h1,frame,hn]
    have t451 : tickNatural program (state h1 (next+1) b b next d frames source 451)=
        some ⟨state h1 (next+1) vertices b next d frames source 452,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hb [frame],h1]
    have t452 : tickNatural program (state h1 (next+1) vertices b next d frames source 452)=
        some ⟨state h1 (next+1) vertices head next d frames source 453,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp [frame],h1]
    have t453 : tickNatural program (state h1 (next+1) vertices head next d frames source 453)=
        some ⟨state h1 (next+1) tail head next d frames source 454,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hp [frame],h1]
    have t454 : tickNatural program (state h1 (next+1) tail head next d frames source 454)=
        some ⟨state h1 (next+1) tail head next d
          (⟨455,.r3,⟨tail,head,next,d⟩⟩::frames) source 470,[],0⟩ := by
      simp [tickNatural,program,state]
    have t455 : tickNatural program (state (h1++et) n1 tail head next rt frames source 455)=
        some ⟨state ((h1++et)++[.flag true]) (n1+1) n1 head next rt frames source 456,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
    have t456 : tickNatural program (state ((h1++et)++[.flag true]) (n1+1) n1 head next rt frames source 456)=
        some ⟨state (((h1++et)++[.flag true])++[.pair n1 rt]) (n1+1+1)
          n1 head next (n1+1) frames source 457,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
    have t457 : tickNatural program
        (state (((h1++et)++[.flag true])++[.pair n1 rt]) (n1+1+1) n1 head next (n1+1) frames source 457)=
        some ⟨state ((((h1++et)++[.flag true])++[.pair n1 rt])++[.pair (n1+1) head])
          (n1+1+1+1) n1 head next (n1+1+1) frames source 458,[],0⟩ := by
      simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
    have t458 : tickNatural program
        (state ((((h1++et)++[.flag true])++[.pair n1 rt])++[.pair (n1+1) head])
          (n1+1+1+1) n1 head next (n1+1+1) frames source 458)=
        some ⟨state ((((h1++et)++[.flag true])++[.pair n1 rt])++[.pair (n1+1) head])
          (n1+1+1+1) saved.a saved.b saved.c (n1+1+1) stack source pc,[],0⟩ := by
      simp [tickNatural,program,state,frames,Registers.get,Registers.set]
    let ext : NaturalHeap := [frame]++et++[.flag true,.pair n1 rt,.pair (n1+1) head]
    have hd : n1=(h1++et).length := by simp [n1,h1,hn];omega
    have he : heap++ext=(h1++et)++[.flag true,.pair n1 rt,.pair (n1+1) head] := by
      simp [ext,h1,List.append_assoc]
    refine ⟨ext,n1+1+1,n1+1,head,by simp [ext,lt],?_,?_,?_,?_⟩
    · have all := NaturalRun.step t410 (.step t411 (.step t450 (.step t451 (.step t452
        (.step t453 (.step t454 (run_append body (.step t455 (.step t456 (.step t457 (.step t458 (.done _))))))))))))
      convert all using 1 <;> simp [ext,n1,h1,state,List.append_assoc]
      all_goals omega
    · rw [he,List.getElem?_append_right (show (h1++et).length≤n1+1+1 by omega)]
      have index : n1+1+1-(h1++et).length=2 := by omega
      rw [index]
      rfl
    · apply BoolList.cons (head:=n1) (tail:=rt)
      · rw [he,List.getElem?_append_right (show (h1++et).length≤n1+1 by omega)]
        have index : n1+1-(h1++et).length=1 := by omega
        rw [index]
        rfl
      · rw [he,List.getElem?_append_right (show (h1++et).length≤n1 by omega)]
        have index : n1-(h1++et).length=0 := by omega
        rw [index]
        rfl
      · simpa [ext,h1,List.append_assoc] using boolList_extend rep [.flag true,.pair n1 rt,.pair (n1+1) head]
    · exact boolList_extend hz ext

end DirectedFlowCutGap.OracleChoice
