import DirectedFlowCutGap.RowVertexScan
import DirectedFlowCutGap.HeapWordReverse

namespace DirectedFlowCutGap.VertexListReverse
open BinaryArithmetic ImmutableReferenceSimulation PackedBooleanConstructor
open BooleanTableRead (BoolList)
open GraphDiscoveryProgram (Vertices vertices_extend)
open HeapWordReverse (program state)

theorem loop (word : List Bits) {heap : NaturalHeap} {a b : ℕ} {acc : List Bits}
    (rep : Vertices heap a word) (accRep : Vertices heap b acc)
    (next c d : ℕ) (hn : next=heap.length) (stack : List (Frame ℕ 6)) (source : Bits) :
    ∃ out, NaturalRun program (4*word.length+1) (state heap next a b c d stack source 1) [] out ∧
      Vertices out.heap out.registers.b (word.reverse++acc) ∧
      (∃ extra,out.heap=heap++extra ∧ extra.length=word.length) ∧
      out.next=out.heap.length ∧ out.stack=stack ∧ out.source=source ∧ out.pc=5 := by
  induction word generalizing heap a b acc next c with
  | nil =>
      cases rep with
      | nil h =>
          refine ⟨state heap next a b c d stack source 5,?_,?_,⟨[],by simp [state],by simp⟩,hn,rfl,rfl,rfl⟩
          · have ht : tickNatural program (state heap next a b c d stack source 1)=
                some ⟨state heap next a b c d stack source 5,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,h,tagBranch]
            simpa using NaturalRun.step ht (NaturalRun.done _)
          · simpa [state] using accRep
  | cons bit bits ih =>
      cases rep with
      | @cons _ flag tail _ _ hp hf hr =>
          let heap' := heap++[Cell.pair flag b]
          have hc : heap'[next]?=some (.pair flag b) := by simp [heap',hn]
          have ap : Vertices heap' next (bit::acc) :=
            .cons hc (boolList_extend hf _) (vertices_extend accRep _)
          have rp : Vertices heap' tail bits := vertices_extend hr _
          have hn' : next+1=heap'.length := by simp [heap',hn]
          obtain ⟨out,run,represented,⟨extra,he,hlen⟩,dense,frames,src,pc⟩ :=
            ih rp ap (next+1) flag hn'
          refine ⟨out,?_,?_,⟨Cell.pair flag b::extra,?_,?_⟩,dense,frames,src,pc⟩
          · have t1 : tickNatural program (state heap next a b c d stack source 1)=
                some ⟨state heap next a b c d stack source 2,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,hp,tagBranch]
            have t2 : tickNatural program (state heap next a b c d stack source 2)=
                some ⟨state heap next a b flag d stack source 3,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,Registers.set,hp]
            have t3 : tickNatural program (state heap next a b flag d stack source 3)=
                some ⟨state heap' (next+1) a next flag d stack source 4,[],0⟩ := by
              simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,heap']
            have t4 : tickNatural program (state heap' (next+1) a next flag d stack source 4)=
                some ⟨state heap' (next+1) tail next flag d stack source 1,[],0⟩ := by
              have hp' : heap'[a]?=some (.pair flag tail) := lookup_extend hp [Cell.pair flag b]
              simp [tickNatural,program,state,Registers.get,Registers.set,hp']
            simpa [Nat.mul_add,Nat.add_assoc] using
              NaturalRun.step t1 (NaturalRun.step t2 (NaturalRun.step t3 (NaturalRun.step t4 run)))
          · simpa [List.reverse_cons,List.append_assoc] using represented
          · simpa [heap',List.append_assoc] using he
          · simp [hlen]

theorem reverse_high {word : List Bits} (initial : NaturalState 6) (pc0 : initial.pc=0)
    (hn : initial.next=initial.heap.length)
    (rep : Vertices initial.heap initial.registers.a word) :
    ∃ out, NaturalRun program (4*word.length+2) initial [] out ∧
      Vertices out.heap out.registers.b word.reverse ∧
      (∃ extra,out.heap=initial.heap++extra ∧ extra.length=word.length+1) ∧
      out.next=out.heap.length ∧ out.stack=initial.stack ∧ out.source=initial.source ∧
      out.pc=5 ∧ tickNatural program out=none := by
  cases initial with
  | mk heap next regs stack pc source =>
      cases regs with
      | mk a b c d =>
          simp only at hn pc0 rep
          subst pc
          have nilRep : Vertices (heap++[Cell.nil]) next [] := .nil (by simp [hn])
          have rep' := vertices_extend rep [Cell.nil]
          obtain ⟨out,run,represented,⟨extra,he,hlen⟩,dense,frames,src,pc⟩ :=
            loop word rep' nilRep (next+1) c d (by simp [hn]) stack source
          refine ⟨out,?_,?_,⟨Cell.nil::extra,?_,?_⟩,dense,frames,src,pc,?_⟩
          · have ht : tickNatural program (state heap next a b c d stack source 0)=
                some ⟨state (heap++[Cell.nil]) (next+1) a next c d stack source 1,[],0⟩ := by
              simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
            simpa [state,Nat.add_assoc] using NaturalRun.step ht run
          · simpa using represented
          · simpa [List.append_assoc] using he
          · simp [hlen]
          · simp [tickNatural,pc,program]

end DirectedFlowCutGap.VertexListReverse
