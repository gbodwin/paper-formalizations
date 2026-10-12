import DirectedFlowCutGap.CapacityCandidateStep

namespace DirectedFlowCutGap.CapacityBottleneck
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor RationalComparisonProgram

theorem collect_return {heap : NaturalHeap} {a b : ℕ} {xs : List Slot}
    (input : Input heap a b xs) (next c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 244) (stack : List (Frame ℕ 244)) (source : Bits) :
    ∃ ext root,ext.length=cells xs ∧ NaturalRun program (steps xs)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 200) []
      (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      RetainedArgminProgram.ItemList (heap++ext) root (items next xs) := by
  induction xs generalizing heap a b next c d saved pc stack with
  | nil =>
    obtain ⟨v,t,hc,hp⟩ := input
    cases hp with
    | nil hm hv ht =>
      let frames := (⟨pc,.r3,saved⟩::stack)
      have t200 : tickNatural program (state heap next a b c d frames source 200)=
          some ⟨state heap next a b c d frames source 201,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hm,tagBranch]
      have t201 : tickNatural program (state heap next a b c d frames source 201)=
          some ⟨state (heap++[.nil]) (next+1) a b c next frames source 202,[],0⟩ := by
        simp [tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
      have t202 : tickNatural program (state (heap++[.nil]) (next+1) a b c next frames source 202)=
          some ⟨state (heap++[.nil]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,frames,Registers.get,Registers.set]
      exact ⟨[.nil],next,rfl,.step t200 (.step t201 (.step t202 (.done _))),.nil (by simp [hn])⟩
  | cons x xs ih =>
    obtain ⟨v,t,hc,hp⟩ := input
    cases hp with
    | @cons _ _ _ f mt vt score tt _ _ hm hf hv hw ht hq tail =>
      let frames := (⟨pc,.r3,saved⟩::stack)
      let e0 : NaturalHeap := [.pair a b,.pair vt tt]
      have tailInput : Input (heap++e0) mt (next+1) xs :=
        ⟨vt,tt,by simp [e0,hn],parallel_extend tail e0⟩
      obtain ⟨et,rt,lt,tailRun,tailRep⟩ := ih tailInput (next+2) next vt
        (by simp [e0,hn]) ⟨mt,next+1,next,vt⟩ 211 frames
      let earlier := e0++et
      have hs : (heap++earlier)[next]?=some (.pair a b) := by simp [earlier,e0,hn]
      obtain ⟨eh,rh,lh,headRun,headRep⟩ := head_return hs (lookup_extend hc earlier)
        (lookup_extend hm earlier) (lookup_extend hf earlier) (lookup_extend hv earlier)
        (lookup_extend ht earlier) (stored_extend hq earlier)
        (by simpa [earlier,List.append_assoc] using tailRep)
        (next+2+et.length) mt (next+1) (by simp [earlier,e0,hn];omega) saved pc stack source
      have t200 : tickNatural program (state heap next a b c d frames source 200)=
          some ⟨state heap next a b c d frames source 203,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hm,tagBranch]
      have t203 : tickNatural program (state heap next a b c d frames source 203)=
          some ⟨state (heap++[.pair a b]) (next+1) a b next d frames source 204,[],0⟩ := by
        simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set]
      have t204 : tickNatural program (state (heap++[.pair a b]) (next+1) a b next d frames source 204)=
          some ⟨state (heap++[.pair a b]) (next+1) mt b next d frames source 205,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hm [.pair a b]]
      have t205 : tickNatural program (state (heap++[.pair a b]) (next+1) mt b next d frames source 205)=
          some ⟨state (heap++[.pair a b]) (next+1) mt b next v frames source 206,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hc [.pair a b]]
      have t206 : tickNatural program (state (heap++[.pair a b]) (next+1) mt b next v frames source 206)=
          some ⟨state (heap++[.pair a b]) (next+1) mt b next vt frames source 207,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hv [.pair a b]]
      have t207 : tickNatural program (state (heap++[.pair a b]) (next+1) mt b next vt frames source 207)=
          some ⟨state (heap++[.pair a b]) (next+1) mt t next vt frames source 208,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend hc [.pair a b]]
      have t208 : tickNatural program (state (heap++[.pair a b]) (next+1) mt t next vt frames source 208)=
          some ⟨state (heap++[.pair a b]) (next+1) mt tt next vt frames source 209,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,lookup_extend ht [.pair a b]]
      have t209 : tickNatural program (state (heap++[.pair a b]) (next+1) mt tt next vt frames source 209)=
          some ⟨state (heap++e0) (next+2) mt (next+1) next vt frames source 210,[],0⟩ := by
        simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.get,Registers.set,e0,List.append_assoc,Nat.add_assoc]
      have t210 : tickNatural program (state (heap++e0) (next+2) mt (next+1) next vt frames source 210)=
          some ⟨state (heap++e0) (next+2) mt (next+1) next vt
            (⟨211,.r3,⟨mt,next+1,next,vt⟩⟩::frames) source 200,[],0⟩ := by
        simp [tickNatural,program,state]
      refine ⟨e0++et++eh,rh,?_,?_,?_⟩
      · cases h : x.enabled <;> simp [cells,e0,lt,lh,h]
      · have all := NaturalRun.step t200 (.step t203 (.step t204 (.step t205 (.step t206
          (.step t207 (.step t208 (.step t209 (.step t210
          (run_append tailRun (by simpa [earlier,List.append_assoc] using headRun))))))))))
        cases h : x.enabled <;>
          convert all using 1 <;> simp [steps,e0,state,h] <;> omega
      · have eqItems : headItems (next+2+et.length) x (items (next+2) xs)=items next (x::xs) := by
          cases h : x.enabled <;> simp [headItems,items,h,lt,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm];omega
        simpa only [earlier,List.append_assoc,eqItems] using headRep

end DirectedFlowCutGap.CapacityBottleneck
