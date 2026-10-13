import DirectedFlowCutGap.PackingLoadRowProgram

namespace DirectedFlowCutGap.PackingLoadRow
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

theorem entry_return (enabled : Bool) (amount y : Fraction) {heap : NaturalHeap} {a b c : ℕ}
    (weight : Stored heap a y) (amt : Stored heap b amount) (flag : heap[c]?=some (.flag enabled))
    (next d : ℕ) (hn : next=heap.length) (saved : Registers ℕ)
    (pc : Fin 200) (stack : List (Frame ℕ 200)) (source : Bits) :
    ∃ ext root,ext.length=PackingLoadEntry.cells enabled amount y ∧
      NaturalRun program (PackingLoadEntry.steps enabled amount y+1)
        (state heap next a b c d (⟨pc,.r0,saved⟩::stack) source 142) []
        (state (heap++ext) (next+ext.length) root saved.b saved.c saved.d stack source pc) ∧
      Stored (heap++ext) root (PackingLoadEntry.result enabled amount y) := by
  obtain ⟨ext,root,br,cr,len,high,rep⟩ := PackingLoadEntry.entry_high enabled amount y
    weight amt flag next d hn source
  have lifted := ReferenceProgramLabels.run label PackingLoadEntry.program program slots high
  have lifted := ReferenceProgramStack.run program (⟨pc,.r0,saved⟩::stack) lifted
  have body : NaturalRun program (PackingLoadEntry.steps enabled amount y)
      (state heap next a b c d (⟨pc,.r0,saved⟩::stack) source 142) []
      (state (heap++ext) (next+ext.length) a br cr root (⟨pc,.r0,saved⟩::stack) source 149) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramStack.state,label,state,PackingLoadEntry.state] using lifted
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) a br cr root (⟨pc,.r0,saved⟩::stack) source 149)=
      some ⟨state (heap++ext) (next+ext.length) root saved.b saved.c saved.d stack source pc,[],0⟩ := by
    simp [tickNatural,program,callable,PackingLoadEntry.program,state,Registers.get,Registers.set]
  exact ⟨ext,root,len,by simpa using run_append body (.step ret (.done _)),rep⟩

theorem head_high (enabled : Bool) (amount y : Fraction) {heap : NaturalHeap}
    {next a ctx c d ya yt mask mf mt ar : ℕ}
    (hy : heap[a]?=some (.pair ya yt)) (hx : heap[ctx]?=some (.pair mask ar))
    (hm : heap[mask]?=some (.pair mf mt)) (hf : heap[mf]?=some (.flag enabled))
    (weight : Stored heap ya y) (amt : Stored heap ar amount)
    (hn : next=heap.length) (stack : List (Frame ℕ 200)) (source : Bits) :
    ∃ ext root,ext.length=PackingLoadEntry.cells enabled amount y+1 ∧
      NaturalRun program (PackingLoadEntry.steps enabled amount y+8)
        (state heap next a ctx c d stack source 160) []
        (state (heap++ext) (next+ext.length) root ar mf next stack source 169) ∧
      Stored (heap++ext) root (PackingLoadEntry.result enabled amount y) ∧
      (heap++ext)[next]?=some (.pair a ctx) := by
  let e0 : NaturalHeap := [.pair a ctx]
  let h0 := heap++e0
  have hx0 : h0[ctx]?=some (.pair mask ar) := lookup_extend hx e0
  have hm0 : h0[mask]?=some (.pair mf mt) := lookup_extend hm e0
  have hy0 : h0[a]?=some (.pair ya yt) := lookup_extend hy e0
  have dense : next+1=h0.length := by simp [h0,e0,hn]
  obtain ⟨ee,re,le,entryRun,entryRep⟩ := entry_return enabled amount y
    (stored_extend weight e0) (stored_extend amt e0) (lookup_extend hf e0)
    (next+1) next dense ⟨ya,ar,mf,next⟩ 169 stack source
  have t160 : tickNatural program (state heap next a ctx c d stack source 160)=
      some ⟨state heap next a ctx c d stack source 163,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,tagBranch,hy]
  have t163 : tickNatural program (state heap next a ctx c d stack source 163)=
      some ⟨state h0 (next+1) a ctx c next stack source 164,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h0,e0]
  have t164 : tickNatural program (state h0 (next+1) a ctx c next stack source 164)=
      some ⟨state h0 (next+1) a ctx mask next stack source 165,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hx0]
  have t165 : tickNatural program (state h0 (next+1) a ctx mask next stack source 165)=
      some ⟨state h0 (next+1) a ctx mf next stack source 166,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hm0]
  have t166 : tickNatural program (state h0 (next+1) a ctx mf next stack source 166)=
      some ⟨state h0 (next+1) a ar mf next stack source 167,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hx0]
  have t167 : tickNatural program (state h0 (next+1) a ar mf next stack source 167)=
      some ⟨state h0 (next+1) ya ar mf next stack source 168,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hy0]
  have t168 : tickNatural program (state h0 (next+1) ya ar mf next stack source 168)=
      some ⟨state h0 (next+1) ya ar mf next (⟨169,.r0,⟨ya,ar,mf,next⟩⟩::stack) source 142,[],0⟩ := by
    simp [tickNatural,program,state]
  refine ⟨e0++ee,re,by simp [e0,le],?_,?_,?_⟩
  · have run := NaturalRun.step t160 (.step t163 (.step t164 (.step t165 (.step t166 (.step t167 (.step t168 entryRun))))))
    convert run using 1 <;> simp [e0,List.append_assoc,Nat.add_assoc,Nat.add_comm]
  · simpa [h0,List.append_assoc] using entryRep
  · have hcell : (heap++e0)[next]?=some (.pair a ctx) := by simp [e0,hn]
    simpa [List.append_assoc] using lookup_extend hcell ee
end DirectedFlowCutGap.PackingLoadRow
