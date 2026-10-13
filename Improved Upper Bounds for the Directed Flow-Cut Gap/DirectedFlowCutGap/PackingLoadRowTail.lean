import DirectedFlowCutGap.PackingLoadRowHead

namespace DirectedFlowCutGap.PackingLoadRow
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem tail_prepare {heap : NaturalHeap} {next head rb rc frame ctx a mask amount ya yt mf mt : ℕ}
    (hf : heap[frame]?=some (.pair a ctx))
    (hx : heap[ctx]?=some (.pair mask amount)) (hm : heap[mask]?=some (.pair mf mt))
    (hy : heap[a]?=some (.pair ya yt))
    (hn : next=heap.length) (stack : List (Frame ℕ 200)) (source : Bits) :
    NaturalRun program 10 (state heap next head rb rc frame stack source 169) []
      (state (heap++[.pair head frame,.pair mt amount]) (next+2) yt (next+1) frame next
        (⟨179,.r0,⟨yt,next+1,frame,next⟩⟩::stack) source 160) := by
  let h1 := heap++[.pair head frame]
  let h2 := h1++[.pair mt amount]
  have new1 : h1[next]?=some (.pair head frame) := by simp [h1,hn]
  have hf1 : h1[frame]?=some (.pair a ctx) := lookup_extend hf _
  have hx1 : h1[ctx]?=some (.pair mask amount) := lookup_extend hx _
  have hm1 : h1[mask]?=some (.pair mf mt) := lookup_extend hm _
  have hf2 : h2[frame]?=some (.pair a ctx) := lookup_extend hf1 _
  have hy2 : h2[a]?=some (.pair ya yt) := lookup_extend (lookup_extend hy _) _
  have t169 : tickNatural program (state heap (next) head rb rc frame stack source 169)=
      some ⟨(state h1 (next+1) head rb rc next stack source 170),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h1]
  have t170 : tickNatural program (state h1 (next+1) head rb rc next stack source 170)=
      some ⟨(state h1 (next+1) head rb frame next stack source 171),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,new1]
  have t171 : tickNatural program (state h1 (next+1) head rb frame next stack source 171)=
      some ⟨(state h1 (next+1) head ctx frame next stack source 172),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hf1]
  have t172 : tickNatural program (state h1 (next+1) head ctx frame next stack source 172)=
      some ⟨(state h1 (next+1) mask ctx frame next stack source 173),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hx1]
  have t173 : tickNatural program (state h1 (next+1) mask ctx frame next stack source 173)=
      some ⟨(state h1 (next+1) mt ctx frame next stack source 174),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hm1]
  have t174 : tickNatural program (state h1 (next+1) mt ctx frame next stack source 174)=
      some ⟨(state h1 (next+1) mt amount frame next stack source 175),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hx1]
  have t175 : tickNatural program (state h1 (next+1) mt amount frame next stack source 175)=
      some ⟨(state h2 (next+2) mt (next+1) frame next stack source 176),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h2,Nat.add_assoc]
  have t176 : tickNatural program (state h2 (next+2) mt (next+1) frame next stack source 176)=
      some ⟨(state h2 (next+2) a (next+1) frame next stack source 177),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hf2]
  have t177 : tickNatural program (state h2 (next+2) a (next+1) frame next stack source 177)=
      some ⟨(state h2 (next+2) yt (next+1) frame next stack source 178),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hy2]
  have t178 : tickNatural program (state h2 (next+2) yt (next+1) frame next stack source 178)=
      some ⟨state h2 (next+2) yt (next+1) frame next
        (⟨179,.r0,⟨yt,next+1,frame,next⟩⟩::stack) source 160,[],0⟩ := by
    simp [tickNatural,program,state]
  simpa [h2,h1,List.append_assoc] using (show NaturalRun program 10 _ _ _ from (.step t169 (.step t170 (.step t171 (.step t172 (.step t173 (.step t174 (.step t175 (.step t176 (.step t177 (.step t178 (.done _))))))))))))

theorem cons_return {heap : NaturalHeap} {next tail b c frame head oldFrame : ℕ}
    {y : Fraction} {ys : List Fraction}
    (hf : heap[frame]?=some (.pair head oldFrame)) (headRep : Stored heap head y)
    (tailRep : StoredList heap tail ys) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 200) (stack : List (Frame ℕ 200)) (source : Bits) :
    NaturalRun program 3 (state heap next tail b c frame (⟨pc,.r0,saved⟩::stack) source 179) []
      (state (heap++[.pair head tail]) (next+1) next saved.b saved.c saved.d stack source pc) ∧
    StoredList (heap++[.pair head tail]) next (y::ys) := by
  let frames : List (Frame ℕ 200) := ⟨pc,.r0,saved⟩::stack
  have t179 : tickNatural program (state heap next tail b c frame frames source 179)=
      some ⟨state heap next tail head c frame frames source 180,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hf]
  have t180 : tickNatural program (state heap next tail head c frame frames source 180)=
      some ⟨state (heap++[.pair head tail]) (next+1) tail head c next frames source 181,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural]
  have t181 : tickNatural program (state (heap++[.pair head tail]) (next+1) tail head c next frames source 181)=
      some ⟨state (heap++[.pair head tail]) (next+1) next saved.b saved.c saved.d stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  exact ⟨.step t179 (.step t180 (.step t181 (.done _))),
    .cons (by simp [hn]) (stored_extend headRep _) (list_extend tailRep _)⟩
end DirectedFlowCutGap.PackingLoadRow
