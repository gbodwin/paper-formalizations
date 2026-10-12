import DirectedFlowCutGap.PackingUpdateRowHead

namespace DirectedFlowCutGap.PackingUpdateRow
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

theorem tail_prepare {heap : NaturalHeap} {next head rb rc frame orig ctx a b mask amount ca ct ya yt mf mt : ℕ}
    (hf : heap[frame]?=some (.pair orig ctx)) (ho : heap[orig]?=some (.pair a b))
    (hx : heap[ctx]?=some (.pair mask amount)) (hm : heap[mask]?=some (.pair mf mt))
    (hc : heap[a]?=some (.pair ca ct)) (hy : heap[b]?=some (.pair ya yt))
    (hn : next=heap.length) (stack : List (Frame ℕ 520)) (source : Bits) :
    NaturalRun program 14 (state heap next head rb rc frame stack source 499) []
      (state (heap++[.pair head frame,.pair mt amount]) (next+2) ct yt (next+1) next
        (⟨513,.r0,⟨ct,yt,next+1,next⟩⟩::stack) source 480) := by
  let h1 := heap++[.pair head frame]
  let h2 := h1++[.pair mt amount]
  have new1 : h1[next]?=some (.pair head frame) := by simp [h1,hn]
  have hf1 : h1[frame]?=some (.pair orig ctx) := lookup_extend hf _
  have hx1 : h1[ctx]?=some (.pair mask amount) := lookup_extend hx _
  have hm1 : h1[mask]?=some (.pair mf mt) := lookup_extend hm _
  have new2 : h2[next]?=some (.pair head frame) := lookup_extend new1 _
  have hf2 : h2[frame]?=some (.pair orig ctx) := lookup_extend hf1 _
  have ho2 : h2[orig]?=some (.pair a b) := lookup_extend (lookup_extend ho _) _
  have hc2 : h2[a]?=some (.pair ca ct) := lookup_extend (lookup_extend hc _) _
  have hy2 : h2[b]?=some (.pair ya yt) := lookup_extend (lookup_extend hy _) _
  have t499 : tickNatural program (state heap (next) head rb rc frame stack source 499)=
      some ⟨(state h1 (next+1) head rb rc next stack source 500),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h1]
  have t500 : tickNatural program (state h1 (next+1) head rb rc next stack source 500)=
      some ⟨(state h1 (next+1) head rb frame next stack source 501),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,new1]
  have t501 : tickNatural program (state h1 (next+1) head rb frame next stack source 501)=
      some ⟨(state h1 (next+1) head rb ctx next stack source 502),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hf1]
  have t502 : tickNatural program (state h1 (next+1) head rb ctx next stack source 502)=
      some ⟨(state h1 (next+1) mask rb ctx next stack source 503),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hx1]
  have t503 : tickNatural program (state h1 (next+1) mask rb ctx next stack source 503)=
      some ⟨(state h1 (next+1) mt rb ctx next stack source 504),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hm1]
  have t504 : tickNatural program (state h1 (next+1) mt rb ctx next stack source 504)=
      some ⟨(state h1 (next+1) mt amount ctx next stack source 505),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hx1]
  have t505 : tickNatural program (state h1 (next+1) mt amount ctx next stack source 505)=
      some ⟨(state h2 (next+2) mt amount (next+1) next stack source 506),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h2,Nat.add_assoc]
  have t506 : tickNatural program (state h2 (next+2) mt amount (next+1) next stack source 506)=
      some ⟨(state h2 (next+2) frame amount (next+1) next stack source 507),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,new2]
  have t507 : tickNatural program (state h2 (next+2) frame amount (next+1) next stack source 507)=
      some ⟨(state h2 (next+2) orig amount (next+1) next stack source 508),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hf2]
  have t508 : tickNatural program (state h2 (next+2) orig amount (next+1) next stack source 508)=
      some ⟨(state h2 (next+2) orig b (next+1) next stack source 509),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ho2]
  have t509 : tickNatural program (state h2 (next+2) orig b (next+1) next stack source 509)=
      some ⟨(state h2 (next+2) a b (next+1) next stack source 510),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ho2]
  have t510 : tickNatural program (state h2 (next+2) a b (next+1) next stack source 510)=
      some ⟨(state h2 (next+2) ct b (next+1) next stack source 511),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hc2]
  have t511 : tickNatural program (state h2 (next+2) ct b (next+1) next stack source 511)=
      some ⟨(state h2 (next+2) ct yt (next+1) next stack source 512),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hy2]
  have t512 : tickNatural program (state h2 (next+2) ct yt (next+1) next stack source 512)=
      some ⟨state h2 (next+2) ct yt (next+1) next
        (⟨513,.r0,⟨ct,yt,next+1,next⟩⟩::stack) source 480,[],0⟩ := by
    simp [tickNatural,program,state]
  simpa [h2,h1,List.append_assoc] using (show NaturalRun program 14 _ _ _ from (.step t499 (.step t500 (.step t501 (.step t502 (.step t503 (.step t504 (.step t505 (.step t506 (.step t507 (.step t508 (.step t509 (.step t510 (.step t511 (.step t512 (.done _))))))))))))))))

theorem cons_return {heap : NaturalHeap} {next tail b c frame head oldFrame : ℕ}
    {y : Fraction} {ys : List Fraction}
    (hf : heap[frame]?=some (.pair head oldFrame)) (headRep : Stored heap head y)
    (tailRep : StoredList heap tail ys) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 520) (stack : List (Frame ℕ 520)) (source : Bits) :
    NaturalRun program 3 (state heap next tail b c frame (⟨pc,.r0,saved⟩::stack) source 513) []
      (state (heap++[.pair head tail]) (next+1) next saved.b saved.c saved.d stack source pc) ∧
    StoredList (heap++[.pair head tail]) next (y::ys) := by
  let frames : List (Frame ℕ 520) := ⟨pc,.r0,saved⟩::stack
  have t513 : tickNatural program (state heap next tail b c frame frames source 513)=
      some ⟨state heap next tail head c frame frames source 514,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hf]
  have t514 : tickNatural program (state heap next tail head c frame frames source 514)=
      some ⟨state (heap++[.pair head tail]) (next+1) tail head c next frames source 515,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural]
  have t515 : tickNatural program (state (heap++[.pair head tail]) (next+1) tail head c next frames source 515)=
      some ⟨state (heap++[.pair head tail]) (next+1) next saved.b saved.c saved.d stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,frames]
  exact ⟨.step t513 (.step t514 (.step t515 (.done _))),
    .cons (by simp [hn]) (stored_extend headRep _) (list_extend tailRep _)⟩
end DirectedFlowCutGap.PackingUpdateRow
