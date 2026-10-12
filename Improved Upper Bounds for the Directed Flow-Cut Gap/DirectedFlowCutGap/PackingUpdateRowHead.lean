import DirectedFlowCutGap.PackingUpdateEntryCall

namespace DirectedFlowCutGap.PackingUpdateRow
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram

theorem head_prepare {heap : NaturalHeap} {next a b ctx d ca ct mask mf mt amount : ℕ}
    (hc : heap[a]?=some (.pair ca ct))
    (hx : heap[ctx]?=some (.pair mask amount)) (hm : heap[mask]?=some (.pair mf mt))
    (stack : List (Frame ℕ 520)) (source : Bits) :
    NaturalRun program 5 (state heap next a b ctx d stack source 480) []
      (state (heap++[.pair a b,.pair next ctx]) (next+2) a b mf (next+1) stack source 487) := by
  let h1 := heap++[.pair a b]
  let h2 := h1++[.pair next ctx]
  have hx2 : h2[ctx]?=some (.pair mask amount) := lookup_extend (lookup_extend hx _) _
  have hm2 : h2[mask]?=some (.pair mf mt) := lookup_extend (lookup_extend hm _) _
  have t480 : tickNatural program (state heap (next) a b ctx d stack source 480)=
      some ⟨(state heap (next) a b ctx d stack source 483),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,tagBranch,hc]
  have t483 : tickNatural program (state heap (next) a b ctx d stack source 483)=
      some ⟨(state h1 (next+1) a b ctx next stack source 484),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h1]
  have t484 : tickNatural program (state h1 (next+1) a b ctx next stack source 484)=
      some ⟨(state h2 (next+2) a b ctx (next+1) stack source 485),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h1,h2,Nat.add_assoc]
  have t485 : tickNatural program (state h2 (next+2) a b ctx (next+1) stack source 485)=
      some ⟨(state h2 (next+2) a b mask (next+1) stack source 486),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hx2]
  have t486 : tickNatural program (state h2 (next+2) a b mask (next+1) stack source 486)=
      some ⟨(state h2 (next+2) a b mf (next+1) stack source 487),[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,hm2]
  simpa [h2,h1,List.append_assoc] using NaturalRun.step t480 (.step t483 (.step t484 (.step t485 (.step t486 (.done _)))))

theorem head_high (ci amount y : Fraction) (enabled : Bool)
    {heap : NaturalHeap} {next a b ctx d ca ct ya yt mask mf mt amountRoot : ℕ}
    (hc : heap[a]?=some (.pair ca ct)) (hy : heap[b]?=some (.pair ya yt))
    (hx : heap[ctx]?=some (.pair mask amountRoot)) (hm : heap[mask]?=some (.pair mf mt))
    (hf : heap[mf]?=some (.flag enabled))
    (cap : Stored heap ca ci) (amt : Stored heap amountRoot amount) (weight : Stored heap ya y)
    (hn : next=heap.length) (stack : List (Frame ℕ 520)) (source : Bits) :
    ∃ ext root rb rc,ext.length=(if enabled then PackingEntry.cells ci amount y+3 else 2) ∧
      NaturalRun program (if enabled then PackingEntry.steps ci amount y+15 else 8)
        (state heap next a b ctx d stack source 480) []
        (state (heap++ext) (next+ext.length) root rb rc (next+1) stack source 499) ∧
      Stored (heap++ext) root (if enabled then PackingEntry.result ci amount y else y) ∧
      (heap++ext)[next]?=some (.pair a b) ∧
      (heap++ext)[next+1]?=some (.pair next ctx) := by
  let e0 : NaturalHeap := [.pair a b,.pair next ctx]
  let h0 := heap++e0
  have pre := head_prepare (next:=next) (b:=b) (d:=d) hc hx hm stack source
  have pre : NaturalRun program 5 (state heap next a b ctx d stack source 480) []
      (state h0 (next+2) a b mf (next+1) stack source 487) := by simpa [h0,e0] using pre
  have hf0 : h0[mf]?=some (.flag enabled) := lookup_extend hf e0
  have hy0 : h0[b]?=some (.pair ya yt) := lookup_extend hy e0
  have hc0 : h0[a]?=some (.pair ca ct) := lookup_extend hc e0
  have hx0 : h0[ctx]?=some (.pair mask amountRoot) := lookup_extend hx e0
  have frame0 : h0[next+1]?=some (.pair next ctx) := by simp [h0,e0,hn]
  cases enabled with
  | false =>
    have t487 : tickNatural program (state h0 (next+2) a b mf (next+1) stack source 487)=
        some ⟨state h0 (next+2) a b mf (next+1) stack source 488,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hf0,tagBranch]
    have t488 : tickNatural program (state h0 (next+2) a b mf (next+1) stack source 488)=
        some ⟨state h0 (next+2) ya b mf (next+1) stack source 489,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hy0]
    have t489 : tickNatural program (state h0 (next+2) ya b mf (next+1) stack source 489)=
        some ⟨state h0 (next+2) ya b mf (next+1) stack source 499,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set]
    refine ⟨e0,ya,b,mf,rfl,?_,stored_extend weight e0,?_,frame0⟩
    · simpa [e0] using run_append pre (.step t487 (.step t488 (.step t489 (.done _))))
    · simp [e0,hn]
  | true =>
    let e1 : NaturalHeap := [.pair amountRoot ya]
    let h1 := h0++e1
    have dense1 : next+3=h1.length := by simp [h1,h0,e0,e1,hn]
    have dense0 : next+2=h0.length := by simp [h0,e0,hn]
    have newPair : h1[next+2]?=some (.pair amountRoot ya) := by simp [h1,e1,dense0]
    obtain ⟨ee,re,le,entryRun,entryRep⟩ := entry_return ci amount y
      (stored_extend (stored_extend cap e0) e1)
      (stored_extend (stored_extend amt e0) e1)
      (stored_extend (stored_extend weight e0) e1)
      (next+3) (next+1) dense1 ⟨ca,amountRoot,ya,next+1⟩ 499 stack source
    have t487 : tickNatural program (state h0 (next+2) a b mf (next+1) stack source 487)=
        some ⟨(state h0 (next+2) a b mf (next+1) stack source 490),[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,hf0,tagBranch]
    have t490 : tickNatural program (state h0 (next+2) a b mf (next+1) stack source 490)=
        some ⟨(state h0 (next+2) ca b mf (next+1) stack source 491),[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hc0]
    have t491 : tickNatural program (state h0 (next+2) ca b mf (next+1) stack source 491)=
        some ⟨(state h0 (next+2) ca ya mf (next+1) stack source 492),[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hy0]
    have t492 : tickNatural program (state h0 (next+2) ca ya mf (next+1) stack source 492)=
        some ⟨(state h0 (next+2) ca ya ctx (next+1) stack source 493),[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,frame0]
    have t493 : tickNatural program (state h0 (next+2) ca ya ctx (next+1) stack source 493)=
        some ⟨(state h0 (next+2) ca ya amountRoot (next+1) stack source 494),[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,hx0]
    have t494 : tickNatural program (state h0 (next+2) ca ya amountRoot (next+1) stack source 494)=
        some ⟨(state h1 (next+3) ca ya (next+2) (next+1) stack source 495),[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,Recipe.cell,allocateNatural,h1,e1,Nat.add_assoc]
    have t495 : tickNatural program (state h1 (next+3) ca ya (next+2) (next+1) stack source 495)=
        some ⟨(state h1 (next+3) ca amountRoot (next+2) (next+1) stack source 496),[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,newPair]
    have t496 : tickNatural program (state h1 (next+3) ca amountRoot (next+2) (next+1) stack source 496)=
        some ⟨(state h1 (next+3) ca amountRoot ya (next+1) stack source 497),[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,Registers.set,newPair]
    have t497 : tickNatural program (state h1 (next+3) ca amountRoot ya (next+1) stack source 497)=
        some ⟨state h1 (next+3) ca amountRoot ya (next+1)
          (⟨499,.r0,⟨ca,amountRoot,ya,next+1⟩⟩::stack) source 440,[],0⟩ := by
      simp [tickNatural,program,state]
    let ext := e0++e1++ee
    have eh : heap++ext=h1++ee := by simp [ext,h1,h0,List.append_assoc]
    have en : next+ext.length=next+3+ee.length := by simp [ext,e0,e1];omega
    refine ⟨ext,re,amountRoot,ya,by simp [ext,e0,e1,le],?_,?_,?_,?_⟩
    · rw [eh,en]
      have whole := run_append pre (.step t487 (.step t490 (.step t491 (.step t492
        (.step t493 (.step t494 (.step t495 (.step t496 (.step t497 entryRun)))))))))
      convert whole using 1 <;> simp [Nat.add_assoc]
      omega
    · rw [eh];exact entryRep
    · rw [eh];apply lookup_extend;apply lookup_extend
      simp [h0,e0,hn]
    · rw [eh];exact lookup_extend (lookup_extend frame0 e1) ee
end DirectedFlowCutGap.PackingUpdateRow
