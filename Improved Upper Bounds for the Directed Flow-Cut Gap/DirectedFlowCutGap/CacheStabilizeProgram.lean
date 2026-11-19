import DirectedFlowCutGap.CacheAdvanceProgram

/-! Stabilization consumes the actual stored restart fuel. -/

namespace DirectedFlowCutGap.CacheStabilizeProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor
open RetainedGridState IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open AdaptiveControllerStorage (Parameters parameters_extend)
open EpochScanData (Graph Stored stored_extend cacheOf optimizer)
open CandidateEnumeration (Node Network)

def advanceLabel (pc : Fin 7288) : Fin 7320 := ⟨32+pc.val,by omega⟩

def program : Program 7320 := fun pc =>
  if pc.val < 32 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 8 => .branch .r0 12 15 15 9
    | 9 => .call (advanceLabel 0) 10 .r3
    | 10 => .field .r0 .r0 true 8
    | 12 => .ret .r3
    | _ => .halt
  else if pc.val=35 then .ret .r3
  else ReferenceProgramLabels.instruction advanceLabel (CacheAdvanceProgram.program ⟨pc.val-32,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 7320

private theorem slots (pc : Fin 7288) (h : CacheAdvanceProgram.program pc≠.halt) :
    program (advanceLabel pc)=ReferenceProgramLabels.instruction advanceLabel (CacheAdvanceProgram.program pc) := by
  by_cases stop : pc.val=3
  · have eq : pc=3 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,advanceLabel,show ¬32+pc.val<32 by omega,show 32+pc.val≠35 by omega]

noncomputable abbrev stableCode {n L : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)} (positive : 0<L)
    (E : ResidualSearch.Enumeration (Network n L)) (R : Bits) (fuel : ℕ) (s : Code (Graph adj) demands L) :
    Code (Graph adj) demands L :=
  (IntegerAdaptiveExecution.stabilize (optimizer (adj:=adj) (demands:=demands) positive E) (value R) fuel
    (cacheOf positive E s)).cache.state

theorem stable_zero {n L : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)} (positive : 0<L)
    (E : ResidualSearch.Enumeration (Network n L)) (R : Bits) (s : Code (Graph adj) demands L) :
    stableCode positive E R 0 s=s := rfl

theorem stable_succ {n L fuel : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)} (positive : 0<L)
    (E : ResidualSearch.Enumeration (Network n L)) (R : Bits) (s : Code (Graph adj) demands L) :
    stableCode positive E R (fuel+1) s=stableCode positive E R fuel (CacheAdvanceProgram.nextCode positive E R s) := by
  change (IntegerAdaptiveExecution.stabilize _ (value R) fuel
    (IntegerAdaptiveExecution.advance _ (value R) (cacheOf positive E s)).cache).cache.state=_
  rw [CacheAdvanceProgram.advance_exact]

theorem stable_exact {n L : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)} (positive : 0<L)
    (E : ResidualSearch.Enumeration (Network n L)) (R : Bits) (fuel : ℕ) (s : Code (Graph adj) demands L) :
    (IntegerAdaptiveExecution.stabilize (optimizer (adj:=adj) (demands:=demands) positive E) (value R) fuel
      (cacheOf positive E s)).cache = cacheOf positive E (stableCode positive E R fuel s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [stable_succ]
    change (IntegerAdaptiveExecution.stabilize _ (value R) fuel
      (IntegerAdaptiveExecution.advance _ (value R) (cacheOf positive E s)).cache).cache=_
    rw [CacheAdvanceProgram.advance_exact]
    exact ih _

def allocationBound (n L fuel B S R M : ℕ) : ℕ := fuel*CacheAdvanceProgram.allocationBound n L B S R M

def instructionBound (n L fuel H B S R M : ℕ) : ℕ :=
  EpochScanBounds.loopBound fuel H (CacheAdvanceProgram.allocationBound n L B S R M)
    (CacheAdvanceProgram.instructionBound n L 0 B S R M+4)+1

set_option maxHeartbeats 2300000 in
private theorem run_loop {n L B S fuel : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {demands : Finset (Pair n)} (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)}
    (params : Parameters (L:=L) heap r.c adj R M) (cache : Stored heap r.d s positive EN E words scale)
    (counter : IndexSpine heap r.a fuel) (grid : max L.size (L+1).size≤B)
    (widths : ∀ ws ∈ words,∀ w ∈ ws,w.length≤B) (scaleBound : scale.length+2*fuel≤S)
    (frame : Frame ℕ 7320) (stack : List (Frame ℕ 7320)) (tape : Bits) :
    let A := CacheAdvanceProgram.allocationBound n L B S R.length M.length
    let base := CacheAdvanceProgram.instructionBound n L 0 B S R.length M.length+4
    ∃ (ext : NaturalHeap) (root k : ℕ) (nextWords : List (List Bits)) (nextScale : Bits),
      Stored (heap++ext) root (stableCode positive E R fuel s) positive EN E nextWords nextScale ∧
      (∀ ws ∈ nextWords,∀ w ∈ ws,w.length≤B) ∧ nextScale.length≤ scale.length+2*fuel ∧
      NaturalRun program k (state heap r (frame::stack) tape 8) []
        (state (heap++ext) (frame.saved.set frame.destination root) stack tape frame.continuation) ∧
      k≤ EpochScanBounds.loopBound fuel heap.length A base ∧ ext.length≤ fuel*A := by
  induction fuel generalizing heap r s words scale with
  | zero =>
    cases counter with
    | nil atNil =>
      have body : NaturalRun program 2 (state heap r (frame::stack) tape 8) []
          (state heap (frame.saved.set frame.destination r.d) stack tape frame.continuation) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,
          Registers.get,Registers.set,atNil,tagBranch]
      exact ⟨[],r.d,2,words,scale,by simpa only [List.append_nil,stable_zero] using cache,widths,by simp,by simpa using body,
        by simp [EpochScanBounds.loopBound],by simp⟩
  | succ fuel ih =>
    cases counter with
    | cons atPair counter =>
      rename_i payload tail
      let saved := frame::stack
      have branch : tickNatural program (state heap r saved tape 8)=some ⟨state heap r saved tape 9,[],0⟩ := by
        simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,atPair,tagBranch]
      obtain ⟨ea,next,sc,live,k,ws,bs,advanced,wordBound,scaleGrowth,body,time,alloc⟩ :=
        CacheAdvanceProgram.natural_advance s positive EN E params cache grid widths tape
      let mid := heap++ea
      let after := r.set .r3 next
      let args := after.set .r0 tail
      have invoke := ReferenceProgramInvocation.call advanceLabel slots (caller:=9) (continuation:=10)
        (result:=.r3) (dst:=.r3) (by rfl) (by rfl) saved body
      have advance : NaturalRun program (k+2) (state heap r saved tape 9) [] (state mid after saved tape 10) := by
        simpa only [mid,after,Registers.get] using invoke
      have atCounter : mid[r.a]?=some (.pair payload tail) := lookup_extend atPair ea
      have dec : tickNatural program (state mid after saved tape 10)=some ⟨state mid args saved tape 8,[],0⟩ := by
        simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,after,args,atCounter]
      have newScale : bs.length+2*fuel≤S := by omega
      obtain ⟨eb,root,v,endWords,endScale,stored,width,scaleEnd,rest,cost,space⟩ := ih
        (CacheAdvanceProgram.nextCode positive E R s) (r:=args) (parameters_extend params ea) advanced
        (indexSpine_extend counter ea) wordBound newScale
      let A := CacheAdvanceProgram.allocationBound n L B S R.length M.length
      let base := CacheAdvanceProgram.instructionBound n L 0 B S R.length M.length+4
      have mono := CacheAdvanceProgram.fresh_mono n L (show scale.length≤S by omega)
      have grow : ea.length≤A := by
        dsimp only [A,CacheAdvanceProgram.allocationBound] at alloc ⊢
        omega
      have ht : k+4≤16*heap.length+base := by
        dsimp only [base,CacheAdvanceProgram.instructionBound,CacheGatesProgram.instructionBound] at time ⊢
        omega
      have heapBound : mid.length≤ heap.length+A := by simp only [mid,List.length_append]; omega
      have total := EpochScanBounds.loop_extend fuel heap.length mid.length A base (k+4) v heapBound ht cost
      refine ⟨ea++eb,root,k+4+v,endWords,endScale,?_,width,by omega,?_,total,?_⟩
      · rw [stable_succ]
        simpa only [mid,List.append_assoc] using stored
      · have count : (k+2+(v+1))+1=k+4+v := by omega
        rw [← count]
        simpa only [mid,saved,List.append_assoc,List.nil_append] using
          NaturalRun.step branch (append_run advance (.step dec rest))
      · change (ea++eb).length≤ (fuel+1)*A
        rw [List.length_append,Nat.succ_mul]
        change eb.length≤fuel*A at space
        omega

theorem natural_stabilize {n L B S fuel : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {demands : Finset (Pair n)} (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)}
    (params : Parameters (L:=L) heap r.c adj R M) (cache : Stored heap r.d s positive EN E words scale)
    (counter : IndexSpine heap r.a fuel) (grid : max L.size (L+1).size≤B)
    (widths : ∀ ws ∈ words,∀ w ∈ ws,w.length≤B) (scaleBound : scale.length+2*fuel≤S) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ) (nextWords : List (List Bits)) (nextScale : Bits),
      Stored (heap++ext) root (stableCode positive E R fuel s) positive EN E nextWords nextScale ∧
      (∀ ws ∈ nextWords,∀ w ∈ ws,w.length≤B) ∧ nextScale.length≤ scale.length+2*fuel ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) ∧
      k≤ instructionBound n L fuel heap.length B S R.length M.length ∧
      ext.length≤ allocationBound n L fuel B S R.length M.length := by
  let frame : Frame ℕ 7320 := ⟨1,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [frame] tape 8,[],0⟩ := rfl
  obtain ⟨ext,root,k,nextWords,nextScale,stored,widths',grow,run,stepsBound,extBound⟩ := run_loop s positive EN E
    params cache counter grid widths scaleBound frame [] tape
  exact ⟨ext,root,k+1,nextWords,nextScale,stored,widths',grow,.step enter run,Nat.add_le_add_right stepsBound 1,extBound⟩

end DirectedFlowCutGap.CacheStabilizeProgram
