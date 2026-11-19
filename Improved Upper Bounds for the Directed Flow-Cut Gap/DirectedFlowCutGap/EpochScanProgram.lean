import DirectedFlowCutGap.EpochScanBounds

/-! Scan the real permuted list through the cache gates, selected round, and refresh. -/

namespace DirectedFlowCutGap.EpochScanProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open EpochScanData (Graph Stored stored_extend cacheOf optimizer cutOracle kept)
open AdaptiveControllerStorage (Parameters parameters_extend)
open EpochActiveFromMaskProgram (labelPair)
open GraphWalkExtension (Edge EdgeList edge_extend edgeList_extend)
open CandidateEnumeration (Node Network)
open EpochScanBounds (loopBound stepCells baseInstructions)

def headLabel (pc : Fin 382) : Fin 7324 := ⟨64+pc.val,by omega⟩
def roundLabel (pc : Fin 6878) : Fin 7324 := ⟨446+pc.val,by omega⟩

def program : Program 7324 := fun pc =>
  if pc.val<64 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 8 => .branch .r0 10 63 63 12
    | 10 => .ret .r3
    | 12 => .call (headLabel 0) 13 .r0
    | 13 => .branch .r0 10 63 63 14
    | 14 => .call 32 15 .r3
    | 15 => .field .r0 .r0 true 8
    | 32 => .field .r0 .r0 false 33
    | 33 => .call (roundLabel 0) 34 .r3
    | 34 => .ret .r3
    | _ => .halt
  else if h : pc.val<446 then
    if pc.val=71 then .ret .r3
    else ReferenceProgramLabels.instruction headLabel (EpochScanHeadProgram.program ⟨pc.val-64,by omega⟩)
  else if pc.val=450 then .ret .r3
  else ReferenceProgramLabels.instruction roundLabel
    (AdaptiveRoundRefreshProgram.program ⟨pc.val-446,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 7324

private theorem head_slots (pc : Fin 382) (h : EpochScanHeadProgram.program pc≠.halt) :
    program (headLabel pc)=ReferenceProgramLabels.instruction headLabel (EpochScanHeadProgram.program pc) := by
  by_cases stop : pc.val=7
  · have eq : pc=7 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,headLabel,show ¬64+pc.val<64 by omega,show 64+pc.val<446 by omega,show 64+pc.val≠71 by omega]

private theorem round_slots (pc : Fin 6878) (h : AdaptiveRoundRefreshProgram.program pc≠.halt) :
    program (roundLabel pc)=ReferenceProgramLabels.instruction roundLabel (AdaptiveRoundRefreshProgram.program pc) := by
  by_cases stop : pc.val=4
  · have eq : pc=4 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,roundLabel,show ¬446+pc.val<64 by omega,show ¬446+pc.val<446 by omega,show 446+pc.val≠450 by omega]

private theorem round_call {n L W B : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {key tail : ℕ} {adj : PairFlags n}
    {demands : Finset (Pair n)} (s : Code (Graph adj) demands L)
    {p : Pair n} (hp : p∈(interpret s).remaining) (positive : 0<L) (j : Fin L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)} {cells : List (Pair n×Bits)}
    (sample : value (EpochGridLookupProgram.word p cells)=j.val)
    (head : heap[r.a]?=some (.pair key tail)) (label : Edge heap key (labelPair p)) (grid : EpochGridLookupProgram.Table heap r.b cells)
    (params : Parameters (L:=L) heap r.c adj R M) (cache : Stored heap r.d s positive EN E words scale)
    (hW : 1≤W) (vertexWidth : n.size≤W) (rowWidth : ∀ v : Fin n,(row s.data.weights p)[v.val].bits.length≤W)
    (levelWidth : (EpochGridLookupProgram.word p cells).length≤W)
    (weightWidths : ∀ ws∈words,∀ w∈ws,w.length≤B) (stack : List (Frame ℕ 7324)) (tape : Bits) :
    let next := sampleRound positive (cutOracle adj positive) s p hp j
    ∃ (ext : NaturalHeap) (root k : ℕ),Stored (heap++ext) root next positive EN E words scale ∧
      NaturalRun program (k+5) (state heap r stack tape 14) [] (state (heap++ext) (r.set .r3 root) stack tape 15) ∧
      k ≤ AdaptiveRoundRefreshProgram.instructionBound n L cells.length W p.1.val.bits.length B scale.length ∧ ext.length≤k := by
  let args := r.set .r0 key
  let frame : Frame ℕ 7324 := ⟨15,.r3,r⟩
  have enter : NaturalRun program 2 (state heap r stack tape 14) [] (state heap args (frame::stack) tape 33) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      head,args,frame]
  obtain ⟨ext,out,root,k,rep,body,within⟩ := AdaptiveRoundRefreshProgram.natural_round_refresh (r:=args) s hp positive j
    EN E sample label grid params cache hW vertexWidth rowWidth levelWidth weightWidths tape
  have invoke := ReferenceProgramInvocation.call roundLabel round_slots (caller:=33) (continuation:=34)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) (frame::stack) body
  let stop := state (heap++ext) (args.set .r3 root) (frame::stack) tape 34
  have run : NaturalRun program (k+2) (state heap args (frame::stack) tape 33) [] stop := by
    simpa only [stop,Registers.get,Registers.set] using invoke
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) stack tape 15,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,k,rep,?_,within,ControllerWordWidth.extension_bound body rfl⟩
  have count : 2+(k+2+1)=k+5 := by omega
  rw [← count]
  exact append_run enter (append_run run (.step ret (.done _)))

set_option maxHeartbeats 2700000 in
private theorem scan_return {n L W B : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {demands : Finset (Pair n)} (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)} {cells : List (Pair n×Bits)} {order : List (Pair n)}
    (levels : Pair n → Fin L) (samples : ∀ p,value (EpochGridLookupProgram.word p cells)=(levels p).val)
    (keys : EdgeList heap r.a (order.map labelPair)) (grid : EpochGridLookupProgram.Table heap r.b cells)
    (params : Parameters (L:=L) heap r.c adj R M) (cache : Stored heap r.d s positive EN E words scale)
    (hW : 1≤W) (vertexWidth : n.size≤W) (rowWidths : ∀ p (v : Fin n),(row s.data.weights p)[v.val].bits.length≤W)
    (levelWidths : ∀ p,(EpochGridLookupProgram.word p cells).length≤W)
    (weightWidths : ∀ ws∈words,∀ w∈ws,w.length≤B) (caller : Frame ℕ 7324) (stack : List (Frame ℕ 7324)) (tape : Bits) :
    let A := stepCells n L cells.length W B scale.length R.length M.length
    let base := baseInstructions n L cells.length W B scale.length R.length M.length
    ∃ (ext : NaturalHeap) (root k : ℕ),
      Stored (heap++ext) root (EpochScanData.scan positive E R M levels order s) positive EN E words scale ∧
      NaturalRun program k (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) ∧
      k≤loopBound order.length heap.length A base ∧ ext.length≤order.length*A := by
  induction order generalizing heap r s caller stack with
  | nil =>
    cases keys with
    | nil empty =>
      refine ⟨[],r.d,2,by simpa only [EpochScanData.scan,List.append_nil] using cache,?_,by simp [loopBound],by simp⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,tagBranch,empty]
  | cons p ps ih =>
    cases keys with
    | @cons _ key tail _ _ head label remain =>
      let saved := caller::stack
      have branch : tickNatural program (state heap r saved tape 8)=some ⟨state heap r saved tape 12,[],0⟩ := by
        simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,tagBranch,head]
      obtain ⟨eh,out,test,k,decision,body,headLimit,headCells⟩ := EpochScanHeadProgram.natural_head head label params cache tape
      let mid := heap++eh
      let tested := r.set .r0 test
      have invoke := ReferenceProgramInvocation.call headLabel head_slots (caller:=12) (continuation:=13)
        (dst:=.r0) (result:=.r3) (by rfl) (by rfl) saved body
      have testRun : NaturalRun program (k+2) (state heap r saved tape 12) [] (state mid tested saved tape 13) := by
        simpa only [mid,tested,Registers.get,Registers.set] using invoke
      let A := stepCells n L cells.length W B scale.length R.length M.length
      let base := baseInstructions n L cells.length W B scale.length R.length M.length
      have widths := EpochScanBounds.mass_widths cache weightWidths
      have headTime := headLimit.trans (EpochScanBounds.instructions_mono n heap.length R.length M.length widths.1 widths.2)
      have headAllocation := headCells.trans (EpochScanBounds.allocation_mono n R.length M.length widths.1 widths.2)
      unfold EpochScanHeadProgram.instructionBound CacheGatesProgram.instructionBound at headTime
      by_cases visit : EpochScanHeadProgram.keep s.data (cacheOf positive E s).optimal R M p=true
      · have theHead : test=r.a := by simpa only [visit,ite_true] using decision
        have same : tested=r := by rw [show tested=r.set .r0 test from rfl,theHead]; cases r; rfl
        have pair : mid[r.a]?=some (.pair key tail) := lookup_extend head eh
        have advance : tickNatural program (state mid tested saved tape 13)=some ⟨state mid r saved tape 14,[],0⟩ := by
          rw [same]
          simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,tagBranch,pair]
        let hp := membership_of_flag s p (kept visit)
        let next := sampleRound positive (cutOracle adj positive) s p hp (levels p)
        obtain ⟨er,newCache,j,newRep,roundRun,roundLimit,roundCells⟩ := round_call (r:=r) s hp positive (levels p) EN E
          (samples p) pair (edge_extend label eh) (EpochGridLookupProgram.table_extend grid eh)
          (parameters_extend params eh) (stored_extend cache eh) hW vertexWidth (rowWidths p) (levelWidths p) weightWidths saved tape
        let grown := mid++er
        let updated := r.set .r3 newCache
        let args := updated.set .r0 tail
        have tailAt : grown[r.a]?=some (.pair key tail) := lookup_extend pair er
        have nextStep : tickNatural program (state grown updated saved tape 15)=some ⟨state grown args saved tape 8,[],0⟩ := by
          simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,tailAt,updated,args]
        obtain ⟨et,root,t,rep,rest,tailTime,tailAllocation⟩ := ih (r:=args) next (edgeList_extend (edgeList_extend remain eh) er)
          (EpochGridLookupProgram.table_extend (EpochGridLookupProgram.table_extend grid eh) er)
          (parameters_extend (parameters_extend params eh) er) newRep rowWidths caller stack
        have maxRound := roundLimit.trans (EpochScanBounds.round_bound p L cells.length W B scale.length)
        have now : k+j+10≤16*heap.length+base := by
          unfold base baseInstructions EpochScanHeadProgram.instructionBound CacheGatesProgram.instructionBound
          omega
        have grow : eh.length+er.length≤A := by unfold A stepCells; omega
        have nextSize : grown.length ≤ heap.length+A := by simp only [grown,mid,List.length_append]; omega
        refine ⟨eh++er++et,root,k+2+(j+5+(t+1)+1)+1,?_,?_,?_,?_⟩
        · simpa only [EpochScanData.scan,visit,dite_true,mid,grown,next,hp,List.append_assoc] using rep
        · simpa only [grown,mid,List.append_assoc,List.nil_append,Nat.add_assoc] using
            NaturalRun.step branch (append_run testRun (.step advance (append_run roundRun (.step nextStep rest))))
        · have total := EpochScanBounds.loop_extend ps.length heap.length grown.length A base (k+j+10) t nextSize now tailTime
          change k+2+(j+5+(t+1)+1)+1≤loopBound (ps.length+1) heap.length A base
          omega
        · change (eh++er++et).length≤(ps.length+1)*A
          change et.length≤ps.length*A at tailAllocation
          have joined := Nat.add_le_add grow tailAllocation
          simpa only [List.length_append,Nat.succ_mul,Nat.add_comm A,Nat.add_assoc] using joined
      · have nil : mid[test]?=some .nil := by simpa only [visit,Bool.false_eq_true,ite_false] using decision
        have stop : NaturalRun program 2 (state mid tested saved tape 13) []
            (state mid (caller.saved.set caller.destination r.d) stack tape caller.continuation) := by
          apply ReferenceProgramSteps.sound
          simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
            tagBranch,nil,tested,saved]
        have now : k+2+2+1≤16*heap.length+base := by
          unfold base baseInstructions EpochScanHeadProgram.instructionBound CacheGatesProgram.instructionBound
          omega
        refine ⟨eh,r.d,k+2+2+1,?_,?_,EpochScanBounds.loop_stop ps.length heap.length A base _ now,?_⟩
        · simpa only [EpochScanData.scan,visit,Bool.false_eq_true,dite_false] using stored_extend cache eh
        · exact .step branch (append_run testRun stop)
        · change eh.length≤(ps.length+1)*A
          have lt : eh.length≤A := by unfold A stepCells; omega
          rw [Nat.succ_mul]
          omega

theorem natural_scan {n L W B : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {adj : PairFlags n}
    {demands : Finset (Pair n)} (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)} {cells : List (Pair n×Bits)} {order : List (Pair n)}
    (levels : Pair n → Fin L) (samples : ∀ p,value (EpochGridLookupProgram.word p cells)=(levels p).val)
    (keys : EdgeList heap r.a (order.map labelPair)) (grid : EpochGridLookupProgram.Table heap r.b cells)
    (params : Parameters (L:=L) heap r.c adj R M) (cache : Stored heap r.d s positive EN E words scale)
    (hW : 1≤W) (vertexWidth : n.size≤W) (rowWidths : ∀ p (v : Fin n),(row s.data.weights p)[v.val].bits.length≤W)
    (levelWidths : ∀ p,(EpochGridLookupProgram.word p cells).length≤W)
    (weightWidths : ∀ ws∈words,∀ w∈ws,w.length≤B) (tape : Bits) :
    let A := stepCells n L cells.length W B scale.length R.length M.length
    let base := baseInstructions n L cells.length W B scale.length R.length M.length
    ∃ (ext : NaturalHeap) (root k : ℕ),
      Stored (heap++ext) root (EpochScanData.scan positive E R M levels order s) positive EN E words scale ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) ∧
      k≤loopBound order.length heap.length A base+1 ∧ ext.length≤order.length*A := by
  let caller : Frame ℕ 7324 := ⟨1,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [caller] tape 8,[],0⟩ := rfl
  obtain ⟨ext,root,k,rep,run,time,allocation⟩ := scan_return s positive EN E levels samples keys grid params cache hW vertexWidth rowWidths
    levelWidths weightWidths caller [] tape
  exact ⟨ext,root,k+1,rep,.step enter run,Nat.add_le_add_right time 1,allocation⟩

private theorem at_entry (s : NaturalState 7324) (entry : s.pc=0) (quiet : s.stack=[])
    (dense : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [ReferenceProgramInvocation.state]

theorem physical_scan {n L W B H A : ℕ} {adj : PairFlags n} {demands : Finset (Pair n)}
    (s : Code (Graph adj) demands L) (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    {R M scale : Bits} {words : List (List Bits)} {cells : List (Pair n×Bits)} {order : List (Pair n)}
    (levels : Pair n → Fin L) (samples : ∀ p,value (EpochGridLookupProgram.word p cells)=(levels p).val)
    (hW : 1≤W) (vertexWidth : n.size≤W) (rowWidths : ∀ p (v : Fin n),(row s.data.weights p)[v.val].bits.length≤W)
    (levelWidths : ∀ p,(EpochGridLookupProgram.word p cells).length≤W)
    (weightWidths : ∀ ws∈words,∀ w∈ws,w.length≤B) (initial : BitState 7324)
    (bounded : initial.Bounded H A) (entry : initial.pc=0) (quiet : initial.stack=[])
    (dense : (eraseState initial).next=(eraseState initial).heap.length)
    (keys : EdgeList (eraseState initial).heap (eraseState initial).registers.a (order.map labelPair))
    (grid : EpochGridLookupProgram.Table (eraseState initial).heap (eraseState initial).registers.b cells)
    (params : Parameters (L:=L) (eraseState initial).heap (eraseState initial).registers.c adj R M)
    (cache : Stored (eraseState initial).heap (eraseState initial).registers.d s positive EN E words scale) :
    let alloc := stepCells n L cells.length W B scale.length R.length M.length
    let base := baseInstructions n L cells.length W B scale.length R.length M.length
    ∃ (paid k : ℕ) (out : BitState 7324),Run program k paid initial [] out ∧
      Stored (eraseState out).heap (eraseState out).registers.d (EpochScanData.scan positive E R M levels order s)
        positive EN E words scale ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ out.pc=1 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length≤order.length*alloc) ∧
      (attempt program out).result=none ∧ paid+(attempt program out).operations ≤ completeBound 7324 H A
        (loopBound order.length (eraseState initial).heap.length alloc base+1) := by
  let old := eraseState initial
  obtain ⟨ext,root,k,rep,body,within,allocated⟩ := natural_scan s positive EN E levels samples keys grid params cache hW
    vertexWidth rowWidths levelWidths weightWidths old.source
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] old.source 1
  have empty : old.stack=[] := by simp [old,eraseState,State.map,quiet]
  have run : NaturalRun program k old [] final := by
    rw [at_entry old entry empty dense]
    exact body
  have halt : tickNatural program final=none := rfl
  obtain ⟨paid,out,actual,exactState,stopped,cost,tape⟩ := terminating_simulation bounded run halt
  refine ⟨paid,k,out,actual,?_,tape,?_,?_,⟨ext,?_,allocated⟩,stopped,cost.trans ?_⟩
  · rw [exactState]; exact rep
  · rw [exactState]; rfl
  · exact congrArg (fun s : NaturalState 7324 => s.pc) exactState
  · rw [exactState]; rfl
  · exact SupportSearchEncoding.complete_mono _ _ _ _ _ within

end DirectedFlowCutGap.EpochScanProgram
