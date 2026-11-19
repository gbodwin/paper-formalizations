import DirectedFlowCutGap.CandidateCapacityValues

/-!
# Core-to-core capacity from stored threshold operands

The program uses the actual shift word to test the two levels. It passes
the returned barrier flag directly to the stored capacity selector.
-/

namespace DirectedFlowCutGap.CandidateCoreCapacityProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open CandidateShiftSelectProgram (Flags)
open CandidatePortGapProgram (InputBounds bounds_extend)
open EncodedCandidateCapacity (Input)
open CandidateEnumeration (Node)

def shiftLabel (pc : Fin 24) : Fin 208 := ⟨32+pc.val,by omega⟩
def levelLabel (pc : Fin 144) : Fin 208 := ⟨56+pc.val,by omega⟩
def wordLabel (pc : Fin 8) : Fin 208 := ⟨200+pc.val,by omega⟩

def program : Program 208 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .call 8 1 .r2
    | 1 => .move .r0 .r3 2
    | 2 => .make .r1 (.flag false) 3
    | 3 => .call (wordLabel 0) 4 .r3
    | 8 => .field .r3 .r2 true 9
    | 9 => .field .r2 .r2 false 10
    | 10 => .call 20 11 .r1
    | 11 => .move .r2 .r1 12
    | 12 => .field .r1 .r0 true 13
    | 13 => .field .r0 .r0 false 14
    | 14 => .call (levelLabel 0) 15 .r3
    | 15 => .ret .r3
    | 20 => .move .r0 .r1 21
    | 21 => .field .r1 .r2 true 22
    | 22 => .field .r2 .r2 false (shiftLabel 0)
    | _ => .halt
  else if h : pc.val<56 then
    if pc.val=52 then .ret .r3
    else ReferenceProgramLabels.instruction shiftLabel (CandidateShiftSelectProgram.program ⟨pc.val-32,by omega⟩)
  else if h : pc.val<200 then
    if pc.val=72 then .ret .r3
    else ReferenceProgramLabels.instruction levelLabel (CandidateLevelTestProgram.program ⟨pc.val-56,by omega⟩)
  else if pc.val=206 then .ret .r3
  else ReferenceProgramLabels.instruction wordLabel (CandidateCapacityWords.select ⟨pc.val-200,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 208))
    (tape : Bits) (pc : Fin 208) : NaturalState 208 := ⟨heap,heap.length,r,stack,pc,tape⟩

def SignsAndRelations (heap : NaturalHeap) (root : ℕ) (a b same edge : Bool) : Prop :=
  ∃ signs rels,heap[root]?=some (.pair signs rels) ∧ Flags heap signs a b ∧ Flags heap rels same edge

def Relations (heap : NaturalHeap) (root : ℕ) (a b samePort edge samePoint : Bool) : Prop :=
  ∃ rel flag,heap[root]?=some (.pair rel flag) ∧ SignsAndRelations heap rel a b samePort edge ∧
    heap[flag]?=some (.flag samePoint)

private theorem shift_slots (pc : Fin 24) (h : CandidateShiftSelectProgram.program pc≠.halt) :
    program (shiftLabel pc)=ReferenceProgramLabels.instruction shiftLabel (CandidateShiftSelectProgram.program pc) := by
  by_cases hp : pc.val=20
  · have eq : pc=20 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,shiftLabel,show ¬32+pc.val<32 by omega,show 32+pc.val<56 by omega,show 32+pc.val≠52 by omega]

private theorem level_slots (pc : Fin 144) (h : CandidateLevelTestProgram.program pc≠.halt) :
    program (levelLabel pc)=ReferenceProgramLabels.instruction levelLabel (CandidateLevelTestProgram.program pc) := by
  by_cases hp : pc.val=16
  · have eq : pc=16 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,levelLabel,show ¬56+pc.val<32 by omega,show ¬56+pc.val<56 by omega,
      show 56+pc.val<200 by omega,show 56+pc.val≠72 by omega]

private theorem word_slots (pc : Fin 8) (h : CandidateCapacityWords.select pc≠.halt) :
    program (wordLabel pc)=ReferenceProgramLabels.instruction wordLabel (CandidateCapacityWords.select pc) := by
  by_cases hp : pc.val=6
  · have eq : pc=6 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,wordLabel,show ¬200+pc.val<32 by omega,show ¬200+pc.val<56 by omega,
      show ¬200+pc.val<200 by omega,show 200+pc.val≠206 by omega]

private theorem shift_call {heap : NaturalHeap} {r : Registers ℕ} {grid gap : Bits} {a b same edge : Bool}
    (bounds : InputBounds heap r.b grid gap) (relations : SignsAndRelations heap r.c a b same edge)
    (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (CandidateShiftSelectProgram.word grid gap a b same edge) ∧
      NaturalRun program (CandidateShiftSelectProgram.steps a b same+5) (state heap r [] tape 10) []
        (state (heap++ext) (r.set .r1 root) [] tape 11) := by
  obtain ⟨signs,rels,pair,hs,hr⟩ := relations
  let args := ((r.set .r0 r.b).set .r1 rels).set .r2 signs
  let frame : Frame ℕ 208 := ⟨11,.r1,r⟩
  have setup : NaturalRun program 4 (state heap r [] tape 10) [] (state heap args [frame] tape (shiftLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,frame,args,pair]
  obtain ⟨ext,root,rep,body⟩ := CandidateShiftSelectProgram.natural_shift (r:=args) bounds hr hs tape
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape (shiftLabel 20)
  have lift := ReferenceProgramLabels.run shiftLabel CandidateShiftSelectProgram.program program shift_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program (CandidateShiftSelectProgram.steps a b same)
      (state heap args [frame] tape (shiftLabel 0)) [] stop := by
    simpa [stop,state,CandidateShiftSelectProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r1 root) [] tape 11,[],0⟩ := by
    simp [stop,state,program,tickNatural,shiftLabel,frame,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have trace := append_run setup (append_run run (.step ret (.done _)))
  have num : 4+(CandidateShiftSelectProgram.steps a b same+1)=CandidateShiftSelectProgram.steps a b same+5 := by omega
  rw [← num]
  exact trace

private theorem levels_call {heap : NaturalHeap} {r : Registers ℕ} {x y shifted : Bits} {same : Bool}
    (levels : InputBounds heap r.a x y) (shift : BoolList heap r.b shifted) (flag : heap[r.d]?=some (.flag same))
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      (heap++ext)[root]?=some (.flag (CandidateLevelTestProgram.answer same x y shifted)) ∧
      NaturalRun program (CandidateLevelTestProgram.steps same x y shifted+5) (state heap r [] tape 11) []
        (state (heap++ext) (args.set .r3 root) [] tape 15) := by
  obtain ⟨a,b,pair,ha,hb⟩ := levels
  let inputs := ((r.set .r2 r.b).set .r1 b).set .r0 a
  let frame : Frame ℕ 208 := ⟨15,.r3,inputs⟩
  have setup : NaturalRun program 4 (state heap r [] tape 11) [] (state heap inputs [frame] tape (levelLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,frame,inputs,pair]
  obtain ⟨ext,regs,root,rep,body⟩ := CandidateLevelTestProgram.natural_test (r:=inputs) ha hb shift flag tape
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (levelLabel 16)
  have lift := ReferenceProgramLabels.run levelLabel CandidateLevelTestProgram.program program level_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program (CandidateLevelTestProgram.steps same x y shifted)
      (state heap inputs [frame] tape (levelLabel 0)) [] stop := by
    simpa [stop,state,CandidateLevelTestProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (inputs.set .r3 root) [] tape 15,[],0⟩ := by
    simp [stop,state,program,tickNatural,levelLabel,frame,Registers.get,Registers.set]
  refine ⟨ext,inputs,root,rep,?_⟩
  have trace := append_run setup (append_run run (.step ret (.done _)))
  have num : 4+(CandidateLevelTestProgram.steps same x y shifted+1)=CandidateLevelTestProgram.steps same x y shifted+5 := by omega
  rw [← num]
  exact trace

def barrierSteps (a b samePort samePoint : Bool) (x y shifted : Bits) : ℕ :=
  CandidateShiftSelectProgram.steps a b samePort+CandidateLevelTestProgram.steps samePoint x y shifted+14

def instructionBound (left right grid bound : ℕ) : ℕ := 64*(left+right+grid+bound+2)+31

private theorem barrier_call {heap : NaturalHeap} {r : Registers ℕ} {grid gap x y : Bits} {a b samePort edge samePoint : Bool}
    (levels : InputBounds heap r.a x y) (bounds : InputBounds heap r.b grid gap)
    (rel : Relations heap r.c a b samePort edge samePoint) (tape : Bits) :
    let shifted := CandidateShiftSelectProgram.word grid gap a b samePort edge
    ∃ ext root,(heap++ext)[root]?=some (.flag (CandidateLevelTestProgram.answer samePoint x y shifted)) ∧
      NaturalRun program (barrierSteps a b samePort samePoint x y shifted) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r2 root) [] tape 1) := by
  dsimp only
  obtain ⟨rel,flag,pair,relations,hflag⟩ := rel
  let args := (r.set .r3 flag).set .r2 rel
  let frame : Frame ℕ 208 := ⟨1,.r2,r⟩
  have setup : NaturalRun program 3 (state heap r [] tape 0) [] (state heap args [frame] tape 10) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,frame,args,pair]
  obtain ⟨es,word,rep,shift⟩ := shift_call (r:=args) bounds relations tape
  let mid := heap++es
  let withShift := args.set .r1 word
  obtain ⟨el,regs,root,barrier,level⟩ := levels_call (r:=withShift) (bounds_extend levels es) rep
    (lookup_extend hflag es) tape
  have run := append_run shift level
  have lift := ReferenceProgramStack.run program [frame] run
  let stop := state (mid++el) (regs.set .r3 root) [frame] tape 15
  have ret : tickNatural program stop=some ⟨state (mid++el) (r.set .r2 root) [] tape 1,[],0⟩ := by
    simp [stop,state,program,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨es++el,root,?_,?_⟩
  · simpa only [mid,List.append_assoc] using barrier
  · have whole := append_run setup (append_run lift (.step ret (.done _)))
    unfold barrierSteps
    convert whole using 1 <;> first | rfl | omega | simp only [mid,List.append_assoc]

private theorem word_call {heap : NaturalHeap} {r : Registers ℕ} {budget : Bits} {hard : Bool}
    (palette : CandidateCapacityWords.Stored heap r.d budget) (flag : heap[r.c]?=some (.flag hard)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),BoolList (heap++ext) root (CandidateCapacityWords.word budget false hard) ∧
      NaturalRun program 8 (state heap r [] tape 1) [] (state (heap++ext) (args.set .r3 root) [] tape 4) := by
  let extra : NaturalHeap := [.flag false]
  let mid := heap++extra
  let inputs := (r.set .r0 r.d).set .r1 heap.length
  let frame : Frame ℕ 208 := ⟨4,.r3,inputs⟩
  have setup : NaturalRun program 3 (state heap r [] tape 1) [] (state mid inputs [frame] tape (wordLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,frame,inputs,mid,extra,
      allocateNatural,Recipe.cell]
  have zero : mid[inputs.b]?=some (.flag false) := by simp [mid,extra,inputs,Registers.set]
  obtain ⟨regs,root,rep,body⟩ := CandidateCapacityWords.natural_select (r:=inputs)
    (CandidateCapacityWords.stored_extend palette extra) zero (lookup_extend flag extra) tape
  let stop := state mid (regs.set .r3 root) [frame] tape (wordLabel 6)
  have lift := ReferenceProgramLabels.run wordLabel CandidateCapacityWords.select program word_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program 4 (state mid inputs [frame] tape (wordLabel 0)) [] stop := by
    simpa [stop,mid,state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state mid (inputs.set .r3 root) [] tape 4,[],0⟩ := by
    simp [stop,state,program,tickNatural,wordLabel,frame,Registers.get,Registers.set]
  exact ⟨extra,inputs,root,rep,append_run setup (append_run run (.step ret (.done _)))⟩

theorem natural_core_capacity {heap : NaturalHeap} {r : Registers ℕ} {n : ℕ}
    (D : Input n) (s t : Fin n) (L B : ℕ) (a b : Node n L) (x y grid bound : Bits)
    (hx : value x=a.2.val) (hy : value y=b.2.val) (hg : value grid=L) (hb : value bound=B)
    (levels : InputBounds heap r.a x y)
    (bounds : InputBounds heap r.b grid (CandidatePortGapProgram.gap D grid (BinaryMinimumWordProgram.word grid bound) a.1.1))
    (relations : Relations heap r.c a.1.2 b.1.2 (decide (a.1.1=b.1.1))
      (CandidatePortAdjacencyProgram.result D b.1.1 a.1.1) (decide (a.1=b.1)))
    (palette : CandidateCapacityWords.Stored heap r.d (CandidatePhysicalCut.fuelWord D s t L B)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      BoolList (heap++ext) root
        (CandidatePhysicalCut.capacities D s t L B (CandidatePhysicalCut.numberEquiv n L (.inl a))
          (CandidatePhysicalCut.numberEquiv n L (.inl b))).bits ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 4) ∧
      k ≤ instructionBound x.length y.length grid.length bound.length := by
  let gap := CandidatePortGapProgram.gap D grid (BinaryMinimumWordProgram.word grid bound) a.1.1
  let same := decide (a.1.1=b.1.1)
  let point := decide (a.1=b.1)
  let edge := CandidatePortAdjacencyProgram.result D b.1.1 a.1.1
  let shifted := CandidateShiftSelectProgram.word grid gap a.1.2 b.1.2 same edge
  have hs : value shifted=CandidateCapacityFlags.shift D L B a.1 b.1 := by
    simpa only [shifted,gap,same,edge,hg,hb] using CandidateShiftSelectProgram.word_value D grid bound a.1 b.1
  have correct := CandidateCapacityValues.threshold_matches D L B a b x y shifted hx hy hs
  obtain ⟨ec,test,flag,core⟩ := barrier_call levels bounds relations tape
  let mid := heap++ec
  let saved := r.set .r2 test
  have testFlag : mid[saved.c]?=some (.flag (CandidateCapacityFlags.barrierFlag D L B a b)) := by
    rw [← correct]
    exact flag
  obtain ⟨eo,args,root,rep,finish⟩ := word_call (r:=saved) (CandidateCapacityWords.stored_extend palette ec) testFlag tape
  refine ⟨ec++eo,args,root,barrierSteps a.1.2 b.1.2 same point x y shifted+8,?_,?_,?_⟩
  · have word := CandidateCapacityValues.capacity_word D s t L B (.inl a) (.inl b)
    simp only [CandidateCapacityFlags.flags] at word
    rw [← word]
    simpa only [mid,List.append_assoc] using rep
  · have run := append_run core finish
    simpa only [mid,gap,same,point,edge,shifted,List.append_assoc,List.nil_append] using run
  · have sh := CandidateShiftSelectProgram.steps_le a.1.2 b.1.2 same
    have lv := CandidateLevelTestProgram.steps_le point x y shifted
    have gwidth : gap.length≤grid.length+bound.length := by
      have m := BinaryMinimumWordProgram.word_length grid bound
      have hm : max grid.length bound.length≤grid.length+bound.length := max_le (by omega) (by omega)
      dsimp [gap]
      cases a.1.1 <;> simp only [CandidatePortGapProgram.gap,List.length_nil]
      · split <;> omega
      · omega
    have swidth : shifted.length≤grid.length+bound.length := by
      dsimp [shifted,CandidateShiftSelectProgram.word]
      split
      · omega
      · exact gwidth
      · simp
    unfold barrierSteps instructionBound
    omega

private theorem at_entry (s : NaturalState 208) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_core_capacity {n H A : ℕ}
    (D : Input n) (s t : Fin n) (L B : ℕ) (a b : Node n L) (x y grid bound : Bits)
    (hx : value x=a.2.val) (hy : value y=b.2.val) (hg : value grid=L) (hb : value bound=B)
    (initial : BitState 208) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (levels : InputBounds (eraseState initial).heap (eraseState initial).registers.a x y)
    (bounds : InputBounds (eraseState initial).heap (eraseState initial).registers.b grid
      (CandidatePortGapProgram.gap D grid (BinaryMinimumWordProgram.word grid bound) a.1.1))
    (relations : Relations (eraseState initial).heap (eraseState initial).registers.c a.1.2 b.1.2 (decide (a.1.1=b.1.1))
      (CandidatePortAdjacencyProgram.result D b.1.1 a.1.1) (decide (a.1=b.1)))
    (palette : CandidateCapacityWords.Stored (eraseState initial).heap (eraseState initial).registers.d
      (CandidatePhysicalCut.fuelWord D s t L B)) :
    ∃ (charge steps : ℕ) (out : BitState 208),Run program steps charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d
        (CandidatePhysicalCut.capacities D s t L B (CandidatePhysicalCut.numberEquiv n L (.inl a))
          (CandidatePhysicalCut.numberEquiv n L (.inl b))).bits ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=4 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 208 H A (instructionBound x.length y.length grid.length bound.length) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,k,rep,body,kbound⟩ := natural_core_capacity D s t L B a b x y grid bound hx hy hg hb
    levels bounds relations palette old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 4
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have run : NaturalRun program k old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨paid,out,execution,hout,hstop,charge,unchanged⟩ := terminating_simulation bounded run stop
  refine ⟨paid,k,out,execution,?_,unchanged,?_,?_,⟨ext,?_⟩,hstop,
    charge.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ kbound)⟩
  · rw [hout]; exact rep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.CandidateCoreCapacityProgram
