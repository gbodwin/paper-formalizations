import DirectedFlowCutGap.CandidateNumeratorScanProgram

/-!
# Candidate numerator decoding from a stored grid word

The program increments the stored grid word and constructs the unary
block length. Its scan consumes the input mask and removal list, returning
one word per original vertex in order.
-/

namespace DirectedFlowCutGap.CandidateDecoderProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open PathCostMaterialization (WordList)
open CandidateNumeratorScanProgram (Context scan)

def incrementLabel (pc : Fin 16) : Fin 193 := ⟨16+pc.val,by omega⟩
def counterLabel (pc : Fin 17) : Fin 193 := ⟨32+pc.val,by omega⟩
def scanLabel (pc : Fin 144) : Fin 193 := ⟨49+pc.val,by omega⟩

def program : Program 193 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 1 => .make .r2 (.pair .r2 .r3) 2
    | 2 => .call (scanLabel 0) 3 .r3
    | 8 => .move .r0 .r2 9
    | 9 => .call (incrementLabel 0) (incrementLabel 14) .r3
    | 11 => .call (counterLabel 0) (counterLabel 16) .r3
    | _ => .halt
  else if h : pc.val<32 then
    if pc.val=30 then .move .r0 .r3 11
    else ReferenceProgramLabels.instruction incrementLabel
      (BinaryIncrementProgram.program ⟨pc.val-16,by omega⟩)
  else if h : pc.val<49 then
    if pc.val=48 then .ret .r3
    else ReferenceProgramLabels.instruction counterLabel
      (BinaryCounterProgram.program ⟨pc.val-32,by omega⟩)
  else if pc.val=50 then .ret .r3
  else ReferenceProgramLabels.instruction scanLabel
    (CandidateNumeratorScanProgram.program ⟨pc.val-49,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 193))
    (tape : Bits) (pc : Fin 193) : NaturalState 193 := ⟨heap,heap.length,r,stack,pc,tape⟩

def steps (grid flags removed : Bits) : ℕ :=
  BinaryIncrementProgram.steps grid+BinaryCounterProgram.steps (increment true grid).1+
    CandidateNumeratorScanProgram.steps (value grid+1) flags removed+9

def instructionBound (L n width : ℕ) : ℕ :=
  CandidateNumeratorScanProgram.instructionBound (L+1) n+18*width+3*(L+1)+27

theorem steps_le (grid flags removed : Bits) :
    steps grid flags removed ≤ instructionBound (value grid) removed.length grid.length := by
  have inc := BinaryIncrementProgram.steps_bound grid
  have convert := BinaryCounterProgram.steps_bound (increment true grid).1
  have scanBound := CandidateNumeratorScanProgram.steps_le (value grid+1) flags removed
  have numeric : value (increment true grid).1=value grid+1 := (increment_spec true grid).1
  have width := (increment_spec true grid).2.1
  rw [numeric] at convert
  unfold steps instructionBound
  omega

private theorem increment_slots (pc : Fin 16) (h : BinaryIncrementProgram.program pc≠.halt) :
    program (incrementLabel pc)=ReferenceProgramLabels.instruction incrementLabel (BinaryIncrementProgram.program pc) := by
  by_cases hp : pc.val=14
  · have eq : pc=14 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,incrementLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<32 by omega,show 16+pc.val≠30 by omega]

private theorem counter_slots (pc : Fin 17) (h : BinaryCounterProgram.program pc≠.halt) :
    program (counterLabel pc)=ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program pc) := by
  by_cases hp : pc.val=16
  · have eq : pc=16 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,counterLabel,show ¬32+pc.val<16 by omega,show ¬32+pc.val<32 by omega,
      show 32+pc.val<49 by omega,show 32+pc.val≠48 by omega]

private theorem scan_slots (pc : Fin 144) (h : CandidateNumeratorScanProgram.program pc≠.halt) :
    program (scanLabel pc)=ReferenceProgramLabels.instruction scanLabel (CandidateNumeratorScanProgram.program pc) := by
  by_cases hp : pc.val=1
  · have eq : pc=1 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,scanLabel,show ¬49+pc.val<16 by omega,show ¬49+pc.val<32 by omega,
      show ¬49+pc.val<49 by omega,show 49+pc.val≠50 by omega]

private theorem increment_call {heap : NaturalHeap} {r : Registers ℕ} {grid : Bits}
    (input : BoolList heap r.c grid) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (increment true grid).1 ∧
      NaturalRun program (BinaryIncrementProgram.steps grid+3) (state heap r [] tape 0) []
        (state (heap++ext) ((r.set .r0 r.c).set .r3 root) [⟨1,.r3,r⟩] tape (incrementLabel 14)) := by
  let args := r.set .r0 r.c
  let outer : Frame ℕ 193 := ⟨1,.r3,r⟩
  let inner : Frame ℕ 193 := ⟨incrementLabel 14,.r3,args⟩
  have setup : NaturalRun program 3 (state heap r [] tape 0) []
      (state heap args [inner,outer] tape (incrementLabel 0)) := by
    apply ReferenceProgramSteps.sound
    rfl
  obtain ⟨ext,root,len,body,rep⟩ := BinaryIncrementProgram.increment_return (a:=args.a) input heap.length
    args.b args.c args.d rfl args 14 [] tape
  have lifted := ReferenceProgramLabels.run incrementLabel BinaryIncrementProgram.program program increment_slots body
  have lifted := ReferenceProgramStack.run program [outer] lifted
  have run : NaturalRun program (BinaryIncrementProgram.steps grid) (state heap args [inner,outer] tape (incrementLabel 0)) []
      (state (heap++ext) (args.set .r3 root) [outer] tape (incrementLabel 14)) := by
    cases r
    simpa [state,args,outer,inner,BinaryIncrementProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,ReferenceProgramStack.state,Registers.set,len] using lifted
  exact ⟨ext,root,rep,by simpa only [List.nil_append,Nat.add_comm 3] using append_run setup run⟩

private theorem counter_call {heap : NaturalHeap} {r : Registers ℕ} {word : Bits} {root : ℕ}
    (input : BoolList heap root word) (caller : Frame ℕ 193) (tape : Bits) :
    ∃ ext fuel,IndexSpine (heap++ext) fuel (value word) ∧
      NaturalRun program (BinaryCounterProgram.steps word+3)
        (state heap (r.set .r3 root) [caller] tape (incrementLabel 14)) []
        (state (heap++ext) (caller.saved.set caller.destination fuel) [] tape caller.continuation) := by
  let args := (r.set .r3 root).set .r0 root
  let inner : Frame ℕ 193 := ⟨counterLabel 16,.r3,args⟩
  have setup : NaturalRun program 2 (state heap (r.set .r3 root) [caller] tape (incrementLabel 14)) []
      (state heap args [inner,caller] tape (counterLabel 0)) := by
    apply ReferenceProgramSteps.sound
    rfl
  obtain ⟨ext,fuel,len,body,rep⟩ := BinaryCounterProgram.convert_return (a:=args.a) input heap.length
    args.b args.c args.d rfl args 16 [] tape
  let stop := state (heap++ext) (args.set .r3 fuel) [caller] tape (counterLabel 16)
  have lifted := ReferenceProgramLabels.run counterLabel BinaryCounterProgram.program program counter_slots body
  have lifted := ReferenceProgramStack.run program [caller] lifted
  have run : NaturalRun program (BinaryCounterProgram.steps word) (state heap args [inner,caller] tape (counterLabel 0)) []
      stop := by
    cases r
    simpa [state,stop,args,inner,BinaryCounterProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,ReferenceProgramStack.state,Registers.set,len] using lifted
  have ret : tickNatural program stop = some
      ⟨state (heap++ext) (caller.saved.set caller.destination fuel) [] tape caller.continuation,[],0⟩ := by
    simp [state,stop,program,counterLabel,tickNatural,Registers.get,Registers.set]
  refine ⟨ext,fuel,rep,?_⟩
  have count : 2+(BinaryCounterProgram.steps word+1)=BinaryCounterProgram.steps word+3 := by omega
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

private theorem decode_scan {heap : NaturalHeap} {r : Registers ℕ} {flags grid removed : Bits} {fuel : ℕ}
    (mask : BoolList heap r.a flags) (removal : BoolList heap r.b removed) (word : BoolList heap r.c grid)
    (limit : IndexSpine heap fuel (value grid+1)) (fits : ((value grid+1)+(value grid+1))*removed.length≤flags.length)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),WordList (heap++ext) root (scan (value grid+1) grid flags removed) ∧
      NaturalRun program (CandidateNumeratorScanProgram.steps (value grid+1) flags removed+3)
        (state heap (r.set .r3 fuel) [] tape 1) [] (state (heap++ext) (args.set .r3 root) [] tape 3) := by
  let node : Cell ℕ := .pair r.c fuel
  let mid := heap++[node]
  let args := (r.set .r3 fuel).set .r2 heap.length
  let frame : Frame ℕ 193 := ⟨3,.r3,args⟩
  have setup : NaturalRun program 2 (state heap (r.set .r3 fuel) [] tape 1) []
      (state mid args [frame] tape (scanLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
      node,mid,args,frame]
  have context : Context mid args.c (value grid+1) grid :=
    ⟨r.c,fuel,by simp [mid,args,node,Registers.set],boolList_extend word [node],indexSpine_extend limit [node]⟩
  obtain ⟨ext,root,rep,body⟩ :=
    CandidateNumeratorScanProgram.natural_scan (r:=args) (boolList_extend mask [node]) (boolList_extend removal [node])
      context fits tape
  let stop := state (mid++ext) (args.set .r3 root) [frame] tape (scanLabel 1)
  have lifted := ReferenceProgramLabels.run scanLabel CandidateNumeratorScanProgram.program program scan_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have run : NaturalRun program (CandidateNumeratorScanProgram.steps (value grid+1) flags removed)
      (state mid args [frame] tape (scanLabel 0)) [] stop := by
    simpa [state,stop,mid,CandidateNumeratorScanProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (mid++ext) (args.set .r3 root) [] tape 3,[],0⟩ := by
    simp [state,stop,program,scanLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨[node]++ext,args,root,?_,?_⟩
  · simpa only [mid,List.append_assoc] using rep
  · let work := CandidateNumeratorScanProgram.steps (value grid+1) flags removed
    have count : 2+(work+1)=work+3 := by omega
    change NaturalRun program (work+3) _ [] _
    rw [← count]
    simpa only [mid,work,List.append_assoc,List.nil_append,Nat.zero_add] using
      append_run setup (append_run run (.step ret (.done _)))

theorem natural_decode {heap : NaturalHeap} {r : Registers ℕ} {flags grid removed : Bits}
    (mask : BoolList heap r.a flags) (removal : BoolList heap r.b removed) (word : BoolList heap r.c grid)
    (fits : ((value grid+1)+(value grid+1))*removed.length≤flags.length) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),WordList (heap++ext) root (scan (value grid+1) grid flags removed) ∧
      NaturalRun program (steps grid flags removed) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 3) := by
  obtain ⟨ei,i,rep,inc⟩ := increment_call word tape
  let mid := heap++ei
  let args := r.set .r0 r.c
  let caller : Frame ℕ 193 := ⟨1,.r3,r⟩
  obtain ⟨ec,fuel,unary,convert⟩ := counter_call (r:=args) rep caller tape
  have numeric : value (increment true grid).1=value grid+1 := (increment_spec true grid).1
  rw [numeric] at unary
  obtain ⟨ed,regs,root,output,decode⟩ := decode_scan (boolList_extend (boolList_extend mask ei) ec)
    (boolList_extend (boolList_extend removal ei) ec) (boolList_extend (boolList_extend word ei) ec) unary fits tape
  refine ⟨ei++ec++ed,regs,root,?_,?_⟩
  · simpa only [mid,List.append_assoc] using output
  · let u := BinaryIncrementProgram.steps grid
    let v := BinaryCounterProgram.steps (increment true grid).1
    let w := CandidateNumeratorScanProgram.steps (value grid+1) flags removed
    have count : u+3+(v+3+(w+3))=u+v+w+9 := by omega
    change NaturalRun program (u+v+w+9) _ [] _
    rw [← count]
    simpa only [caller,mid,u,v,w,List.append_assoc,List.nil_append] using append_run inc (append_run convert decode)

end DirectedFlowCutGap.CandidateDecoderProgram
