import DirectedFlowCutGap.OriginalControlWordsProgram
import DirectedFlowCutGap.BinaryGeometricCounterProgram
import DirectedFlowCutGap.PhysicalControllerInitializer

/-! Compute the control record from a canonical dimension and a trial word. -/

namespace DirectedFlowCutGap.PhysicalControllerControls

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor
open BooleanTableRead (BoolList IndexSpine)
open ConcreteExpressionProgram (append_run)
open IntegerEpochParameters (restart fuel)

def wordsLabel (pc : Fin 180) : Fin 413 := ⟨48+pc.val,by omega⟩
def geometricLabel (pc : Fin 168) : Fin 413 := ⟨228+pc.val,by omega⟩
def counterLabel (pc : Fin 17) : Fin 413 := if pc.val=16 then 36 else ⟨396+pc.val,by omega⟩

def program : Program 413 := fun pc =>
  if h : pc.val < 48 then
    match pc.val with
    | 0 => .call 16 1 .r3
    | 1 => .call 24 2 .r2
    | 2 => .call (wordsLabel 8) 3 .r0
    | 3 => .call 28 4 .r0
    | 4 => .call 34 5 .r1
    | 5 => .make .r3 .nil 6
    | 6 => .make .r2 (.pair .r2 .r3) 7
    | 7 => .make .r1 (.pair .r1 .r0) 8
    | 8 => .make .r1 (.pair .r0 .r1) 9
    | 9 => .make .r3 (.pair .r2 .r1) 10
    | 16 => .make .r3 .nil 17
    | 17 => .make .r0 (.flag true) 18
    | 18 => .make .r2 (.flag false) 19
    | 19 => .make .r1 (.pair .r0 .r3) 20
    | 20 => .make .r2 (.pair .r2 .r1) 21
    | 21 => .make .r3 (.pair .r0 .r1) 22
    | 22 => .make .r3 (.pair .r2 .r3) 23
    | 23 => .ret .r3
    | 24 => .field .r1 .r3 false 25
    | 25 => .call (wordsLabel 0) 26 .r3
    | 26 => .ret .r3
    | 28 => .make .r1 (.pair .r0 .r2) 29
    | 29 => .move .r0 .r2 30
    | 30 => .field .r3 .r3 true 31
    | 31 => .call (geometricLabel 0) 32 .r3
    | 32 => .ret .r3
    | 34 => .move .r0 .r1 35
    | 35 => .call (counterLabel 0) 36 .r3
    | 36 => .ret .r3
    | _ => .halt
  else if h : pc.val < 228 then
    if pc.val=53 ∨ pc.val=59 then .ret .r3
    else ReferenceProgramLabels.instruction wordsLabel (OriginalControlWordsProgram.program ⟨pc.val-48,by omega⟩)
  else if h : pc.val < 396 then
    if pc.val=235 then .ret .r3
    else ReferenceProgramLabels.instruction geometricLabel (BinaryGeometricCounterProgram.program ⟨pc.val-228,by omega⟩)
  else ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program ⟨pc.val-396,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 413

private theorem words_slots (pc : Fin 180) (used : OriginalControlWordsProgram.program pc≠.halt) :
    program (wordsLabel pc)=ReferenceProgramLabels.instruction wordsLabel (OriginalControlWordsProgram.program pc) := by
  by_cases stop : pc.val=5 ∨ pc.val=11
  · obtain h|h := stop
    · have eq : pc=5 := Fin.ext h
      subst pc
      exact (used rfl).elim
    · have eq : pc=11 := Fin.ext h
      subst pc
      exact (used rfl).elim
  · simp [program,wordsLabel,show ¬48+pc.val<48 by omega,show 48+pc.val<228 by omega,
      show ¬(48+pc.val=53 ∨ 48+pc.val=59) by omega]

private theorem geometric_slots (pc : Fin 168) (used : BinaryGeometricCounterProgram.program pc≠.halt) :
    program (geometricLabel pc)=ReferenceProgramLabels.instruction geometricLabel (BinaryGeometricCounterProgram.program pc) := by
  by_cases stop : pc.val=7
  · have eq : pc=7 := Fin.ext stop
    subst pc
    exact (used rfl).elim
  · simp [program,geometricLabel,show ¬228+pc.val<48 by omega,show ¬228+pc.val<228 by omega,
      show 228+pc.val<396 by omega,show 228+pc.val≠235 by omega]

private theorem counter_slots (pc : Fin 17) (used : BinaryCounterProgram.program pc≠.halt) :
    program (counterLabel pc)=ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program pc) := by
  by_cases stop : pc.val=16
  · have eq : pc=16 := Fin.ext stop
    subst pc
    exact (used rfl).elim
  · simp [program,counterLabel,stop,show ¬396+pc.val<48 by omega,show ¬396+pc.val<228 by omega,
      show ¬396+pc.val<396 by omega]

private def Seeds (heap : NaturalHeap) (root : ℕ) : Prop :=
  ∃ two clock, heap[root]?=some (.pair two clock) ∧ BoolList heap two [false,true] ∧ IndexSpine heap clock 2

private theorem seeds_extend {heap : NaturalHeap} {root : ℕ} (h : Seeds heap root) (ext : NaturalHeap) :
    Seeds (heap++ext) root := by
  obtain ⟨two,clock,atRoot,w,s⟩ := h
  exact ⟨two,clock,lookup_extend atRoot ext,boolList_extend w ext,indexSpine_extend s ext⟩

private theorem extra_lookup (heap ext : NaturalHeap) (i : ℕ) : (heap++ext)[heap.length+i]?=ext[i]? := by
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]

set_option maxHeartbeats 1700000 in
private theorem allocate_seeds (heap : NaturalHeap) (r : Registers ℕ) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ), Seeds (heap++ext) root ∧
      NaturalRun program 9 (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  let a := heap.length
  let ext : NaturalHeap :=
    [.nil,.flag true,.flag false,.pair (a+1) a,.pair (a+2) (a+3),.pair (a+1) (a+3),.pair (a+4) (a+5)]
  let h := heap++ext
  have lookup (i : ℕ) : h[a+i]?=ext[i]? := extra_lookup heap ext i
  have nil : h[a]?=some .nil := by simpa [ext] using lookup 0
  have tru : h[a+1]?=some (.flag true) := by simpa [ext] using lookup 1
  have fal : h[a+2]?=some (.flag false) := by simpa [ext] using lookup 2
  have one : h[a+3]?=some (.pair (a+1) a) := by simpa [ext] using lookup 3
  have two : h[a+4]?=some (.pair (a+2) (a+3)) := by simpa [ext] using lookup 4
  have count : h[a+5]?=some (.pair (a+1) (a+3)) := by simpa [ext] using lookup 5
  have all : h[a+6]?=some (.pair (a+4) (a+5)) := by simpa [ext] using lookup 6
  refine ⟨ext,a+6,⟨a+4,a+5,all,.cons two fal (.cons one tru (.nil nil)),.cons count (.cons one (.nil nil))⟩,?_⟩
  have p0 : program 0=.call 16 1 .r3 := rfl
  have p16 : program 16=.make .r3 .nil 17 := rfl
  have p17 : program 17=.make .r0 (.flag true) 18 := rfl
  have p18 : program 18=.make .r2 (.flag false) 19 := rfl
  have p19 : program 19=.make .r1 (.pair .r0 .r3) 20 := rfl
  have p20 : program 20=.make .r2 (.pair .r2 .r1) 21 := rfl
  have p21 : program 21=.make .r3 (.pair .r0 .r1) 22 := rfl
  have p22 : program 22=.make .r3 (.pair .r2 .r3) 23 := rfl
  have p23 : program 23=.ret .r3 := rfl
  apply ReferenceProgramSteps.sound
  simp only [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,tickNatural,p0,p16,p17,p18,p19,p20,p21,p22,p23,
    Registers.get,Registers.set,allocateNatural,Recipe.cell,ext,a,Nat.add_assoc,Nat.reduceAdd,
    Option.bind_some,Option.map_some,List.nil_append,List.append_assoc,List.length_append,List.length_cons,List.length_nil]
  rfl

private theorem compute_ratio {heap : NaturalHeap} {r : Registers ℕ} {n : ℕ}
    (count : BoolList heap r.a n.bits) (one : BoolList heap r.c [true])
    (seed : Seeds heap r.d) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      BoolList (heap++ext) root (restart n).bits ∧ k≤OriginalControlWordsProgram.restartLimit n+5 ∧
      NaturalRun program k (state heap r [] tape 1) []
        (state (heap++ext) (r.set .r2 root) [] tape 2) := by
  obtain ⟨two,_,atSeed,twoWord,_⟩ := seed
  let frame : Frame ℕ 413 := ⟨2,.r2,r⟩
  let args := r.set .r1 two
  have load : NaturalRun program 2 (state heap r [] tape 1) [] (state heap args [frame] tape 25) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,frame,atSeed]
  obtain ⟨ext,out,k,ratio,time,run⟩ := OriginalControlWordsProgram.natural_restart (r:=args) count twoWord one tape
  have call := ReferenceProgramInvocation.call wordsLabel words_slots (caller:=25) (continuation:=26)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] run
  have finish : tickNatural program (state (heap++ext) (args.set .r3 out.d) [frame] tape 26) =
      some ⟨state (heap++ext) (r.set .r2 out.d) [] tape 2,[],0⟩ := rfl
  refine ⟨ext,out.d,k+5,ratio,by omega,?_⟩
  have lengthEq : k+5=2+((k+2)+1) := by omega
  rw [lengthEq]
  simpa only [Registers.get,List.nil_append] using append_run load (append_run call (.step finish (.done _)))

def logLimit (n : ℕ) : ℕ :=
  let logs := Nat.log (restart n) (n^3)
  let r := (restart n).size
  (logs+1)*BinaryGeometricCounterProgram.stepBound (r+(n^3).size+logs*(2*r+1))

set_option maxHeartbeats 1600000 in
private theorem compute_caps {heap : NaturalHeap} {r : Registers ℕ} {n : ℕ}
    (cube : BoolList heap r.a (n^3).bits) (ratio : BoolList heap r.c (restart n).bits)
    (seeds : Seeds heap r.d) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),
      IndexSpine (heap++ext) root (fuel n+1) ∧ k≤logLimit n+7 ∧
      NaturalRun program k (state heap r [] tape 3) []
        (state (heap++ext) (r.set .r0 root) [] tape 4) := by
  obtain ⟨_,clock,atSeed,_,clockRep⟩ := seeds
  let frame : Frame ℕ 413 := ⟨4,.r0,r⟩
  let ext : NaturalHeap := [.pair r.a r.c]
  let mid := heap++ext
  let args : Registers ℕ := ⟨r.c,heap.length,r.c,clock⟩
  have prefixRun : NaturalRun program 4 (state heap r [] tape 3) [] (state mid args [frame] tape 31) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,frame,ext,mid,allocateNatural,Recipe.cell,lookup_extend atSeed]
  have cfg : BinaryGeometricCounterProgram.Parameters mid args.b (n^3).bits (restart n).bits :=
    ⟨r.a,r.c,by simp [mid,ext,args],boolList_extend cube ext,boolList_extend ratio ext⟩
  have pos : 1<value (restart n).bits := by rw [value_bits]; exact IntegerEpochParameters.one_lt_restart n
  obtain ⟨ep,out,k,spine,ticks,loop⟩ := BinaryGeometricCounterProgram.natural_count (r:=args)
    (boolList_extend ratio ext) cfg (indexSpine_extend clockRep ext) pos tape
  have call := ReferenceProgramInvocation.call geometricLabel geometric_slots (caller:=31) (continuation:=32)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] loop
  have finish : tickNatural program (state (mid++ep) (args.set .r3 out.d) [frame] tape 32) =
      some ⟨state (mid++ep) (r.set .r0 out.d) [] tape 4,[],0⟩ := rfl
  simp only [value_bits,Nat.size_eq_bits_len] at ticks spine
  have count : 2+Nat.log (restart n) (n^3)=fuel n+1 := by unfold fuel; omega
  refine ⟨ext++ep,out.d,k+7,?_,?_,?_⟩
  · simpa only [count,mid,List.append_assoc] using spine
  · exact Nat.add_le_add_right (show k≤logLimit n from ticks) 7
  · have lengthEq : k+7=4+((k+2)+1) := by omega
    rw [lengthEq]
    simpa only [mid,List.append_assoc,List.nil_append,Registers.get] using
      append_run prefixRun (append_run call (.step finish (.done _)))

private theorem compute_trials {heap : NaturalHeap} {r : Registers ℕ} {trialWord : Bits}
    (trial : BoolList heap r.b trialWord) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),
      IndexSpine (heap++ext) root (value trialWord) ∧
      NaturalRun program (BinaryCounterProgram.steps trialWord+4)
        (state heap r [] tape 4) [] (state (heap++ext) (r.set .r1 root) [] tape 5) := by
  let frame : Frame ℕ 413 := ⟨5,.r1,r⟩
  let args := r.set .r0 r.b
  obtain ⟨ext,root,len,body,spine⟩ := BinaryCounterProgram.convert_return trial heap.length args.b args.c args.d
    rfl args 16 [] tape
  have start : NaturalRun program 3 (state heap r [] tape 4) []
      (state heap args (⟨36,.r3,args⟩::[frame]) tape (counterLabel 0)) := by
    apply ReferenceProgramSteps.sound
    rfl
  have lifted := ReferenceProgramLabels.run counterLabel BinaryCounterProgram.program program counter_slots body
  have full : NaturalRun program (BinaryCounterProgram.steps trialWord)
      (state heap args (⟨36,.r3,args⟩::[frame]) tape (counterLabel 0)) []
      (state (heap++ext) (args.set .r3 root) [frame] tape 36) := by
    have h := ReferenceProgramStack.run program [frame] lifted
    have atEnd : counterLabel 16=36 := rfl
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryCounterProgram.state,ReferenceProgramInvocation.state,Registers.set,args,atEnd,len] using h
  have finish : tickNatural program (state (heap++ext) (args.set .r3 root) [frame] tape 36) =
      some ⟨state (heap++ext) (r.set .r1 root) [] tape 5,[],0⟩ := rfl
  refine ⟨ext,root,spine,?_⟩
  have lengthEq : BinaryCounterProgram.steps trialWord+4=3+(BinaryCounterProgram.steps trialWord+1) := by omega
  rw [lengthEq]
  simpa only [List.nil_append] using append_run start (append_run full (.step finish (.done _)))

set_option maxHeartbeats 1500000 in
private theorem pack_controls {heap : NaturalHeap} {r : Registers ℕ} {R : Bits} {trials epochs : ℕ}
    (ratio : BoolList heap r.c R) (caps : IndexSpine heap r.a epochs) (trial : IndexSpine heap r.b trials)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),
      PhysicalControllerInitializer.Control (heap++ext) root R [] trials epochs epochs ∧
      NaturalRun program 5 (state heap r [] tape 5) []
        (state (heap++ext) ⟨r.a,heap.length+3,heap.length+1,root⟩ [] tape 10) := by
  let a := heap.length
  let ext : NaturalHeap := [.nil,.pair r.c a,.pair r.b r.a,.pair r.a (a+2),.pair (a+1) (a+3)]
  have atCell (i : ℕ) : (heap++ext)[a+i]?=ext[i]? := extra_lookup heap ext i
  have nil : (heap++ext)[a]?=some .nil := by simpa [ext] using atCell 0
  have gate : (heap++ext)[a+1]?=some (.pair r.c a) := by simpa [ext] using atCell 1
  have budget : (heap++ext)[a+2]?=some (.pair r.b r.a) := by simpa [ext] using atCell 2
  have slots : (heap++ext)[a+3]?=some (.pair r.a (a+2)) := by simpa [ext] using atCell 3
  have out : (heap++ext)[a+4]?=some (.pair (a+1) (a+3)) := by simpa [ext] using atCell 4
  refine ⟨ext,a+4,⟨a+1,a+3,r.a,a+2,r.b,r.a,out,slots,budget,
    ⟨r.c,a,gate,boolList_extend ratio ext,.nil nil⟩,
    indexSpine_extend caps ext,indexSpine_extend trial ext,indexSpine_extend caps ext⟩,?_⟩
  apply ReferenceProgramSteps.sound
  simp (config := {maxSteps := 1000000}) [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,
    tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,ext,a,Nat.add_assoc]

def instructionBound (n maxTrials trialWidth : ℕ) : ℕ :=
  OriginalControlWordsProgram.restartLimit n+OriginalControlWordsProgram.cubeLimit n+logLimit n+
    3*maxTrials+10*trialWidth+35

/-- Both epoch and restart counts are allocated from the actual powers of
the integer ratio. The trial word is converted on the same heap. -/
theorem natural_controls {heap : NaturalHeap} {r : Registers ℕ} {n : ℕ} {trialWord : Bits}
    (count : BoolList heap r.a n.bits) (trial : BoolList heap r.b trialWord)
    (unit : BoolList heap r.c [true]) (tape : Bits) :
    ∃ (ext : NaturalHeap) (out : Registers ℕ) (k : ℕ),
      PhysicalControllerInitializer.Control (heap++ext) out.d (restart n).bits []
        (value trialWord) (fuel n+1) (fuel n+1) ∧
      k ≤ instructionBound n (value trialWord) trialWord.length ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) out [] tape 10) := by
  obtain ⟨e1,seed,seeds,allocate⟩ := allocate_seeds heap r tape
  let firstHeap := heap++e1
  let first := r.set .r3 seed
  obtain ⟨e2,ratio,t,ratioRep,ratioTime,ratioRun⟩ := compute_ratio (r:=first)
    (boolList_extend count e1) (boolList_extend unit e1) seeds tape
  let ratioHeap := firstHeap++e2
  let args := first.set .r2 ratio
  obtain ⟨e3,body,u,cubeRep,cubeTime,cubeRun⟩ := OriginalControlWordsProgram.natural_cube (r:=args)
    (boolList_extend (boolList_extend count e1) e2) tape
  have callCube := ReferenceProgramInvocation.call wordsLabel words_slots (caller:=2) (continuation:=3)
    (result:=.r3) (dst:=.r0) (by rfl) (by rfl) [] cubeRun
  let cubicHeap := ratioHeap++e3
  let cubic := args.set .r0 body.d
  obtain ⟨e4,epochs,v,epochsRep,epochsTime,epochsRun⟩ := compute_caps (r:=cubic) cubeRep
    (boolList_extend ratioRep e3) (seeds_extend (seeds_extend seeds e2) e3) tape
  let epochHeap := cubicHeap++e4
  let withEpochs := cubic.set .r0 epochs
  obtain ⟨e5,trials,trialRep,trialRun⟩ := compute_trials (r:=withEpochs)
    (boolList_extend (boolList_extend (boolList_extend (boolList_extend trial e1) e2) e3) e4) tape
  let lastHeap := epochHeap++e5
  let withTrials := withEpochs.set .r1 trials
  obtain ⟨e6,root,control,packed⟩ := pack_controls (r:=withTrials)
    (boolList_extend (boolList_extend (boolList_extend ratioRep e3) e4) e5)
    (indexSpine_extend epochsRep e5) trialRep tape
  let endRegs : Registers ℕ := ⟨epochs,lastHeap.length+3,lastHeap.length+1,root⟩
  let k := 9+t+(u+2)+v+(BinaryCounterProgram.steps trialWord+4)+5
  refine ⟨e1++e2++e3++e4++e5++e6,endRegs,k,?_,?_,?_⟩
  · simpa only [List.append_assoc, endRegs] using control
  · have trialTime := BinaryCounterProgram.steps_bound trialWord
    unfold instructionBound k
    omega
  · simpa only [k,List.append_assoc,List.nil_append,Nat.add_assoc,Registers.get,Registers.set,firstHeap,ratioHeap,
      cubicHeap,epochHeap,lastHeap,first,args,cubic,withEpochs,withTrials,endRegs] using
      append_run allocate (append_run ratioRun (append_run callCube (append_run epochsRun (append_run trialRun packed))))

end DirectedFlowCutGap.PhysicalControllerControls
