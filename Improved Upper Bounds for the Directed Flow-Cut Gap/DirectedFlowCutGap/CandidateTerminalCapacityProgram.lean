import DirectedFlowCutGap.CandidateCapacityValues

/-!
# Capacity at a candidate's artificial source or sink

The returned flag pair is opened in the same heap and passed to the
capacity selector. The endpoints of the two covered cell types are the
artificial source and a threshold node, or a threshold node and the
artificial sink.
-/

namespace DirectedFlowCutGap.CandidateTerminalCapacityProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open CandidateShiftSelectProgram (Flags)
open CandidateTerminalFlagsProgram (result)
open EncodedCandidateCapacity (Input)
open CandidateEnumeration (Node)

def flagLabel (pc : Fin 41) : Fin 65 := ⟨16+pc.val,by omega⟩
def wordLabel (pc : Fin 8) : Fin 65 := ⟨57+pc.val,by omega⟩

def program : Program 65 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call (flagLabel 0) 1 .r2
    | 1 => .move .r0 .r3 2
    | 2 => .field .r1 .r2 false 3
    | 3 => .field .r2 .r2 true 4
    | 4 => .call (wordLabel 0) 5 .r3
    | _ => .halt
  else if h : pc.val<57 then
    if pc.val=37 then .ret .r3
    else ReferenceProgramLabels.instruction flagLabel (CandidateTerminalFlagsProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=63 then .ret .r3
  else ReferenceProgramLabels.instruction wordLabel (CandidateCapacityWords.select ⟨pc.val-57,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 65))
    (tape : Bits) (pc : Fin 65) : NaturalState 65 := ⟨heap,heap.length,r,stack,pc,tape⟩

def steps (level : Bits) : ℕ := CandidateTerminalFlagsProgram.steps level+11

theorem steps_le (level : Bits) : steps level ≤ 4*level.length+23 := by
  have h := CandidateTerminalFlagsProgram.steps_le level
  unfold steps
  omega

private theorem flag_slots (pc : Fin 41) (h : CandidateTerminalFlagsProgram.program pc≠.halt) :
    program (flagLabel pc)=ReferenceProgramLabels.instruction flagLabel (CandidateTerminalFlagsProgram.program pc) := by
  by_cases hp : pc.val=21
  · have eq : pc=21 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,flagLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<57 by omega,show 16+pc.val≠37 by omega]

private theorem word_slots (pc : Fin 8) (h : CandidateCapacityWords.select pc≠.halt) :
    program (wordLabel pc)=ReferenceProgramLabels.instruction wordLabel (CandidateCapacityWords.select pc) := by
  by_cases hp : pc.val=6
  · have eq : pc=6 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,wordLabel,show ¬57+pc.val<16 by omega,show ¬57+pc.val<57 by omega,show 57+pc.val≠63 by omega]

private theorem flag_call {heap : NaturalHeap} {r : Registers ℕ} {level : Bits} {side sign active pin : Bool}
    (size : BoolList heap r.a level) (nodeFields : Flags heap r.b sign active)
    (termFields : Flags heap r.c side pin) (tape : Bits) :
    let cell := result side (isZero level).1 sign active pin
    ∃ ext root,Flags (heap++ext) root cell.1 cell.2 ∧
      NaturalRun program (CandidateTerminalFlagsProgram.steps level+2) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r2 root) [] tape 1) := by
  dsimp only
  obtain ⟨ext,args,root,rep,body⟩ := CandidateTerminalFlagsProgram.natural_flags size nodeFields termFields tape
  let caller : Frame ℕ 65 := ⟨1,.r2,r⟩
  let stop := state (heap++ext) (args.set .r3 root) [caller] tape (flagLabel 21)
  have enter : tickNatural program (state heap r [] tape 0)=
      some ⟨state heap r [caller] tape (flagLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run flagLabel CandidateTerminalFlagsProgram.program program flag_slots body
  have lift := ReferenceProgramStack.run program [caller] lift
  have run : NaturalRun program (CandidateTerminalFlagsProgram.steps level)
      (state heap r [caller] tape (flagLabel 0)) [] stop := by
    simpa [state,stop,CandidateTerminalFlagsProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r2 root) [] tape 1,[],0⟩ := by
    simp [state,stop,flagLabel,program,tickNatural,caller,Registers.get,Registers.set]
  exact ⟨ext,root,rep,.step enter (append_run run (.step ret (.done _)))⟩

private theorem word_call {heap : NaturalHeap} {r : Registers ℕ} {budget : Bits} {unit hard : Bool}
    (palette : CandidateCapacityWords.Stored heap r.d budget) (flags : Flags heap r.c unit hard) (tape : Bits) :
    ∃ (args : Registers ℕ) (root : ℕ), BoolList heap root (CandidateCapacityWords.word budget unit hard) ∧
      NaturalRun program 9 (state heap r [] tape 1) [] (state heap (args.set .r3 root) [] tape 5) := by
  obtain ⟨u,h,pair,unitRep,hardRep⟩ := flags
  let inputs := ((r.set .r0 r.d).set .r1 u).set .r2 h
  let caller : Frame ℕ 65 := ⟨5,.r3,inputs⟩
  have setup : NaturalRun program 4 (state heap r [] tape 1) [] (state heap inputs [caller] tape (wordLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,inputs,caller,pair]
  obtain ⟨args,root,rep,body⟩ := CandidateCapacityWords.natural_select (r:=inputs) palette unitRep hardRep tape
  let stop := state heap (args.set .r3 root) [caller] tape (wordLabel 6)
  have lift := ReferenceProgramLabels.run wordLabel CandidateCapacityWords.select program word_slots body
  have lift := ReferenceProgramStack.run program [caller] lift
  have run : NaturalRun program 4 (state heap inputs [caller] tape (wordLabel 0)) [] stop := by
    simpa [state,stop,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state heap (inputs.set .r3 root) [] tape 5,[],0⟩ := by
    simp [state,stop,wordLabel,program,tickNatural,caller,Registers.get,Registers.set]
  exact ⟨inputs,root,rep,append_run setup (append_run run (.step ret (.done _)))⟩

theorem natural_capacity {heap : NaturalHeap} {r : Registers ℕ} {level budget : Bits} {side sign active pin : Bool}
    (size : BoolList heap r.a level) (nodeFields : Flags heap r.b sign active)
    (termFields : Flags heap r.c side pin) (palette : CandidateCapacityWords.Stored heap r.d budget) (tape : Bits) :
    let cell := result side (isZero level).1 sign active pin
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      BoolList (heap++ext) root (CandidateCapacityWords.word budget cell.1 cell.2) ∧
      NaturalRun program (steps level) (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 5) := by
  dsimp only
  obtain ⟨ext,root,flags,setup⟩ := flag_call size nodeFields termFields tape
  obtain ⟨args,out,rep,finish⟩ := word_call (r:=r.set .r2 root) (CandidateCapacityWords.stored_extend palette ext) flags tape
  exact ⟨ext,args,out,rep,append_run setup finish⟩

theorem natural_source {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (D : Input n) (s t : Fin n) (L B : ℕ) (a : Node n L) (level : Bits) (numeric : value level=a.2.val)
    (size : BoolList heap r.a level) (nodeFields : Flags heap r.b a.1.2 (CandidatePortGapProgram.active D a.1.1))
    (termFields : Flags heap r.c false (decide (a.1.1=TerminalPorts.sink t)))
    (palette : CandidateCapacityWords.Stored heap r.d (CandidatePhysicalCut.fuelWord D s t L B)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      BoolList (heap++ext) root
        (CandidatePhysicalCut.capacities D s t L B (CandidatePhysicalCut.numberEquiv n L (.inr false))
          (CandidatePhysicalCut.numberEquiv n L (.inl a))).bits ∧
      NaturalRun program (steps level) (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 5) := by
  obtain ⟨ext,args,root,rep,body⟩ := natural_capacity size nodeFields termFields palette tape
  refine ⟨ext,args,root,?_,body⟩
  rw [← CandidateCapacityValues.capacity_word D s t L B (.inr false) (.inl a),
    ← CandidateTerminalFlagsProgram.result_source D s t L B a level numeric]
  exact rep

theorem natural_sink {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (D : Input n) (s t : Fin n) (L B : ℕ) (a : Node n L) (level : Bits) (numeric : value level=a.2.val)
    (size : BoolList heap r.a level) (nodeFields : Flags heap r.b a.1.2 (CandidatePortGapProgram.active D a.1.1))
    (termFields : Flags heap r.c true (decide (a.1.1=TerminalPorts.source s)))
    (palette : CandidateCapacityWords.Stored heap r.d (CandidatePhysicalCut.fuelWord D s t L B)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      BoolList (heap++ext) root
        (CandidatePhysicalCut.capacities D s t L B (CandidatePhysicalCut.numberEquiv n L (.inl a))
          (CandidatePhysicalCut.numberEquiv n L (.inr true))).bits ∧
      NaturalRun program (steps level) (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 5) := by
  obtain ⟨ext,args,root,rep,body⟩ := natural_capacity size nodeFields termFields palette tape
  refine ⟨ext,args,root,?_,body⟩
  rw [← CandidateCapacityValues.capacity_word D s t L B (.inl a) (.inr true),
    ← CandidateTerminalFlagsProgram.result_sink D s t L B a level numeric]
  exact rep

end DirectedFlowCutGap.CandidateTerminalCapacityProgram
