import DirectedFlowCutGap.CandidateShiftSelectProgram

/-!
# Capacity flags at the artificial source and sink

The program tests the stored threshold word for zero. It then checks a
node's sign and active flag and uses the supplied matching-port flag to
enforce the terminal pin.
-/

namespace DirectedFlowCutGap.CandidateTerminalFlagsProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open EncodedCandidateCapacity (Input)
open CandidateEnumeration (Node)
open CandidateShiftSelectProgram (Flags)

def result (sinkSide isZeroLevel sign active pinned : Bool) : Bool×Bool :=
  (!isZeroLevel && sign==sinkSide && active,if isZeroLevel then !sinkSide else pinned)

private theorem unitFlag_active {n L : ℕ} (D : Input n) (sign : Bool) (a : Node n L) :
    CandidateCapacityFlags.unitFlag D sign a =
      (a.2.val != 0 && a.1.2==sign && CandidatePortGapProgram.active D a.1.1) := by
  rcases a with ⟨⟨p,b⟩,i⟩
  cases p <;> rfl

theorem result_source {n : ℕ} (D : Input n) (s t : Fin n) (L B : ℕ) (a : Node n L)
    (level : Bits) (numeric : value level=a.2.val) :
    result false (isZero level).1 a.1.2 (CandidatePortGapProgram.active D a.1.1)
        (decide (a.1.1=TerminalPorts.sink t)) = CandidateCapacityFlags.flags D s t L B (.inr false) (.inl a) := by
  have zz : (isZero level).1=(a.2.val==0) := by
    rw [Bool.eq_iff_iff,(isZero_spec level).1,numeric,beq_iff_eq]
  simp only [CandidateCapacityFlags.flags,unitFlag_active,result,zz,bne]
  cases a.2.val==0 <;> rfl

theorem result_sink {n : ℕ} (D : Input n) (s t : Fin n) (L B : ℕ) (a : Node n L)
    (level : Bits) (numeric : value level=a.2.val) :
    result true (isZero level).1 a.1.2 (CandidatePortGapProgram.active D a.1.1)
        (decide (a.1.1=TerminalPorts.source s)) = CandidateCapacityFlags.flags D s t L B (.inl a) (.inr true) := by
  have zz : (isZero level).1=(a.2.val==0) := by
    rw [Bool.eq_iff_iff,(isZero_spec level).1,numeric,beq_iff_eq]
  have pos : decide (0<a.2.val)= !(a.2.val==0) := by
    apply Bool.eq_iff_iff.mpr
    simp [Nat.pos_iff_ne_zero]
  simp only [CandidateCapacityFlags.flags,unitFlag_active,result,zz,bne,pos]
  cases a.2.val==0 <;> rfl

def label (pc : Fin 9) : Fin 41 := if pc.val=8 then 1 else ⟨32+pc.val,by omega⟩

def program : Program 41 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .call (label 0) 1 .r3
    | 1 => .branch .r3 31 2 12 31
    | 2 => .field .r0 .r2 false 3
    | 3 => .field .r2 .r2 true 4
    | 4 => .field .r3 .r1 false 5
    | 5 => .branch .r0 31 6 7 31
    | 6 => .branch .r3 31 8 9 31
    | 7 => .branch .r3 31 9 8 31
    | 8 => .field .r0 .r1 true 20
    | 9 => .make .r0 (.flag false) 20
    | 12 => .field .r0 .r2 false 13
    | 13 => .branch .r0 31 14 15 31
    | 14 => .make .r2 (.flag true) 16
    | 15 => .make .r2 (.flag false) 16
    | 16 => .make .r0 (.flag false) 20
    | 20 => .make .r3 (.pair .r0 .r2) 21
    | _ => .halt
  else ReferenceProgramLabels.instruction label (BinaryZeroProgram.program ⟨pc.val-32,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 41))
    (tape : Bits) (pc : Fin 41) : NaturalState 41 := ⟨heap,heap.length,r,stack,pc,tape⟩

def steps (level : Bits) : ℕ := BinaryZeroProgram.steps level + 1 + if (isZero level).1 then 6 else 8

theorem steps_le (level : Bits) : steps level ≤ 4*level.length+12 := by
  have h := BinaryZeroProgram.steps_bound level
  unfold steps
  split <;> omega

private theorem slots (pc : Fin 9) (h : BinaryZeroProgram.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (BinaryZeroProgram.program pc) := by
  by_cases hp : pc.val=8
  · have eq : pc=8 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,label,hp,show ¬32+pc.val<32 by omega]

private theorem flags_extend {heap : NaturalHeap} {root : ℕ} {b c : Bool}
    (h : Flags heap root b c) (ext : NaturalHeap) : Flags (heap++ext) root b c := by
  obtain ⟨x,y,pair,a,d⟩ := h
  exact ⟨x,y,lookup_extend pair ext,lookup_extend a ext,lookup_extend d ext⟩

private theorem finish_nonzero {heap : NaturalHeap} {r : Registers ℕ} {side sign active pin : Bool}
    (tested : heap[r.d]?=some (.flag false)) (nodeFields : Flags heap r.b sign active)
    (terminalFields : Flags heap r.c side pin) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      Flags (heap++ext) root (result side false sign active pin).1 pin ∧
      NaturalRun program 8 (state heap r [] tape 1) [] (state (heap++ext) (args.set .r3 root) [] tape 21) := by
  obtain ⟨s,a,nodePair,hs,ha⟩ := nodeFields
  obtain ⟨mode,p,terminalPair,hm,hp⟩ := terminalFields
  let i := heap.length
  let same := sign==side
  let gate := if same then a else i
  let root := if same then i else i+1
  let ext : NaturalHeap := if same then [.pair gate p] else [.flag false,.pair gate p]
  let args := ((r.set .r0 gate).set .r2 p).set .r3 s
  refine ⟨ext,args,root,⟨gate,p,?_,?_,lookup_extend hp _⟩,?_⟩
  · cases selected : same
    · have inside : heap.length ≤ i+1 := Nat.le_succ _
      rw [show root=i+1 by simp [root,selected],show ext=[.flag false,.pair gate p] by simp [ext,selected],
        List.getElem?_append_right inside]
      rw [show i+1-heap.length=1 by simp [i]]
      rfl
    · simp [root,ext,selected,i]
  · cases hb : same
    · have hg : gate=i := by simp [gate,hb]
      have hw : (result side false sign active pin).1=false := by simp [result,← show same=(sign==side) from rfl,hb]
      simp [ext,hb,hg,hw,i]
    · have hg : gate=a := by simp [gate,hb]
      have hw : (result side false sign active pin).1=active := by simp [result,← show same=(sign==side) from rfl,hb]
      rw [hg,hw]
      exact lookup_extend ha ext
  · let loaded := ((r.set .r0 mode).set .r2 p).set .r3 s
    have setup : NaturalRun program 4 (state heap r [] tape 1) [] (state heap loaded [] tape 5) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,tagBranch,Registers.get,Registers.set,
        loaded,tested,terminalPair,nodePair]
    have compare : NaturalRun program 2 (state heap loaded [] tape 5) []
        (state heap loaded [] tape (if same then 8 else 9)) := by
      apply ReferenceProgramSteps.sound
      cases sign <;> cases side <;>
        simp [ReferenceProgramSteps.run,state,program,tickNatural,tagBranch,Registers.get,Registers.set,loaded,same,hm,hs]
    have finish : NaturalRun program 2 (state heap loaded [] tape (if same then 8 else 9)) []
        (state (heap++ext) (args.set .r3 root) [] tape 21) := by
      apply ReferenceProgramSteps.sound
      cases selected : same <;>
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,loaded,
          gate,root,args,ext,i,allocateNatural,Recipe.cell,List.append_assoc,Nat.add_assoc, *]
    exact append_run setup (append_run compare finish)

private theorem finish_zero {heap : NaturalHeap} {r : Registers ℕ} {side pin : Bool}
    (tested : heap[r.d]?=some (.flag true)) (terminalFields : Flags heap r.c side pin) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),Flags (heap++ext) root false (!side) ∧
      NaturalRun program 6 (state heap r [] tape 1) [] (state (heap++ext) (args.set .r3 root) [] tape 21) := by
  obtain ⟨s,p,pair,mode,_⟩ := terminalFields
  let i := heap.length
  let ext : NaturalHeap := [.flag (!side),.flag false,.pair (i+1) i]
  let args := (r.set .r0 (i+1)).set .r2 i
  refine ⟨ext,args,i+2,⟨i+1,i,?_,?_,?_⟩,?_⟩
  · rw [List.getElem?_append_right (show heap.length ≤ i+2 by change i ≤ i+2; omega)]
    rw [show i+2-heap.length=2 by simp [i]]
    rfl
  · rw [List.getElem?_append_right (show heap.length ≤ i+1 from Nat.le_succ _)]
    rw [show i+1-heap.length=1 by simp [i]]
    rfl
  · simp [i,ext]
  · let loaded := r.set .r0 s
    have setup : NaturalRun program 2 (state heap r [] tape 1) [] (state heap loaded [] tape 13) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,tagBranch,Registers.get,Registers.set,loaded,tested,pair]
    have compare : NaturalRun program 1 (state heap loaded [] tape 13) []
        (state heap loaded [] tape (if side then 15 else 14)) := by
      apply ReferenceProgramSteps.sound
      cases side <;>
        simp [ReferenceProgramSteps.run,state,program,tickNatural,tagBranch,Registers.get,Registers.set,loaded,mode]
    have finish : NaturalRun program 3 (state heap loaded [] tape (if side then 15 else 14)) []
        (state (heap++ext) (args.set .r3 (i+2)) [] tape 21) := by
      apply ReferenceProgramSteps.sound
      cases side <;>
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,
          allocateNatural,Recipe.cell,i,ext,args,loaded,List.append_assoc,Nat.add_assoc]
    exact append_run setup (append_run compare finish)

theorem natural_flags {heap : NaturalHeap} {r : Registers ℕ} {level : Bits} {side sign active pin : Bool}
    (size : BoolList heap r.a level) (nodeFields : Flags heap r.b sign active)
    (terminalFields : Flags heap r.c side pin) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      Flags (heap++ext) root (result side (isZero level).1 sign active pin).1 (result side (isZero level).1 sign active pin).2 ∧
      NaturalRun program (steps level) (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 21) := by
  let b := (isZero level).1
  let extra : NaturalHeap := [.flag b]
  let mid := heap++extra
  let args := r.set .r3 heap.length
  let frame : Frame ℕ 41 := ⟨1,.r3,r⟩
  have zeroRun := BinaryZeroProgram.zero_return size heap.length r.b r.c r.d rfl r 8 [] tape
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [frame] tape (label 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run label BinaryZeroProgram.program program slots zeroRun
  have trace : NaturalRun program (BinaryZeroProgram.steps level)
      (state heap r [frame] tape (label 0)) [] (state mid args [] tape 1) := by
    cases r
    simpa [state,mid,extra,b,args,frame,Registers.set,BinaryZeroProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,label] using lift
  have test := NaturalRun.step enter trace
  have read : mid[args.d]?=some (.flag b) := by simp [mid,extra,args,Registers.set]
  have nd : Flags mid args.b sign active := flags_extend nodeFields extra
  have tf : Flags mid args.c side pin := flags_extend terminalFields extra
  change ∃ ext args root,Flags _ root (result side b sign active pin).1 (result side b sign active pin).2 ∧ _
  cases next : b
  · obtain ⟨ext,out,root,rep,run⟩ := finish_nonzero (next ▸ read) nd tf tape
    refine ⟨extra++ext,out,root,?_,?_⟩
    · simpa only [mid,List.append_assoc,result,ite_false,Bool.false_eq_true] using rep
    · have execution := append_run test run
      simpa only [mid,steps,← show b=(isZero level).1 from rfl,next,Bool.false_eq_true,ite_false,
        List.append_assoc,List.nil_append] using execution
  · obtain ⟨ext,out,root,rep,run⟩ := finish_zero (next ▸ read) tf tape
    refine ⟨extra++ext,out,root,?_,?_⟩
    · simpa only [mid,List.append_assoc,result,Bool.not_true,Bool.false_and,ite_true] using rep
    · have execution := append_run test run
      simpa only [mid,steps,← show b=(isZero level).1 from rfl,next,ite_true,
        List.append_assoc,List.nil_append] using execution

end DirectedFlowCutGap.CandidateTerminalFlagsProgram
