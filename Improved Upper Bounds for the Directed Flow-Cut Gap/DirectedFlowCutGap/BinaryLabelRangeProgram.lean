import DirectedFlowCutGap.CandidateCapacityWords
import DirectedFlowCutGap.PathCostMaterialization
import DirectedFlowCutGap.ConcreteExpressionProgram

/-! Enumerate canonical binary labels in order from a stored binary count. -/

namespace DirectedFlowCutGap.BinaryLabelRangeProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open PathCostMaterialization (WordList list_extend)

def incrementLabel (pc : Fin 16) : Fin 65 := ⟨32+pc.val,by omega⟩
def counterLabel (pc : Fin 17) : Fin 65 := if pc.val=16 then 1 else ⟨48+pc.val,by omega⟩

def program : Program 65 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .call (counterLabel 0) 1 .r3
    | 1 => .move .r0 .r3 2
    | 2 => .make .r1 .nil 3
    | 3 => .call 8 4 .r3
    | 8 => .branch .r0 9 31 31 10
    | 9 => .ret .r0
    | 10 => .field .r0 .r0 true 11
    | 11 => .call 20 12 .r2
    | 12 => .move .r3 .r1 13
    | 13 => .move .r1 .r2 14
    | 14 => .call 8 15 .r1
    | 15 => .make .r3 (.pair .r3 .r1) 16
    | 16 => .ret .r3
    | 20 => .move .r0 .r1 (incrementLabel 15)
    | _ => .halt
  else if h : pc.val<48 then
    if pc.val=46 then .ret .r3
    else ReferenceProgramLabels.instruction incrementLabel (BinaryIncrementProgram.program ⟨pc.val-32,by omega⟩)
  else ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program ⟨pc.val-48,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 65))
    (tape : Bits) (pc : Fin 65) : NaturalState 65 := ⟨heap,heap.length,r,stack,pc,tape⟩

def wordsFrom (start : ℕ) : ℕ→List Bits
  | 0 => []
  | count+1 => start.bits::wordsFrom (start+1) count

@[simp] theorem words_length (start count : ℕ) : (wordsFrom start count).length=count := by
  induction count generalizing start with
  | zero => rfl
  | succ k ih => simp [wordsFrom,ih]

theorem words_get (start count i : ℕ) (hi : i<(wordsFrom start count).length) :
    (wordsFrom start count)[i]=(start+i).bits := by
  induction count generalizing start i with
  | zero => simp [wordsFrom] at hi
  | succ k ih =>
    cases i
    · simp [wordsFrom]
    · rename_i i
      have inside : i<(wordsFrom (start+1) k).length := by simp at hi ⊢; omega
      simpa [wordsFrom,Nat.add_assoc,Nat.add_comm 1] using ih (start+1) i inside

theorem words_fin (n : ℕ) : wordsFrom 0 n = (List.finRange n).map (fun i => i.val.bits) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [words_get _ _ _ hi,Nat.zero_add,List.getElem_map,List.getElem_finRange,Fin.val_cast]

def loopSteps (start : ℕ) : ℕ→ℕ
  | 0 => 2
  | count+1 => BinaryIncrementProgram.steps start.bits+loopSteps (start+1) count+11

theorem loopSteps_le (start count limit : ℕ) (within : start+count≤limit) :
    loopSteps start count ≤ count*(8*limit.size+16)+2 := by
  induction count generalizing start with
  | zero => simp [loopSteps]
  | succ k ih =>
    have preceding := ih (start+1) (by omega)
    have increment := BinaryIncrementProgram.steps_bound start.bits
    rw [Nat.size_eq_bits_len] at increment
    have width := Nat.size_le_size (by omega : start≤limit)
    rw [loopSteps,Nat.succ_mul k (8*limit.size+16)]
    omega

private theorem increment_bits (j : ℕ) : (increment true j.bits).1=(j+1).bits := by
  have h := trim_spec j.bits
  have e := normal_bits h.1
  rw [h.2.1,value_bits] at e
  have hn : Normal j.bits := e ▸ h.1
  simpa [CandidateCapacityWords.word,CandidateCapacityWords.barrier,CandidateCapacityFlags.amount,value_bits]
    using CandidateCapacityWords.canonical hn false true

private theorem increment_slots (pc : Fin 16) (h : BinaryIncrementProgram.program pc≠.halt) :
    program (incrementLabel pc)=
      ReferenceProgramLabels.instruction incrementLabel (BinaryIncrementProgram.program pc) := by
  by_cases hp : pc.val=14
  · have eq : pc=14 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,incrementLabel,show ¬32+pc.val<32 by omega,show 32+pc.val<48 by omega,show 32+pc.val≠46 by omega]

private theorem counter_slots (pc : Fin 17) (h : BinaryCounterProgram.program pc≠.halt) :
    program (counterLabel pc)=ReferenceProgramLabels.instruction counterLabel (BinaryCounterProgram.program pc) := by
  by_cases hp : pc.val=16
  · have eq : pc=16 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,counterLabel,hp,show ¬48+pc.val<32 by omega,show ¬48+pc.val<48 by omega]

private theorem increment_call {heap : NaturalHeap} {r : Registers ℕ} {j : ℕ}
    (label : BoolList heap r.b j.bits) (stack : List (Frame ℕ 65)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (j+1).bits ∧
      NaturalRun program (BinaryIncrementProgram.steps j.bits+4) (state heap r stack tape 11) []
        (state (heap++ext) (r.set .r2 root) stack tape 12) := by
  let args := r.set .r0 r.b
  let caller : Frame ℕ 65 := ⟨12,.r2,r⟩
  have setup : NaturalRun program 2 (state heap r stack tape 11) []
      (state heap args (caller::stack) tape (incrementLabel 15)) := by
    apply ReferenceProgramSteps.sound
    rfl
  obtain ⟨ext,root,len,body,rep⟩ := BinaryIncrementProgram.increment_return (a:=args.a) label heap.length
    args.b args.c args.d rfl args 14 [] tape
  have oldCall : tickNatural BinaryIncrementProgram.program
      (BinaryIncrementProgram.state heap heap.length args.a args.b args.c args.d [] tape 15)=
      some ⟨BinaryIncrementProgram.state heap heap.length args.a args.b args.c args.d [⟨14,.r3,args⟩] tape 0,[],0⟩ := by
    cases r
    rfl
  let stop := state (heap++ext) (args.set .r3 root) (caller::stack) tape (incrementLabel 14)
  have lift := ReferenceProgramLabels.run incrementLabel BinaryIncrementProgram.program program increment_slots (.step oldCall body)
  have lift := ReferenceProgramStack.run program (caller::stack) lift
  have run : NaturalRun program (BinaryIncrementProgram.steps j.bits+1)
      (state heap args (caller::stack) tape (incrementLabel 15)) [] stop := by
    cases r
    simpa [state,args,stop,BinaryIncrementProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramStack.state,Registers.set,len] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r2 root) stack tape 12,[],0⟩ := by
    simp [state,stop,program,tickNatural,incrementLabel,caller,Registers.get,Registers.set]
  refine ⟨ext,root,by simpa only [increment_bits] using rep,?_⟩
  have trace := append_run setup (append_run run (.step ret (.done _)))
  have num : 2+(BinaryIncrementProgram.steps j.bits+1+1)=BinaryIncrementProgram.steps j.bits+4 := by omega
  rw [← num]
  exact trace

private theorem loop_return {heap : NaturalHeap} {r : Registers ℕ} {start count : ℕ}
    (fuel : IndexSpine heap r.a count) (label : BoolList heap r.b start.bits)
    (caller : Frame ℕ 65) (stack : List (Frame ℕ 65)) (tape : Bits) :
    ∃ ext root,WordList (heap++ext) root (wordsFrom start count) ∧
      NaturalRun program (loopSteps start count) (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction count generalizing heap r start caller stack with
  | zero =>
    cases fuel with
    | nil hp =>
      refine ⟨[],r.a,by simpa [wordsFrom] using WordList.nil hp,?_⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,loopSteps,state,program,tickNatural,Registers.get,tagBranch,hp]
  | succ k ih =>
    cases fuel with
    | @cons _ payload tail _ hp ht =>
      let saved := caller::stack
      let next := r.set .r0 tail
      have setup : NaturalRun program 2 (state heap r saved tape 8) [] (state heap next saved tape 11) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,tagBranch,next,hp]
      obtain ⟨ei,nxt,stepWord,advance⟩ := increment_call (r:=next) label saved tape
      let mid := heap++ei
      let before := next.set .r2 nxt
      let args := (before.set .r3 r.b).set .r1 nxt
      let recFrame : Frame ℕ 65 := ⟨15,.r1,args⟩
      have descend : NaturalRun program 3 (state mid before saved tape 12) [] (state mid args (recFrame::saved) tape 8) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,before,next,recFrame]
      obtain ⟨er,rest,rep,body⟩ := ih (r:=args) (indexSpine_extend ht ei) stepWord recFrame saved
      let grown := mid++er
      let cell : Cell ℕ := .pair r.b rest
      let fresh := grown.length
      have finish : NaturalRun program 2 (state grown (args.set .r1 rest) saved tape 15) []
          (state (grown++[cell]) (caller.saved.set caller.destination fresh) stack tape caller.continuation) := by
        apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,
          allocateNatural,Recipe.cell,args,cell,fresh,saved]
      have stored : WordList (grown++[cell]) fresh (wordsFrom start (k+1)) := .cons
        (by simp [fresh,cell]) (boolList_extend (boolList_extend (boolList_extend label ei) er) [cell])
        (list_extend rep [cell])
      refine ⟨ei++er++[cell],fresh,?_,?_⟩
      · simpa only [grown,mid,List.append_assoc] using stored
      · have run := append_run setup (append_run advance (append_run descend (append_run body finish)))
        simp only [loopSteps]
        convert run using 1 <;> first | rfl | omega | simp only [grown,mid,List.append_assoc]

def steps (count : Bits) : ℕ := BinaryCounterProgram.steps count+loopSteps 0 (value count)+4

theorem steps_le (count : Bits) : steps count ≤
    value count*(8*(value count).size+19)+10*count.length+9 := by
  have a := BinaryCounterProgram.steps_bound count
  have b := loopSteps_le 0 (value count) (value count) (by simp)
  unfold steps
  simp only [Nat.mul_add] at b ⊢
  omega

theorem natural_range {heap : NaturalHeap} {r : Registers ℕ} {count : Bits}
    (input : BoolList heap r.a count) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),WordList (heap++ext) root (wordsFrom 0 (value count)) ∧
      NaturalRun program (steps count) (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 4) := by
  obtain ⟨ec,fuel,len,convert,spine⟩ := BinaryCounterProgram.convert_return input heap.length r.b r.c r.d rfl r 16 [] tape
  let counter : Frame ℕ 65 := ⟨1,.r3,r⟩
  let after := r.set .r3 fuel
  let mid := heap++ec
  let args := (after.set .r0 fuel).set .r1 mid.length
  let caller : Frame ℕ 65 := ⟨4,.r3,args⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [counter] tape (counterLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run counterLabel BinaryCounterProgram.program program counter_slots convert
  have counterRun : NaturalRun program (BinaryCounterProgram.steps count)
      (state heap r [counter] tape (counterLabel 0)) [] (state mid after [] tape 1) := by
    cases r
    simpa [state,mid,after,counter,BinaryCounterProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,counterLabel,Registers.set,len] using lift
  have setup : NaturalRun program 3 (state mid after [] tape 1) [] (state (mid++[.nil]) args [caller] tape 8) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,after,caller,
      allocateNatural,Recipe.cell]
  have zeroWord : BoolList (mid++[.nil]) args.b (0 : ℕ).bits := .nil (by simp [args,Registers.set])
  obtain ⟨er,root,rep,body⟩ := loop_return (r:=args) (indexSpine_extend spine [.nil]) zeroWord caller [] tape
  refine ⟨ec++[.nil]++er,args,root,?_,?_⟩
  · simpa only [mid,List.append_assoc] using rep
  · have run := NaturalRun.step enter (append_run counterRun (append_run setup body))
    unfold steps
    convert run using 1 <;> first | rfl | omega | simp only [caller,List.append_assoc]

end DirectedFlowCutGap.BinaryLabelRangeProgram
