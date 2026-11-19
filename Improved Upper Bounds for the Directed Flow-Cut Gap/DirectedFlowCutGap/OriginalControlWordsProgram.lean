import DirectedFlowCutGap.BinarySizeExecution
import DirectedFlowCutGap.CanonicalArithmeticProgram
import DirectedFlowCutGap.ReferenceProgramInvocation
import DirectedFlowCutGap.ReferenceProgramSteps
import DirectedFlowCutGap.BinaryBoundedSampler
import DirectedFlowCutGap.IntegerEpochParameters

/-! Compute the integer restart ratio and cubic limit on the represented count. -/

namespace DirectedFlowCutGap.OriginalControlWordsProgram

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor
open BooleanTableRead (BoolList)
open ConcreteExpressionProgram (append_run)
open IntegerEpochParameters (restart)

def arithmeticLabel (pc : Fin 116) : Fin 180 := ⟨16+pc.val,by omega⟩
def sizeLabel (pc : Fin 48) : Fin 180 := ⟨132+pc.val,by omega⟩

def program : Program 180 := fun pc =>
  if h : pc.val < 16 then
    match pc.val with
    | 0 => .call (arithmeticLabel 114) 1 .r3
    | 1 => .move .r0 .r3 2
    | 2 => .call (sizeLabel 46) 3 .r0
    | 3 => .move .r1 .r2 4
    | 4 => .call (arithmeticLabel 114) 5 .r3
    | 8 => .move .r1 .r0 9
    | 9 => .call (arithmeticLabel 110) 10 .r1
    | 10 => .call (arithmeticLabel 110) 11 .r3
    | _ => .halt
  else if h : pc.val < 132 then
    if pc.val=131 then .ret .r3
    else ReferenceProgramLabels.instruction arithmeticLabel (CanonicalArithmeticProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=179 then .ret .r3
  else ReferenceProgramLabels.instruction sizeLabel (BinarySizeProgram.program ⟨pc.val-132,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 180

private theorem arithmetic_slots (pc : Fin 116) (used : CanonicalArithmeticProgram.program pc≠.halt) :
    program (arithmeticLabel pc)=ReferenceProgramLabels.instruction arithmeticLabel (CanonicalArithmeticProgram.program pc) := by
  by_cases stop : pc.val=115
  · have eq : pc=115 := Fin.ext stop
    subst pc
    exact (used rfl).elim
  · simp [program,arithmeticLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<132 by omega,
      show 16+pc.val≠131 by omega]

private theorem size_slots (pc : Fin 48) (used : BinarySizeProgram.program pc≠.halt) :
    program (sizeLabel pc)=ReferenceProgramLabels.instruction sizeLabel (BinarySizeProgram.program pc) := by
  by_cases stop : pc.val=47
  · have eq : pc=47 := Fin.ext stop
    subst pc
    exact (used rfl).elim
  · simp [program,sizeLabel,show ¬132+pc.val<16 by omega,show ¬132+pc.val<132 by omega,
      show 132+pc.val≠179 by omega]

private theorem arithmetic (product : Bool) {xs ys : Bits} {heap : NaturalHeap} {r : Registers ℕ}
    (left : BoolList heap r.a xs) (right : BoolList heap r.b ys) {pc dest : Fin 180} {dst : Reg}
    (call : program pc=.call (arithmeticLabel (CanonicalArithmeticProgram.top product)) dest dst)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),
      BoolList (heap++ext) root (CanonicalArithmeticProgram.result product xs ys) ∧
      NaturalRun program (CanonicalArithmeticProgram.instructions product xs ys+2) (state heap r [] tape pc) []
        (state (heap++ext) (r.set dst root) [] tape dest) := by
  let start := @ReferenceProgramInvocation.state 116 heap r [] tape (CanonicalArithmeticProgram.top product)
  obtain ⟨ext,root,_,run,result⟩ := CanonicalArithmeticProgram.canonical_high product start rfl rfl left right rfl
  have run' : NaturalRun CanonicalArithmeticProgram.program (CanonicalArithmeticProgram.instructions product xs ys)
      start [] (@ReferenceProgramInvocation.state 116 (heap++ext) (r.set .r3 root) [] tape 115) := by
    simpa [start,ReferenceProgramInvocation.state,CanonicalArithmeticProgram.state,Registers.set] using run
  refine ⟨ext,root,result,?_⟩
  simpa [start,Registers.set,Registers.get] using ReferenceProgramInvocation.call arithmeticLabel arithmetic_slots
    (result:=.r3) call (by rfl) [] run'

private theorem measured {xs : Bits} {heap : NaturalHeap} {r : Registers ℕ}
    (left : BoolList heap r.a xs) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),
      BoolList (heap++ext) root (BinaryCounters.sizeBits xs).1 ∧
      NaturalRun program (BinarySizeProgram.steps xs+3) (state heap r [] tape 2) []
        (state (heap++ext) (r.set .r0 root) [] tape 3) := by
  obtain ⟨ext,root,_,run,result⟩ := BinarySizeProgram.size left heap.length r.b r.c r.d rfl [] tape
  have run' : NaturalRun BinarySizeProgram.program (BinarySizeProgram.steps xs+1)
      (@ReferenceProgramInvocation.state 48 heap r [] tape 46) []
      (@ReferenceProgramInvocation.state 48 (heap++ext) (r.set .r3 root) [] tape 47) := by
    simpa [ReferenceProgramInvocation.state,BinarySizeProgram.state,Registers.set] using run
  refine ⟨ext,root,result,?_⟩
  simpa [Registers.set,Registers.get,Nat.add_assoc] using ReferenceProgramInvocation.call sizeLabel size_slots
    (caller:=2) (continuation:=3) (result:=.r3) (dst:=.r0) (by rfl) (by rfl) [] run'

private theorem arithmetic_exact (product : Bool) (xs ys : Bits) :
    (CanonicalArithmeticProgram.result product xs ys)=
      (if product then value xs*value ys else value xs+value ys).bits := by
  have spec := trim_spec (CanonicalArithmeticProgram.raw product xs ys)
  have normal := normal_bits spec.1
  rw [spec.2.1] at normal
  cases product with
  | false => simpa only [CanonicalArithmeticProgram.result,CanonicalArithmeticProgram.raw,Bool.false_eq_true,ite_false,
      (add_spec false xs ys).1,Bool.false_eq_true,ite_false,Bool.toNat_false,Nat.add_zero] using normal.symm
  | true => simpa only [CanonicalArithmeticProgram.result,CanonicalArithmeticProgram.raw,ite_true,(mul_spec xs ys).1] using normal.symm

def restartLimit (n : ℕ) : ℕ := 500*(n+6)^2

private theorem word_width (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

set_option maxHeartbeats 1800000 in
theorem natural_restart {heap : NaturalHeap} {r : Registers ℕ} {n : ℕ}
    (count : BoolList heap r.a n.bits) (two : BoolList heap r.b [false,true]) (one : BoolList heap r.c [true])
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (out : Registers ℕ) (k : ℕ),
      BoolList (heap++ext) out.d (restart n).bits ∧ k≤restartLimit n ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) out [] tape 5) := by
  obtain ⟨e1,sum,sumWord,add⟩ := arithmetic false count two (pc:=0) (dest:=1) (dst:=.r3) (by rfl) tape
  have shifted : CanonicalArithmeticProgram.result false n.bits [false,true]=(n+2).bits := by
    rw [arithmetic_exact,value_bits]
    rfl
  rw [shifted] at sumWord
  let h1 := heap++e1
  let regs := (r.set .r3 sum).set .r0 sum
  have move : tickNatural program (state h1 (r.set .r3 sum) [] tape 1) = some ⟨state h1 regs [] tape 2,[],0⟩ := rfl
  obtain ⟨e2,len,lenWord,size⟩ := measured (r:=regs) sumWord tape
  let h2 := h1++e2
  let lengthRegs := regs.set .r0 len
  let ready := lengthRegs.set .r1 r.c
  have put : tickNatural program (state h2 lengthRegs [] tape 3) = some ⟨state h2 ready [] tape 4,[],0⟩ := rfl
  obtain ⟨e3,result,bits,finish⟩ := arithmetic false (r:=ready) lenWord
    (boolList_extend (boolList_extend one e1) e2) (pc:=4) (dest:=5) (dst:=.r3) (by rfl) tape
  have sizeValue := (BinaryCounters.sizeBits_spec (n+2).bits).1
  rw [value_bits] at sizeValue
  have sizeEq : (n+2).size=Nat.log2 (n+2)+1 := BinaryBoundedSampler.size_eq_width (by omega)
  have correct : CanonicalArithmeticProgram.result false (BinaryCounters.sizeBits (n+2).bits).1 [true] =
      (restart n).bits := by
    rw [arithmetic_exact]
    simp only [Bool.false_eq_true,ite_false,sizeValue,sizeEq,restart]
    rfl
  have c1 := CanonicalArithmeticProgram.instructions_bound false n.bits [false,true]
  have c2 := BinarySizeProgram.steps_bound (n+2).bits
  have c3 := CanonicalArithmeticProgram.instructions_bound false (BinaryCounters.sizeBits (n+2).bits).1 [true]
  have w2 := word_width (n+2)
  have w1 := word_width n
  have w3 : (BinaryCounters.sizeBits (n+2).bits).1.length≤n+3 := by
    exact (BinaryCounters.lengthBits_spec (trim (n+2).bits).1).2.1.trans
      (Nat.add_le_add_right ((trim_spec (n+2).bits).2.2.1.trans w2) 1)
  rw [correct] at bits
  let cost := CanonicalArithmeticProgram.instructions false n.bits [false,true]+2+
    (BinarySizeProgram.steps (n+2).bits+3+
      (CanonicalArithmeticProgram.instructions false (BinaryCounters.sizeBits (n+2).bits).1 [true]+2+1)+1)
  refine ⟨e1++e2++e3,ready.set .r3 result,cost,?_,?_,?_⟩
  · simpa only [h2,h1,List.append_assoc,Registers.set] using bits
  · have p1 : (n.bits.length+4)^2≤(n+6)^2 := Nat.pow_le_pow_left (by omega) 2
    have p2 : ((n+2).bits.length+1)^2≤(n+6)^2 := Nat.pow_le_pow_left (by omega) 2
    have p3 : ((BinaryCounters.sizeBits (n+2).bits).1.length+3)^2≤(n+6)^2 := Nat.pow_le_pow_left (by omega) 2
    simp only [List.length_cons,List.length_nil,Nat.zero_add,Nat.reduceAdd,Nat.add_assoc] at c1 c3
    unfold cost restartLimit BinarySizeProgram.inputSteps at *
    nlinarith
  · simpa only [cost,h2,h1,regs,lengthRegs,ready,List.append_assoc,List.nil_append,Nat.add_assoc] using
      append_run add (NaturalRun.step move (append_run size (NaturalRun.step put finish)))

def cubeLimit (n : ℕ) : ℕ := 400*(n^2+n+2)^2+5

theorem natural_cube {heap : NaturalHeap} {r : Registers ℕ} {n : ℕ}
    (count : BoolList heap r.a n.bits) (tape : Bits) :
    ∃ (ext : NaturalHeap) (out : Registers ℕ) (k : ℕ),
      BoolList (heap++ext) out.d (n^3).bits ∧ k≤cubeLimit n ∧
      NaturalRun program k (state heap r [] tape 8) [] (state (heap++ext) out [] tape 11) := by
  let args := r.set .r1 r.a
  have move : tickNatural program (state heap r [] tape 8)=some ⟨state heap args [] tape 9,[],0⟩ := rfl
  obtain ⟨ex,sq,squared,first⟩ := arithmetic true (r:=args) count count (pc:=9) (dest:=10) (dst:=.r1)
    (by rfl) tape
  have square : CanonicalArithmeticProgram.result true n.bits n.bits=(n^2).bits := by
    simp only [arithmetic_exact,ite_true,value_bits,pow_two]
  rw [square] at squared
  let again := args.set .r1 sq
  obtain ⟨ext,cube,cubed,last⟩ := arithmetic true (r:=again) (boolList_extend count ex) squared
    (pc:=10) (dest:=11) (dst:=.r3) (by rfl) tape
  have perfect : CanonicalArithmeticProgram.result true n.bits (n^2).bits=(n^3).bits := by
    simp only [arithmetic_exact,ite_true,value_bits]
    apply congrArg Nat.bits
    ring
  rw [perfect] at cubed
  let cost := CanonicalArithmeticProgram.instructions true n.bits n.bits+2+
    (CanonicalArithmeticProgram.instructions true n.bits (n^2).bits+2)+1
  refine ⟨ex++ext,again.set .r3 cube,cost,?_,?_,?_⟩
  · simpa only [List.append_assoc,Registers.set] using cubed
  · have h1 := CanonicalArithmeticProgram.instructions_bound true n.bits n.bits
    have h2 := CanonicalArithmeticProgram.instructions_bound true n.bits (n^2).bits
    have hn := word_width n
    have hn2 := word_width (n^2)
    have small : n≤n^2 := by
      calc n = n*1 := by simp
        _ ≤ n^2 := by
          cases n with
          | zero => decide
          | succ n => rw [pow_two]; exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le _))
    have p1 : (n.bits.length+n.bits.length+2)^2≤(n^2+n+2)^2 := Nat.pow_le_pow_left (by omega) 2
    have p2 : (n.bits.length+(n^2).bits.length+2)^2≤(n^2+n+2)^2 := Nat.pow_le_pow_left (by omega) 2
    unfold cost cubeLimit
    omega
  · simpa only [cost,args,again,List.append_assoc,List.nil_append,Nat.add_assoc] using
      NaturalRun.step move (append_run first last)

end DirectedFlowCutGap.OriginalControlWordsProgram
