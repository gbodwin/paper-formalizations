import DirectedFlowCutGap.BinaryTrimProgram
import DirectedFlowCutGap.BinaryMultiplicationProgram

/-! Real addition and multiplication followed by the literal padding trimmer.
The returned bit list is exactly the canonical arithmetic output, rather than
merely a padded representation of the same number. -/
namespace DirectedFlowCutGap.CanonicalArithmeticProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor

def mulLabel (pc : Fin 96) : Fin 116 := ⟨pc.val,by omega⟩
def trimLabel (pc : Fin 13) : Fin 116 := ⟨pc.val+96,by omega⟩
def program : Program 116 := fun pc =>
  if pc.val=95 then .move .r0 .r3 107
  else if pc.val=108 then .ret .r3
  else if h : pc.val<96 then
    ReferenceProgramLabels.instruction mulLabel (BinaryMultiplicationProgram.program ⟨pc.val,h⟩)
  else if h : pc.val<109 then
    ReferenceProgramLabels.instruction trimLabel (BinaryTrimProgram.program ⟨pc.val-96,by omega⟩)
  else match pc.val with
  | 110 => .call 94 115 .r3
  | 111 => .call 60 95 .r3
  | 114 => .call 111 115 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 116)) (source : Bits) (pc : Fin 116) : NaturalState 116 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩
def raw (product : Bool) (xs ys : Bits) : Bits :=
  if product then (mul xs ys).1 else (add false xs ys).1
def result (product : Bool) (xs ys : Bits) : Bits := (trim (raw product xs ys)).1
def entry (product : Bool) : Fin 116 := if product then 94 else 111
def top (product : Bool) : Fin 116 := if product then 110 else 114
def rawSteps (product : Bool) (xs ys : Bits) : ℕ :=
  if product then BinaryMultiplicationProgram.steps xs ys+1
  else BinaryAdditionProgram.steps false xs ys+3
def rawCells (product : Bool) (xs ys : Bits) : ℕ :=
  if product then BinaryMultiplicationProgram.cells xs ys
  else BinaryAdditionProgram.cells false xs ys
def instructions (product : Bool) (xs ys : Bits) : ℕ :=
  rawSteps product xs ys+BinaryTrimProgram.steps (raw product xs ys)+4

theorem result_exact (product : Bool) (xs ys : Bits) :
    result product xs ys=(if product then mulCanonical xs ys else addCanonical xs ys).1 := by
  cases product <;> rfl

theorem mul_slots (pc : Fin 96) (h : BinaryMultiplicationProgram.program pc ≠ .halt) :
    program (mulLabel pc)=ReferenceProgramLabels.instruction mulLabel (BinaryMultiplicationProgram.program pc) := by
  by_cases hp : pc.val=95
  · have he : pc=95 := Fin.ext hp
    subst pc;simp [BinaryMultiplicationProgram.program] at h
  · simp [program,mulLabel,pc.isLt,hp,show ¬pc.val=108 by omega]

theorem trim_slots (pc : Fin 13) (h : BinaryTrimProgram.program pc ≠ .halt) :
    program (trimLabel pc)=ReferenceProgramLabels.instruction trimLabel (BinaryTrimProgram.program pc) := by
  by_cases hp : pc.val=12
  · have he : pc=12 := Fin.ext hp
    subst pc;simp [BinaryTrimProgram.program] at h
  · simp [program,trimLabel,show ¬pc.val+96=95 by omega,show ¬pc.val+96=108 by omega,
      show ¬pc.val+96<96 by omega,show pc.val+96<109 by omega]

theorem run_append {s u v : NaturalState 116} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- Both literal arithmetic branches reach the same real normalization move. -/
theorem raw_run (product : Bool) {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ)
    (hn : next=heap.length) (stack : List (Frame ℕ 116)) (source : Bits) :
    ∃ ext root, ext.length=rawCells product xs ys ∧
      NaturalRun program (rawSteps product xs ys)
        (state heap next a b c d stack source (entry product)) []
        (state (heap++ext) (next+ext.length) a b c root stack source 95) ∧
      BoolList (heap++ext) root (raw product xs ys) := by
  cases product with
  | true =>
    obtain ⟨ext,root,len,core,rep⟩ := BinaryMultiplicationProgram.mul_return left right next c d hn ⟨a,b,c,d⟩ 95 [] source
    have t94 : tickNatural BinaryMultiplicationProgram.program
        (BinaryMultiplicationProgram.state heap next a b c d [] source 94)=
        some ⟨BinaryMultiplicationProgram.state heap next a b c d [⟨95,.r3,⟨a,b,c,d⟩⟩] source 64,[],0⟩ := by
      simp [tickNatural,BinaryMultiplicationProgram.program,BinaryMultiplicationProgram.state]
    have lift := ReferenceProgramLabels.run mulLabel BinaryMultiplicationProgram.program program mul_slots (.step t94 core)
    have lift := ReferenceProgramStack.run program stack lift
    exact ⟨ext,root,len,by simpa [rawSteps,entry,ReferenceProgramLabels.state,ReferenceProgramLabels.frame,
      ReferenceProgramStack.state,BinaryMultiplicationProgram.state,mulLabel,state,len] using lift,rep⟩
  | false =>
    obtain ⟨ext,root,len,core,rep⟩ := BinaryMultiplicationProgram.addition_return left right next c d hn ⟨a,b,c,d⟩ 95 [] source
    have lift := ReferenceProgramLabels.run mulLabel BinaryMultiplicationProgram.program program mul_slots core
    have lift := ReferenceProgramStack.run program stack lift
    have body : NaturalRun program (BinaryAdditionProgram.steps false xs ys+2)
        (state heap next a b c d (⟨95,.r3,⟨a,b,c,d⟩⟩::stack) source 60) []
        (state (heap++ext) (next+ext.length) a b c root stack source 95) := by
      simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
        BinaryMultiplicationProgram.state,mulLabel,state,len] using lift
    have t111 : tickNatural program (state heap next a b c d stack source 111)=
        some ⟨state heap next a b c d (⟨95,.r3,⟨a,b,c,d⟩⟩::stack) source 60,[],0⟩ := by
      simp [tickNatural,program,state]
    exact ⟨ext,root,len,by simpa [rawSteps,entry,Nat.add_assoc] using NaturalRun.step t111 body,rep⟩

/-- The old arithmetic halt is an actual move; the trimmer's old halt is an
actual return through the preserved caller. -/
theorem normalize_return {word : Bits} {heap : NaturalHeap} {root : ℕ}
    (input : BoolList heap root word) (next a b c : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 116) (stack : List (Frame ℕ 116)) (source : Bits) :
    ∃ ext out, ext.length=(trim word).1.length ∧
      NaturalRun program (BinaryTrimProgram.steps word+3)
        (state heap next a b c root (⟨pc,.r3,saved⟩::stack) source 95) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc) ∧
      BoolList (heap++ext) out (trim word).1 := by
  obtain ⟨ext,out,len,core,rep⟩ := BinaryTrimProgram.trim_high
    (BinaryTrimProgram.state heap next root b c root [] source 11) rfl hn input rfl
  have lift := ReferenceProgramLabels.run trimLabel BinaryTrimProgram.program program trim_slots core
  have lift := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) lift
  have body : NaturalRun program (1+BinaryTrimProgram.steps word)
      (state heap next root b c root (⟨pc,.r3,saved⟩::stack) source 107) []
      (state (heap++ext) (next+ext.length) root b c out (⟨pc,.r3,saved⟩::stack) source 108) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
      BinaryTrimProgram.state,trimLabel,state] using lift
  have move : tickNatural program (state heap next a b c root (⟨pc,.r3,saved⟩::stack) source 95)=
      some ⟨state heap next root b c root (⟨pc,.r3,saved⟩::stack) source 107,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have ret : tickNatural program
      (state (heap++ext) (next+ext.length) root b c out (⟨pc,.r3,saved⟩::stack) source 108)=
      some ⟨state (heap++ext) (next+ext.length) saved.a saved.b saved.c out stack source pc,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  refine ⟨ext,out,len,?_,rep⟩
  convert run_append (NaturalRun.step move body) (.step ret (.done _)) using 1 <;> simp
  omega

/-- Callable exact canonical arithmetic, with exact heap extension count. -/
theorem canonical_return (product : Bool) {xs ys : Bits} {heap : NaturalHeap} {a b : ℕ}
    (left : BoolList heap a xs) (right : BoolList heap b ys) (next c d : ℕ)
    (hn : next=heap.length) (saved : Registers ℕ) (pc : Fin 116)
    (stack : List (Frame ℕ 116)) (source : Bits) :
    ∃ ext root, ext.length=rawCells product xs ys+(result product xs ys).length ∧
      NaturalRun program (rawSteps product xs ys+BinaryTrimProgram.steps (raw product xs ys)+3)
        (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source (entry product)) []
        (state (heap++ext) (next+ext.length) saved.a saved.b saved.c root stack source pc) ∧
      BoolList (heap++ext) root (result product xs ys) := by
  obtain ⟨ext1,r1,len1,run1,rep1⟩ := raw_run product left right next c d hn (⟨pc,.r3,saved⟩::stack) source
  obtain ⟨ext2,r2,len2,run2,rep2⟩ := normalize_return rep1 (next+ext1.length) a b c
    (by simp [hn]) saved pc stack source
  refine ⟨ext1++ext2,r2,by simp [len1,len2,result],?_,?_⟩
  · simpa [List.append_assoc,Nat.add_assoc] using run_append run1 run2
  · simpa [List.append_assoc,result] using rep2

theorem canonical_high (product : Bool) {xs ys : Bits} (initial : NaturalState 116)
    (pc0 : initial.pc=top product) (hn : initial.next=initial.heap.length)
    (left : BoolList initial.heap initial.registers.a xs)
    (right : BoolList initial.heap initial.registers.b ys) (empty : initial.stack=[]) :
    ∃ ext root, ext.length=rawCells product xs ys+(result product xs ys).length ∧
      NaturalRun program (instructions product xs ys) initial []
        (state (initial.heap++ext) (initial.next+ext.length) initial.registers.a
          initial.registers.b initial.registers.c root [] initial.source 115) ∧
      BoolList (initial.heap++ext) root (result product xs ys) := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn left right empty
      subst pc;subst stack
      have first : tickNatural program (state heap next a b c d [] source (top product))=
          some ⟨state heap next a b c d [⟨115,.r3,⟨a,b,c,d⟩⟩] source (entry product),[],0⟩ := by
        cases product <;> simp [tickNatural,program,state,top,entry]
      obtain ⟨ext,root,len,run,rep⟩ := canonical_return product left right next c d hn ⟨a,b,c,d⟩ 115 [] source
      refine ⟨ext,root,len,?_,rep⟩
      simpa [instructions,state,Nat.add_assoc] using NaturalRun.step first run

/-- Stored input lengths pay for the raw arithmetic and its actual trim. -/
theorem instructions_bound (product : Bool) (xs ys : Bits) :
    instructions product xs ys ≤ 200*(xs.length+ys.length+2)^2 := by
  have ht := BinaryTrimProgram.steps_bound (raw product xs ys)
  cases product with
  | false =>
    have ha := BinaryAdditionProgram.steps_bound false xs ys
    have hl := (add_spec false xs ys).2.1
    have hm : max xs.length ys.length ≤ xs.length+ys.length := by omega
    simp only [raw,rawSteps,instructions,Bool.false_eq_true,ite_false] at ht ⊢
    nlinarith [sq_nonneg (xs.length+ys.length+2)]
  | true =>
    have ha := BinaryMultiplicationProgram.steps_bound xs ys
    have hl := (mul_spec xs ys).2.1
    simp only [raw,rawSteps,instructions,ite_true] at ht ⊢
    nlinarith [sq_nonneg (xs.length+ys.length+2)]

/-- One terminal-inclusive lower-machine charge for the same canonical result.
The original two padded operands, reader and caller-free stack survive. -/
theorem canonical_bit (product : Bool) {xs ys : Bits} {H B : ℕ} (initial : BitState 116)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=top product)
    (hn : value initial.next=initial.heap.length)
    (left : BoolList (eraseState initial).heap (eraseState initial).registers.a xs)
    (right : BoolList (eraseState initial).heap (eraseState initial).registers.b ys)
    (empty : initial.stack=[]) :
    ∃ charge out, Run program (instructions product xs ys) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (result product xs ys) ∧
      BoolList (eraseState out).heap (eraseState initial).registers.a xs ∧
      BoolList (eraseState out).heap (eraseState initial).registers.b ys ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=115 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧
        ext.length=rawCells product xs ys+(result product xs ys).length) ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤
        completeBound 116 H B (200*(xs.length+ys.length+2)^2) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by
    simpa [eraseState,State.map] using hn
  have hs : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨ext,root,len,high,rep⟩ := canonical_high product (eraseState initial) pc0 hn' left right hs
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have halt : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase] at obs
    have hn : tickNatural program
        (state ((eraseState initial).heap++ext) ((eraseState initial).next+ext.length)
          (eraseState initial).registers.a (eraseState initial).registers.b
          (eraseState initial).registers.c root [] (eraseState initial).source 115)=none := rfl
    rw [hn] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  have cost := (terminal_accounting run bounded halt).2
  have hb := instructions_bound product xs ys
  have hm : completeBound 116 H B (instructions product xs ys) ≤
      completeBound 116 H B (200*(xs.length+ys.length+2)^2) := by
    unfold completeBound runBound stepBound
    gcongr
  refine ⟨charge,out,run,?_,?_,?_,source,?_,?_,⟨ext,?_,len⟩,halt,cost.trans hm⟩
  · rw [erase];exact rep
  · rw [erase];exact boolList_extend left ext
  · rw [erase];exact boolList_extend right ext
  · have h : (eraseState out).stack=[] := by rw [erase];rfl
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).pc=115 := by rw [erase];rfl
    exact h
  · rw [erase];rfl

end DirectedFlowCutGap.CanonicalArithmeticProgram
