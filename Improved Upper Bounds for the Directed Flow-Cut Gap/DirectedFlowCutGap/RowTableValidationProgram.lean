import DirectedFlowCutGap.SourceRowTableProgram
import DirectedFlowCutGap.BinaryZeroProgram

/-! A literal whole-table denominator scan. Every visited denominator is tested
by the actual nine-slot zero program. A zero returns immediately; otherwise the
stored tail is visited. No denominator-positivity premise or value oracle is used.
The original row table and source remain in the same append-only execution. -/
namespace DirectedFlowCutGap.RowTableValidationProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def zeroLabel (pc : Fin 9) : Fin 26 := if pc.val=8 then 6 else ⟨pc.val+16,by omega⟩
def program : Program 26 := fun pc =>
  if h : 16 ≤ pc.val ∧ pc.val < 25 then
    ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program ⟨pc.val-16,by omega⟩)
  else match pc.val with
  | 0 => .branch .r0 8 25 25 1
  | 1 => .field .r2 .r0 false 2
  | 2 => .field .r2 .r2 true 3
  | 3 => .field .r1 .r0 true 4
  | 4 => .move .r0 .r2 5
  | 5 => .call 16 6 .r3
  | 6 => .branch .r3 25 7 9 25
  | 7 => .move .r0 .r1 0
  | 8 => .make .r3 (.flag false) 9
  | 9 => .ret .r3
  | 14 => .call 0 15 .r3
  | _ => .halt

def state (heap : NaturalHeap) (next a b c d : ℕ)
    (stack : List (Frame ℕ 26)) (source : Bits) (pc : Fin 26) : NaturalState 26 :=
  ⟨heap,next,⟨a,b,c,d⟩,stack,pc,source⟩

def reject : List (Bits × Bits) → Bool
  | [] => false
  | (_,den)::rows => if (isZero den).1 then true else reject rows

def flags : List (Bits × Bits) → NaturalHeap
  | [] => [.flag false]
  | (_,den)::rows => .flag (isZero den).1 :: (if (isZero den).1 then [] else flags rows)

def steps : List (Bits × Bits) → ℕ
  | [] => 3
  | (_,den)::rows => 8+BinaryZeroProgram.steps den+(if (isZero den).1 then 0 else steps rows)

theorem flags_bound (rows : List (Bits × Bits)) : 1 ≤ (flags rows).length ∧
    (flags rows).length ≤ rows.length+1 := by
  induction rows with
  | nil => simp [flags]
  | cons p rows ih => cases p; simp only [flags]; split <;> simp_all

theorem steps_bound (rows : List (Bits × Bits)) :
    steps rows ≤ 4*SourceRowTableProgram.bits rows+11*rows.length+3 := by
  induction rows with
  | nil => simp [steps,SourceRowTableProgram.bits]
  | cons p rows ih =>
    rcases p with ⟨num,den⟩
    have h := BinaryZeroProgram.steps_bound den
    simp only [steps,SourceRowTableProgram.bits,List.length_cons]
    split <;> omega

theorem accepted_iff (rows : List (Bits × Bits)) :
    reject rows=false ↔ ∀ p ∈ rows, 0 < value p.2 := by
  induction rows with
  | nil => simp [reject]
  | cons p rows ih =>
    have hz := (isZero_spec p.2).1
    cases h : (isZero p.2).1 <;> simp_all [reject]
    omega

theorem zero_slots (pc : Fin 9) (h : BinaryZeroProgram.program pc ≠ .halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program pc) := by
  fin_cases pc <;> simp_all [program,zeroLabel,BinaryZeroProgram.program]

theorem run_append {s u v : NaturalState 26} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- The table caller remains below each actual zero-test caller. Returning from
that arithmetic call restores the exact stored table tail, even on rejection. -/
theorem scan_return {rows : List (Bits × Bits)} {heap : NaturalHeap} {a : ℕ}
    (table : WordPairTableRead.Table heap a rows) (next b c d : ℕ) (hn : next=heap.length)
    (saved : Registers ℕ) (pc : Fin 26) (stack : List (Frame ℕ 26)) (source : Bits) :
    ∃ root, NaturalRun program (steps rows)
      (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0) []
      (state (heap++flags rows) (next+(flags rows).length)
        saved.a saved.b saved.c root stack source pc) ∧
      (heap++flags rows)[root]?=some (.flag (reject rows)) := by
  induction rows generalizing heap a next b c d with
  | nil =>
    cases table with
    | nil hnil =>
      have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0)=
          some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 8,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hnil,tagBranch]
      have t8 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 8)=
          some ⟨state (heap++[.flag false]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 9,[],0⟩ := by
        simp [tickNatural,program,state,allocateNatural,Recipe.cell,Registers.set]
      have t9 : tickNatural program (state (heap++[.flag false]) (next+1) a b c next (⟨pc,.r3,saved⟩::stack) source 9)=
          some ⟨state (heap++[.flag false]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      refine ⟨next,?_,?_⟩
      · simpa [steps,flags] using NaturalRun.step t0 (.step t8 (.step t9 (.done _)))
      · simp [flags,reject,hn]
  | cons p rows ih =>
    rcases p with ⟨num,den⟩
    cases table with
    | @cons a item tail numRoot denRoot num den rows hp hi rn rd rt =>
      have t0 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 0)=
          some ⟨state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,hp,tagBranch]
      have t1 : tickNatural program (state heap next a b c d (⟨pc,.r3,saved⟩::stack) source 1)=
          some ⟨state heap next a b item d (⟨pc,.r3,saved⟩::stack) source 2,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t2 : tickNatural program (state heap next a b item d (⟨pc,.r3,saved⟩::stack) source 2)=
          some ⟨state heap next a b denRoot d (⟨pc,.r3,saved⟩::stack) source 3,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hi]
      have t3 : tickNatural program (state heap next a b denRoot d (⟨pc,.r3,saved⟩::stack) source 3)=
          some ⟨state heap next a tail denRoot d (⟨pc,.r3,saved⟩::stack) source 4,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set,hp]
      have t4 : tickNatural program (state heap next a tail denRoot d (⟨pc,.r3,saved⟩::stack) source 4)=
          some ⟨state heap next denRoot tail denRoot d (⟨pc,.r3,saved⟩::stack) source 5,[],0⟩ := by
        simp [tickNatural,program,state,Registers.get,Registers.set]
      have t5 : tickNatural program (state heap next denRoot tail denRoot d (⟨pc,.r3,saved⟩::stack) source 5)=
          some ⟨state heap next denRoot tail denRoot d
            (⟨6,.r3,⟨denRoot,tail,denRoot,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 16,[],0⟩ := by
        simp [tickNatural,program,state]
      have z0 := BinaryZeroProgram.zero_return rd next tail denRoot d hn ⟨denRoot,tail,denRoot,d⟩ 8 [] source
      have z1 := ReferenceProgramLabels.run zeroLabel BinaryZeroProgram.program program zero_slots z0
      have z2 := ReferenceProgramStack.run program (⟨pc,.r3,saved⟩::stack) z1
      have z : NaturalRun program (BinaryZeroProgram.steps den)
          (state heap next denRoot tail denRoot d
            (⟨6,.r3,⟨denRoot,tail,denRoot,d⟩⟩::⟨pc,.r3,saved⟩::stack) source 16) []
          (state (heap++[.flag (isZero den).1]) (next+1) denRoot tail denRoot next
            (⟨pc,.r3,saved⟩::stack) source 6) := by
        simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,ReferenceProgramStack.state,
          BinaryZeroProgram.state,zeroLabel,state] using z2
      have flag : (heap++[Cell.flag (isZero den).1])[next]?=some (.flag (isZero den).1) := by simp [hn]
      cases hz : (isZero den).1 with
      | true =>
        have t6 : tickNatural program
            (state (heap++[.flag true]) (next+1) denRoot tail denRoot next (⟨pc,.r3,saved⟩::stack) source 6)=
            some ⟨state (heap++[.flag true]) (next+1) denRoot tail denRoot next (⟨pc,.r3,saved⟩::stack) source 9,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,hn,tagBranch]
        have t9 : tickNatural program
            (state (heap++[.flag true]) (next+1) denRoot tail denRoot next (⟨pc,.r3,saved⟩::stack) source 9)=
            some ⟨state (heap++[.flag true]) (next+1) saved.a saved.b saved.c next stack source pc,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        refine ⟨next,?_,?_⟩
        · rw [hz] at z
          have body := run_append z (.step t6 (.step t9 (.done _)))
          have run := NaturalRun.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 body)))))
          convert run using 1 <;> simp [steps,flags,hz,Nat.add_comm]
          omega
        · simp [flags,reject,hz,hn]
      | false =>
        have t6 : tickNatural program
            (state (heap++[.flag false]) (next+1) denRoot tail denRoot next (⟨pc,.r3,saved⟩::stack) source 6)=
            some ⟨state (heap++[.flag false]) (next+1) denRoot tail denRoot next (⟨pc,.r3,saved⟩::stack) source 7,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,hn,tagBranch]
        have t7 : tickNatural program
            (state (heap++[.flag false]) (next+1) denRoot tail denRoot next (⟨pc,.r3,saved⟩::stack) source 7)=
            some ⟨state (heap++[.flag false]) (next+1) tail tail denRoot next (⟨pc,.r3,saved⟩::stack) source 0,[],0⟩ := by
          simp [tickNatural,program,state,Registers.get,Registers.set]
        obtain ⟨root,rest,rf⟩ := ih (BinaryIndexedPairRead.table_extend rt [.flag false])
          (next+1) tail denRoot next (by simp [hn])
        refine ⟨root,?_,?_⟩
        · rw [hz] at z
          have body := run_append z (.step t6 (.step t7 rest))
          have run := NaturalRun.step t0 (.step t1 (.step t2 (.step t3 (.step t4 (.step t5 body)))))
          convert run using 1 <;> simp [steps,flags,hz,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          omega
        · simpa [flags,reject,hz,List.append_assoc] using rf


/-- The actual top-level call restores the original table pointer and returns
one flag; the original table is preserved even on the short rejection branch. -/
theorem validate_high {rows : List (Bits × Bits)} (initial : NaturalState 26)
    (pc0 : initial.pc=14) (hn : initial.next=initial.heap.length)
    (table : WordPairTableRead.Table initial.heap initial.registers.a rows)
    (empty : initial.stack=[]) :
    ∃ out, NaturalRun program (1+steps rows) initial [] out ∧
      out.heap=initial.heap++flags rows ∧ out.next=out.heap.length ∧
      out.registers.a=initial.registers.a ∧
      WordPairTableRead.Table out.heap out.registers.a rows ∧
      out.heap[out.registers.d]?=some (.flag (reject rows)) ∧
      out.stack=[] ∧ out.source=initial.source ∧ out.pc=15 ∧ tickNatural program out=none := by
  cases initial with
  | mk heap next regs stack pc source =>
    cases regs with
    | mk a b c d =>
      simp only at pc0 hn table empty
      subst pc; subst stack
      obtain ⟨root,body,flag⟩ := scan_return table next b c d hn ⟨a,b,c,d⟩ 15 [] source
      have start : tickNatural program (state heap next a b c d [] source 14)=
          some ⟨state heap next a b c d [⟨15,.r3,⟨a,b,c,d⟩⟩] source 0,[],0⟩ := by
        simp [tickNatural,program,state]
      refine ⟨state (heap++flags rows) (next+(flags rows).length) a b c root [] source 15,
        ?_,rfl,?_,rfl,BinaryIndexedPairRead.table_extend table _,flag,rfl,rfl,rfl,rfl⟩
      · simpa [state,Nat.add_comm] using NaturalRun.step start body
      · simp [state,hn]

/-- One lower execution pays every scan/call/allocation and its final halt.
The input may contain any padded zero or positive denominator. -/
theorem validate_bit {rows : List (Bits × Bits)} {H B : ℕ} (initial : BitState 26)
    (bounded : initial.Bounded H B) (pc0 : initial.pc=14)
    (hn : value initial.next=initial.heap.length)
    (table : WordPairTableRead.Table (eraseState initial).heap (eraseState initial).registers.a rows)
    (empty : initial.stack=[]) :
    ∃ charge out, Run program (1+steps rows) charge initial [] out ∧
      WordPairTableRead.Table (eraseState out).heap (eraseState out).registers.a rows ∧
      (eraseState out).heap[(eraseState out).registers.d]?=some (.flag (reject rows)) ∧
      out.heap.length=initial.heap.length+(flags rows).length ∧
      out.source=initial.source ∧ out.stack=[] ∧ out.pc=15 ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 26 H B (1+steps rows) := by
  have hn' : (eraseState initial).next=(eraseState initial).heap.length := by simpa [eraseState,State.map] using hn
  have empty' : (eraseState initial).stack=[] := by simp [eraseState,State.map,empty]
  obtain ⟨final,high,heap,_,_,tab,flag,frames,src,pc,halt⟩ := validate_high (eraseState initial) pc0 hn' table empty'
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation bounded high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,?_,source.trans src,?_,?_,stop,
    (terminal_accounting run bounded stop).2⟩
  · rw [erase];exact tab
  · rw [erase];exact flag
  · have h : (eraseState out).heap.length=(eraseState initial).heap.length+(flags rows).length := by
      rw [erase,heap,List.length_append]
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h
  · exact (congrArg State.pc erase).trans pc

end DirectedFlowCutGap.RowTableValidationProgram
