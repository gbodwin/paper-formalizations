import DirectedFlowCutGap.SourceRowReadProgram
import DirectedFlowCutGap.BinaryZeroProgram

/-! An actual source-to-rational-field validation run. The constructed row
and binary index feed the actual indexed reader; its stored denominator then
feeds the literal zero-test instructions in the same heap. The returned flag
means rejection (zero denominator), with both original fields retained. -/
namespace DirectedFlowCutGap.SourceRowValidationProgram
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic

def rowLabel (pc : Fin 68) : Fin 79 := ⟨pc.val,by omega⟩
def zeroLabel (pc : Fin 9) : Fin 79 := ⟨pc.val+68,by omega⟩
def program : Program 79 := fun pc =>
  if pc.val=66 then .move .r2 .r0 77
  else if pc.val=76 then .move .r0 .r2 78
  else if pc.val=77 then .move .r0 .r1 75
  else if h : pc.val < 68 then
    ReferenceProgramLabels.instruction rowLabel (SourceRowReadProgram.program ⟨pc.val,h⟩)
  else if h : pc.val < 77 then
    ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program ⟨pc.val-68,by omega⟩)
  else .halt

def initial (source : Bits) : BitState 79 := ⟨[],[],⟨[],[],[],[]⟩,[],30,source⟩
def state (heap : NaturalHeap) (next a b c d : ℕ) (source : Bits) (pc : Fin 79) : NaturalState 79 :=
  ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩
def instructions (rows : List (Bits × Bits)) (word : Bits) (hi : value word < rows.length) : ℕ :=
  SourceRowReadProgram.instructions rows word+BinaryZeroProgram.steps rows[value word].2+4

theorem row_slots (pc : Fin 68) (h : SourceRowReadProgram.program pc ≠ .halt) :
    program (rowLabel pc)=ReferenceProgramLabels.instruction rowLabel (SourceRowReadProgram.program pc) := by
  have hn : pc.val ≠ 66 := by
    intro he
    have eq : pc=66 := Fin.ext he
    subst pc
    exact h rfl
  simp [program,rowLabel,hn,pc.isLt,show pc.val ≠ 76 by omega,show pc.val ≠ 77 by omega]

theorem zero_slots (pc : Fin 9) (h : BinaryZeroProgram.program pc ≠ .halt) :
    program (zeroLabel pc)=ReferenceProgramLabels.instruction zeroLabel (BinaryZeroProgram.program pc) := by
  fin_cases pc <;> simp_all [program,zeroLabel,BinaryZeroProgram.program]

theorem run_append {s u v : NaturalState 79} {t k : ℕ} {events more : List Event}
    (h : NaturalRun program t s events u) (g : NaturalRun program k u more v) :
    NaturalRun program (t+k) s (events++more) v := by
  induction h with
  | done s => simpa using g
  | step ht _ ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,List.append_assoc]
      using NaturalRun.step ht (ih g)

/-- Actual construction, indexed read and denominator scan share one heap and
one source. Input index validity remains explicit; denominator positivity does
not. The rejection flag is produced by the real scan, even for padded zero. -/
theorem validate_high (rows : List (Bits × Bits)) (word suffix : Bits)
    (hi : value word < rows.length) :
    ∃ final, NaturalRun program (instructions rows word hi)
        (eraseState (initial (SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word++suffix)))
        ((SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word).map Event.request) final ∧
      BoolList final.heap final.registers.a rows[value word].1 ∧
      BoolList final.heap final.registers.b rows[value word].2 ∧
      final.heap[final.registers.d]?=some (.flag (isZero rows[value word].2).1) ∧
      final.source=suffix ∧ final.pc=78 ∧ final.stack=[] ∧
      final.heap.length=SourceRowTableProgram.cells rows+3*word.length+value word+4 ∧
      final.next=final.heap.length ∧ tickNatural program final=none := by
  obtain ⟨r,readRun,num,den,src,rpc,frames,len,dense,_⟩ := SourceRowReadProgram.run_high rows word suffix hi
  let z := BinaryZeroProgram.state r.heap r.next r.registers.b r.registers.b r.registers.a r.registers.d [] suffix 7
  obtain ⟨u,zeroRun,heap,next,a,b,c,d,stack,source,pc,flag,_⟩ := BinaryZeroProgram.zero_high z rfl dense den rfl
  let mapped := ReferenceProgramLabels.state zeroLabel u
  let final : NaturalState 79 := {mapped with registers := mapped.registers.set .r0 mapped.registers.c, pc := 78}
  have first : NaturalRun program (SourceRowReadProgram.instructions rows word)
      (eraseState (initial (SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word++suffix)))
      ((SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word).map Event.request)
      (state r.heap r.next r.registers.a r.registers.b r.registers.c r.registers.d suffix 66) := by
    have h := ReferenceProgramLabels.run rowLabel SourceRowReadProgram.program program row_slots readRun
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,rowLabel,SourceRowReadProgram.initial,
      initial,eraseState,State.map,state,rpc,frames,src] using h
  have t66 : tickNatural program
      (state r.heap r.next r.registers.a r.registers.b r.registers.c r.registers.d suffix 66)=
      some ⟨state r.heap r.next r.registers.a r.registers.b r.registers.a r.registers.d suffix 77,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set]
  have t77 : tickNatural program
      (state r.heap r.next r.registers.a r.registers.b r.registers.a r.registers.d suffix 77)=
      some ⟨ReferenceProgramLabels.state zeroLabel z,[],0⟩ := by
    simp [tickNatural,program,state,Registers.get,Registers.set,ReferenceProgramLabels.state,
      zeroLabel,z,BinaryZeroProgram.state]
  have t76 : tickNatural program mapped=some ⟨final,[],0⟩ := by
    simp [tickNatural,program,mapped,ReferenceProgramLabels.state,zeroLabel,pc,final,Registers.get]
  have last := NaturalRun.step t76 (NaturalRun.done _)
  have zeroRun' := ReferenceProgramLabels.run zeroLabel BinaryZeroProgram.program program zero_slots zeroRun
  refine ⟨final,?_,?_,?_,?_,?_,rfl,?_,?_,?_,rfl⟩
  · have full := run_append first (NaturalRun.step t66 (NaturalRun.step t77 (run_append zeroRun' last)))
    convert full using 1 <;> simp [instructions,Nat.add_assoc,List.append_nil]
    omega
  · change BoolList u.heap u.registers.c rows[value word].1
    rw [heap,c]
    exact boolList_extend num _
  · change BoolList u.heap u.registers.b rows[value word].2
    rw [heap,b]
    exact boolList_extend den _
  · exact flag
  · exact source
  · simp [final,mapped,ReferenceProgramLabels.state,stack]
  · change u.heap.length=_
    rw [heap]
    simp [z,BinaryZeroProgram.state,len]
  · change u.next=u.heap.length
    rw [next,heap]
    simp [z,BinaryZeroProgram.state,dense]

theorem initial_bounded (source : Bits) : (initial source).Bounded 1 0 := by
  simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]

/-- The selected denominator is accepted exactly when positive; the actual
returned fields keep every supplied padding bit. All operations and one final
halt belong to this same lower execution. -/
theorem validate_from_source (rows : List (Bits × Bits)) (word suffix : Bits)
    (hi : value word < rows.length) :
    ∃ charge out, Run program (instructions rows word hi) charge
        (initial (SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word++suffix))
        ((SourceRowTableProgram.encode rows++SelfDelimitedWordProgram.encode word).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.a rows[value word].1 ∧
      BoolList (eraseState out).heap (eraseState out).registers.b rows[value word].2 ∧
      (eraseState out).heap[(eraseState out).registers.d]?=some (.flag (isZero rows[value word].2).1) ∧
      ((isZero rows[value word].2).1=true ↔ value rows[value word].2=0) ∧
      out.source=suffix ∧ out.stack=[] ∧ out.pc=78 ∧
      out.heap.length=SourceRowTableProgram.cells rows+3*word.length+value word+4 ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound 79 1 0 (instructions rows word hi) := by
  obtain ⟨final,high,num,den,flag,src,pc,frames,len,_,halt⟩ := validate_high rows word suffix hi
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation (initial_bounded _) high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,?_,(isZero_spec _).1,source.trans src,?_,?_,?_,stop,
    (terminal_accounting run (initial_bounded _) stop).2⟩
  · rw [erase];exact num
  · rw [erase];exact den
  · rw [erase];exact flag
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).heap.length=SourceRowTableProgram.cells rows+3*word.length+value word+4 := by rw [erase];exact len
    simpa [eraseState,State.map] using h

theorem field_length_le (rows : List (Bits × Bits)) (p : Bits × Bits) (hp : p ∈ rows) :
    p.1.length+p.2.length ≤ SourceRowTableProgram.bits rows := by
  induction rows with
  | nil => simp at hp
  | cons q rows ih =>
    rcases List.mem_cons.mp hp with he | hp
    · subst p; cases q; simp [SourceRowTableProgram.bits]
    · have h := ih hp
      cases q
      simp only [SourceRowTableProgram.bits]
      omega

theorem instructions_bound (rows : List (Bits × Bits)) (word : Bits)
    (hi : value word < rows.length) :
    instructions rows word hi ≤ 48*(SourceRowTableProgram.bits rows+rows.length+word.length+1) := by
  have hr := SourceRowReadProgram.instructions_bound rows word hi
  have hz := BinaryZeroProgram.steps_bound rows[value word].2
  have hf := field_length_le rows rows[value word] (List.getElem_mem hi)
  dsimp [instructions]
  omega

theorem total_bound (rows : List (Bits × Bits)) (word : Bits)
    (hi : value word < rows.length) :
    completeBound 79 1 0 (instructions rows word hi) ≤
      200000000*(SourceRowTableProgram.bits rows+rows.length+word.length+1)^3 := by
  let z := SourceRowTableProgram.bits rows+rows.length+word.length+1
  have hz : 1 ≤ z := by dsimp [z];omega
  have ht : instructions rows word hi ≤ 48*z := instructions_bound rows word hi
  have hs : 2*instructions rows word hi+2 ≤ 98*z := by omega
  have hr : instructions rows word hi+2 ≤ 50*z := by omega
  unfold completeBound runBound stepBound controlCost
  norm_num
  calc
    _ ≤ 223*(48*z)*(98*z)^2+223*(50*z)*(50*z) := by gcongr <;> omega
    _ ≤ 200000000*z^3 := by
      have hz2 : z^2 ≤ z^3 := by nlinarith
      nlinarith

/-- The rejection flag's complement is exactly denominator positivity. -/
theorem accepted_iff (den : Bits) : (isZero den).1=false ↔ 0 < value den := by
  have h := (isZero_spec den).1
  cases hz : (isZero den).1 <;> simp_all
  omega

end DirectedFlowCutGap.SourceRowValidationProgram
