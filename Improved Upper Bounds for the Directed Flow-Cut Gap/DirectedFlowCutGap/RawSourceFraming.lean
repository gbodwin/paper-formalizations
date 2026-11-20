import DirectedFlowCutGap.ActualPackingSourceInput
import DirectedFlowCutGap.ReferenceProgramInvocation

/-! The framing prefix keeps all three unprojected source tables in the
same bit-addressed heap. Typed validation can read these exact stored fields. -/
namespace DirectedFlowCutGap.RawSourceFraming

open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackingSourceInput (encode inputLabel state initial initial_bounded)
open WordPairTableRead (Table)

def program : Program 64 := fun pc =>
  if pc.val = 51 then .halt else PackingSourceInput.program pc

private theorem table_call (rows : List (Bits × Bits)) (suffix : Bits)
    (heap : NaturalHeap) (r : Registers ℕ) (caller continuation : Fin 64) (dst : Reg)
    (enter : program caller = .call (inputLabel 30) continuation dst) :
    ∃ ext root, NaturalRun program (SourceRowTableProgram.steps rows+3)
        ⟨heap,heap.length,r,[],caller,SourceRowTableProgram.encode rows++suffix⟩
        ((SourceRowTableProgram.encode rows).map Event.request)
        ⟨heap++ext,(heap++ext).length,r.set dst root,[],continuation,suffix⟩ ∧
      Table (heap++ext) root rows := by
  obtain ⟨ext,root,len,body,rep⟩ := SourceRowTableProgram.read_return rows suffix heap
    heap.length r.a r.b r.c r.d rfl r 31 []
  have start : tickNatural SourceRowTableProgram.program
      ⟨heap,heap.length,r,[],30,SourceRowTableProgram.encode rows++suffix⟩ =
      some ⟨⟨heap,heap.length,r,[⟨31,.r3,r⟩],0,SourceRowTableProgram.encode rows++suffix⟩,[],0⟩ := rfl
  have child : NaturalRun SourceRowTableProgram.program (SourceRowTableProgram.steps rows+1)
      (ReferenceProgramInvocation.state heap r [] (SourceRowTableProgram.encode rows++suffix) 30)
      ((SourceRowTableProgram.encode rows).map Event.request)
      (ReferenceProgramInvocation.state (heap++ext) (r.set .r3 root) [] suffix 31) := by
    simpa only [ReferenceProgramInvocation.state,SourceRowTableProgram.state,Registers.set,
      List.nil_append,List.length_append,len] using NaturalRun.step start body
  have slots (pc : Fin 32) (h : SourceRowTableProgram.program pc ≠ .halt) :
      program (inputLabel pc)=ReferenceProgramLabels.instruction inputLabel (SourceRowTableProgram.program pc) := by
    have neq : pc.val ≠ 51 := by omega
    simpa only [program,inputLabel,neq,ite_false] using PackingSourceInput.input_slots pc h
  refine ⟨ext,root,?_,rep⟩
  have h := ReferenceProgramInvocation.call inputLabel slots enter (by decide : program (inputLabel 31)=.ret .r3)
    [] child
  exact h

def framingSteps (costs matrix demands : List (Bits × Bits)) : ℕ :=
  SourceRowTableProgram.steps costs + SourceRowTableProgram.steps matrix +
    SourceRowTableProgram.steps demands + 9

private theorem natural_framing (costs matrix demands : List (Bits × Bits)) (suffix : Bits) :
    ∃ heap c m d, NaturalRun program (framingSteps costs matrix demands)
        (state [] 0 0 0 0 0 [] (encode costs matrix demands ++ suffix) 48)
        ((encode costs matrix demands).map Event.request)
        (state heap heap.length c m 0 d [] suffix 51) ∧
      Table heap c costs ∧ Table heap m matrix ∧ Table heap d demands := by
  let tail2 := SourceRowTableProgram.encode demands ++ suffix
  let tail1 := SourceRowTableProgram.encode matrix ++ tail2
  let input := SourceRowTableProgram.encode costs ++ tail1
  obtain ⟨h₁, c, first, costRows⟩ := table_call costs tail1 [] ⟨0,0,0,0⟩ 48 49 .r0 rfl
  simp only [List.nil_append,Registers.set] at first costRows
  obtain ⟨h₂, m, second, matrixRows⟩ := table_call matrix tail2 h₁ ⟨c,0,0,0⟩ 49 50 .r1 rfl
  simp only [Registers.set] at second
  obtain ⟨h₃, d, third, demandRows⟩ := table_call demands suffix (h₁++h₂) ⟨c,m,0,0⟩ 50 51 .r3 rfl
  simp only [Registers.set] at third
  have count : (SourceRowTableProgram.steps costs+3)+
      ((SourceRowTableProgram.steps matrix+3)+(SourceRowTableProgram.steps demands+3)) =
      framingSteps costs matrix demands := by
    unfold framingSteps
    omega
  have all := ConcreteExpressionProgram.append_run first
    (ConcreteExpressionProgram.append_run second third)
  rw [count] at all
  refine ⟨(h₁++h₂)++h₃,c,m,d,?_,?_,?_,demandRows⟩
  · simpa only [Nat.add_assoc,state,
      input,tail1,tail2,encode,List.append_assoc,List.map_append,List.length_append,
      List.length_nil,Nat.zero_add] using all
  · exact BinaryIndexedPairRead.table_extend
      (BinaryIndexedPairRead.table_extend costRows h₂) h₃
  · exact BinaryIndexedPairRead.table_extend matrixRows h₃

private theorem encoded_length (rows : List (Bits × Bits)) :
    (SourceRowTableProgram.encode rows).length =
      2 * SourceRowTableProgram.bits rows + 3 * rows.length + 1 := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨a,b⟩
    simp only [SourceRowTableProgram.encode,SourceRowTableProgram.bits,List.length_cons,
      List.length_append,SelfDelimitedWordProgram.encode_length,ih]
    omega

theorem instructions_bound (costs matrix demands : List (Bits × Bits)) :
    framingSteps costs matrix demands ≤ 8 * (encode costs matrix demands).length := by
  simp only [framingSteps,SourceRowTableProgram.steps,encode,List.length_append,encoded_length]
  omega

/-- The framed input yields the three original raw tables in one heap.
The typed validation phase can continue from this state. -/
theorem read_framed (costs matrix demands : List (Bits × Bits)) (suffix : Bits) :
    ∃ paid out, Run program (framingSteps costs matrix demands) paid
        (initial (encode costs matrix demands ++ suffix))
        ((encode costs matrix demands).map Event.request) out ∧
      Table (eraseState out).heap (eraseState out).registers.a costs ∧
      Table (eraseState out).heap (eraseState out).registers.b matrix ∧
      Table (eraseState out).heap (eraseState out).registers.d demands ∧
      out.pc = 51 ∧ out.source = suffix ∧
      out.stack = [] ∧ value out.next = out.heap.length ∧
      out.Bounded (1+framingSteps costs matrix demands) (framingSteps costs matrix demands) ∧
      paid ≤ 539136 * ((encode costs matrix demands ++ suffix).length + 1)^3 := by
  obtain ⟨heap,c,m,d,ran,hc,hm,hd⟩ := natural_framing costs matrix demands suffix
  have high : NaturalRun program (framingSteps costs matrix demands)
      (eraseState (initial (encode costs matrix demands ++ suffix)))
      ((encode costs matrix demands).map Event.request) (state heap heap.length c m 0 d [] suffix 51) :=
    ran
  obtain ⟨paid,out,low,erased,bounded,bound,rest⟩ := polynomial_simulation (initial_bounded _) high
  refine ⟨paid,out,low,?_,?_,?_,congrArg State.pc erased,rest,?_,?_,
    by simpa only [Nat.zero_add] using bounded,?_⟩
  · simpa only [erased,state] using hc
  · simpa only [erased,state] using hm
  · simpa only [erased,state] using hd
  · have frames := congrArg State.stack erased
    simpa only [eraseState,State.map,List.map_eq_nil_iff,state] using frames
  · have h : (eraseState out).next = (eraseState out).heap.length := by rw [erased]; rfl
    simpa only [eraseState,State.map,List.length_map] using h
  · let x := (encode costs matrix demands ++ suffix).length + 1
    have steps : framingSteps costs matrix demands ≤ 8*x := by
      apply (instructions_bound costs matrix demands).trans
      simp only [x,List.length_append]
      omega
    have extent : 1+0+2*framingSteps costs matrix demands+1 ≤ 18*x := by
      have hx : 1≤x := Nat.le_add_left _ _
      omega
    apply bound.trans
    unfold runBound controlCost
    calc
      _ ≤ 208*(8*x)*(18*x)^2 := by gcongr
      _ = 539136*x^3 := by ring

end DirectedFlowCutGap.RawSourceFraming
