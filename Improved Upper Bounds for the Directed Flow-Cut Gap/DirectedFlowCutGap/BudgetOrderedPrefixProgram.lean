import DirectedFlowCutGap.PackingBudgetProgram
import DirectedFlowCutGap.OrderedCounterPrefix

/-! The computed budget word feeds the actual unary-counter, source request
and persistent reversal instructions in the same machine and heap. -/
namespace DirectedFlowCutGap.BudgetOrderedPrefixProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

abbrev baseCapacity := InputExpressionProgram.capacity PackingBudgetProgram.body
def capacity : ℕ := baseCapacity+30
def budgetLabel (pc : Fin baseCapacity) : Fin capacity := ⟨30+pc.val,by dsimp [capacity];omega⟩
def prefixLabel (pc : Fin 30) : Fin capacity := ⟨pc.val,by dsimp [capacity];omega⟩
def budgetExit : Fin baseCapacity := InputExpressionProgram.expressionLabel PackingBudgetProgram.body
  (ConcreteExpressionProgram.exit PackingBudgetProgram.body)

def program : Program capacity := fun pc =>
  if h : pc.val < 30 then ReferenceProgramLabels.instruction prefixLabel
    (OrderedCounterPrefix.program ⟨pc.val,h⟩)
  else if pc.val=30+budgetExit.val then .move .r0 .r3 (prefixLabel 23)
  else ReferenceProgramLabels.instruction budgetLabel
    (PackingBudgetProgram.program ⟨pc.val-30,by change pc.val-30 < baseCapacity; have hh : pc.val < baseCapacity+30 := pc.isLt;omega⟩)

def initial (source : Bits) : BitState capacity :=
  ⟨[],[],⟨[],[],[],[]⟩,[],budgetLabel (InputExpressionProgram.readerLabel PackingBudgetProgram.body 0 9),source⟩
def word := EncodedPackingBitBudget.run
def steps (n b s : Bits) : ℕ := PackingBudgetProgram.instructions n b s+1+
  OrderedCounterPrefix.steps (word n b s).1

theorem budget_halt : PackingBudgetProgram.program budgetExit=.halt := by
  rw [PackingBudgetProgram.program,budgetExit,InputExpressionProgram.expression_slots]
  simp [InputExpressionProgram.EP,ConcreteExpressionProgram.program_exit,ReferenceProgramLabels.instruction]

theorem budget_agree (pc : Fin baseCapacity) (h : PackingBudgetProgram.program pc ≠ .halt) :
    program (budgetLabel pc)=ReferenceProgramLabels.instruction budgetLabel (PackingBudgetProgram.program pc) := by
  have he : pc ≠ budgetExit := by intro he;exact h (he ▸ budget_halt)
  have hev : pc.val ≠ budgetExit.val := by intro hv;exact he (Fin.ext hv)
  simp [program,budgetLabel,hev]

theorem prefix_agree (pc : Fin 30) :
    program (prefixLabel pc)=ReferenceProgramLabels.instruction prefixLabel (OrderedCounterPrefix.program pc) := by
  simp [program,prefixLabel,pc.isLt]

/-- The budget is actually computed, then consumed as the unary-counter
input. No binary quota representation is supplied to the initial state. -/
theorem run_high (n b s source : Bits) (enough : value (word n b s).1 ≤ source.length) :
    ∃ final, NaturalRun program (steps n b s)
        (eraseState (initial (SelfDelimitedWordProgram.encode n++SelfDelimitedWordProgram.encode b++
          SelfDelimitedWordProgram.encode s++source)))
        (((SelfDelimitedWordProgram.encode n++SelfDelimitedWordProgram.encode b++
          SelfDelimitedWordProgram.encode s)++source.take (value (word n b s).1)).map Event.request) final ∧
      BoolList final.heap final.registers.b (source.take (value (word n b s).1)) ∧
      final.source=source.drop (value (word n b s).1) ∧ final.pc=prefixLabel 29 ∧ final.stack=[] ∧
      final.heap.length=3*(n.length+b.length+s.length)+6+
        ConcreteExpressionProgram.runCells ![n,b,s] PackingBudgetProgram.body+4*value (word n b s).1+3 ∧
      final.next=final.heap.length ∧ tickNatural program final=none := by
  obtain ⟨mid,compute,rep,_old,src,pc,stk,len,dense,_halt⟩ :=
    InputExpressionProgram.run_high PackingBudgetProgram.body n b s source
  have represented : BoolList mid.heap mid.registers.d (word n b s).1 := by
    simpa only [PackingBudgetProgram.body,ConcreteExpressionProgram.evaluate_translate,word,
      EncodedPackingBitBudget.run] using rep
  obtain ⟨final,materialize,stored,suffix,finalpc,finalheap,finaldense,finalstack,_⟩ :=
    OrderedCounterPrefix.materialize represented mid.next mid.registers.b mid.registers.c
      mid.registers.d dense source enough
  have first := ReferenceProgramLabels.run budgetLabel PackingBudgetProgram.program program budget_agree compute
  have second := ReferenceProgramLabels.run prefixLabel OrderedCounterPrefix.program program
    (fun pc _ => prefix_agree pc) materialize
  have hop : tickNatural program (ReferenceProgramLabels.state budgetLabel mid)=
      some ⟨ReferenceProgramLabels.state prefixLabel
        (OrderedCounterPrefix.state mid.heap mid.next mid.registers.d mid.registers.b
          mid.registers.c mid.registers.d source 23),[],0⟩ := by
    simp [tickNatural,program,ReferenceProgramLabels.state,budgetLabel,pc,budgetExit,stk,src,
      OrderedCounterPrefix.state,prefixLabel,Registers.get,Registers.set]
  refine ⟨ReferenceProgramLabels.state prefixLabel final,?_,stored,suffix,?_,?_,?_,finaldense,?_⟩
  · have all := ConcreteExpressionProgram.append_run first (NaturalRun.step hop second)
    convert all using 1 <;> simp [steps,PackingBudgetProgram.instructions,initial,
      ReferenceProgramLabels.state,InputExpressionProgram.initial,eraseState,State.map,Registers.map,
      value,List.map_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  · exact congrArg prefixLabel finalpc
  · simp [ReferenceProgramLabels.state,finalstack]
  · change final.heap.length=_
    rw [finalheap,len]
  · have he : program (prefixLabel final.pc)=.halt := by
      rw [finalpc,prefix_agree]
      rfl
    simp [tickNatural,ReferenceProgramLabels.state,he]

theorem initial_bounded (source : Bits) : (initial source).Bounded 1 0 := by
  simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]

/-- The one lower run computes its own quota and requests/stores exactly
that many subsequent source bits in literal order, paying one final halt. -/
theorem materialize_from_source (n b s source : Bits)
    (enough : value (word n b s).1 ≤ source.length) :
    ∃ charge out, Run program (steps n b s) charge
        (initial (SelfDelimitedWordProgram.encode n++SelfDelimitedWordProgram.encode b++
          SelfDelimitedWordProgram.encode s++source))
        (((SelfDelimitedWordProgram.encode n++SelfDelimitedWordProgram.encode b++
          SelfDelimitedWordProgram.encode s)++source.take (value (word n b s).1)).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.b (source.take (value (word n b s).1)) ∧
      out.source=source.drop (value (word n b s).1) ∧ out.pc=prefixLabel 29 ∧ out.stack=[] ∧
      out.heap.length=3*(n.length+b.length+s.length)+6+
        ConcreteExpressionProgram.runCells ![n,b,s] PackingBudgetProgram.body+4*value (word n b s).1+3 ∧
      value out.next=out.heap.length ∧
      (attempt program out).result=none ∧
      charge+(attempt program out).operations ≤ completeBound capacity 1 0 (steps n b s) := by
  obtain ⟨final,high,stored,src,pc,frames,len,dense,halt⟩ := run_high n b s source enough
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation (initial_bounded _) high
  have stop : (attempt program out).result=none := by
    rw [attempt_result]
    have obs := tick_refines program out
    rw [erase,halt] at obs
    cases ht : tick program out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,source.trans src,?_,?_,?_,?_,stop,
    (terminal_accounting run (initial_bounded _) stop).2⟩
  · rw [erase];exact stored
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).heap.length=3*(n.length+b.length+s.length)+6+
        ConcreteExpressionProgram.runCells ![n,b,s] PackingBudgetProgram.body+4*value (word n b s).1+3 := by
      rw [erase];exact len
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];exact dense
    simpa [eraseState,State.map] using h

def stepCoefficient : ℕ := ConcreteExpressionBounds.cost PackingBudgetProgram.body+
  10*BinaryBudgetExpression.widthCoefficient EncodedPackingBitBudget.body+42

theorem steps_bound (n b s : Bits) : steps n b s ≤
    stepCoefficient*(value (word n b s).1+n.length+b.length+s.length+1)^2 := by
  let L := n.length+b.length+s.length
  let q := value (word n b s).1
  let Z := q+n.length+b.length+s.length+1
  have hZ : 1 ≤ Z := by dsimp [Z];omega
  have hZZ : Z ≤ Z^2 := by nlinarith
  have hL : L+1 ≤ Z := by dsimp [L,Z];omega
  have hq : q ≤ Z := by dsimp [q,Z];omega
  have hw := (EncodedPackingBitBudget.run_bounds n b s L (by dsimp [L];omega)
    (by dsimp [L];omega) (by dsimp [L];omega)).1
  have hp := OrderedCounterPrefix.steps_bound (word n b s).1
  have he := InputExpressionProgram.instructions_bound PackingBudgetProgram.body n b s
  have he' : PackingBudgetProgram.instructions n b s ≤
      (ConcreteExpressionBounds.cost PackingBudgetProgram.body+20)*Z^2 := by
    apply he.trans
    gcongr
  have hw' : (word n b s).1.length ≤
      BinaryBudgetExpression.widthCoefficient EncodedPackingBitBudget.body*Z :=
    hw.trans (Nat.mul_le_mul_left _ hL)
  have hp' : OrderedCounterPrefix.steps (word n b s).1 ≤
      (10*BinaryBudgetExpression.widthCoefficient EncodedPackingBitBudget.body+21)*Z^2 := by
    calc
      _ ≤ (10*BinaryBudgetExpression.widthCoefficient EncodedPackingBitBudget.body+21)*Z := by
        nlinarith [hp,hw']
      _ ≤ _ := Nat.mul_le_mul_left _ hZZ
  have hOne : 1 ≤ Z^2 := Nat.one_le_pow _ _ hZ
  unfold steps
  change _ ≤ stepCoefficient*Z^2
  calc
    _ ≤ (ConcreteExpressionBounds.cost PackingBudgetProgram.body+20)*Z^2+
        Z^2+(10*BinaryBudgetExpression.widthCoefficient EncodedPackingBitBudget.body+21)*Z^2 :=
      Nat.add_le_add (Nat.add_le_add he' hOne) hp'
    _ = _ := by unfold stepCoefficient;ring

/-- The bound is output-sensitive in the computed quota q: requesting q
actual bits cannot have a bound depending only on log q. -/
theorem total_bound (n b s : Bits) : completeBound capacity 1 0 (steps n b s) ≤
    ConcreteExpressionBounds.terminalCoefficient capacity stepCoefficient*
      (value (word n b s).1+n.length+b.length+s.length+1)^6 := by
  apply ConcreteExpressionBounds.complete_polynomial <;> try omega
  exact steps_bound n b s

end DirectedFlowCutGap.BudgetOrderedPrefixProgram
