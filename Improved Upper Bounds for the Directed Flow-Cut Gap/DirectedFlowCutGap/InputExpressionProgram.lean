import DirectedFlowCutGap.ConcreteExpressionBounds
import DirectedFlowCutGap.InputAdditionProgram

/-! Three real self-delimited readers followed by the constructed expression
instruction table. The run begins with empty heap and stack. -/
namespace DirectedFlowCutGap.InputExpressionProgram
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor
abbrev EP := ConcreteExpressionProgram.program

def capacity (t : ConcreteExpressionProgram.Term) : ℕ := ConcreteExpressionProgram.capacity t+30
def expressionLabel (t : ConcreteExpressionProgram.Term)
    (pc : Fin (ConcreteExpressionProgram.capacity t)) : Fin (capacity t) := ⟨pc.val,by dsimp [capacity];omega⟩
def readerLabel (t : ConcreteExpressionProgram.Term) (i : Fin 3) (pc : Fin 10) : Fin (capacity t) :=
  ⟨ConcreteExpressionProgram.capacity t+10*i.val+pc.val,by dsimp [capacity];omega⟩

def program (t : ConcreteExpressionProgram.Term) : Program (capacity t) := fun pc =>
  if h : pc.val < ConcreteExpressionProgram.capacity t then
    ReferenceProgramLabels.instruction (expressionLabel t) (EP t ⟨pc.val,h⟩)
  else if pc.val=ConcreteExpressionProgram.capacity t+8 then .move .r0 .r3 (readerLabel t 1 9)
  else if pc.val=ConcreteExpressionProgram.capacity t+18 then .move .r1 .r3 (readerLabel t 2 9)
  else if pc.val=ConcreteExpressionProgram.capacity t+28 then
    .move .r2 .r3 (expressionLabel t (ConcreteExpressionProgram.entry t))
  else if h : pc.val < ConcreteExpressionProgram.capacity t+10 then
    ReferenceProgramLabels.instruction (readerLabel t 0)
      (SelfDelimitedWordProgram.program ⟨pc.val-ConcreteExpressionProgram.capacity t,by omega⟩)
  else if h : pc.val < ConcreteExpressionProgram.capacity t+20 then
    ReferenceProgramLabels.instruction (readerLabel t 1)
      (SelfDelimitedWordProgram.program ⟨pc.val-(ConcreteExpressionProgram.capacity t+10),by omega⟩)
  else
    ReferenceProgramLabels.instruction (readerLabel t 2)
      (SelfDelimitedWordProgram.program ⟨pc.val-(ConcreteExpressionProgram.capacity t+20),by
        have := pc.isLt;dsimp [capacity] at this;omega⟩)

def state (t : ConcreteExpressionProgram.Term) (heap : NaturalHeap) (next a b c d : ℕ)
    (source : Bits) (pc : Fin (capacity t)) : NaturalState (capacity t) :=
  ⟨heap,next,⟨a,b,c,d⟩,[],pc,source⟩
def initial (t : ConcreteExpressionProgram.Term) (source : Bits) : BitState (capacity t) :=
  ⟨[],[],⟨[],[],[],[]⟩,[],readerLabel t 0 9,source⟩
def instructions (t : ConcreteExpressionProgram.Term) (xs ys zs : Bits) : ℕ :=
  (6*xs.length+5)+1+(6*ys.length+5)+1+(6*zs.length+5)+1+
    (ConcreteExpressionProgram.runSteps ![xs,ys,zs] t+1)

theorem expression_slots (t : ConcreteExpressionProgram.Term)
    (pc : Fin (ConcreteExpressionProgram.capacity t)) :
    program t (expressionLabel t pc)=ReferenceProgramLabels.instruction (expressionLabel t) (EP t pc) := by
  simp [program,expressionLabel,pc.isLt]

theorem reader_slots (t : ConcreteExpressionProgram.Term) (i : Fin 3) (pc : Fin 10)
    (h : SelfDelimitedWordProgram.program pc ≠ .halt) :
    program t (readerLabel t i pc)=ReferenceProgramLabels.instruction (readerLabel t i)
      (SelfDelimitedWordProgram.program pc) := by
  fin_cases i <;> fin_cases pc <;> simp_all [program,readerLabel,SelfDelimitedWordProgram.program,Nat.add_assoc]

theorem run_high (t : ConcreteExpressionProgram.Term) (xs ys zs suffix : Bits) :
    ∃ final, NaturalRun (program t) (instructions t xs ys zs)
        (eraseState (initial t (SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys++
          SelfDelimitedWordProgram.encode zs++suffix)))
        ((SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys++
          SelfDelimitedWordProgram.encode zs).map Event.request) final ∧
      BoolList final.heap final.registers.d (ConcreteExpressionProgram.evaluate ![xs,ys,zs] t) ∧
      ConcreteExpressionProgram.Inputs final.heap final.registers.a final.registers.b final.registers.c ![xs,ys,zs] ∧
      final.source=suffix ∧ final.pc=expressionLabel t (ConcreteExpressionProgram.exit t) ∧ final.stack=[] ∧
      final.heap.length=3*(xs.length+ys.length+zs.length)+6+
        ConcreteExpressionProgram.runCells ![xs,ys,zs] t ∧
      final.next=final.heap.length ∧ tickNatural (program t) final=none := by
  obtain ⟨ex,rx,lx,hx,repX⟩ := InputAdditionProgram.reader_high xs
    (SelfDelimitedWordProgram.encode ys++SelfDelimitedWordProgram.encode zs++suffix) [] 0 0 0 0 0 rfl
  obtain ⟨ey,ry,ly,hy,repY⟩ := InputAdditionProgram.reader_high ys
    (SelfDelimitedWordProgram.encode zs++suffix) ex (3*xs.length+2) rx 0 0 rx lx.symm
  let ny := (3*xs.length+2)+3*ys.length+2
  have hny : ny=(ex++ey).length := by simp [ny,lx,ly];omega
  obtain ⟨ez,rz,lz,hz,repZ⟩ := InputAdditionProgram.reader_high zs suffix
    (ex++ey) ny rx ry 0 ry hny
  let nz := ny+3*zs.length+2
  have hnz : nz=((ex++ey)++ez).length := by simp [nz,ny,lx,ly,lz];omega
  have inputs : ConcreteExpressionProgram.Inputs ((ex++ey)++ez) rx ry rz ![xs,ys,zs] := by
    refine ⟨?_,?_,?_⟩
    · exact boolList_extend (boolList_extend (by simpa using repX) ey) ez
    · exact boolList_extend repY ez
    · exact repZ
  let s : NaturalState (ConcreteExpressionProgram.capacity t) :=
    ConcreteExpressionProgram.state ((ex++ey)++ez) nz ⟨rx,ry,rz,rz⟩ [] suffix (ConcreteExpressionProgram.entry t)
  obtain ⟨f,eval,word,old,src,pc,stk,ra,rb,rc,dense,ext,halt⟩ :=
    ConcreteExpressionProgram.evaluate_high t ![xs,ys,zs] s rfl hnz inputs rfl
  have first := ReferenceProgramLabels.run (readerLabel t 0) SelfDelimitedWordProgram.program
    (program t) (reader_slots t 0) hx
  have second := ReferenceProgramLabels.run (readerLabel t 1) SelfDelimitedWordProgram.program
    (program t) (reader_slots t 1) hy
  have third := ReferenceProgramLabels.run (readerLabel t 2) SelfDelimitedWordProgram.program
    (program t) (reader_slots t 2) hz
  have fourth := ReferenceProgramLabels.run (expressionLabel t) (EP t) (program t)
    (fun pc _ => expression_slots t pc) eval
  have h1 : NaturalRun (program t) (6*xs.length+5)
      (eraseState (initial t (SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys++
        SelfDelimitedWordProgram.encode zs++suffix)))
      ((SelfDelimitedWordProgram.encode xs).map Event.request)
      (state t ex (3*xs.length+2) 0 0 0 rx
        (SelfDelimitedWordProgram.encode ys++SelfDelimitedWordProgram.encode zs++suffix) (readerLabel t 0 8)) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,SelfDelimitedWordProgram.state,
      state,initial,eraseState,State.map,Registers.map,value,List.append_assoc] using first
  have move1 : tickNatural (program t)
      (state t ex (3*xs.length+2) 0 0 0 rx
        (SelfDelimitedWordProgram.encode ys++SelfDelimitedWordProgram.encode zs++suffix) (readerLabel t 0 8))=
      some ⟨state t ex (3*xs.length+2) rx 0 0 rx
        (SelfDelimitedWordProgram.encode ys++SelfDelimitedWordProgram.encode zs++suffix) (readerLabel t 1 9),[],0⟩ := by
    simp [tickNatural,program,state,readerLabel,Registers.get,Registers.set,Nat.add_assoc]
  have h2 : NaturalRun (program t) (6*ys.length+5)
      (state t ex (3*xs.length+2) rx 0 0 rx
        (SelfDelimitedWordProgram.encode ys++SelfDelimitedWordProgram.encode zs++suffix) (readerLabel t 1 9))
      ((SelfDelimitedWordProgram.encode ys).map Event.request)
      (state t (ex++ey) ny rx 0 0 ry (SelfDelimitedWordProgram.encode zs++suffix) (readerLabel t 1 8)) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,SelfDelimitedWordProgram.state,
      state,ny] using second
  have move2 : tickNatural (program t)
      (state t (ex++ey) ny rx 0 0 ry (SelfDelimitedWordProgram.encode zs++suffix) (readerLabel t 1 8))=
      some ⟨state t (ex++ey) ny rx ry 0 ry (SelfDelimitedWordProgram.encode zs++suffix) (readerLabel t 2 9),[],0⟩ := by
    simp [tickNatural,program,state,readerLabel,Registers.get,Registers.set,Nat.add_assoc]
  have h3 : NaturalRun (program t) (6*zs.length+5)
      (state t (ex++ey) ny rx ry 0 ry (SelfDelimitedWordProgram.encode zs++suffix) (readerLabel t 2 9))
      ((SelfDelimitedWordProgram.encode zs).map Event.request)
      (state t ((ex++ey)++ez) nz rx ry 0 rz suffix (readerLabel t 2 8)) := by
    simpa [ReferenceProgramLabels.state,ReferenceProgramLabels.frame,SelfDelimitedWordProgram.state,
      state,nz] using third
  have move3 : tickNatural (program t)
      (state t ((ex++ey)++ez) nz rx ry 0 rz suffix (readerLabel t 2 8))=
      some ⟨ReferenceProgramLabels.state (expressionLabel t) s,[],0⟩ := by
    simp [tickNatural,program,state,readerLabel,Registers.get,Registers.set,
      ReferenceProgramLabels.state,ConcreteExpressionProgram.state,s,Nat.add_assoc]
  refine ⟨ReferenceProgramLabels.state (expressionLabel t) f,?_,word,?_,src,?_,?_,?_,dense,?_⟩
  · have all := ConcreteExpressionProgram.append_run h1 (.step move1
        (ConcreteExpressionProgram.append_run h2 (.step move2
          (ConcreteExpressionProgram.append_run h3 (.step move3 fourth)))))
    convert all using 1 <;> simp [instructions,List.map_append,List.append_assoc,Nat.add_assoc]
    omega
  · simpa [ReferenceProgramLabels.state,ra,rb,rc,s,ConcreteExpressionProgram.state] using old
  · exact congrArg (expressionLabel t) pc
  · simp [ReferenceProgramLabels.state,stk]
  · obtain ⟨extra,he,hlen⟩ := ext
    simp [ReferenceProgramLabels.state,he,s,ConcreteExpressionProgram.state,lx,ly,lz,hlen]
    omega
  · have pe : program t (expressionLabel t f.pc)=.halt := by
      rw [pc,expression_slots]
      simp [EP,ConcreteExpressionProgram.program_exit,ReferenceProgramLabels.instruction]
    simp [tickNatural,ReferenceProgramLabels.state,pe]

theorem initial_bounded (t : ConcreteExpressionProgram.Term) (source : Bits) :
    (initial t source).Bounded 1 0 := by
  simp [initial,State.Bounded,State.records,Registers.All,Heap.Bounded]

theorem instructions_bound (t : ConcreteExpressionProgram.Term) (xs ys zs : Bits) :
    instructions t xs ys zs ≤ (ConcreteExpressionBounds.cost t+20)*(xs.length+ys.length+zs.length+1)^2 := by
  have hw : ∀ i, (![xs,ys,zs] i).length ≤ xs.length+ys.length+zs.length := by
    intro i;fin_cases i <;> simp <;> omega
  have hb := (ConcreteExpressionBounds.evaluate_bounds ![xs,ys,zs] t
    (xs.length+ys.length+zs.length) hw).2.1
  let Z := xs.length+ys.length+zs.length+1
  have hZZ : Z ≤ Z^2 := by dsimp [Z];nlinarith
  have hZ : 1 ≤ Z := by dsimp [Z];omega
  unfold instructions
  change _ ≤ (ConcreteExpressionBounds.cost t+20)*Z^2
  have hsmall : 6*xs.length+5+1+(6*ys.length+5)+1+(6*zs.length+5)+1+1 ≤ 20*Z^2 := by
    dsimp [Z] at *;nlinarith
  change ConcreteExpressionProgram.runSteps ![xs,ys,zs] t ≤ ConcreteExpressionBounds.cost t*Z^2 at hb
  calc
    _ ≤ 20*Z^2+ConcreteExpressionBounds.cost t*Z^2 := by omega
    _ = _ := by ring

/-- The full run constructs all three inputs and computes the exact padded
expression word. No input heap, pointer or arithmetic operation is supplied. -/
theorem evaluate_from_source (t : ConcreteExpressionProgram.Term) (xs ys zs suffix : Bits) :
    ∃ charge out, Run (program t) (instructions t xs ys zs) charge
        (initial t (SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys++
          SelfDelimitedWordProgram.encode zs++suffix))
        ((SelfDelimitedWordProgram.encode xs++SelfDelimitedWordProgram.encode ys++
          SelfDelimitedWordProgram.encode zs).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d
        (ConcreteExpressionProgram.evaluate ![xs,ys,zs] t) ∧
      ConcreteExpressionProgram.Inputs (eraseState out).heap (eraseState out).registers.a
        (eraseState out).registers.b (eraseState out).registers.c ![xs,ys,zs] ∧
      out.source=suffix ∧ out.pc=expressionLabel t (ConcreteExpressionProgram.exit t) ∧ out.stack=[] ∧
      out.heap.length=3*(xs.length+ys.length+zs.length)+6+
        ConcreteExpressionProgram.runCells ![xs,ys,zs] t ∧
      value out.next=out.heap.length ∧
      (attempt (program t) out).result=none ∧
      charge+(attempt (program t) out).operations ≤
        completeBound (capacity t) 1 0 (instructions t xs ys zs) := by
  obtain ⟨final,high,word,old,src,pc,frames,len,dense,halt⟩ := run_high t xs ys zs suffix
  obtain ⟨charge,out,run,erase,_,_,source⟩ := polynomial_simulation (initial_bounded t _) high
  have stop : (attempt (program t) out).result=none := by
    rw [attempt_result]
    have obs := tick_refines (program t) out
    rw [erase,halt] at obs
    cases ht : tick (program t) out with
    | none => rfl
    | some r => simp [ht] at obs
  refine ⟨charge,out,run,?_,?_,source.trans src,?_,?_,?_,?_,stop,
    (terminal_accounting run (initial_bounded t _) stop).2⟩
  · rw [erase];exact word
  · rw [erase];exact old
  · exact (congrArg State.pc erase).trans pc
  · have h : (eraseState out).stack=[] := by rw [erase];exact frames
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).heap.length=3*(xs.length+ys.length+zs.length)+6+
        ConcreteExpressionProgram.runCells ![xs,ys,zs] t := by rw [erase];exact len
    simpa [eraseState,State.map] using h
  · have h : (eraseState out).next=(eraseState out).heap.length := by rw [erase];exact dense
    simpa [eraseState,State.map] using h

theorem total_bound (t : ConcreteExpressionProgram.Term) (xs ys zs : Bits) :
    completeBound (capacity t) 1 0 (instructions t xs ys zs) ≤
      ConcreteExpressionBounds.terminalCoefficient (capacity t) (ConcreteExpressionBounds.cost t+20)*
        (xs.length+ys.length+zs.length+1)^6 := by
  apply ConcreteExpressionBounds.complete_polynomial <;> try omega
  exact instructions_bound t xs ys zs

end DirectedFlowCutGap.InputExpressionProgram
