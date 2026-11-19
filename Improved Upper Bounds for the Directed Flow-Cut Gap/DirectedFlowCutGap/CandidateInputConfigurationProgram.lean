import DirectedFlowCutGap.CandidateSearchConfigurationProgram
import DirectedFlowCutGap.ConcreteExpressionBounds

/-!
# Candidate search configuration from the vertex count and grid size

The fixed arithmetic expression computes the exact network size from the
two stored words. The returned word is the input to the label and pair
enumeration, in the same heap and without consuming the tape.
-/

namespace DirectedFlowCutGap.CandidateInputConfigurationProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open CandidatePhysicalCut (networkSize numberEquiv label)
open ResidualFlowLoopProgram (Configuration)
open ResidualFlowStepProgram (wordTable pairTable)
open MinimumClosureCut (source sink)

def expression : BinaryBudgetExpression.Expr :=
  .plus (.times (.times (.literal [false,true,true]) (.input 0)) (.plus (.input 1) (.literal [true])))
    (.literal [false,true])

def term : ConcreteExpressionProgram.Term := ConcreteExpressionProgram.translate expression
def inputs (vertices grid : Bits) : Fin 3→Bits := ![vertices,grid,[]]
def countWord (vertices grid : Bits) : Bits := ConcreteExpressionProgram.evaluate (inputs vertices grid) term

theorem count_value (vertices grid : Bits) :
    value (countWord vertices grid)=networkSize (value vertices) (value grid) := by
  rw [countWord,term,ConcreteExpressionProgram.evaluate_translate,BinaryBudgetExpression.evaluate_value]
  simp [expression,inputs,BinaryBudgetExpression.denote,networkSize,value]

def sizeLabel (pc : Fin (ConcreteExpressionProgram.capacity term)) : Fin 299 :=
  ⟨16+pc.val,by have h := pc.isLt; change pc.val<154 at h; omega⟩
def configurationLabel (pc : Fin 129) : Fin 299 := ⟨170+pc.val,by omega⟩

def program : Program 299 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .make .r2 .nil 1
    | 1 => .call (sizeLabel (ConcreteExpressionProgram.entry term)) 2 .r0
    | 2 => .call (configurationLabel 0) 3 .r3
    | _ => .halt
  else if h : pc.val<170 then
    if pc.val=169 then .ret .r3
    else ReferenceProgramLabels.instruction sizeLabel
      (ConcreteExpressionProgram.program term ⟨pc.val-16,by change pc.val-16<154; omega⟩)
  else if pc.val=179 then .ret .r3
  else ReferenceProgramLabels.instruction configurationLabel
    (CandidateSearchConfigurationProgram.program ⟨pc.val-170,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 299))
    (tape : Bits) (pc : Fin 299) : NaturalState 299 := ⟨heap,heap.length,r,stack,pc,tape⟩

def steps (vertices grid : Bits) : ℕ :=
  ConcreteExpressionProgram.runSteps (inputs vertices grid) term+
    CandidateSearchConfigurationProgram.steps (countWord vertices grid)+6

def instructionBound (n L width : ℕ) : ℕ :=
  ConcreteExpressionBounds.cost term*(width+1)^2+
    CandidateSearchConfigurationProgram.instructionBound (networkSize n L)
      (ConcreteExpressionBounds.width term*(width+1))+6

theorem steps_le (vertices grid : Bits) : steps vertices grid ≤
    instructionBound (value vertices) (value grid) (max vertices.length grid.length) := by
  let W := max vertices.length grid.length
  have inputWidths (i : Fin 3) : ((inputs vertices grid) i).length≤W := by
    fin_cases i <;> simp [inputs,W]
  obtain ⟨length,cost,_⟩ := ConcreteExpressionBounds.evaluate_bounds (inputs vertices grid) term W inputWidths
  change (countWord vertices grid).length ≤ ConcreteExpressionBounds.width term*(W+1) at length
  have config := CandidateSearchConfigurationProgram.steps_le (countWord vertices grid)
  rw [count_value] at config
  have h : CandidateSearchConfigurationProgram.instructionBound (networkSize (value vertices) (value grid))
      (countWord vertices grid).length ≤
    CandidateSearchConfigurationProgram.instructionBound (networkSize (value vertices) (value grid))
      (ConcreteExpressionBounds.width term*(W+1)) := by
    unfold CandidateSearchConfigurationProgram.instructionBound
    exact by gcongr
  unfold steps instructionBound
  exact Nat.add_le_add_right (Nat.add_le_add cost (config.trans h)) 6

private theorem size_slots (pc : Fin (ConcreteExpressionProgram.capacity term))
    (h : ConcreteExpressionProgram.program term pc≠.halt) :
    program (sizeLabel pc)=ReferenceProgramLabels.instruction sizeLabel (ConcreteExpressionProgram.program term pc) := by
  have bound := pc.isLt
  change pc.val<154 at bound
  by_cases hp : pc.val=153
  · have eq : pc=ConcreteExpressionProgram.exit term := Fin.ext hp
    subst pc
    exact (h (ConcreteExpressionProgram.program_exit term)).elim
  · simp [program,sizeLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<170 by omega,
      show 16+pc.val≠169 by omega]

private theorem configuration_slots (pc : Fin 129) (h : CandidateSearchConfigurationProgram.program pc≠.halt) :
    program (configurationLabel pc)=
      ReferenceProgramLabels.instruction configurationLabel (CandidateSearchConfigurationProgram.program pc) := by
  by_cases hp : pc.val=9
  · have eq : pc=9 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,configurationLabel,show ¬170+pc.val<16 by omega,show ¬170+pc.val<170 by omega,
      show 170+pc.val≠179 by omega]

private theorem size_call {heap : NaturalHeap} {r : Registers ℕ} {vertices grid : Bits}
    (nv : BoolList heap r.a vertices) (gw : BoolList heap r.b grid) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),BoolList (heap++ext) root (countWord vertices grid) ∧
      NaturalRun program (ConcreteExpressionProgram.runSteps (inputs vertices grid) term+4)
        (state heap r [] tape 0) [] (state (heap++ext) (args.set .r0 root) [] tape 2) := by
  let I := inputs vertices grid
  let mid := heap++[.nil]
  let args := r.set .r2 heap.length
  let frame : Frame ℕ 299 := ⟨2,.r0,args⟩
  have p : ConcreteExpressionProgram.Inputs mid args.a args.b args.c I :=
    ⟨boolList_extend nv _,boolList_extend gw _,.nil (by simp [mid,args,Registers.set])⟩
  obtain ⟨e,root,len,body,rep⟩ := ConcreteExpressionProgram.node_return term I term 96
    (ConcreteExpressionProgram.program_agree term) mid mid.length args.a args.b args.c args.d rfl p
    args .r3 (ConcreteExpressionProgram.exit term) [] tape
  have enter : tickNatural (ConcreteExpressionProgram.program term)
      (ConcreteExpressionProgram.state mid mid.length args [] tape (ConcreteExpressionProgram.entry term)) =
      some ⟨ConcreteExpressionProgram.state mid mid.length args [⟨ConcreteExpressionProgram.exit term,.r3,args⟩]
        tape (ConcreteExpressionProgram.label (ConcreteExpressionProgram.capacity_pos term) 96),[],0⟩ := by
    simp [tickNatural,ConcreteExpressionProgram.state,ConcreteExpressionProgram.program_entry]
  have setup : NaturalRun program 2 (state heap r [] tape 0) []
      (state mid args [frame] tape (sizeLabel (ConcreteExpressionProgram.entry term))) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,allocateNatural,Recipe.cell,mid,args,frame]
  let stop := state (mid++e) (args.set .r3 root) [frame] tape (sizeLabel (ConcreteExpressionProgram.exit term))
  have lift := ReferenceProgramLabels.run sizeLabel (ConcreteExpressionProgram.program term) program size_slots (.step enter body)
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program (ConcreteExpressionProgram.runSteps I term+1)
      (state mid args [frame] tape (sizeLabel (ConcreteExpressionProgram.entry term))) [] stop := by
    cases r
    simpa [state,stop,args,ReferenceProgramLabels.state,ReferenceProgramStack.state,ConcreteExpressionProgram.state,
      len] using lift
  have ret : tickNatural program stop=some ⟨state (mid++e) (args.set .r0 root) [] tape 2,[],0⟩ := by
    simp [state,stop,program,sizeLabel,ConcreteExpressionProgram.exit,ConcreteExpressionProgram.label,term,expression,
      ConcreteExpressionProgram.capacity,ConcreteExpressionProgram.size,ConcreteExpressionProgram.translate,
      ConcreteExpressionProgram.literal,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨[.nil]++e,args,root,?_,?_⟩
  · simpa only [mid,I,countWord,List.append_assoc] using rep
  · have trace := append_run setup (append_run run (.step ret (.done _)))
    convert trace using 1 <;> first | rfl | (simp only [I]; omega) | simp only [mid,List.append_assoc]

theorem natural_input_configuration {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {vertices grid : Bits}
    (nh : value vertices=n) (lh : value grid=L)
    (nv : BoolList heap r.a vertices) (gw : BoolList heap r.b grid) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      Configuration (heap++ext) root (wordTable (label (n:=n) (L:=L)))
        (label ((numberEquiv n L) source)) (label ((numberEquiv n L) sink)) (pairTable (label (n:=n) (L:=L))) ∧
      NaturalRun program (steps vertices grid) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 3) := by
  obtain ⟨es,regs,size,sizeRep,compute⟩ := size_call nv gw tape
  let mid := heap++es
  let args := regs.set .r0 size
  have numeric : value (countWord vertices grid)=networkSize n L := by rw [count_value,nh,lh]
  obtain ⟨ec,out,root,rep,body⟩ := CandidateSearchConfigurationProgram.natural_candidate_configuration (r:=args)
    numeric sizeRep tape
  let frame : Frame ℕ 299 := ⟨3,.r3,args⟩
  let stop := state (mid++ec) (out.set .r3 root) [frame] tape (configurationLabel 9)
  have enter : tickNatural program (state mid args [] tape 2)=
      some ⟨state mid args [frame] tape (configurationLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run configurationLabel CandidateSearchConfigurationProgram.program program configuration_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program (CandidateSearchConfigurationProgram.steps (countWord vertices grid))
      (state mid args [frame] tape (configurationLabel 0)) [] stop := by
    simpa [state,stop,mid,List.append_assoc,CandidateSearchConfigurationProgram.state,
      ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (mid++ec) (args.set .r3 root) [] tape 3,[],0⟩ := by
    simp [state,stop,program,configurationLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨es++ec,args,root,?_,?_⟩
  · simpa only [mid,List.append_assoc] using rep
  · have whole := append_run compute (.step enter (append_run run (.step ret (.done _))))
    let arithmetic := ConcreteExpressionProgram.runSteps (inputs vertices grid) term
    let configure := CandidateSearchConfigurationProgram.steps (countWord vertices grid)
    have count : arithmetic+4+(configure+1+1)=steps vertices grid := by
      change arithmetic+4+(configure+1+1)=arithmetic+configure+6
      omega
    rw [← count]
    simpa only [mid,List.append_assoc,List.nil_append] using whole

private theorem at_entry (s : NaturalState 299) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_input_configuration {n L H A : ℕ} (vertices grid : Bits)
    (nh : value vertices=n) (lh : value grid=L)
    (initial : BitState 299) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (nv : BoolList (eraseState initial).heap (eraseState initial).registers.a vertices)
    (gw : BoolList (eraseState initial).heap (eraseState initial).registers.b grid) :
    ∃ charge out, Run program (steps vertices grid) charge initial [] out ∧
      Configuration (eraseState out).heap (eraseState out).registers.d (wordTable (label (n:=n) (L:=L)))
        (label ((numberEquiv n L) source)) (label ((numberEquiv n L) sink)) (pairTable (label (n:=n) (L:=L))) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=3 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 299 H A (instructionBound n L (max vertices.length grid.length)) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,rep,body⟩ := natural_input_configuration nh lh nv gw old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 3
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have run : NaturalRun program (steps vertices grid) old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨paid,out,execution,hout,hstop,charge,unchanged⟩ := terminating_simulation bounded run stop
  have stepBound := steps_le vertices grid
  rw [nh,lh] at stepBound
  refine ⟨paid,out,execution,?_,unchanged,?_,?_,⟨ext,?_⟩,hstop,
    charge.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ stepBound)⟩
  · rw [hout]; exact rep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.CandidateInputConfigurationProgram
