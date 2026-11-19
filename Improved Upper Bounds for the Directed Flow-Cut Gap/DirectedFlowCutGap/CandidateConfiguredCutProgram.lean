import DirectedFlowCutGap.CandidateInputConfigurationProgram
import DirectedFlowCutGap.CandidateBudgetCutProgram

/-!
# Candidate cut with physical search setup

The program retains the stored capacity matrix. It constructs the search
configuration from the vertex count and the same grid word that the
budget computation uses. Both returned inputs feed the zero-start cut.
-/

namespace DirectedFlowCutGap.CandidateConfiguredCutProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor CandidateClosureProvider IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open EncodedCandidateCapacity (Input)
open CandidatePhysicalCut (networkSize capacityWidth capacities label numberEquiv outputMask)
open ResidualZeroTableProgram (CapacityRows CapacityValues capacityRows_extend)
open ResidualFlowLoopProgram (Configuration)
open ResidualFlowStepProgram (wordTable pairTable)
open MinimumClosureCut (source sink)

def configLabel (pc : Fin 299) : Fin 2177 := ⟨16+pc.val,by omega⟩
def cutLabel (pc : Fin 1862) : Fin 2177 := ⟨315+pc.val,by omega⟩

def program : Program 2177 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call 8 1 .r1
    | 1 => .call (cutLabel 0) 2 .r3
    | 8 => .move .r0 .r1 9
    | 9 => .field .r1 .r2 true (configLabel 0)
    | _ => .halt
  else if h : pc.val<315 then
    if pc.val=19 then .ret .r3
    else ReferenceProgramLabels.instruction configLabel (CandidateInputConfigurationProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=317 then .ret .r3
  else ReferenceProgramLabels.instruction cutLabel
    (CandidateBudgetCutProgram.program ⟨pc.val-315,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 2177))
    (tape : Bits) (pc : Fin 2177) : NaturalState 2177 := ⟨heap,heap.length,r,stack,pc,tape⟩

def instructionBound (n L vertexWidth gridWidth : ℕ) : ℕ :=
  CandidateInputConfigurationProgram.instructionBound n L (max vertexWidth gridWidth)+
    CandidateBudgetCutProgram.instructionBound n L gridWidth+6

private theorem config_slots (pc : Fin 299) (h : CandidateInputConfigurationProgram.program pc≠.halt) :
    program (configLabel pc)=ReferenceProgramLabels.instruction configLabel (CandidateInputConfigurationProgram.program pc) := by
  by_cases hp : pc.val=3
  · have eq : pc=3 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,configLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<315 by omega,show 16+pc.val≠19 by omega]

private theorem cut_slots (pc : Fin 1862) (h : CandidateBudgetCutProgram.program pc≠.halt) :
    program (cutLabel pc)=ReferenceProgramLabels.instruction cutLabel (CandidateBudgetCutProgram.program pc) := by
  by_cases hp : pc.val=2
  · have eq : pc=2 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,cutLabel,show ¬315+pc.val<16 by omega,show ¬315+pc.val<315 by omega,show 315+pc.val≠317 by omega]

private theorem config_call {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {left right : ℕ} {vertices grid : Bits}
    (numeric : value vertices=n) (scale : value grid=L) (size : BoolList heap r.b vertices)
    (pair : heap[r.c]?=some (.pair left right)) (word : BoolList heap right grid) (tape : Bits) :
    ∃ ext root,Configuration (heap++ext) root (wordTable (label (n:=n) (L:=L)))
        (label ((numberEquiv n L) source)) (label ((numberEquiv n L) sink)) (pairTable (label (n:=n) (L:=L))) ∧
      NaturalRun program (CandidateInputConfigurationProgram.steps vertices grid+4) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r1 root) [] tape 1) := by
  let args := (r.set .r0 r.b).set .r1 right
  let frame : Frame ℕ 2177 := ⟨1,.r1,r⟩
  have setup : NaturalRun program 3 (state heap r [] tape 0) [] (state heap args [frame] tape (configLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,frame,args,Registers.get,Registers.set,pair]
  obtain ⟨ext,regs,root,rep,body⟩ := CandidateInputConfigurationProgram.natural_input_configuration (r:=args)
    numeric scale size word tape
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (configLabel 3)
  have lift := ReferenceProgramLabels.run configLabel CandidateInputConfigurationProgram.program program config_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program (CandidateInputConfigurationProgram.steps vertices grid)
      (state heap args [frame] tape (configLabel 0)) [] stop := by
    simpa [state,stop,CandidateInputConfigurationProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r1 root) [] tape 1,[],0⟩ := by
    simp [state,stop,configLabel,program,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have trace := append_run setup (append_run run (.step ret (.done _)))
  let len := CandidateInputConfigurationProgram.steps vertices grid
  have count : 3+(len+1)=len+4 := by omega
  change NaturalRun program (len+4) _ [] _
  rw [← count]
  exact trace

theorem natural_configured_cut {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {left right : ℕ}
    (D : Input n) (s t : Fin n) (L B : ℕ)
    (positive : 0<L) (feasible : CandidateFeasible D.graph s t D.cut L B)
    (EN : ResidualSearch.Enumeration (CandidateEnumeration.Node n L))
    (E : ResidualSearch.Enumeration (CandidateEnumeration.Network n L))
    (cs : List (List Bits)) (values : CapacityValues (capacities D s t L B) cs (List.finRange (networkSize n L))
      (List.finRange (networkSize n L)))
    (widths : ∀ row ∈ cs,∀ cap ∈ row,cap.length≤capacityWidth n L) (input : CapacityRows heap r.a cs)
    (vertices grid : Bits) (numeric : value vertices=n) (scale : value grid=L) (size : BoolList heap r.b vertices)
    (pair : heap[r.c]?=some (.pair left right)) (mask : BoolList heap left D.removed.toList)
    (word : BoolList heap right grid) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      BoolList (heap++ext) root (outputMask D s t L B EN E) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 2) ∧
      k ≤ instructionBound n L vertices.length grid.length := by
  obtain ⟨ep,configuration,config,setup⟩ := config_call numeric scale size pair word tape
  let mid := heap++ep
  let args := r.set .r1 configuration
  obtain ⟨ec,regs,root,k,rep,body,bound⟩ := CandidateBudgetCutProgram.natural_budget_cut (r:=args)
    D s t L B positive feasible EN E cs values widths (capacityRows_extend input ep) config
    (lookup_extend pair ep) (boolList_extend mask ep) grid (boolList_extend word ep) scale tape
  let frame : Frame ℕ 2177 := ⟨2,.r3,args⟩
  let stop := state (mid++ec) (regs.set .r3 root) [frame] tape (cutLabel 2)
  have enter : tickNatural program (state mid args [] tape 1)=some ⟨state mid args [frame] tape (cutLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run cutLabel CandidateBudgetCutProgram.program program cut_slots body
  have lift := ReferenceProgramStack.run program [frame] lift
  have run : NaturalRun program k (state mid args [frame] tape (cutLabel 0)) [] stop := by
    simpa [state,stop,mid,List.append_assoc,CandidateBudgetCutProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramStack.state] using lift
  have ret : tickNatural program stop=some ⟨state (mid++ec) (args.set .r3 root) [] tape 2,[],0⟩ := by
    simp [state,stop,program,cutLabel,tickNatural,frame,Registers.get,Registers.set]
  let ksetup := CandidateInputConfigurationProgram.steps vertices grid
  refine ⟨ep++ec,args,root,ksetup+k+6,?_,?_,?_⟩
  · simpa only [mid,List.append_assoc] using rep
  · have trace := append_run setup (.step enter (append_run run (.step ret (.done _))))
    have count : ksetup+4+(k+1+1)=ksetup+k+6 := by omega
    rw [← count]
    simpa only [mid,List.append_assoc,List.nil_append] using trace
  · have prep := CandidateInputConfigurationProgram.steps_le vertices grid
    rw [numeric,scale] at prep
    unfold instructionBound
    omega

private theorem at_entry (s : NaturalState 2177) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_configured_cut {n H A left right : ℕ} (D : Input n) (s t : Fin n) (L B : ℕ)
    (positive : 0<L) (feasible : CandidateFeasible D.graph s t D.cut L B)
    (EN : ResidualSearch.Enumeration (CandidateEnumeration.Node n L))
    (E : ResidualSearch.Enumeration (CandidateEnumeration.Network n L))
    (cs : List (List Bits)) (values : CapacityValues (capacities D s t L B) cs (List.finRange (networkSize n L))
      (List.finRange (networkSize n L)))
    (widths : ∀ row ∈ cs,∀ cap ∈ row,cap.length≤capacityWidth n L)
    (initial : BitState 2177) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : CapacityRows (eraseState initial).heap (eraseState initial).registers.a cs)
    (vertices grid : Bits) (numeric : value vertices=n) (scale : value grid=L)
    (size : BoolList (eraseState initial).heap (eraseState initial).registers.b vertices)
    (pair : (eraseState initial).heap[(eraseState initial).registers.c]?=some (.pair left right))
    (mask : BoolList (eraseState initial).heap left D.removed.toList) (word : BoolList (eraseState initial).heap right grid) :
    ∃ (charge steps : ℕ) (out : BitState 2177),Run program steps charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (outputMask D s t L B EN E) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=2 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 2177 H A (instructionBound n L vertices.length grid.length) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,k,rep,body,bound⟩ := natural_configured_cut D s t L B positive feasible EN E cs values widths
    input vertices grid numeric scale size pair mask word old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 2
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have run : NaturalRun program k old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨paid,out,execution,hout,hstop,charge,unchanged⟩ := terminating_simulation bounded run stop
  refine ⟨paid,k,out,execution,?_,unchanged,?_,?_,⟨ext,?_⟩,hstop,
    charge.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ bound)⟩
  · rw [hout]; exact rep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.CandidateConfiguredCutProgram
