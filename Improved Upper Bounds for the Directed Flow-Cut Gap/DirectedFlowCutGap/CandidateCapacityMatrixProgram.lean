import DirectedFlowCutGap.CandidateInputNodeListsProgram
import DirectedFlowCutGap.CandidateCapacitySetupProgram
import DirectedFlowCutGap.CandidateCapacityTableProgram

/-! Lower the whole capacity matrix from the graph and scalar input words. -/

namespace DirectedFlowCutGap.CandidateCapacityMatrixProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open CandidateEnumeration (networkOrder)
open CandidatePortAdjacencyProgram (rows)
open CandidateNodeListsProgram (Stored stored_extend)
open CandidateCapacitySetupProgram (Parameters parameters_extend)
open CandidateCapacityTableData (table)
open CandidateCapacityCellProgram (Inputs)
open ResidualZeroTableProgram (CapacityRows)
open EncodedCandidateCapacity (Input)

def nodesLabel (pc : Fin 145) : Fin 1395 := ⟨16+pc.val,by omega⟩
def setupLabel (pc : Fin 309) : Fin 1395 := ⟨161+pc.val,by omega⟩
def tableLabel (pc : Fin 925) : Fin 1395 := ⟨470+pc.val,by omega⟩

def program : Program 1395 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call 8 1 .r1
    | 1 => .call (setupLabel 0) 2 .r2
    | 2 => .move .r0 .r1 3
    | 3 => .call (tableLabel 0) 4 .r3
    | 8 => .move .r0 .r1 9
    | 9 => .field .r1 .r2 true (nodesLabel 0)
    | _ => .halt
  else if h : pc.val<161 then
    if pc.val=21 then .ret .r3
    else ReferenceProgramLabels.instruction nodesLabel (CandidateInputNodeListsProgram.program ⟨pc.val-16,by omega⟩)
  else if h : pc.val<470 then
    if pc.val=165 then .ret .r3
    else ReferenceProgramLabels.instruction setupLabel (CandidateCapacitySetupProgram.program ⟨pc.val-161,by omega⟩)
  else if pc.val=472 then .ret .r3
  else ReferenceProgramLabels.instruction tableLabel
    (CandidateCapacityTableProgram.program ⟨pc.val-470,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 1395))
    (tape : Bits) (pc : Fin 1395) : NaturalState 1395 := ⟨heap,heap.length,r,stack,pc,tape⟩

def instructionBound (n L nWidth gridWidth boundWidth : ℕ) : ℕ :=
  CandidateInputNodeListsProgram.instructionBound n L nWidth gridWidth+
    CandidateCapacitySetupProgram.instructionBound n L gridWidth boundWidth+
    CandidateCapacityTableProgram.instructionBound n L gridWidth boundWidth+9

private theorem nodes_slots (pc : Fin 145) (h : CandidateInputNodeListsProgram.program pc≠.halt) :
    program (nodesLabel pc)=ReferenceProgramLabels.instruction nodesLabel (CandidateInputNodeListsProgram.program pc) := by
  by_cases hp : pc.val=5
  · have eq : pc=5 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,nodesLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<161 by omega,show 16+pc.val≠21 by omega]

private theorem setup_slots (pc : Fin 309) (h : CandidateCapacitySetupProgram.program pc≠.halt) :
    program (setupLabel pc)=ReferenceProgramLabels.instruction setupLabel (CandidateCapacitySetupProgram.program pc) := by
  by_cases hp : pc.val=4
  · have eq : pc=4 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,setupLabel,show ¬161+pc.val<16 by omega,show ¬161+pc.val<161 by omega,
      show 161+pc.val<470 by omega,show 161+pc.val≠165 by omega]

private theorem table_slots (pc : Fin 925) (h : CandidateCapacityTableProgram.program pc≠.halt) :
    program (tableLabel pc)=ReferenceProgramLabels.instruction tableLabel (CandidateCapacityTableProgram.program pc) := by
  by_cases hp : pc.val=2
  · have eq : pc=2 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,tableLabel,show ¬470+pc.val<16 by omega,show ¬470+pc.val<161 by omega,
      show ¬470+pc.val<470 by omega,show 470+pc.val≠472 by omega]

private theorem nodes_call {n L : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {vertices grid : Bits}
    {removal scale : ℕ} (size : BoolList heap r.b vertices) (word : BoolList heap scale grid)
    (numeric : value vertices=n) (gridValue : value grid=L) (input : heap[r.c]?=some (.pair removal scale)) (tape : Bits) :
    ∃ ext root,Stored (heap++ext) root (networkOrder n L) ∧
      NaturalRun program (CandidateInputNodeListsProgram.steps vertices grid+4) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r1 root) [] tape 1) := by
  let args := (r.set .r0 r.b).set .r1 scale
  let caller : Frame ℕ 1395 := ⟨1,.r1,r⟩
  have setup : NaturalRun program 3 (state heap r [] tape 0) [] (state heap args [caller] tape (nodesLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,input,args,caller]
  obtain ⟨ext,regs,root,rep,body⟩ := CandidateInputNodeListsProgram.natural_input_nodes (r:=args) size word numeric gridValue tape
  let stop := state (heap++ext) (regs.set .r3 root) [caller] tape (nodesLabel 5)
  have lifted := ReferenceProgramLabels.run nodesLabel CandidateInputNodeListsProgram.program program nodes_slots body
  have lifted := ReferenceProgramStack.run program [caller] lifted
  let work := CandidateInputNodeListsProgram.steps vertices grid
  have run : NaturalRun program work (state heap args [caller] tape (nodesLabel 0)) [] stop := by
    simpa [state,stop,work,CandidateInputNodeListsProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r1 root) [] tape 1,[],0⟩ := by
    simp [state,stop,program,nodesLabel,tickNatural,caller,Registers.get,Registers.set]
  refine ⟨ext,root,rep,?_⟩
  have count : 3+(work+1)=work+4 := by omega
  change NaturalRun program (work+4) _ [] _
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

private theorem setup_call {n L B : ℕ} {D : Input n} {s t : Fin n} {heap : NaturalHeap} {r : Registers ℕ}
    {grid bound : Bits} {removal scale : ℕ}
    (graph : GraphAdjacencyProgram.Matrix heap r.a (rows D)) (input : heap[r.c]?=some (.pair removal scale))
    (mask : BoolList heap removal D.removed.toList) (word : BoolList heap scale grid) (numeric : value grid=L)
    (parameters : Parameters heap r.d bound s t) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ),Inputs (heap++ext) root D s t L B grid bound ∧
      NaturalRun program k (state heap r [] tape 1) [] (state (heap++ext) (r.set .r2 root) [] tape 2) ∧
      k ≤ CandidateCapacitySetupProgram.instructionBound n L grid.length bound.length+2 := by
  obtain ⟨ext,regs,root,k,rep,body,bound⟩ := CandidateCapacitySetupProgram.natural_setup (B:=B)
    graph input mask word numeric parameters tape
  let frame : Frame ℕ 1395 := ⟨2,.r2,r⟩
  have enter : tickNatural program (state heap r [] tape 1)=some ⟨state heap r [frame] tape (setupLabel 0),[],0⟩ := rfl
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (setupLabel 4)
  have lifted := ReferenceProgramLabels.run setupLabel CandidateCapacitySetupProgram.program program setup_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have run : NaturalRun program k (state heap r [frame] tape (setupLabel 0)) [] stop := by
    simpa [state,stop,CandidateCapacitySetupProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r2 root) [] tape 2,[],0⟩ := by
    simp [state,stop,program,setupLabel,tickNatural,frame,Registers.get,Registers.set]
  exact ⟨ext,root,k+2,rep,.step enter (append_run run (.step ret (.done _))),by omega⟩

private theorem table_call {n L B : ℕ} {D : Input n} {s t : Fin n} {heap : NaturalHeap} {r : Registers ℕ}
    {grid bound : Bits} (descriptors : Stored heap r.b (networkOrder n L))
    (inputs : Inputs heap r.c D s t L B grid bound)
    (scale : value grid=L) (cap : value bound=B) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      CapacityRows (heap++ext) root (table D s t L B (networkOrder n L) (networkOrder n L)) ∧
      NaturalRun program k (state heap r [] tape 2) [] (state (heap++ext) (args.set .r3 root) [] tape 4) ∧
      k ≤ CandidateCapacityTableProgram.instructionBound n L grid.length bound.length+3 := by
  let args := r.set .r0 r.b
  let frame : Frame ℕ 1395 := ⟨4,.r3,args⟩
  have setup : NaturalRun program 2 (state heap r [] tape 2) [] (state heap args [frame] tape (tableLabel 0)) := by
    apply ReferenceProgramSteps.sound
    rfl
  obtain ⟨ext,regs,root,k,rep,body,bound⟩ := CandidateCapacityTableProgram.natural_table (r:=args) descriptors inputs scale cap tape
  let stop := state (heap++ext) (regs.set .r3 root) [frame] tape (tableLabel 2)
  have lifted := ReferenceProgramLabels.run tableLabel CandidateCapacityTableProgram.program program table_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have run : NaturalRun program k (state heap args [frame] tape (tableLabel 0)) [] stop := by
    simpa [state,stop,CandidateCapacityTableProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (args.set .r3 root) [] tape 4,[],0⟩ := by
    simp [state,stop,program,tableLabel,tickNatural,frame,Registers.get,Registers.set]
  refine ⟨ext,args,root,k+3,rep,?_,by omega⟩
  have count : 2+(k+1)=k+3 := by omega
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

theorem natural_matrix {n L B : ℕ} {D : Input n} {s t : Fin n} {heap : NaturalHeap} {r : Registers ℕ}
    {vertices grid bound : Bits} {removal scale : ℕ}
    (graph : GraphAdjacencyProgram.Matrix heap r.a (rows D)) (size : BoolList heap r.b vertices) (numeric : value vertices=n)
    (pair : heap[r.c]?=some (.pair removal scale)) (mask : BoolList heap removal D.removed.toList)
    (word : BoolList heap scale grid) (gridValue : value grid=L) (params : Parameters heap r.d bound s t)
    (cap : value bound=B) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      CapacityRows (heap++ext) root (table D s t L B (networkOrder n L) (networkOrder n L)) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 4) ∧
      k ≤ instructionBound n L vertices.length grid.length bound.length := by
  obtain ⟨en,nodes,descriptors,enumerate⟩ := nodes_call size word numeric gridValue pair tape
  let mid := heap++en
  let ready := r.set .r1 nodes
  obtain ⟨ep,context,k,inputs,prepare,pbound⟩ := setup_call (r:=ready) (B:=B)
    (GraphAdjacencyProgram.matrix_extend graph en) (lookup_extend pair en) (boolList_extend mask en)
    (boolList_extend word en) gridValue (parameters_extend params en) tape
  let grown := mid++ep
  let args := ready.set .r2 context
  obtain ⟨et,regs,root,m,rep,compute,mbound⟩ := table_call (r:=args) (stored_extend descriptors ep) inputs gridValue cap tape
  let prep := CandidateInputNodeListsProgram.steps vertices grid
  refine ⟨en++ep++et,regs,root,prep+4+(k+m),?_,?_,?_⟩
  · simpa only [mid,grown,List.append_assoc] using rep
  · simpa only [mid,grown,prep,List.append_assoc,List.nil_append] using append_run enumerate (append_run prepare compute)
  · have limit := CandidateInputNodeListsProgram.steps_le vertices grid
    rw [numeric,gridValue] at limit
    unfold instructionBound
    omega

end DirectedFlowCutGap.CandidateCapacityMatrixProgram
