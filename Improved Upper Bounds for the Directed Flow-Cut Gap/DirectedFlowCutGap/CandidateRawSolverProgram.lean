import DirectedFlowCutGap.CandidateCapacityMatrixProgram
import DirectedFlowCutGap.CandidatePreparedSolverProgram

/-!
# Physical candidate solver over the original graph

The fixed program compiles the capacity matrix in canonical order, then
solves and decodes the cut. The matrix pointer is the one returned by the
compiler, and the solver reuses the original grid and removal words.
-/

namespace DirectedFlowCutGap.CandidateRawSolverProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor CandidateClosureProvider IntegralNetworkFlow
open ConcreteExpressionProgram (append_run)
open CandidateEnumeration (Node Network networkOrder)
open CandidatePortAdjacencyProgram (rows)
open CandidateCapacitySetupProgram (Parameters)
open CandidateCapacityTableData (table table_values table_widths)
open PathCostMaterialization (WordList)
open CandidatePhysicalCut (outputMask)
open CandidateNumeratorScanProgram (scan)
open EncodedCandidateCapacity (Input)

def matrixLabel (pc : Fin 1395) : Fin 3797 := ⟨16+pc.val,by omega⟩
def solveLabel (pc : Fin 2386) : Fin 3797 := ⟨1411+pc.val,by omega⟩

def program : Program 3797 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call (matrixLabel 0) 1 .r0
    | 1 => .call (solveLabel 0) 2 .r3
    | _ => .halt
  else if h : pc.val<1411 then
    if pc.val=20 then .ret .r3
    else ReferenceProgramLabels.instruction matrixLabel (CandidateCapacityMatrixProgram.program ⟨pc.val-16,by omega⟩)
  else if pc.val=1415 then .ret .r3
  else ReferenceProgramLabels.instruction solveLabel
    (CandidatePreparedSolverProgram.program ⟨pc.val-1411,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 3797))
    (tape : Bits) (pc : Fin 3797) : NaturalState 3797 := ⟨heap,heap.length,r,stack,pc,tape⟩

def instructionBound (n L nWidth gridWidth boundWidth : ℕ) : ℕ :=
  CandidateCapacityMatrixProgram.instructionBound n L nWidth gridWidth boundWidth+
    CandidatePreparedSolverProgram.instructionBound n L nWidth gridWidth+4

private theorem matrix_slots (pc : Fin 1395) (h : CandidateCapacityMatrixProgram.program pc≠.halt) :
    program (matrixLabel pc)=ReferenceProgramLabels.instruction matrixLabel (CandidateCapacityMatrixProgram.program pc) := by
  by_cases hp : pc.val=4
  · have eq : pc=4 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,matrixLabel,show ¬16+pc.val<16 by omega,show 16+pc.val<1411 by omega,show 16+pc.val≠20 by omega]

private theorem solve_slots (pc : Fin 2386) (h : CandidatePreparedSolverProgram.program pc≠.halt) :
    program (solveLabel pc)=ReferenceProgramLabels.instruction solveLabel (CandidatePreparedSolverProgram.program pc) := by
  by_cases hp : pc.val=4
  · have eq : pc=4 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,solveLabel,show ¬1411+pc.val<16 by omega,show ¬1411+pc.val<1411 by omega,show 1411+pc.val≠1415 by omega]

private theorem build_call {heap ext : NaturalHeap} {r args : Registers ℕ} {root k : ℕ} {tape : Bits}
    (body : NaturalRun CandidateCapacityMatrixProgram.program k
      (CandidateCapacityMatrixProgram.state heap r [] tape 0) []
      (CandidateCapacityMatrixProgram.state (heap++ext) (args.set .r3 root) [] tape 4)) :
    NaturalRun program (k+2) (state heap r [] tape 0) [] (state (heap++ext) (r.set .r0 root) [] tape 1) := by
  let frame : Frame ℕ 3797 := ⟨1,.r0,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [frame] tape (matrixLabel 0),[],0⟩ := rfl
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape (matrixLabel 4)
  have lifted := ReferenceProgramLabels.run matrixLabel CandidateCapacityMatrixProgram.program program matrix_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have work : NaturalRun program k (state heap r [frame] tape (matrixLabel 0)) [] stop := by
    simpa [state,stop,CandidateCapacityMatrixProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r0 root) [] tape 1,[],0⟩ := by
    simp [state,stop,program,matrixLabel,tickNatural,frame,Registers.get,Registers.set]
  exact .step enter (append_run work (.step ret (.done _)))

private theorem solve_call {heap ext : NaturalHeap} {r args : Registers ℕ} {root k : ℕ} {tape : Bits}
    (body : NaturalRun CandidatePreparedSolverProgram.program k
      (CandidatePreparedSolverProgram.state heap r [] tape 0) []
      (CandidatePreparedSolverProgram.state (heap++ext) (args.set .r3 root) [] tape 4)) :
    NaturalRun program (k+2) (state heap r [] tape 1) [] (state (heap++ext) (r.set .r3 root) [] tape 2) := by
  let frame : Frame ℕ 3797 := ⟨2,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 1)=some ⟨state heap r [frame] tape (solveLabel 0),[],0⟩ := rfl
  let stop := state (heap++ext) (args.set .r3 root) [frame] tape (solveLabel 4)
  have lifted := ReferenceProgramLabels.run solveLabel CandidatePreparedSolverProgram.program program solve_slots body
  have lifted := ReferenceProgramStack.run program [frame] lifted
  have work : NaturalRun program k (state heap r [frame] tape (solveLabel 0)) [] stop := by
    simpa [state,stop,CandidatePreparedSolverProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 2,[],0⟩ := by
    simp [state,stop,program,solveLabel,tickNatural,frame,Registers.get,Registers.set]
  exact .step enter (append_run work (.step ret (.done _)))

theorem natural_raw_solver {n L B : ℕ} {D : Input n} {s t : Fin n} {heap : NaturalHeap} {r : Registers ℕ}
    {vertices grid bound : Bits} {removal scale : ℕ}
    (positive : 0<L) (feasible : CandidateFeasible D.graph s t D.cut L B)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (graph : GraphAdjacencyProgram.Matrix heap r.a (rows D)) (size : BoolList heap r.b vertices) (numeric : value vertices=n)
    (pair : heap[r.c]?=some (.pair removal scale)) (mask : BoolList heap removal D.removed.toList)
    (word : BoolList heap scale grid) (gridValue : value grid=L)
    (params : Parameters heap r.d bound s t) (cap : value bound=B) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),
      WordList (heap++ext) root (scan (L+1) grid (outputMask D s t L B EN E) D.removed.toList) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 2) ∧
      k ≤ instructionBound n L vertices.length grid.length bound.length := by
  obtain ⟨em,regs,matrix,k,matrixRep,build,boundBuild⟩ := CandidateCapacityMatrixProgram.natural_matrix
    graph size numeric pair mask word gridValue params cap tape
  let mid := heap++em
  let args := r.set .r0 matrix
  let cs := table D s t L B (networkOrder n L) (networkOrder n L)
  obtain ⟨es,out,root,j,rep,solve,boundSolve⟩ := CandidatePreparedSolverProgram.natural_prepared_solver (r:=args)
    D s t L B positive feasible EN E cs (table_values D s t L B) (table_widths D s t L B _ _) matrixRep
    vertices grid numeric gridValue (boolList_extend size em) (lookup_extend pair em)
    (boolList_extend mask em) (boolList_extend word em) tape
  refine ⟨em++es,args,root,k+2+(j+2),?_,?_,?_⟩
  · simpa only [mid,List.append_assoc] using rep
  · have trace := append_run (build_call build) (solve_call solve)
    simpa only [mid,List.append_assoc,List.nil_append] using trace
  · unfold instructionBound
    omega

private theorem at_entry (s : NaturalState 3797) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_raw_solver {n L B H A removal scale : ℕ} {D : Input n} {s t : Fin n}
    {vertices grid bound : Bits}
    (positive : 0<L) (feasible : CandidateFeasible D.graph s t D.cut L B)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (initial : BitState 3797) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (graph : GraphAdjacencyProgram.Matrix (eraseState initial).heap (eraseState initial).registers.a (rows D))
    (size : BoolList (eraseState initial).heap (eraseState initial).registers.b vertices) (numeric : value vertices=n)
    (pair : (eraseState initial).heap[(eraseState initial).registers.c]?=some (.pair removal scale))
    (mask : BoolList (eraseState initial).heap removal D.removed.toList)
    (word : BoolList (eraseState initial).heap scale grid) (gridValue : value grid=L)
    (params : Parameters (eraseState initial).heap (eraseState initial).registers.d bound s t) (cap : value bound=B) :
    ∃ (charge steps : ℕ) (out : BitState 3797) (words : List Bits),Run program steps charge initial [] out ∧
      WordList (eraseState out).heap (eraseState out).registers.d words ∧
      words.map (fun x => (value x : ℤ)) =
        (EncodedCandidateOutput.solve D s t L B EN E (ResidualSearch.Enumeration.fin n)).numerators.map Prod.snd ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=2 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 3797 H A (instructionBound n L vertices.length grid.length bound.length) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,k,rep,body,limit⟩ := natural_raw_solver positive feasible EN E graph size numeric pair mask word
    gridValue params cap old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 2
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have run : NaturalRun program k old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨paid,out,execution,hout,hstop,cost,tape⟩ := terminating_simulation bounded run stop
  refine ⟨paid,k,out,_,execution,?_,CandidateNumeratorScanProgram.scan_candidate_values D s t L B positive feasible EN E grid gridValue,
    tape,?_,?_,⟨ext,?_⟩,hstop,cost.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ limit)⟩
  · rw [hout]; exact rep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.CandidateRawSolverProgram
