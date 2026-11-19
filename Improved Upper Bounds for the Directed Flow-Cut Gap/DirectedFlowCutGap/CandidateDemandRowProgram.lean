import DirectedFlowCutGap.CandidateRawSolverProgram
import DirectedFlowCutGap.ReferenceProgramInvocation
import DirectedFlowCutGap.EpochActiveFromMaskProgram

/-! Prepare a candidate query from the stored demand label and call the raw solver. -/

namespace DirectedFlowCutGap.CandidateDemandRowProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState
open ConcreteExpressionProgram (append_run)
open EncodedCandidateCapacity (Input)
open EpochActiveFromMaskProgram (labelPair)
open GraphWalkExtension (Edge)
open CandidateEnumeration (Node Network)
open CandidatePortAdjacencyProgram (rows)
open CandidateClosureProvider (CandidateFeasible)
open PathCostMaterialization (WordList)
open IntegralNetworkFlow

def GraphSizeAt {n : ℕ} (heap : NaturalHeap) (addr : ℕ) (D : Input n) (vertices : Bits) : Prop :=
  ∃ graph count,heap[addr]?=some (.pair graph count) ∧ GraphAdjacencyProgram.Matrix heap graph (rows D) ∧
    BoolList heap count vertices

def GridAt {n : ℕ} (heap : NaturalHeap) (addr : ℕ) (D : Input n) (grid : Bits) : Prop :=
  ∃ mask scale,heap[addr]?=some (.pair mask scale) ∧ BoolList heap mask D.removed.toList ∧ BoolList heap scale grid

theorem graph_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {D : Input n} {vertices : Bits}
    (g : GraphSizeAt heap root D vertices) (ext : NaturalHeap) : GraphSizeAt (heap++ext) root D vertices := by
  obtain ⟨matrix,count,read,graph,word⟩ := g
  exact ⟨matrix,count,lookup_extend read ext,GraphAdjacencyProgram.matrix_extend graph ext,boolList_extend word ext⟩

theorem grid_extend {n : ℕ} {heap : NaturalHeap} {root : ℕ} {D : Input n} {grid : Bits}
    (g : GridAt heap root D grid) (ext : NaturalHeap) : GridAt (heap++ext) root D grid := by
  obtain ⟨mask,level,read,left,right⟩ := g
  exact ⟨mask,level,lookup_extend read ext,boolList_extend left ext,boolList_extend right ext⟩

def label (pc : Fin 3797) : Fin 3813 := ⟨16+pc.val,by omega⟩

def program : Program 3813 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .make .r3 (.pair .r3 .r0) 1
    | 1 => .field .r0 .r1 false 2
    | 2 => .field .r1 .r1 true 3
    | 3 => .call (label 0) 4 .r3
    | _ => .halt
  else if pc.val=18 then .ret .r3
  else ReferenceProgramLabels.instruction label (CandidateRawSolverProgram.program ⟨pc.val-16,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 3813

noncomputable def rowWords {n : ℕ} (D : Input n) (p : Pair n) (L B : ℕ) (grid : Bits)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L)) : List Bits :=
  CandidateNumeratorScanProgram.scan (L+1) grid (CandidatePhysicalCut.outputMask D p.1 p.2 L B EN E) D.removed.toList

def instructionBound (n L vertices grid bound : ℕ) : ℕ :=
  CandidateRawSolverProgram.instructionBound n L vertices grid bound+5

private theorem slots (pc : Fin 3797) (h : CandidateRawSolverProgram.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (CandidateRawSolverProgram.program pc) := by
  by_cases stop : pc.val=2
  · have eq : pc=2 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,label,show ¬16+pc.val<16 by omega,show 16+pc.val≠18 by omega]

theorem natural_row {n L B : ℕ} {D : Input n} {p : Pair n} {heap : NaturalHeap} {r : Registers ℕ}
    {vertices grid bound : Bits} (positive : 0<L) (feasible : CandidateFeasible D.graph p.1 p.2 D.cut L B)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (key : Edge heap r.a (labelPair p)) (graph : GraphSizeAt heap r.b D vertices) (gridAt : GridAt heap r.c D grid)
    (boundAt : BoolList heap r.d bound) (size : value vertices=n) (gridValue : value grid=L) (cap : value bound=B) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root k : ℕ),WordList (heap++ext) root (rowWords D p L B grid EN E) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 4) ∧
      k ≤ instructionBound n L vertices.length grid.length bound.length := by
  obtain ⟨source,target,atKey,sourceRep,targetRep⟩ := key
  obtain ⟨matrix,count,atGraph,matrixRep,countRep⟩ := graph
  obtain ⟨mask,level,atGrid,maskRep,levelRep⟩ := gridAt
  let cell : Cell ℕ := .pair r.d r.a
  let mid := heap++[cell]
  let args : Registers ℕ := ⟨matrix,count,r.c,heap.length⟩
  have graphAt : mid[r.b]?=some (.pair matrix count) := lookup_extend atGraph [cell]
  have setup : NaturalRun program 3 (state heap r [] tape 0) [] (state mid args [] tape 3) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,graphAt,cell,mid,args]
  have parameters : CandidateCapacitySetupProgram.Parameters mid args.d bound p.1 p.2 :=
    ⟨r.d,r.a,source,target,by simp [mid,args,cell],lookup_extend atKey _,boolList_extend boundAt _,
      boolList_extend sourceRep _,boolList_extend targetRep _⟩
  obtain ⟨ext,out,root,k,rep,body,within⟩ := CandidateRawSolverProgram.natural_raw_solver (r:=args)
    positive feasible EN E (GraphAdjacencyProgram.matrix_extend matrixRep [cell]) (boolList_extend countRep [cell]) size
    (lookup_extend atGrid [cell]) (boolList_extend maskRep [cell]) (boolList_extend levelRep [cell]) gridValue parameters cap tape
  have invoke := ReferenceProgramInvocation.call label slots (caller:=3) (continuation:=4)
    (dst:=.r3) (result:=.r3) (by rfl) (by rfl) [] body
  refine ⟨[cell]++ext,args,root,3+(k+2),?_,?_,?_⟩
  · simpa only [mid,rowWords,List.append_assoc] using rep
  · simpa only [Registers.get,Registers.set,mid,List.append_assoc,List.nil_append] using append_run setup invoke
  · unfold instructionBound
    omega

end DirectedFlowCutGap.CandidateDemandRowProgram
