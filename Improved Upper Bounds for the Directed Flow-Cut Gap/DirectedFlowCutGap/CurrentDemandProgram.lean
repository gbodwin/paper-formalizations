import DirectedFlowCutGap.AdaptiveControllerStorage

/-! Read the current active flag for an original demand using its stored labels. -/

namespace DirectedFlowCutGap.CurrentDemandProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor RetainedGridState
open ConcreteExpressionProgram (append_run)
open AdaptiveControllerStorage (CacheAt)
open GraphWalkExtension (Edge edge_extend)
open EpochActiveFromMaskProgram (labelPair)

def label (pc : Fin 36) : Fin 52 := ⟨16+pc.val,by omega⟩

def program : Program 52 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .field .r2 .r0 true 1
    | 1 => .field .r0 .r0 false 2
    | 2 => .field .r3 .r3 false 3
    | 3 => .field .r3 .r3 false 4
    | 4 => .field .r3 .r3 false 5
    | 5 => .field .r3 .r3 false 6
    | 6 => .make .r1 (.pair .r3 .r2) 7
    | 7 => .call (label 34) 8 .r3
    | _ => .halt
  else if pc.val=51 then .ret .r3
  else ReferenceProgramLabels.instruction label (GraphAdjacencyProgram.program ⟨pc.val-16,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 52

def steps {n : ℕ} (p : Pair n) : ℕ := GraphAdjacencyProgram.steps p.1.val.bits p.2.val.bits+10
def instructionBound (n : ℕ) : ℕ := 12*n+20*n.size+39

theorem steps_le {n : ℕ} (p : Pair n) : steps p ≤ instructionBound n := by
  have bound (v : Fin n) : BinaryPointerListRead.steps v.val.bits≤6*n+10*n.size+9 := by
    have read := BinaryPointerListRead.steps_bound v.val.bits
    have width := Nat.size_le_size v.isLt.le
    rw [value_bits,Nat.size_eq_bits_len] at read
    have := v.isLt
    omega
  have first := bound p.1
  have second := bound p.2
  unfold steps instructionBound GraphAdjacencyProgram.steps
  omega

private theorem matrix_rep {n : ℕ} {heap : NaturalHeap} {root : ℕ} {a : PairFlags n}
    (rows : RetainedDemandEraseProgram.RowsAt heap root a) :
    GraphAdjacencyProgram.Matrix heap root (GraphRelaxationRefinement.matrix a) := by
  obtain ⟨refs,spine,words⟩ := rows
  refine ⟨refs,by simpa [GraphRelaxationRefinement.matrix] using words.length_eq,spine,?_⟩
  intro i hi
  have bound : i<a.toList.length := by simpa [GraphRelaxationRefinement.matrix] using hi
  have index : i<refs.length := words.length_eq.symm ▸ bound
  simpa [GraphRelaxationRefinement.matrix] using words.get index bound

private theorem slots (pc : Fin 36) (h : GraphAdjacencyProgram.program pc≠.halt) :
    program (label pc)=ReferenceProgramLabels.instruction label (GraphAdjacencyProgram.program pc) := by
  by_cases stop : pc.val=35
  · have eq : pc=35 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,label,show ¬16+pc.val<16 by omega,show 16+pc.val≠51 by omega]

set_option maxHeartbeats 1700000 in
theorem natural_flag {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {p : Pair n} {d : Data n}
    {optimum : ℕ} {candidate : Family n} {currentWords candidateWords : List (List Bits)} {scale : Bits}
    (key : Edge heap r.a (labelPair p)) (cache : CacheAt heap r.d d optimum candidate currentWords candidateWords scale)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),(heap++ext)[root]?=some (.flag (flag d.remaining p)) ∧
      NaturalRun program (steps p) (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 8) := by
  obtain ⟨u,v,atKey,src,tgt⟩ := key
  obtain ⟨live,best,atCache,⟨packed,runtime,context,si,weights,free,atState,updated,rr,rc,rt,rf,rs,rv,rd⟩,_⟩ := cache
  obtain ⟨masks,mass,bits,atPacked,⟨active,cut,atMasks,activeRep,cutRep⟩,massRep,massValue⟩ := updated
  let first : Registers ℕ := ⟨u,r.b,v,live⟩
  let second : Registers ℕ := ⟨u,r.b,v,active⟩
  let record : Cell ℕ := .pair active v
  let mid := heap++[record]
  let args : Registers ℕ := ⟨u,heap.length,v,active⟩
  have setup : NaturalRun program 3 (state heap r [] tape 0) [] (state heap first [] tape 3) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atKey,atCache,first]
  have fields : NaturalRun program 3 (state heap first [] tape 3) [] (state heap second [] tape 6) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      atState,atPacked,atMasks,first,second]
  have pack : NaturalRun program 1 (state heap second [] tape 6) [] (state mid args [] tape 7) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      allocateNatural,Recipe.cell,second,mid,args,record]
  let matrix := GraphRelaxationRefinement.matrix d.remaining
  have stored : GraphAdjacencyProgram.Context mid args.b matrix p.2.val.bits :=
    ⟨active,v,by simp [mid,args,record],GraphAdjacencyProgram.matrix_extend (matrix_rep activeRep) _,boolList_extend tgt _⟩
  have rows : value p.1.val.bits < matrix.length := by rw [value_bits,GraphRelaxationRefinement.matrix_length]; exact p.1.isLt
  have columns : value p.2.val.bits<(matrix[value p.1.val.bits]).length := by
    simp [matrix,GraphRelaxationRefinement.matrix,value_bits]
  obtain ⟨ext,root,len,body,rep⟩ := GraphAdjacencyProgram.read_return (b:=args.b) (boolList_extend src [record]) stored
    rows columns mid.length args.c args.d rfl args 35 [] tape
  let frame : Frame ℕ 36 := ⟨35,.r3,args⟩
  have start : tickNatural GraphAdjacencyProgram.program (ReferenceProgramInvocation.state mid args [] tape 34)=
      some ⟨ReferenceProgramInvocation.state mid args [frame] tape 27,[],0⟩ := rfl
  have core : NaturalRun GraphAdjacencyProgram.program (GraphAdjacencyProgram.steps p.1.val.bits p.2.val.bits+1)
      (ReferenceProgramInvocation.state mid args [] tape 34) []
      (ReferenceProgramInvocation.state (mid++ext) (args.set .r3 root) [] tape 35) := by
    simpa [GraphAdjacencyProgram.state,ReferenceProgramInvocation.state,frame,args,Registers.set,labelPair,mid,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      NaturalRun.step start body
  have invoke := ReferenceProgramInvocation.call label slots (caller:=7) (continuation:=8)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [] core
  refine ⟨[record]++ext,args,root,?_,?_⟩
  · simpa [mid,List.append_assoc,matrix,GraphRelaxationRefinement.matrix,value_bits,flag,labelPair] using rep
  · have total : 3+(3+(1+(GraphAdjacencyProgram.steps p.1.val.bits p.2.val.bits+1+2)))=steps p := by unfold steps; omega
    rw [← total]
    simpa only [Registers.get,Registers.set,mid,List.append_assoc,List.nil_append] using
      append_run setup (append_run fields (append_run pack invoke))

end DirectedFlowCutGap.CurrentDemandProgram
