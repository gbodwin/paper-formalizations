import DirectedFlowCutGap.CandidateNodeListsProgram
import DirectedFlowCutGap.CandidatePortGapProgram

/-! Read the candidate graph and removal data through the stored port descriptors. -/

namespace DirectedFlowCutGap.CandidateReverseAdjacencyProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open CandidateEnumeration (Port)
open CandidateNodeListsProgram (PortAt)
open CandidatePortAdjacencyProgram (rows result vertex)
open EncodedCandidateCapacity (Input)

def adjLabel (pc : Fin 116) : Fin 132 := ⟨16+pc.val,by omega⟩

def program : Program 132 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 8 => .field .r3 .r0 false 9
    | 9 => .field .r0 .r0 true 10
    | 10 => .make .r2 (.pair .r2 .r0) 11
    | 11 => .field .r0 .r1 false 12
    | 12 => .make .r3 (.pair .r0 .r3) 13
    | 13 => .field .r0 .r1 true 14
    | 14 => .move .r1 .r2 15
    | 15 => .move .r2 .r3 (adjLabel 0)
    | _ => .halt
  else if pc.val=26 then .ret .r3
  else ReferenceProgramLabels.instruction adjLabel
    (CandidatePortAdjacencyProgram.program ⟨pc.val-16,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 132))
    (tape : Bits) (pc : Fin 132) : NaturalState 132 := ⟨heap,heap.length,r,stack,pc,tape⟩

def instructionBound (n : ℕ) : ℕ := CandidatePortAdjacencyProgram.instructionBound n n.size n.size+10

private theorem slots (pc : Fin 116) (h : CandidatePortAdjacencyProgram.program pc≠.halt) :
    program (adjLabel pc)=ReferenceProgramLabels.instruction adjLabel (CandidatePortAdjacencyProgram.program pc) := by
  by_cases hp : pc.val=10
  · have eq : pc=10 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,adjLabel,show ¬16+pc.val<16 by omega,show 16+pc.val≠26 by omega]

set_option maxHeartbeats 1000000 in
theorem natural_reverse {n : ℕ} {D : Input n} {p q : Port n} {heap : NaturalHeap} {r : Registers ℕ}
    (first : PortAt heap r.a p) (second : PortAt heap r.b q)
    (graph : GraphAdjacencyProgram.Matrix heap r.c (rows D)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root k : ℕ), (heap++ext)[root]?=some (.flag (result D q p)) ∧
      NaturalRun program k (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) ∧
      k ≤ instructionBound n := by
  obtain ⟨tp,x,hp,ptag,xRep⟩ := first
  obtain ⟨tq,y,hq,qtag,yRep⟩ := second
  let i := heap.length
  let ext : NaturalHeap := [.pair r.c x,.pair tq tp]
  let mid := heap++ext
  let args : Registers ℕ := ⟨y,i,i+1,i+1⟩
  let caller : Frame ℕ 132 := ⟨1,.r3,r⟩
  let prep := heap++[.pair r.c x]
  let saved := ((r.set .r3 tp).set .r0 x).set .r2 i
  have hqIn : mid[r.b]?=some (.pair tq y) := lookup_extend hq ext
  have qFirst : prep[r.b]?=some (.pair tq y) := lookup_extend hq _
  have setup : NaturalRun program 9 (state heap r [] tape 0) [] (state mid args [caller] tape (adjLabel 0)) := by
    have first : NaturalRun program 4 (state heap r [] tape 0) [] (state prep saved [caller] tape 11) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,caller,hp,
        i,prep,saved,allocateNatural,Recipe.cell]
    have last : NaturalRun program 5 (state prep saved [caller] tape 11)
        [] (state mid args [caller] tape (adjLabel 0)) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,qFirst,
        i,ext,mid,saved,prep,allocateNatural,Recipe.cell,List.append_assoc,hqIn]
    exact append_run first last
  have matrix : GraphAdjacencyProgram.Context mid args.b (rows D) (vertex p).val.bits :=
    ⟨r.c,x,by simp [mid,args,i,ext],GraphAdjacencyProgram.matrix_extend graph ext,boolList_extend xRep ext⟩
  have tags : mid[args.c]?=some (.pair tq tp) := by
    change (heap++ext)[heap.length+1]?=_
    rw [List.getElem?_append_right (by omega)]
    simp [ext]
  obtain ⟨eb,regs,root,k,rep,body,bound⟩ := CandidatePortAdjacencyProgram.natural_adjacency
    (r:=args) (boolList_extend yRep ext) matrix (value_bits _) (value_bits _) tags
    (lookup_extend qtag ext) (lookup_extend ptag ext) tape
  let stop := state (mid++eb) (regs.set .r3 root) [caller] tape (adjLabel 10)
  have lifted := ReferenceProgramLabels.run adjLabel CandidatePortAdjacencyProgram.program program slots body
  have lifted := ReferenceProgramStack.run program [caller] lifted
  have run : NaturalRun program k (state mid args [caller] tape (adjLabel 0)) [] stop := by
    simpa [state,stop,mid,CandidatePortAdjacencyProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (mid++eb) (r.set .r3 root) [] tape 1,[],0⟩ := by
    simp [stop,state,program,adjLabel,tickNatural,caller,Registers.get,Registers.set]
  refine ⟨ext++eb,root,k+10,?_,?_,?_⟩
  · simpa only [mid,List.append_assoc] using rep
  · have count : 9+(k+1)=k+10 := by omega
    rw [← count]
    simpa only [mid,List.append_assoc,List.nil_append,Nat.zero_add] using append_run setup (append_run run (.step ret (.done _)))
  · have a : (vertex p).val.bits.length ≤ n.size := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le_size (vertex p).isLt.le
    have b : (vertex q).val.bits.length ≤ n.size := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le_size (vertex q).isLt.le
    unfold instructionBound CandidatePortAdjacencyProgram.instructionBound at *
    omega

end DirectedFlowCutGap.CandidateReverseAdjacencyProgram

namespace DirectedFlowCutGap.CandidatePortGapAtProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open CandidateEnumeration (Port)
open CandidateNodeListsProgram (PortAt)
open CandidatePortGapProgram (InputBounds Stored active gap)
open CandidatePortAdjacencyProgram (kind vertex)
open EncodedCandidateCapacity (Input)

def gapLabel (pc : Fin 52) : Fin 68 := ⟨16+pc.val,by omega⟩

def program : Program 68 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 8 => .field .r3 .r0 false 9
    | 9 => .field .r0 .r0 true (gapLabel 0)
    | _ => .halt
  else if pc.val=27 then .ret .r3
  else ReferenceProgramLabels.instruction gapLabel
    (CandidatePortGapProgram.program ⟨pc.val-16,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 68))
    (tape : Bits) (pc : Fin 68) : NaturalState 68 := ⟨heap,heap.length,r,stack,pc,tape⟩

def instructionBound (n : ℕ) : ℕ := 6*n+10*n.size+21

private theorem slots (pc : Fin 52) (h : CandidatePortGapProgram.program pc≠.halt) :
    program (gapLabel pc)=ReferenceProgramLabels.instruction gapLabel (CandidatePortGapProgram.program pc) := by
  by_cases hp : pc.val=11
  · have eq : pc=11 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,gapLabel,show ¬16+pc.val<16 by omega,show 16+pc.val≠27 by omega]

theorem natural_gap {n : ℕ} (D : Input n) {p : Port n} {heap : NaturalHeap} {r : Registers ℕ} {grid cap : Bits}
    (port : PortAt heap r.a p) (removed : BoolList heap r.b D.removed.toList)
    (limits : InputBounds heap r.c grid cap) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),Stored (heap++ext) root (active D p) (gap D grid cap p) ∧
      NaturalRun program (CandidatePortGapProgram.steps (kind p) (vertex p).val.bits+4)
        (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  obtain ⟨tag,label,pair,mode,rep⟩ := port
  let args := (r.set .r3 tag).set .r0 label
  let caller : Frame ℕ 68 := ⟨1,.r3,r⟩
  have setup : NaturalRun program 3 (state heap r [] tape 0) [] (state heap args [caller] tape (gapLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,caller,pair]
  obtain ⟨ext,regs,root,output,body⟩ := CandidatePortGapProgram.natural_gap D p (r:=args)
    rep (value_bits _) removed limits mode tape
  let stop := state (heap++ext) (regs.set .r3 root) [caller] tape (gapLabel 11)
  have lifted := ReferenceProgramLabels.run gapLabel CandidatePortGapProgram.program program slots body
  have lifted := ReferenceProgramStack.run program [caller] lifted
  let work := CandidatePortGapProgram.steps (kind p) (vertex p).val.bits
  have run : NaturalRun program work (state heap args [caller] tape (gapLabel 0)) [] stop := by
    simpa [state,stop,work,CandidatePortGapProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r3 root) [] tape 1,[],0⟩ := by
    simp [stop,state,program,gapLabel,tickNatural,caller,Registers.get,Registers.set]
  refine ⟨ext,root,output,?_⟩
  have count : 3+(work+1)=work+4 := by omega
  change NaturalRun program (work+4) _ [] _
  rw [← count]
  exact append_run setup (append_run run (.step ret (.done _)))

theorem steps_le {n : ℕ} (p : Port n) :
    CandidatePortGapProgram.steps (kind p) (vertex p).val.bits+4 ≤ instructionBound n := by
  have w : (vertex p).val.bits.length ≤ n.size := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le_size (vertex p).isLt.le
  have h := CandidatePortGapProgram.steps_le (kind p) (vertex p).val.bits n (by simp [value_bits])
  unfold instructionBound
  omega

end DirectedFlowCutGap.CandidatePortGapAtProgram
