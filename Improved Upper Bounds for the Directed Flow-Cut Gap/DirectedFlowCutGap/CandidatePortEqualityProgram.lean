import DirectedFlowCutGap.CandidateNodeListsProgram
import DirectedFlowCutGap.CandidateLevelTestProgram

/-! Determine port identity from the stored kind and original vertex word. -/

namespace DirectedFlowCutGap.CandidatePortEqualityProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open CandidateEnumeration (Port)
open CandidateNodeListsProgram (PortAt)
open CandidatePortAdjacencyProgram (kind tag vertex)

def compareLabel (pc : Fin 48) : Fin 72 := ⟨24+pc.val,by omega⟩

def program : Program 72 := fun pc =>
  if pc.val<24 then
    match pc.val with
    | 0 => .field .r2 .r0 false 1
    | 1 => .field .r3 .r1 false 2
    | 2 => .branch .r2 3 4 5 23
    | 3 => .branch .r3 8 17 17 23
    | 4 => .branch .r3 17 8 17 23
    | 5 => .branch .r3 17 17 8 23
    | 8 => .field .r0 .r0 true 9
    | 9 => .field .r1 .r1 true 10
    | 10 => .call (compareLabel 0) (compareLabel 47) .r3
    | 16 => .make .r3 (.flag true) 18
    | 17 => .make .r3 (.flag false) 18
    | _ => .halt
  else if pc.val=71 then .branch .r3 16 17 17 23
  else ReferenceProgramLabels.instruction compareLabel
    (BinaryComparisonProgram.program ⟨pc.val-24,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 72))
    (tape : Bits) (pc : Fin 72) : NaturalState 72 := ⟨heap,heap.length,r,stack,pc,tape⟩

def steps {n : ℕ} (p q : Port n) : ℕ :=
  if kind p=kind q then BinaryComparisonProgram.steps (vertex p).val.bits (vertex q).val.bits+9 else 5

def instructionBound (n : ℕ) : ℕ := 16*(2*n.size+1)+9

theorem steps_le {n : ℕ} (p q : Port n) : steps p q ≤ instructionBound n := by
  have a : (vertex p).val.bits.length ≤ n.size := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le_size (vertex p).isLt.le
  have b : (vertex q).val.bits.length ≤ n.size := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le_size (vertex q).isLt.le
  have work := BinaryComparisonProgram.steps_bound (vertex p).val.bits (vertex q).val.bits
  unfold steps instructionBound
  split <;> omega

theorem kind_vertex_iff {n : ℕ} (p q : Port n) : kind p=kind q ∧ vertex p=vertex q ↔ p=q := by
  rcases p with p | (p | p) <;> rcases q with q | (q | q) <;> simp [kind,vertex]

private theorem slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc≠.halt) :
    program (compareLabel pc)=ReferenceProgramLabels.instruction compareLabel (BinaryComparisonProgram.program pc) := by
  by_cases hp : pc.val=47
  · have eq : pc=47 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,compareLabel,show ¬24+pc.val<24 by omega,show 24+pc.val≠71 by omega]

set_option maxHeartbeats 1000000 in
private theorem read_kinds {heap : NaturalHeap} {r : Registers ℕ} {p q l m : ℕ}
    {a b : CandidatePortAdjacencyProgram.Kind}
    (left : heap[r.a]?=some (.pair p l)) (right : heap[r.b]?=some (.pair q m))
    (ta : heap[p]?=some (tag a)) (tb : heap[q]?=some (tag b)) (tape : Bits) :
    NaturalRun program 4 (state heap r [] tape 0) []
      (state heap ((r.set .r2 p).set .r3 q) [] tape (if a=b then 8 else 17)) := by
  apply ReferenceProgramSteps.sound
  cases a <;> cases b <;>
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,tag,left,right,ta,tb]

private theorem compare_call {heap : NaturalHeap} {r : Registers ℕ} {p q l m : ℕ} {x y : Bits}
    (left : heap[r.a]?=some (.pair p l)) (right : heap[r.b]?=some (.pair q m))
    (xRep : BoolList heap l x) (yRep : BoolList heap m y) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      (heap++ext)[root]?=some (BinaryComparisonProgram.tag (BinaryComparisonProgram.order x y)) ∧
      NaturalRun program (BinaryComparisonProgram.steps x y+3) (state heap r [] tape 8) []
        (state (heap++ext) (args.set .r3 root) [] tape (compareLabel 47)) := by
  let args := (r.set .r0 l).set .r1 m
  let caller : Frame ℕ 72 := ⟨compareLabel 47,.r3,args⟩
  have setup : NaturalRun program 3 (state heap r [] tape 8) [] (state heap args [caller] tape (compareLabel 0)) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,caller,left,right]
  obtain ⟨ext,root,len,body,rep⟩ := BinaryComparisonProgram.compare_return
    (a:=args.a) (b:=args.b) xRep yRep heap.length args.c args.d rfl args 47 [] tape
  have lifted := ReferenceProgramLabels.run compareLabel BinaryComparisonProgram.program program slots body
  have run : NaturalRun program (BinaryComparisonProgram.steps x y) (state heap args [caller] tape (compareLabel 0)) []
      (state (heap++ext) (args.set .r3 root) [] tape (compareLabel 47)) := by
    cases r
    simpa [state,args,caller,BinaryComparisonProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,Registers.set,len] using lifted
  exact ⟨ext,args,root,rep,by simpa only [Nat.add_comm 3,List.nil_append] using append_run setup run⟩

private theorem classify {heap : NaturalHeap} {r : Registers ℕ} {o : Ordering}
    (rep : heap[r.d]?=some (BinaryComparisonProgram.tag o)) (tape : Bits) :
    let b := decide (o=.eq)
    NaturalRun program 2 (state heap r [] tape (compareLabel 47)) []
      (state (heap++[.flag b]) (r.set .r3 heap.length) [] tape 18) := by
  apply ReferenceProgramSteps.sound
  cases o <;> simp [ReferenceProgramSteps.run,state,program,compareLabel,tickNatural,Registers.get,
    rep,BinaryComparisonProgram.tag,tagBranch,allocateNatural,Recipe.cell,Registers.set]

theorem natural_equality {n : ℕ} {p q : Port n} {heap : NaturalHeap} {r : Registers ℕ}
    (left : PortAt heap r.a p) (right : PortAt heap r.b q) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ), (heap++ext)[root]?=some (.flag (decide (p=q))) ∧
      NaturalRun program (steps p q) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 18) := by
  obtain ⟨tp,l,hp,ta,xRep⟩ := left
  obtain ⟨tq,m,hq,tb,yRep⟩ := right
  let ready := (r.set .r2 tp).set .r3 tq
  have compareKinds := read_kinds hp hq ta tb tape
  by_cases matching : kind p=kind q
  · simp only [ite_eq_left matching] at compareKinds
    obtain ⟨ext,args,root,rep,body⟩ := compare_call (r:=ready) hp hq xRep yRep tape
    let mid := heap++ext
    let b := decide (BinaryComparisonProgram.order (vertex p).val.bits (vertex q).val.bits=.eq)
    have b_eq : b=decide (p=q) := by
      apply Bool.eq_iff_iff.mpr
      simp only [b,decide_eq_true_eq]
      rw [CandidateLevelTestProgram.order_eq_ite,value_bits,value_bits]
      have marker : (if (vertex p).val<(vertex q).val then Ordering.lt else
          if (vertex p).val=(vertex q).val then .eq else .gt)=.eq ↔ vertex p=vertex q := by
        rw [Fin.ext_iff]
        by_cases lt : (vertex p).val<(vertex q).val
        · simp [lt,lt.ne]
        · simp [lt]
      rw [marker,← kind_vertex_iff p q]
      simp [matching]
    have done := classify (r:=args.set .r3 root) rep tape
    refine ⟨ext++[.flag b],args,mid.length,?_,?_⟩
    · simp [mid,b_eq]
    · have full := append_run compareKinds (append_run body done)
      let work := BinaryComparisonProgram.steps (vertex p).val.bits (vertex q).val.bits
      have count : 4+(work+3+2)=work+9 := by omega
      rw [steps,ite_eq_left matching,← count]
      simpa only [ready,mid,work,b,List.append_assoc,List.nil_append,Registers.set] using full
  · simp only [ite_eq_right matching] at compareKinds
    have diff : p≠q := fun eq => matching (congrArg kind eq)
    have done : NaturalRun program 1 (state heap ready [] tape 17) []
        (state (heap++[.flag false]) (ready.set .r3 heap.length) [] tape 18) := by
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,allocateNatural,Recipe.cell]
    refine ⟨[.flag false],ready,heap.length,by simp [diff],?_⟩
    rw [steps,ite_eq_right matching]
    exact append_run compareKinds done

end DirectedFlowCutGap.CandidatePortEqualityProgram
