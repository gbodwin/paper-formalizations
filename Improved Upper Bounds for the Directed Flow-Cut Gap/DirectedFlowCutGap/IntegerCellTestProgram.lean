import DirectedFlowCutGap.IntegerDistanceFromPhysical
import DirectedFlowCutGap.IntegerLevelCuts
import DirectedFlowCutGap.PhysicalCoverReader

/-!
# Physical integer midpoint test

The fixed program consumes the stored optional walk returned by graph recovery,
a vertex numerator and a level index. It tests both boundaries with the binary
interpreter and leaves the fair tape untouched.
-/

namespace DirectedFlowCutGap.IntegerCellTestProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor

def comparisonLabel (pc : Fin 48) : Fin 186 := ⟨22 + pc.val, by omega⟩
def additionLabel (pc : Fin 116) : Fin 186 := ⟨70 + pc.val, by omega⟩

def program : Program 186 := fun pc =>
  if pc.val < 22 then
    match pc.val with
    | 0 => .branch .r0 1 20 20 2
    | 1 => .make .r3 (.flag false) 21
    | 2 => .field .r0 .r0 true 3
    | 3 => .field .r0 .r0 false 4
    | 4 => .call 13 5 .r3
    | 5 => .branch .r3 20 21 6 20
    | 6 => .call (additionLabel 114) 7 .r0
    | 7 => .move .r1 .r2 9
    | 9 => .call (comparisonLabel 30) 10 .r3
    | 10 => .branch .r3 20 15 16 20
    | 13 => .move .r1 .r2 14
    | 14 => .call (comparisonLabel 30) 17 .r3
    | 15 => .make .r3 (.flag true) 21
    | 16 => .make .r3 (.flag false) 21
    | 17 => .ret .r3
    | 19 => .call 0 20 .r3
    | 21 => .ret .r3
    | _ => .halt
  else if pc.val = 68 ∨ pc.val = 185 then .ret .r3
  else if h : pc.val < 70 then
    ReferenceProgramLabels.instruction comparisonLabel
      (BinaryComparisonProgram.program ⟨pc.val - 22, by omega⟩)
  else ReferenceProgramLabels.instruction additionLabel
    (CanonicalArithmeticProgram.program ⟨pc.val - 70, by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (registers : Registers ℕ) (stack : List (Frame ℕ 186))
    (tape : Bits) (pc : Fin 186) : NaturalState 186 :=
  ⟨heap, heap.length, registers, stack, pc, tape⟩

def lower (distance level : Bits) : Bool := (lessEqual distance level).1

def within (distance weight level : Bits) : Bool :=
  lower distance level && !(lessEqual (addCanonical distance weight).1 level).1

def instructions (distance : Option GraphWalkExtension.Walk) (weight level : Bits) : ℕ :=
  match distance with
  | none => 3
  | some q =>
    let d := q.cost.num
    BinaryComparisonProgram.steps d level +
      if lower d level then
        23 + CanonicalArithmeticProgram.instructions false d weight +
          BinaryComparisonProgram.steps (addCanonical d weight).1 level
      else 13

theorem within_eq (d a j : Bits) :
    within d a j = (IntegerLevelCuts.cellTest (value d : WithTop ℕ) (value a) (value j)).1 := by
  change within d a j = decide (value d ≤ value j ∧ value j < value d + value a)
  apply Bool.eq_iff_iff.mpr
  simp only [within,lower,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq]
  rw [(lessEqual_spec _ _).1,← Bool.not_eq_true,(lessEqual_spec _ _).1,(canonical_values _ _).1]
  omega

private theorem comparison_slots (pc : Fin 48) (h : BinaryComparisonProgram.program pc ≠ .halt) :
    program (comparisonLabel pc) =
      ReferenceProgramLabels.instruction comparisonLabel (BinaryComparisonProgram.program pc) := by
  by_cases he : pc.val = 46
  · have eq : pc = 46 := Fin.ext he
    subst pc
    exact (h rfl).elim
  · simp [program,comparisonLabel,show ¬22+pc.val<22 by omega,
      show 22+pc.val≠68 by omega,show 22+pc.val≠185 by omega,show 22+pc.val<70 by omega]

private theorem addition_slots (pc : Fin 116) (h : CanonicalArithmeticProgram.program pc ≠ .halt) :
    program (additionLabel pc) =
      ReferenceProgramLabels.instruction additionLabel (CanonicalArithmeticProgram.program pc) := by
  by_cases he : pc.val = 115
  · have eq : pc = 115 := Fin.ext he
    subst pc
    exact (h rfl).elim
  · simp [program,additionLabel,show ¬70+pc.val<22 by omega,show 70+pc.val≠68 by omega,
      show 70+pc.val≠185 by omega,show ¬70+pc.val<70 by omega]

private theorem join {a b c : NaturalState 186} {m n : ℕ} {es fs : List Event}
    (h : NaturalRun program m a es b) (hg : NaturalRun program n b fs c) :
    NaturalRun program (m+n) a (es++fs) c := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1]
      using NaturalRun.step ht (ih hg)

private theorem compare_return {heap : NaturalHeap} {a b : ℕ} {x y : Bits}
    (hx : BoolList heap a x) (hy : BoolList heap b y) (c d : ℕ)
    (caller : Frame ℕ 186) (stack : List (Frame ℕ 186)) (tape : Bits) :
    ∃ ext root, (heap++ext)[root]? = some (.flag (lessEqual x y).1) ∧
      NaturalRun program (BinaryComparisonProgram.steps x y + 4)
        (state heap ⟨a,b,c,d⟩ (caller::stack) tape (comparisonLabel 30)) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let start := BinaryComparisonProgram.state heap heap.length a b c d [] tape 30
  obtain ⟨out,hrun,hflag,_,_,ha,hb,hc,hstack,htape,hpc,hdense,⟨ext,he,_⟩,_⟩ :=
    BinaryComparisonProgram.compare_high start rfl rfl hx hy rfl
  have shape : out = BinaryComparisonProgram.state (heap++ext) (heap++ext).length
      a b c out.registers.d [] tape 46 := by
    cases out with
    | mk h p r st pc src =>
      cases r
      simp_all [start,BinaryComparisonProgram.state]
  have lifted := ReferenceProgramLabels.run comparisonLabel BinaryComparisonProgram.program program comparison_slots hrun
  have lifted := ReferenceProgramStack.run program (caller::stack) lifted
  rw [shape] at lifted
  let before := state (heap++ext) ⟨a,b,c,out.registers.d⟩ (caller::stack) tape (comparisonLabel 46)
  let after := state (heap++ext) (caller.saved.set caller.destination out.registers.d) stack tape caller.continuation
  have body : NaturalRun program (BinaryComparisonProgram.steps x y + 3)
      (state heap ⟨a,b,c,d⟩ (caller::stack) tape (comparisonLabel 30)) [] before := by
    simpa [start,before,state,ReferenceProgramLabels.state,ReferenceProgramStack.state,
      BinaryComparisonProgram.state] using lifted
  have ret : tickNatural program before = some ⟨after,[],0⟩ := rfl
  exact ⟨ext,out.registers.d,by simpa only [he,start,BinaryComparisonProgram.state] using hflag,
    by simpa [Nat.add_assoc] using join body (NaturalRun.step ret (.done after))⟩

private theorem add_return {heap : NaturalHeap} {a b : ℕ} {x y : Bits}
    (hx : BoolList heap a x) (hy : BoolList heap b y) (c d : ℕ)
    (caller : Frame ℕ 186) (stack : List (Frame ℕ 186)) (tape : Bits) :
    ∃ ext root, BoolList (heap++ext) root (addCanonical x y).1 ∧
      NaturalRun program (CanonicalArithmeticProgram.instructions false x y + 1)
        (state heap ⟨a,b,c,d⟩ (caller::stack) tape (additionLabel 114)) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let start := CanonicalArithmeticProgram.state heap heap.length a b c d [] tape 114
  obtain ⟨ext,root,_,hrun,hrep⟩ := CanonicalArithmeticProgram.canonical_high false start rfl rfl hx hy rfl
  have lifted := ReferenceProgramLabels.run additionLabel CanonicalArithmeticProgram.program program addition_slots hrun
  have lifted := ReferenceProgramStack.run program (caller::stack) lifted
  let before := state (heap++ext) ⟨a,b,c,root⟩ (caller::stack) tape (additionLabel 115)
  let after := state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation
  have body : NaturalRun program (CanonicalArithmeticProgram.instructions false x y)
      (state heap ⟨a,b,c,d⟩ (caller::stack) tape (additionLabel 114)) [] before := by
    simpa [start,before,state,ReferenceProgramLabels.state,ReferenceProgramStack.state,
      CanonicalArithmeticProgram.state] using lifted
  have ret : tickNatural program before = some ⟨after,[],0⟩ := rfl
  rw [CanonicalArithmeticProgram.result_exact false] at hrep
  exact ⟨ext,root,hrep,join body (NaturalRun.step ret (.done after))⟩

private theorem lower_return {heap : NaturalHeap} {a b c d : ℕ} {distance level : Bits}
    (hx : BoolList heap a distance) (hy : BoolList heap c level)
    (stack : List (Frame ℕ 186)) (tape : Bits) :
    ∃ ext root, (heap++ext)[root]? = some (.flag (lower distance level)) ∧
      NaturalRun program (BinaryComparisonProgram.steps distance level + 7)
        (state heap ⟨a,b,c,d⟩ (⟨5,.r3,⟨a,b,c,d⟩⟩::stack) tape 13) []
        (state (heap++ext) ⟨a,b,c,root⟩ stack tape 5) := by
  let saved : List (Frame ℕ 186) := ⟨5,.r3,⟨a,b,c,d⟩⟩::stack
  let cmp : Frame ℕ 186 := ⟨17,.r3,⟨a,c,c,d⟩⟩
  obtain ⟨ext,root,hflag,hrun⟩ := compare_return hx hy c d cmp saved tape
  have hmove : tickNatural program (state heap ⟨a,b,c,d⟩ saved tape 13) =
      some ⟨state heap ⟨a,c,c,d⟩ saved tape 14,[],0⟩ := rfl
  have hcall : tickNatural program (state heap ⟨a,c,c,d⟩ saved tape 14) =
      some ⟨state heap ⟨a,c,c,d⟩ (cmp::saved) tape (comparisonLabel 30),[],0⟩ := rfl
  have hret : tickNatural program (state (heap++ext) ⟨a,c,c,root⟩ saved tape 17) =
      some ⟨state (heap++ext) ⟨a,b,c,root⟩ stack tape 5,[],0⟩ := rfl
  refine ⟨ext,root,hflag,?_⟩
  have trace := NaturalRun.step hmove (NaturalRun.step hcall (join hrun (NaturalRun.step hret (.done _))))
  exact trace

private theorem finish {heap : NaturalHeap} {r : Registers ℕ} {b : Bool}
    (hflag : heap[r.d]? = some (.flag b)) (caller : Frame ℕ 186)
    (stack : List (Frame ℕ 186)) (tape : Bits) :
    NaturalRun program 3 (state heap r (caller::stack) tape 10) []
      (state (heap++[.flag (!b)]) (caller.saved.set caller.destination heap.length)
        stack tape caller.continuation) := by
  let branch : Fin 186 := if b then 16 else 15
  let out := state (heap++[.flag (!b)]) (r.set .r3 heap.length) (caller::stack) tape 21
  have test : tickNatural program (state heap r (caller::stack) tape 10) =
      some ⟨state heap r (caller::stack) tape branch,[],0⟩ := by
    cases b <;> simp [branch,tickNatural,program,state,Registers.get,hflag,tagBranch]
  have store : tickNatural program (state heap r (caller::stack) tape branch) =
      some ⟨out,[],0⟩ := by
    cases b <;> simp [branch,out,tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
  have ret : tickNatural program out = some ⟨state (heap++[.flag (!b)])
      (caller.saved.set caller.destination heap.length) stack tape caller.continuation,[],0⟩ := by
    cases r
    simp [out,tickNatural,program,state,Registers.set,Registers.get]
  exact .step test (.step store (.step ret (.done _)))

private theorem upper_return {heap : NaturalHeap} {a b c d : ℕ} {distance weight level : Bits}
    (hx : BoolList heap a distance) (hy : BoolList heap b weight) (hz : BoolList heap c level)
    (caller : Frame ℕ 186) (stack : List (Frame ℕ 186)) (tape : Bits) :
    ∃ ext root, (heap++ext)[root]? = some (.flag (!(lessEqual (addCanonical distance weight).1 level).1)) ∧
      NaturalRun program (CanonicalArithmeticProgram.instructions false distance weight +
          BinaryComparisonProgram.steps (addCanonical distance weight).1 level + 11)
        (state heap ⟨a,b,c,d⟩ (caller::stack) tape 6) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let saved := caller::stack
  let add : Frame ℕ 186 := ⟨7,.r0,⟨a,b,c,d⟩⟩
  obtain ⟨ext,sum,hsum,hadd⟩ := add_return hx hy c d add saved tape
  let mid := heap++ext
  let cmp : Frame ℕ 186 := ⟨10,.r3,⟨sum,c,c,d⟩⟩
  obtain ⟨extra,flag,hflag,hcmp⟩ := compare_return hsum (boolList_extend hz ext) c d cmp saved tape
  have first : tickNatural program (state heap ⟨a,b,c,d⟩ saved tape 6) =
      some ⟨state heap ⟨a,b,c,d⟩ (add::saved) tape (additionLabel 114),[],0⟩ := rfl
  have move : tickNatural program (state mid ⟨sum,b,c,d⟩ saved tape 7) =
      some ⟨state mid ⟨sum,c,c,d⟩ saved tape 9,[],0⟩ := rfl
  have call : tickNatural program (state mid ⟨sum,c,c,d⟩ saved tape 9) =
      some ⟨state mid ⟨sum,c,c,d⟩ (cmp::saved) tape (comparisonLabel 30),[],0⟩ := rfl
  let bit := !(lessEqual (addCanonical distance weight).1 level).1
  let last := (mid++extra).length
  have done := finish (r := ⟨sum,c,c,flag⟩) hflag caller stack tape
  refine ⟨ext++extra++[.flag bit],last,?_,?_⟩
  · rw [← List.append_assoc heap, ← List.append_assoc heap ext extra]
    change ((mid++extra) ++ [.flag bit])[(mid++extra).length]? = some (.flag bit)
    simp
  · have trace := NaturalRun.step first (join hadd (NaturalRun.step move (NaturalRun.step call (join hcmp done))))
    convert trace using 1 <;> first | rfl | omega | simp only [last,mid,bit,List.append_assoc]

theorem cell_subroutine {heap : NaturalHeap} {r : Registers ℕ} {path : Option GraphWalkExtension.Walk}
    {weight level : Bits} (hd : GraphDiscoveryProgram.StoredOption heap r.a path)
    (hw : BoolList heap r.b weight) (hj : BoolList heap r.c level)
    (caller : Frame ℕ 186) (stack : List (Frame ℕ 186)) (tape : Bits) :
    ∃ ext root, (heap++ext)[root]? = some
        (.flag (IntegerLevelCuts.cellTest (IntegerDistanceFromPhysical.interpret path) (value weight) (value level)).1) ∧
      NaturalRun program (instructions path weight level)
        (state heap r (caller::stack) tape 0) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let saved := caller::stack
  cases path with
  | none =>
    let result := heap.length
    let more : NaturalHeap := [.flag false]
    have start : tickNatural program (state heap r saved tape 0) =
        some ⟨state heap r saved tape 1,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,GraphRelaxationProgram.StoredOption] at hd ⊢
      rw [hd]
    have alloc : tickNatural program (state heap r saved tape 1) =
        some ⟨state (heap++more) (r.set .r3 result) saved tape 21,[],0⟩ := by
      simp [result,more,tickNatural,program,state,allocateNatural,Recipe.cell]
    have ret : tickNatural program (state (heap++more) (r.set .r3 result) saved tape 21) =
        some ⟨state (heap++more) (caller.saved.set caller.destination result)
          stack tape caller.continuation,[],0⟩ := by
      cases r
      simp [saved,tickNatural,program,state,Registers.get,Registers.set]
    refine ⟨more,result,?_,.step start (.step alloc (.step ret (.done _)))⟩
    simp [more,result,IntegerLevelCuts.cellTest,IntegerDistanceFromPhysical.interpret]
  | some q =>
    obtain ⟨edges,cost,hpath,_,num,den,hcost,hnum,_⟩ := hd
    let pair := r.set .r0 cost
    let args := r.set .r0 num
    let firstFrame : Frame ℕ 186 := ⟨5,.r3,args⟩
    have start : tickNatural program (state heap r saved tape 0) =
        some ⟨state heap r saved tape 2,[],0⟩ := by
      simp [tickNatural,program,state,Registers.get,tagBranch,hpath]
    have field1 : tickNatural program (state heap r saved tape 2) =
        some ⟨state heap pair saved tape 3,[],0⟩ := by
      simp [pair,tickNatural,program,state,Registers.get,hpath]
    have field2 : tickNatural program (state heap pair saved tape 3) =
        some ⟨state heap args saved tape 4,[],0⟩ := by
      cases r
      simp [pair,args,tickNatural,program,state,Registers.get,Registers.set,hcost]
    have call : tickNatural program (state heap args saved tape 4) =
        some ⟨state heap args (firstFrame::saved) tape 13,[],0⟩ := rfl
    obtain ⟨ext,flag,hflag,hcmp⟩ := lower_return hnum hj saved tape
      (b := r.b) (d := r.d)
    let mid := heap++ext
    let tested : Registers ℕ := ⟨num,r.b,r.c,flag⟩
    have testedRun : NaturalRun program (BinaryComparisonProgram.steps q.cost.num level + 11)
        (state heap r saved tape 0) [] (state mid tested saved tape 5) := by
      cases r
      simpa [args,firstFrame,tested,mid,Registers.set,Nat.add_assoc] using
        NaturalRun.step start (NaturalRun.step field1 (NaturalRun.step field2 (NaturalRun.step call hcmp)))
    have meaning : within q.cost.num weight level =
        (IntegerLevelCuts.cellTest (IntegerDistanceFromPhysical.interpret (some q)) (value weight) (value level)).1 :=
      within_eq q.cost.num weight level
    cases hlow : lower q.cost.num level with
    | false =>
      have branch : tickNatural program (state mid tested saved tape 5) =
          some ⟨state mid tested saved tape 21,[],0⟩ := by
        simp [tickNatural,program,state,tested,mid,Registers.get,tagBranch,hflag,hlow]
      have ret : tickNatural program (state mid tested saved tape 21) =
          some ⟨state mid (caller.saved.set caller.destination flag) stack tape caller.continuation,[],0⟩ := rfl
      refine ⟨ext,flag,?_,?_⟩
      · rw [← meaning,within,hlow]
        simpa [hlow] using hflag
      · simpa [instructions,hlow,mid,Nat.add_assoc] using join testedRun (.step branch (.step ret (.done _)))
    | true =>
      have branch : tickNatural program (state mid tested saved tape 5) =
          some ⟨state mid tested saved tape 6,[],0⟩ := by
        simp [tickNatural,program,state,tested,mid,Registers.get,tagBranch,hflag,hlow]
      obtain ⟨extra,answer,hanswer,hupper⟩ := upper_return
        (boolList_extend hnum ext) (boolList_extend hw ext) (boolList_extend hj ext) caller stack tape (d := flag)
      refine ⟨ext++extra,answer,?_,?_⟩
      · rw [← meaning,within,hlow]
        simpa [List.append_assoc] using hanswer
      · have trace := join testedRun (.step branch hupper)
        simp only [instructions,hlow,ite_true]
        convert trace using 1 <;> first | rfl | omega | simp only [List.append_assoc]

def instructionBound (B : ℕ) : ℕ :=
  25 + 16*(2*B+1) + 200*(2*B+2)^2 + 16*(2*B+2)

theorem instructions_le (path : Option GraphWalkExtension.Walk) (weight level : Bits) (B : ℕ)
    (hd : ∀ q ∈ path, q.cost.num.length ≤ B) (hw : weight.length ≤ B) (hj : level.length ≤ B) :
    instructions path weight level + 1 ≤ instructionBound B := by
  cases path with
  | none => simp only [instructions,instructionBound]; omega
  | some q =>
    let ds := q.cost.num
    have hds : ds.length ≤ B := hd q (by simp)
    have hsum : (addCanonical ds weight).1.length ≤ B+1 :=
      ((trim_spec _).2.2.1.trans (add_spec false ds weight).2.1).trans
        (Nat.add_le_add_right (max_le hds hw) 1)
    have hsize : ds.length+weight.length+2 ≤ 2*B+2 := by omega
    have add := (CanonicalArithmeticProgram.instructions_bound false ds weight).trans
      (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left hsize 2))
    have lowerCost := BinaryComparisonProgram.steps_bound ds level
    have upperCost := BinaryComparisonProgram.steps_bound (addCanonical ds weight).1 level
    unfold instructionBound
    change BinaryComparisonProgram.steps ds level +
      (if lower ds level then 23 + CanonicalArithmeticProgram.instructions false ds weight +
        BinaryComparisonProgram.steps (addCanonical ds weight).1 level else 13) + 1 ≤ _
    split <;> omega

theorem natural_cell {heap : NaturalHeap} {r : Registers ℕ} {path : Option GraphWalkExtension.Walk}
    {weight level : Bits} (hd : GraphDiscoveryProgram.StoredOption heap r.a path)
    (hw : BoolList heap r.b weight) (hj : BoolList heap r.c level) (tape : Bits) :
    ∃ ext root, (heap++ext)[root]? = some
        (.flag (IntegerLevelCuts.cellTest (IntegerDistanceFromPhysical.interpret path) (value weight) (value level)).1) ∧
      NaturalRun program (instructions path weight level + 1)
        (state heap r [] tape 19) [] (state (heap++ext) (r.set .r3 root) [] tape 20) := by
  let frame : Frame ℕ 186 := ⟨20,.r3,r⟩
  obtain ⟨ext,root,hflag,hrun⟩ := cell_subroutine hd hw hj frame [] tape
  have call : tickNatural program (state heap r [] tape 19) = some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,hflag,.step call hrun⟩

private theorem at_entry (s : NaturalState 186) (hp : s.pc=19) (hc : s.stack=[])
    (hd : s.next=s.heap.length) : s = state s.heap s.registers [] s.source 19 := by
  cases s
  simp_all [state]

theorem physical_cell {d : WithTop ℕ} {weight level : Bits} {H A : ℕ} (initial : BitState 186)
    (hs : initial.Bounded H A) (hp : initial.pc=19) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (hd : IntegerDistanceFromPhysical.StoredDistance (eraseState initial).heap (eraseState initial).registers.a d)
    (hw : BoolList (eraseState initial).heap (eraseState initial).registers.b weight)
    (hj : BoolList (eraseState initial).heap (eraseState initial).registers.c level) :
    ∃ k charge out, Run program k charge initial [] out ∧
      (eraseState out).heap[(eraseState out).registers.d]? =
        some (.flag (IntegerLevelCuts.cellTest d (value weight) (value level)).1) ∧
      out.source = initial.source ∧ (eraseState out).stack = [] ∧ (eraseState out).pc = 20 ∧
      (∃ ext, (eraseState out).heap = (eraseState initial).heap++ext) ∧
      (attempt program out).result = none ∧
      charge + (attempt program out).operations ≤ completeBound 186 H A (instructionBound H) := by
  let input := eraseState initial
  obtain ⟨path,hpath,hvalue,_⟩ := hd
  obtain ⟨ext,root,hflag,htrace⟩ := natural_cell hpath hw hj input.source
  have hnil : input.stack = [] := by simp [input,eraseState,State.map,hc]
  let final := state (input.heap++ext) (input.registers.set .r3 root) [] input.source 20
  have hrun : NaturalRun program (instructions path weight level + 1) input [] final := by
    rw [at_entry input hp hnil hn]
    exact htrace
  have halt : tickNatural program final = none := rfl
  obtain ⟨charge,out,hactual,hout,hstop,hcharge,htape⟩ := terminating_simulation hs hrun halt
  refine ⟨_,charge,out,hactual,?_,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout,← hvalue]
    exact hflag
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have size : input.heap.length ≤ H := by simpa [input,eraseState,State.map,eraseHeap] using ((show initial.heap.length ≤ initial.records by simp only [State.records]; omega).trans hs.1)
    have width {p : ℕ} {bits : Bits} (rep : BoolList input.heap p bits) : bits.length ≤ H :=
      (PhysicalCoverReader.spine_short (boolList_spine rep)).le.trans size
    have hpw (q : GraphWalkExtension.Walk) (hq : q ∈ path) : q.cost.num.length ≤ H := by
      cases path with
      | none => simp at hq
      | some p =>
        have eq : p = q := by simpa using hq
        subst q
        obtain ⟨_,_,_,_,num,_,_,hnum,_⟩ := hpath
        exact width hnum
    have hk := instructions_le path weight level H hpw (width hw) (width hj)
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.IntegerCellTestProgram
