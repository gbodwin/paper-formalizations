import DirectedFlowCutGap.CandidateRemainingCountProgram
import DirectedFlowCutGap.BinaryMultiplicationProgram
import DirectedFlowCutGap.BinaryTrimProgram

/-!
# Physical closure budget from the removal mask

The fixed program counts unremoved vertices, multiplies by the supplied
grid size, doubles the product, and trims redundant high zero bits.
It returns the exact binary budget consumed by the candidate solver.
-/

namespace DirectedFlowCutGap.CandidateBudgetProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open CandidateRemainingCountProgram (word)

def countLabel (pc : Fin 32) : Fin 157 := if pc.val=15 then 1 else ⟨16+pc.val,by omega⟩
def mulLabel (pc : Fin 96) : Fin 157 := if pc.val=95 then 2 else ⟨48+pc.val,by omega⟩
def trimLabel (pc : Fin 13) : Fin 157 := if pc.val=12 then 5 else ⟨144+pc.val,by omega⟩

def program : Program 157 := fun pc =>
  if pc.val<16 then
    match pc.val with
    | 0 => .call (countLabel 0) 1 .r0
    | 1 => .call (mulLabel 64) 2 .r3
    | 2 => .make .r2 (.flag false) 3
    | 3 => .make .r0 (.pair .r2 .r3) 4
    | 4 => .call (trimLabel 0) 5 .r3
    | _ => .halt
  else if h : pc.val<48 then ReferenceProgramLabels.instruction countLabel
    (CandidateRemainingCountProgram.program ⟨pc.val-16,by omega⟩)
  else if h : pc.val<144 then ReferenceProgramLabels.instruction mulLabel
    (BinaryMultiplicationProgram.program ⟨pc.val-48,by omega⟩)
  else ReferenceProgramLabels.instruction trimLabel
    (BinaryTrimProgram.program ⟨pc.val-144,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 157))
    (tape : Bits) (pc : Fin 157) : NaturalState 157 :=
  ⟨heap,heap.length,r,stack,pc,tape⟩

def result (flags grid : Bits) : Bits := (trim (false::(mul (word flags) grid).1)).1

def steps (flags grid : Bits) : ℕ :=
  CandidateRemainingCountProgram.steps flags+BinaryMultiplicationProgram.steps (word flags) grid+
    BinaryTrimProgram.steps (false::(mul (word flags) grid).1)+5

theorem result_eq (flags grid : Bits) :
    result flags grid=(2*value grid*CandidateBudgetData.remaining flags).bits := by
  have spec := trim_spec (false::(mul (word flags) grid).1)
  have numeric : value (result flags grid)=2*value grid*CandidateBudgetData.remaining flags := by
    rw [result,spec.2.1]
    simp only [value,Bool.toNat_false,zero_add,(mul_spec (word flags) grid).1,
      CandidateRemainingCountProgram.word_value]
    ring
  rw [← numeric]
  exact (normal_bits spec.1).symm

private theorem count_slots (pc : Fin 32) (h : CandidateRemainingCountProgram.program pc≠.halt) :
    program (countLabel pc) = ReferenceProgramLabels.instruction countLabel (CandidateRemainingCountProgram.program pc) := by
  by_cases hp : pc.val=15
  · have eq : pc=15 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,countLabel,hp,show ¬16+pc.val<16 by omega,show 16+pc.val<48 by omega]

private theorem mul_slots (pc : Fin 96) (h : BinaryMultiplicationProgram.program pc≠.halt) :
    program (mulLabel pc) = ReferenceProgramLabels.instruction mulLabel (BinaryMultiplicationProgram.program pc) := by
  by_cases hp : pc.val=95
  · have eq : pc=95 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,mulLabel,hp,show ¬48+pc.val<16 by omega,show ¬48+pc.val<48 by omega,
      show 48+pc.val<144 by omega]

private theorem trim_slots (pc : Fin 13) (h : BinaryTrimProgram.program pc≠.halt) :
    program (trimLabel pc) = ReferenceProgramLabels.instruction trimLabel (BinaryTrimProgram.program pc) := by
  by_cases hp : pc.val=12
  · have eq : pc=12 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,trimLabel,hp,show ¬144+pc.val<16 by omega,show ¬144+pc.val<48 by omega,
      show ¬144+pc.val<144 by omega]

private theorem join {s u v : NaturalState 157} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem count_call {heap : NaturalHeap} {r : Registers ℕ} {flags : Bits}
    (input : BoolList heap r.a flags) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (word flags) ∧
      NaturalRun program (CandidateRemainingCountProgram.steps flags+1) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r0 root) [] tape 1) := by
  let oldFrame : Frame ℕ 32 := ⟨15,.r0,r⟩
  obtain ⟨ext,root,rep,body⟩ := CandidateRemainingCountProgram.count_return input oldFrame [] tape
  let frame : Frame ℕ 157 := ⟨1,.r0,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=
      some ⟨state heap r [frame] tape (countLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run countLabel CandidateRemainingCountProgram.program program count_slots body
  have trace : NaturalRun program (CandidateRemainingCountProgram.steps flags)
      (state heap r [frame] tape (countLabel 0)) [] (state (heap++ext) (r.set .r0 root) [] tape 1) := by
    simpa [oldFrame,frame,state,CandidateRemainingCountProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,countLabel] using lift
  exact ⟨ext,root,rep,.step enter trace⟩

private theorem mul_call {heap : NaturalHeap} {r : Registers ℕ} {xs ys : Bits}
    (left : BoolList heap r.a xs) (right : BoolList heap r.b ys) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (mul xs ys).1 ∧
      NaturalRun program (BinaryMultiplicationProgram.steps xs ys+1) (state heap r [] tape 1) []
        (state (heap++ext) (r.set .r3 root) [] tape 2) := by
  obtain ⟨ext,root,len,body,rep⟩ := BinaryMultiplicationProgram.mul_return left right
    heap.length r.c r.d rfl r 95 [] tape
  let frame : Frame ℕ 157 := ⟨2,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 1)=
      some ⟨state heap r [frame] tape (mulLabel 64),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run mulLabel BinaryMultiplicationProgram.program program mul_slots body
  have trace : NaturalRun program (BinaryMultiplicationProgram.steps xs ys)
      (state heap r [frame] tape (mulLabel 64)) [] (state (heap++ext) (r.set .r3 root) [] tape 2) := by
    cases r
    simpa [frame,state,BinaryMultiplicationProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,mulLabel,Registers.set,len] using lift
  exact ⟨ext,root,rep,.step enter trace⟩

private theorem trim_call {heap : NaturalHeap} {r : Registers ℕ} {bs : Bits}
    (input : BoolList heap r.a bs) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (trim bs).1 ∧
      NaturalRun program (BinaryTrimProgram.steps bs+1) (state heap r [] tape 4) []
        (state (heap++ext) (r.set .r3 root) [] tape 5) := by
  obtain ⟨ext,root,_,body,rep⟩ := BinaryTrimProgram.trim_return input heap.length
    r.b r.c r.d rfl r 12 [] tape
  let frame : Frame ℕ 157 := ⟨5,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 4)=
      some ⟨state heap r [frame] tape (trimLabel 0),[],0⟩ := rfl
  have lift := ReferenceProgramLabels.run trimLabel BinaryTrimProgram.program program trim_slots body
  have trace : NaturalRun program (BinaryTrimProgram.steps bs)
      (state heap r [frame] tape (trimLabel 0)) [] (state (heap++ext) (r.set .r3 root) [] tape 5) := by
    cases r
    simpa [frame,state,BinaryTrimProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,trimLabel,Registers.set] using lift
  exact ⟨ext,root,rep,.step enter trace⟩

theorem natural_budget {heap : NaturalHeap} {r : Registers ℕ} {flags grid : Bits}
    (mask : BoolList heap r.a flags) (size : BoolList heap r.b grid) (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),BoolList (heap++ext) root (result flags grid) ∧
      NaturalRun program (steps flags grid) (state heap r [] tape 0) []
        (state (heap++ext) (args.set .r3 root) [] tape 5) := by
  obtain ⟨ec,count,words,countRun⟩ := count_call mask tape
  let mid := heap++ec
  let withCount := r.set .r0 count
  obtain ⟨em,product,computed,mulRun⟩ := mul_call (r:=withCount) words (boolList_extend size ec) tape
  let grown := mid++em
  let withProduct := withCount.set .r3 product
  let flag : Cell ℕ := .flag false
  let fresh := grown.length
  let cell : Cell ℕ := .pair fresh product
  let stage := grown++[flag]
  let expanded := grown++[flag,cell]
  let withFlag := withProduct.set .r2 fresh
  let args := withFlag.set .r0 (fresh+1)
  have makeFlag : tickNatural program (state grown withProduct [] tape 2)=
      some ⟨state stage withFlag [] tape 3,[],0⟩ := by
    simp [stage,flag,fresh,withFlag,state,program,tickNatural,allocateNatural,Recipe.cell]
  have makeWord : tickNatural program (state stage withFlag [] tape 3)=
      some ⟨state expanded args [] tape 4,[],0⟩ := by
    simp [stage,flag,fresh,expanded,cell,withFlag,withProduct,args,state,program,tickNatural,
      Registers.get,Registers.set,allocateNatural,Recipe.cell,Nat.add_assoc]
  have stored : BoolList expanded args.a (false::(mul (word flags) grid).1) := by
    apply BoolList.cons (head:=fresh) (tail:=product)
    · simp [expanded,args,fresh,cell,Registers.set]
    · simp [expanded,fresh,flag]
    · exact boolList_extend computed _
  obtain ⟨et,root,rep,trimRun⟩ := trim_call stored tape
  refine ⟨ec++em++[flag,cell]++et,args,root,?_,?_⟩
  · simpa only [result,expanded,grown,mid,List.append_assoc] using rep
  · have rest := NaturalRun.step makeFlag (.step makeWord trimRun)
    have trace := join countRun (join mulRun rest)
    simp only [steps]
    convert trace using 1 <;> first | rfl | omega | simp only [expanded,grown,mid,List.append_assoc]

def instructionBound (n P : ℕ) : ℕ :=
  n*(8*n+15)+4+64*(n+1)*(n+P+2)+(8*(2*n+P+2)+4)+2

theorem steps_le (flags grid : Bits) : steps flags grid ≤ instructionBound flags.length grid.length := by
  have count := CandidateRemainingCountProgram.steps_bound flags flags.length le_rfl
  have len := CandidateRemainingCountProgram.word_length flags
  have compute := BinaryMultiplicationProgram.steps_bound (word flags) grid
  have maxMul : 64*((word flags).length+1)*((word flags).length+grid.length+2) ≤
      64*(flags.length+1)*(flags.length+grid.length+2) := by gcongr
  have compute := compute.trans maxMul
  have trim := BinaryTrimProgram.steps_bound (false::(mul (word flags) grid).1)
  have mulSize := (mul_spec (word flags) grid).2.1
  simp only [List.length_cons] at trim
  unfold steps instructionBound
  omega

private theorem at_entry (s : NaturalState 157) (hp : s.pc=0) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s=state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem physical_budget {n H A : ℕ} (D : EncodedCandidateCapacity.Input n) (s t : Fin n) (L B : ℕ)
    (grid : Bits) (exactGrid : value grid=L)
    (initial : BitState 157) (bounded : initial.Bounded H A) (hp : initial.pc=0) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (mask : BoolList (eraseState initial).heap (eraseState initial).registers.a D.removed.toList)
    (size : BoolList (eraseState initial).heap (eraseState initial).registers.b grid) :
    ∃ charge out,Run program (steps D.removed.toList grid) charge initial [] out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (CandidatePhysicalCut.fuelWord D s t L B) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=5 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 157 H A (instructionBound n grid.length) := by
  let old := eraseState initial
  obtain ⟨ext,args,root,rep,body⟩ := natural_budget mask size old.source
  let final := state (old.heap++ext) (args.set .r3 root) [] old.source 5
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  have trace : NaturalRun program (steps D.removed.toList grid) old [] final := by
    rw [at_entry old hp empty hn]
    exact body
  have stop : tickNatural program final=none := rfl
  obtain ⟨charge,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace stop
  have exactWord : result D.removed.toList grid=CandidatePhysicalCut.fuelWord D s t L B := by
    rw [result_eq,exactGrid,CandidatePhysicalCut.fuelWord,CandidateBudgetData.budget_exact]
  have count := steps_le D.removed.toList grid
  rw [Vector.length_toList] at count
  refine ⟨charge,out,hr,?_,htape,?_,?_,⟨ext,?_⟩,hstop,
    hcharge.trans (SupportSearchEncoding.complete_mono _ _ _ _ _ count)⟩
  · rw [hout,← exactWord]
    exact rep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.CandidateBudgetProgram
