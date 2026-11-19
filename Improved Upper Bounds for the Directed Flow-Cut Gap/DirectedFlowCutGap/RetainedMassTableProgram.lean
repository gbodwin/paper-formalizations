import DirectedFlowCutGap.RetainedMassRowProgram
import DirectedFlowCutGap.EncodedRoundingState

/-!
# Integer mass across the retained pair table

For each active pair, the program executes the masked row sum and adds
that word to the total. The same cut mask is shared by all the row calls.
The inactive branch skips both calls.
-/

namespace DirectedFlowCutGap.RetainedMassTableProgram

open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open BinaryArithmetic PackedBooleanConstructor RetainedGridState
open PathCostMaterialization (WordList)

private def rowLabel (pc : Fin 134) : Fin 274 := ⟨24 + pc.val, by omega⟩
private def addLabel (pc : Fin 116) : Fin 274 := ⟨158 + pc.val, by omega⟩

private def callable {C : ℕ} (label : Fin C → Fin 274) : Instruction C → Instruction 274
  | .halt => .ret .r3
  | op => ReferenceProgramLabels.instruction label op

private theorem callable_eq {C : ℕ} (label : Fin C → Fin 274) (op : Instruction C) (h : op ≠ .halt) :
    callable label op = ReferenceProgramLabels.instruction label op := by
  cases op <;> simp_all [callable]

def program : Program 274 := fun pc =>
  if pc.val < 24 then
    match pc.val with
    | 0 => .call 1 23 .r3
    | 1 => .branch .r0 2 22 22 4
    | 2 => .make .r0 .nil 3
    | 3 => .ret .r0
    | 4 => .make .r3 (.pair .r0 .r1) 5
    | 5 => .field .r0 .r0 true 6
    | 6 => .field .r1 .r1 true 7
    | 7 => .call 1 8 .r0
    | 8 => .field .r1 .r3 false 9
    | 9 => .field .r1 .r1 false 10
    | 10 => .branch .r1 22 3 11 22
    | 11 => .field .r1 .r3 true 12
    | 12 => .field .r1 .r1 false 13
    | 13 => .move .r3 .r0 14
    | 14 => .move .r0 .r1 15
    | 15 => .move .r1 .r2 16
    | 16 => .call (rowLabel 0) 17 .r0
    | 17 => .move .r1 .r3 18
    | 18 => .call (addLabel 114) 3 .r0
    | _ => .halt
  else if h : pc.val < 158 then
    callable rowLabel (RetainedMassRowProgram.program ⟨pc.val - 24, by omega⟩)
  else
    callable addLabel (CanonicalArithmeticProgram.program ⟨pc.val - 158, by omega⟩)

private theorem row_slots (pc : Fin 134) (h : RetainedMassRowProgram.program pc ≠ .halt) :
    program (rowLabel pc) = ReferenceProgramLabels.instruction rowLabel (RetainedMassRowProgram.program pc) := by
  simpa [program,rowLabel,show ¬24+pc.val<24 by omega,show 24+pc.val<158 by omega] using
    callable_eq rowLabel (RetainedMassRowProgram.program pc) h

private theorem add_slots (pc : Fin 116) (h : CanonicalArithmeticProgram.program pc ≠ .halt) :
    program (addLabel pc) = ReferenceProgramLabels.instruction addLabel (CanonicalArithmeticProgram.program pc) := by
  simpa [program,addLabel,show ¬158+pc.val<24 by omega,show ¬158+pc.val<158 by omega] using
    callable_eq addLabel (CanonicalArithmeticProgram.program pc) h

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 274))
    (tape : Bits) (pc : Fin 274) : NaturalState 274 :=
  ⟨heap, heap.length, r, stack, pc, tape⟩

inductive TableAt (heap : NaturalHeap) : ℕ → List (List Bits) → Prop where
  | nil {root} : heap[root]? = some .nil → TableAt heap root []
  | cons {root head tail row rows} : heap[root]? = some (.pair head tail) →
      WordList heap head row → TableAt heap tail rows → TableAt heap root (row :: rows)

private theorem table_extend {heap : NaturalHeap} {root : ℕ} {rows : List (List Bits)}
    (h : TableAt heap root rows) (ext : NaturalHeap) :
    TableAt (heap ++ ext) root rows := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp ext)
  | cons hp hw _ ih => exact .cons (lookup_extend hp ext) (PathCostMaterialization.list_extend hw ext) ih

def sum (cut : Bits) : Bits → List (List Bits) → Bits
  | active :: flags, row :: rows =>
    if active then (addCanonical (RetainedMassRowProgram.sum row cut) (sum cut flags rows)).1
    else sum cut flags rows
  | _, _ => []

def steps (cut : Bits) : Bits → List (List Bits) → ℕ
  | active :: flags, row :: rows =>
    steps cut flags rows + if active then
      20 + RetainedMassRowProgram.steps row cut +
        CanonicalArithmeticProgram.instructions false (RetainedMassRowProgram.sum row cut) (sum cut flags rows)
      else 9
  | _, _ => 3

private theorem join {a b c : NaturalState 274} {m n : ℕ} {es fs : List Event}
    (h : NaturalRun program m a es b) (hg : NaturalRun program n b fs c) :
    NaturalRun program (m + n) a (es ++ fs) c := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem row_return {heap : NaturalHeap} {r : Registers ℕ} {xs : List Bits} {cut : Bits}
    (hw : WordList heap r.a xs) (hc : BoolList heap r.b cut) (hl : xs.length = cut.length)
    (caller : Frame ℕ 274) (stack : List (Frame ℕ 274)) (tape : Bits) :
    ∃ ext root, BoolList (heap ++ ext) root (RetainedMassRowProgram.sum xs cut) ∧
      NaturalRun program (RetainedMassRowProgram.steps xs cut + 2)
        (state heap r (caller :: stack) tape (rowLabel 0)) []
        (state (heap ++ ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  obtain ⟨ext, root, rep, run⟩ := RetainedMassRowProgram.natural_trace hw hc hl tape
  have lift := ReferenceProgramLabels.run rowLabel RetainedMassRowProgram.program program row_slots run
  have lift := ReferenceProgramStack.run program (caller :: stack) lift
  let returned := state (heap ++ ext) (r.set .r3 root) (caller :: stack) tape (rowLabel 17)
  let final := state (heap ++ ext) (caller.saved.set caller.destination root) stack tape caller.continuation
  have body : NaturalRun program (RetainedMassRowProgram.steps xs cut + 1)
      (state heap r (caller :: stack) tape (rowLabel 0)) [] returned := lift
  have ret : tickNatural program returned = some ⟨final,[],0⟩ := rfl
  exact ⟨ext,root,rep,join body (.step ret (.done final))⟩

private theorem add_return {heap : NaturalHeap} {r : Registers ℕ} {x y : Bits}
    (hx : BoolList heap r.a x) (hy : BoolList heap r.b y)
    (caller : Frame ℕ 274) (stack : List (Frame ℕ 274)) (tape : Bits) :
    ∃ ext root, BoolList (heap ++ ext) root (addCanonical x y).1 ∧
      NaturalRun program (CanonicalArithmeticProgram.instructions false x y + 1)
        (state heap r (caller :: stack) tape (addLabel 114)) []
        (state (heap ++ ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let base := CanonicalArithmeticProgram.state heap heap.length r.a r.b r.c r.d [] tape 114
  obtain ⟨ext,root,_,run,rep⟩ := CanonicalArithmeticProgram.canonical_high false base rfl rfl hx hy rfl
  have lift := ReferenceProgramLabels.run addLabel CanonicalArithmeticProgram.program program add_slots run
  have lift := ReferenceProgramStack.run program (caller :: stack) lift
  let retState := state (heap ++ ext) (r.set .r3 root) (caller :: stack) tape (addLabel 115)
  let final := state (heap ++ ext) (caller.saved.set caller.destination root) stack tape caller.continuation
  have body : NaturalRun program (CanonicalArithmeticProgram.instructions false x y)
      (state heap r (caller :: stack) tape (addLabel 114)) [] retState := by
    simpa [base,retState,state,ReferenceProgramLabels.state,ReferenceProgramStack.state,
      CanonicalArithmeticProgram.state,Registers.set] using lift
  have ret : tickNatural program retState = some ⟨final,[],0⟩ := by
    simp [tickNatural,retState,final,state,program,callable,addLabel,CanonicalArithmeticProgram.program,
      Registers.get,Registers.set]
  rw [CanonicalArithmeticProgram.result_exact false] at rep
  exact ⟨ext,root,rep,join body (.step ret (.done final))⟩

theorem sum_subroutine {heap : NaturalHeap} {a b c : ℕ} {active cut : Bits} {rows : List (List Bits)}
    (ha : BoolList heap a active) (hw : TableAt heap b rows) (hc : BoolList heap c cut)
    (hlen : active.length = rows.length) (aligned : ∀ row ∈ rows, row.length = cut.length)
    (d : ℕ) (caller : Frame ℕ 274) (stack : List (Frame ℕ 274)) (tape : Bits) :
    ∃ ext root, BoolList (heap ++ ext) root (sum cut active rows) ∧
      NaturalRun program (steps cut active rows)
        (state heap ⟨a,b,c,d⟩ (caller :: stack) tape 1) []
        (state (heap ++ ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction rows generalizing heap a b active d caller stack with
  | nil =>
    have he : active = [] := List.length_eq_zero_iff.mp hlen
    subst active
    cases ha with
    | nil hp =>
      let saved := caller :: stack
      let init : Registers ℕ := ⟨a,b,c,d⟩
      let fresh := heap.length
      let grown := heap ++ [.nil]
      let s1 := state heap init saved tape 1
      let s2 := state heap init saved tape 2
      let s3 := state grown ⟨fresh,b,c,d⟩ saved tape 3
      let final := state grown (caller.saved.set caller.destination fresh) stack tape caller.continuation
      have h1 : tickNatural program s1 = some ⟨s2,[],0⟩ := by
        simp [s1,s2,init,tickNatural,program,state,Registers.get,tagBranch,hp]
      have h2 : tickNatural program s2 = some ⟨s3,[],0⟩ := by
        simp [s2,s3,init,grown,fresh,tickNatural,program,state,Registers.set,allocateNatural,Recipe.cell]
      have h3 : tickNatural program s3 = some ⟨final,[],0⟩ := by
        simp [s3,final,saved,tickNatural,program,state,Registers.get]
      exact ⟨[.nil],fresh,.nil (by simp [fresh]),.step h1 (.step h2 (.step h3 (.done final)))⟩
  | cons x xs ih =>
    cases ha with
    | nil => simp at hlen
    | @cons a ah atail useRow flags haf hflag htail =>
      obtain ⟨bh, bt, hp, hx, htable⟩ := show ∃ (head tail : ℕ),
          heap[b]? = some (.pair head tail) ∧ WordList heap head x ∧ TableAt heap tail xs from by
        cases hw with
        | @cons root head tail row rows hp hx htable => exact ⟨head, tail, hp, hx, htable⟩
      let saved := caller :: stack
      let r : Registers ℕ := ⟨a,b,c,d⟩
      let context : Cell ℕ := .pair a b
      let contextRoot := heap.length
      let start := state heap r saved tape 1
      let s4 := state heap r saved tape 4
      let initialHeap := heap ++ [context]
      let s5 := state initialHeap ⟨a,b,c,contextRoot⟩ saved tape 5
      let s6 := state initialHeap ⟨atail,b,c,contextRoot⟩ saved tape 6
      let callRegs : Registers ℕ := ⟨atail,bt,c,contextRoot⟩
      let s7 := state initialHeap callRegs saved tape 7
      let frame : Frame ℕ 274 := ⟨8,.r0,callRegs⟩
      have h1 : tickNatural program start = some ⟨s4,[],0⟩ := by
        simp [start,s4,r,tickNatural,program,state,Registers.get,tagBranch,haf]
      have h4 : tickNatural program s4 = some ⟨s5,[],0⟩ := by
        simp [s4,s5,r,context,contextRoot,initialHeap,tickNatural,program,state,
          Registers.get,Registers.set,allocateNatural,Recipe.cell]
      have h5 : tickNatural program s5 = some ⟨s6,[],0⟩ := by
        have hold : initialHeap[a]? = some (.pair ah atail) := lookup_extend haf _
        simp [s5,s6,tickNatural,program,state,Registers.get,Registers.set,hold]
      have h6 : tickNatural program s6 = some ⟨s7,[],0⟩ := by
        have hold : initialHeap[b]? = some (.pair bh bt) := lookup_extend hp _
        simp [s6,s7,callRegs,tickNatural,program,state,Registers.get,Registers.set,hold]
      have h7 : tickNatural program s7 = some ⟨state initialHeap callRegs (frame :: saved) tape 1,[],0⟩ := rfl
      have hl' : flags.length = xs.length := Nat.succ.inj hlen
      have ha' : ∀ y ∈ xs, y.length = cut.length := fun y hy => aligned y (List.mem_cons_of_mem _ hy)
      have hcut : BoolList initialHeap c cut := boolList_extend hc [context]
      obtain ⟨tailCells, tail, htotal, hrun⟩ := ih (boolList_extend htail [context])
        (table_extend htable [context]) hcut hl' ha' contextRoot frame saved
      let grown := initialHeap ++ tailCells
      let s8 := state grown ⟨tail,bt,c,contextRoot⟩ saved tape 8
      change NaturalRun program (steps cut flags xs)
        (state initialHeap callRegs (frame :: saved) tape 1) [] s8 at hrun
      have headRun : NaturalRun program (steps cut flags xs + 5) start [] s8 :=
        .step h1 (.step h4 (.step h5 (.step h6 (.step h7 hrun))))
      have keptContext : grown[contextRoot]? = some (.pair a b) :=
        lookup_extend (by simp [initialHeap, contextRoot, context]) tailCells
      have keptFlags : grown[a]? = some (.pair ah atail) := lookup_extend (lookup_extend haf [context]) tailCells
      have keptHead : grown[ah]? = some (.flag useRow) := lookup_extend (lookup_extend hflag [context]) tailCells
      let s9 := state grown ⟨tail,a,c,contextRoot⟩ saved tape 9
      let s10 := state grown ⟨tail,ah,c,contextRoot⟩ saved tape 10
      have h8 : tickNatural program s8 = some ⟨s9,[],0⟩ := by
        simp [s8,s9,tickNatural,program,state,Registers.get,Registers.set,keptContext]
      have h9 : tickNatural program s9 = some ⟨s10,[],0⟩ := by
        simp [s9,s10,tickNatural,program,state,Registers.get,Registers.set,keptFlags]
      cases useRow with
      | false =>
        let s3 := state grown ⟨tail,ah,c,contextRoot⟩ saved tape 3
        let final := state grown (caller.saved.set caller.destination tail) stack tape caller.continuation
        have h10 : tickNatural program s10 = some ⟨s3,[],0⟩ := by
          simp [s10,s3,tickNatural,program,state,Registers.get,tagBranch,keptHead]
        have h3 : tickNatural program s3 = some ⟨final,[],0⟩ := by
          simp [s3,final,saved,tickNatural,program,state,Registers.get]
        have suffix : NaturalRun program 4 s8 [] final := .step h8 (.step h9 (.step h10 (.step h3 (.done final))))
        refine ⟨[context] ++ tailCells,tail,?_ ,?_⟩
        · simpa only [sum,Bool.false_eq_true,ite_false,grown,initialHeap,List.append_assoc] using htotal
        · simpa only [steps,Bool.false_eq_true,ite_false,start,final,grown,initialHeap,r,saved,
            List.append_assoc,List.nil_append,Nat.add_assoc]
            using join headRun suffix
      | true =>
        let s11 := state grown ⟨tail,ah,c,contextRoot⟩ saved tape 11
        let s12 := state grown ⟨tail,b,c,contextRoot⟩ saved tape 12
        let s13 := state grown ⟨tail,bh,c,contextRoot⟩ saved tape 13
        let s14 := state grown ⟨tail,bh,c,tail⟩ saved tape 14
        let s15 := state grown ⟨bh,bh,c,tail⟩ saved tape 15
        let rowRegs : Registers ℕ := ⟨bh,c,c,tail⟩
        let s16 := state grown rowRegs saved tape 16
        let rowFrame : Frame ℕ 274 := ⟨17,.r0,rowRegs⟩
        let rowStart := state grown rowRegs (rowFrame :: saved) tape (rowLabel 0)
        have h10 : tickNatural program s10 = some ⟨s11,[],0⟩ := by
          simp [s10,s11,tickNatural,program,state,Registers.get,tagBranch,keptHead]
        have h11 : tickNatural program s11 = some ⟨s12,[],0⟩ := by
          simp [s11,s12,tickNatural,program,state,Registers.get,Registers.set,keptContext]
        have h12 : tickNatural program s12 = some ⟨s13,[],0⟩ := by
          have keptRows : grown[b]? = some (.pair bh bt) := lookup_extend (lookup_extend hp [context]) tailCells
          simp [s12,s13,tickNatural,program,state,Registers.get,Registers.set,keptRows]
        have h13 : tickNatural program s13 = some ⟨s14,[],0⟩ := rfl
        have h14 : tickNatural program s14 = some ⟨s15,[],0⟩ := rfl
        have h15 : tickNatural program s15 = some ⟨s16,[],0⟩ := rfl
        have h16 : tickNatural program s16 = some ⟨rowStart,[],0⟩ := rfl
        obtain ⟨rowCells, rowRoot, hRow, rowRun⟩ :=
          row_return (r := rowRegs) (PathCostMaterialization.list_extend (PathCostMaterialization.list_extend hx [context]) tailCells)
            (boolList_extend hcut tailCells) (aligned x List.mem_cons_self) rowFrame saved tape
        let afterRow := grown ++ rowCells
        let s17 := state afterRow ⟨rowRoot,c,c,tail⟩ saved tape 17
        change NaturalRun program (RetainedMassRowProgram.steps x cut + 2) rowStart [] s17 at rowRun
        let addRegs : Registers ℕ := ⟨rowRoot,tail,c,tail⟩
        let s18 := state afterRow addRegs saved tape 18
        let addFrame : Frame ℕ 274 := ⟨3,.r0,addRegs⟩
        let addStart := state afterRow addRegs (addFrame :: saved) tape (addLabel 114)
        have h17 : tickNatural program s17 = some ⟨s18,[],0⟩ := rfl
        have h18 : tickNatural program s18 = some ⟨addStart,[],0⟩ := rfl
        obtain ⟨addCells, root, hrep, addRun⟩ :=
          add_return (r := addRegs) hRow (boolList_extend htotal rowCells) addFrame saved tape
        let finalHeap := afterRow ++ addCells
        let s3 := state finalHeap ⟨root,tail,c,tail⟩ saved tape 3
        let final := state finalHeap (caller.saved.set caller.destination root) stack tape caller.continuation
        let addition := CanonicalArithmeticProgram.instructions false (RetainedMassRowProgram.sum x cut) (sum cut flags xs)
        change NaturalRun program (addition+1) addStart [] s3 at addRun
        have h3 : tickNatural program s3 = some ⟨final,[],0⟩ := by
          simp [s3,final,saved,tickNatural,program,state,Registers.get]
        have addSuffix := NaturalRun.step h17 (.step h18 (join addRun (.step h3 (.done final))))
        have rowSuffix := NaturalRun.step h8 (.step h9 (.step h10 (.step h11 (.step h12
          (.step h13 (.step h14 (.step h15 (.step h16 (join rowRun addSuffix)))))))))
        have full := join headRun rowSuffix
        let allCells := [context] ++ tailCells ++ rowCells ++ addCells
        let count := steps cut flags xs + 5 + (RetainedMassRowProgram.steps x cut + 2 +
          (addition+1+(0+1)+1+1)+1+1+1+1+1+1+1+1+1)
        change NaturalRun program count start [] final at full
        have he : count = steps cut (true :: flags) (x :: xs) := by simp only [count,steps,ite_true,addition]; omega
        rw [he] at full
        refine ⟨allCells,root,?_,?_⟩
        · simpa only [sum,ite_true,allCells,finalHeap,afterRow,grown,initialHeap,List.append_assoc] using hrep
        · simpa only [start,r,allCells,final,finalHeap,afterRow,grown,initialHeap,List.append_assoc] using full

def pairOrder (n : ℕ) : List (Pair n) := (List.finRange n).product (List.finRange n)

theorem pairOrder_length (n : ℕ) : (pairOrder n).length = n*n := by
  exact (List.length_product (List.finRange n) (List.finRange n)).trans (by simp)

def DataRows {n : ℕ} (counts : Family n) (words : List (List Bits)) : Prop :=
  List.Forall₂ (fun xs p => xs.map value = (row counts p).toList) words (pairOrder n)

private theorem sum_value_on {n : ℕ} (counts : Family n) (active : PairFlags n) (cut : Flags n)
    {words : List (List Bits)} {pairs : List (Pair n)}
    (h : List.Forall₂ (fun xs p => xs.map value = (row counts p).toList) words pairs) :
    value (sum cut.toList (pairs.map (flag active)) words) =
      (pairs.map (fun p => if flag active p then ∑ v : Fin n, if cut[v.val] then 0 else (row counts p)[v.val]
        else 0)).sum := by
  induction h with
  | nil => rfl
  | @cons xs p words pairs hx _ ih =>
    by_cases hp : flag active p = true
    · simp only [List.map_cons, sum, hp, ite_true, List.sum_cons, (canonical_values _ _).1, ih,
        RetainedMassRowProgram.row_value _ _ _ hx]
    · simp only [List.map_cons, sum, hp, Bool.false_eq_true, ite_false, List.sum_cons, Nat.zero_add, ih]

theorem mass_value {n : ℕ} (counts : Family n) (active : PairFlags n) (cut : Flags n)
    {words : List (List Bits)} (hw : DataRows counts words) :
    value (sum cut.toList ((pairOrder n).map (flag active)) words) = (EncodedRoundingState.mass active cut counts).1 := by
  have hn : (pairOrder n).Nodup := (List.nodup_finRange _).product (List.nodup_finRange _)
  have hu : (pairOrder n).toFinset = (Finset.univ : Finset (Pair n)) := by
    ext p
    rcases p with ⟨a,b⟩
    simp [pairOrder]
  rw [sum_value_on counts active cut hw, ← List.sum_toFinset _ hn, hu, EncodedRoundingState.mass_value]
  simp only [massNumerator, remainingSet, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  split
  · apply Finset.sum_congr rfl
    intro i _
    cases cut[i.val] <;> simp
  · rfl

private theorem rows_width (rows : List (List Bits)) (active cut : Bits) (B : ℕ)
    (halign : ∀ x ∈ rows, x.length = cut.length)
    (hwidth : ∀ x ∈ rows, ∀ w ∈ x, w.length ≤ B) :
    (sum cut active rows).length ≤ B + cut.length + rows.length := by
  induction rows generalizing active with
  | nil => cases active <;> simp [sum]
  | cons x xs ih =>
    cases active with
    | nil => simp [sum]
    | cons bit rest =>
      have hr := RetainedMassRowProgram.result_width x cut B (hwidth x List.mem_cons_self)
      rw [halign x List.mem_cons_self] at hr
      have ht := ih rest (fun y hy => halign y (List.mem_cons_of_mem _ hy))
        (fun y hy => hwidth y (List.mem_cons_of_mem _ hy))
      have ha := (trim_spec (add false (RetainedMassRowProgram.sum x cut) (sum cut rest xs)).1).2.2.1.trans
        (add_spec false (RetainedMassRowProgram.sum x cut) (sum cut rest xs)).2.1
      change (addCanonical (RetainedMassRowProgram.sum x cut) (sum cut rest xs)).1.length ≤ _ at ha
      have hm := max_le (hr.trans (Nat.le_add_right _ _)) ht
      simp only [sum, List.length_cons]
      split <;> omega

def iterationBudget (r n B : ℕ) : ℕ :=
  20 + RetainedMassRowProgram.instructionBudget n B + 200 * (2*(B+n)+r+2)^2

def instructionBudget (r n B : ℕ) : ℕ := r * iterationBudget r n B + 4

private theorem steps_bound_of (rows : List (List Bits)) (active cut : Bits) (B N : ℕ)
    (hN : rows.length ≤ N) (halign : ∀ x ∈ rows, x.length = cut.length)
    (hwidth : ∀ x ∈ rows, ∀ w ∈ x, w.length ≤ B) :
    steps cut active rows ≤ rows.length * iterationBudget N cut.length B + 3 := by
  induction rows generalizing active with
  | nil => cases active <;> simp [steps]
  | cons x xs ih =>
    cases active with
    | nil => simp [steps]
    | cons b rest =>
      have hsub : xs.length ≤ N := by simp only [List.length_cons] at hN; omega
      have hl : ∀ y ∈ xs, y.length = cut.length := fun y hy => halign y (List.mem_cons_of_mem _ hy)
      have hw : ∀ y ∈ xs, ∀ w ∈ y, w.length ≤ B := fun y hy => hwidth y (List.mem_cons_of_mem _ hy)
      have ht := ih rest hsub hl hw
      have htWidth := rows_width xs rest cut B hl hw
      have hx := RetainedMassRowProgram.result_width x cut B (hwidth x List.mem_cons_self)
      have hs := RetainedMassRowProgram.steps_le x cut B (hwidth x List.mem_cons_self)
      rw [halign x List.mem_cons_self] at hx hs
      have hh : (RetainedMassRowProgram.sum x cut).length + (sum cut rest xs).length + 2 ≤
          2 * (B + cut.length) + N + 2 := by omega
      have addCost := (CanonicalArithmeticProgram.instructions_bound false
        (RetainedMassRowProgram.sum x cut) (sum cut rest xs)).trans
        (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left hh 2))
      simp only [steps, List.length_cons, Nat.add_mul, Nat.one_mul, iterationBudget] at ht ⊢
      split <;> omega

theorem steps_le (rows : List (List Bits)) (active cut : Bits) (B : ℕ)
    (halign : ∀ x ∈ rows, x.length = cut.length) (hwidth : ∀ x ∈ rows, ∀ w ∈ x, w.length ≤ B) :
    steps cut active rows + 1 ≤ instructionBudget rows.length cut.length B := by
  simpa only [instructionBudget, Nat.add_assoc] using
    Nat.add_le_add_right (steps_bound_of rows active cut B rows.length le_rfl halign hwidth) 1

theorem natural_trace {heap : NaturalHeap} {r : Registers ℕ} {active cut : Bits} {rows : List (List Bits)}
    (ha : BoolList heap r.a active) (hw : TableAt heap r.b rows) (hc : BoolList heap r.c cut)
    (hl : active.length = rows.length) (halign : ∀ x ∈ rows, x.length = cut.length) (tape : Bits) :
    ∃ ext root, BoolList (heap ++ ext) root (sum cut active rows) ∧
      NaturalRun program (steps cut active rows + 1) (state heap r [] tape 0) []
        (state (heap ++ ext) (r.set .r3 root) [] tape 23) := by
  let caller : Frame ℕ 274 := ⟨23,.r3,r⟩
  obtain ⟨ext,root,hrep,hrun⟩ := sum_subroutine ha hw hc hl halign r.d caller [] tape
  have he : tickNatural program (state heap r [] tape 0) = some ⟨state heap r [caller] tape 1,[],0⟩ := rfl
  exact ⟨ext,root,hrep,.step he hrun⟩

theorem data_length {n : ℕ} {counts : Family n} {words : List (List Bits)}
    (hw : DataRows counts words) : words.length = n*n := by
  exact hw.length_eq.trans (pairOrder_length n)

theorem data_aligned {n : ℕ} {counts : Family n} {words : List (List Bits)}
    (hw : DataRows counts words) : ∀ x ∈ words, x.length = n := by
  have aligned {xs : List (List Bits)} {ps : List (Pair n)}
      (h : List.Forall₂ (fun x p => x.map value = (row counts p).toList) xs ps) :
      ∀ x ∈ xs, x.length = n := by
    induction h with
    | nil => simp
    | cons h _ ih =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · simpa only [List.length_map, Vector.length_toList] using congrArg List.length h
      · exact ih y hy
  exact aligned hw

private theorem at_entry (s : NaturalState 274) (hp : s.pc=0) (hc : s.stack=[])
    (hd : s.next=s.heap.length) : s = state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem retained_mass {n H A B : ℕ} {initial : BitState 274} (counts : Family n)
    (active : PairFlags n) (cut : Flags n) (words : List (List Bits))
    (hdata : DataRows counts words) (hwidth : ∀ x ∈ words, ∀ w ∈ x, w.length ≤ B)
    (hs : initial.Bounded H A) (hp : initial.pc = 0) (hstack : initial.stack = [])
    (hd : (eraseState initial).next=(eraseState initial).heap.length)
    (ha : BoolList (eraseState initial).heap (eraseState initial).registers.a ((pairOrder n).map (flag active)))
    (hw : TableAt (eraseState initial).heap (eraseState initial).registers.b words)
    (hc : BoolList (eraseState initial).heap (eraseState initial).registers.c cut.toList) :
    let mask := (pairOrder n).map (flag active)
    let ans := sum cut.toList mask words
    ∃ q out,
      Run program (steps cut.toList mask words+1) q initial [] out ∧ (attempt program out).result = none ∧
      (eraseState out).pc=23 ∧ (eraseState out).stack=[] ∧ out.source=initial.source ∧
      BoolList (eraseState out).heap (eraseState out).registers.d ans ∧
      value ans = (EncodedRoundingState.mass active cut counts).1 ∧
      ans.length ≤ B+n+n*n ∧
      (∃ ext, (eraseState out).heap=(eraseState initial).heap ++ ext) ∧
      q + (attempt program out).operations ≤ completeBound 274 H A (instructionBudget (n*n) n B) := by
  let input := eraseState initial
  let mask := (pairOrder n).map (flag active)
  have hl := data_length hdata
  have halign : ∀ x ∈ words, x.length = cut.toList.length := by simpa using data_aligned hdata
  have htotal : mask.length = words.length := by simp [mask, pairOrder_length, hl]
  obtain ⟨ext,root,hrep,htrace⟩ := natural_trace ha hw hc htotal halign input.source
  have hnil : input.stack = [] := by simp [input, eraseState, State.map, hstack]
  have he := at_entry input hp hnil hd
  let final := state (input.heap ++ ext) (input.registers.set .r3 root) [] input.source 23
  have hrun : NaturalRun program (steps cut.toList mask words + 1) input [] final := by
    rw [he]
    exact htrace
  have halt : tickNatural program final = none := rfl
  obtain ⟨q,out,hactual,hout,hstop,hcost,htape⟩ := terminating_simulation hs hrun halt
  refine ⟨q,out,hactual,hstop,?_,?_,htape,?_,mass_value counts active cut hdata,?_,⟨ext,?_⟩,hcost.trans ?_⟩
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; exact hrep
  · simpa only [Vector.length_toList,hl] using rows_width words mask cut.toList B halign hwidth
  · rw [hout]; rfl
  · have hk : steps cut.toList mask words + 1 ≤ instructionBudget (n*n) n B := by
      simpa only [Vector.length_toList,hl] using steps_le words mask cut.toList B halign hwidth
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.RetainedMassTableProgram
