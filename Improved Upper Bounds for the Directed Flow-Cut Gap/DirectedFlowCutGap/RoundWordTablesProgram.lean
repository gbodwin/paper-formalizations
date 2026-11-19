import DirectedFlowCutGap.IntegerLevelCutProgram
import DirectedFlowCutGap.BinaryTrimProgram
import DirectedFlowCutGap.ConcreteExpressionProgram
import DirectedFlowCutGap.ReferenceProgramSteps

/-! Build the target list and the outgoing cost table from the same stored integer row. -/

namespace DirectedFlowCutGap.RoundWordTablesProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open PathCostMaterialization (WordList)
open GraphDiscoveryProgram (Vertices)

def trimLabel (pc : Fin 13) : Fin 45 := ⟨32+pc.val,by omega⟩

def program : Program 45 := fun pc =>
  if pc.val<32 then
    match pc.val with
    | 0 => .call 8 1 .r3
    | 8 => .branch .r0 9 31 31 12
    | 9 => .make .r3 .nil 10
    | 10 => .make .r3 (.pair .r3 .r3) 11
    | 11 => .ret .r3
    | 12 => .call 25 13 .r3
    | 13 => .field .r0 .r0 false 14
    | 14 => .field .r1 .r1 false 15
    | 15 => .call 28 16 .r1
    | 16 => .make .r0 (.pair .r0 .r1) 17
    | 17 => .make .r1 (.pair .r1 .r2) 18
    | 18 => .field .r2 .r3 false 19
    | 19 => .make .r0 (.pair .r0 .r2) 20
    | 20 => .field .r3 .r3 true 21
    | 21 => .make .r1 (.pair .r1 .r3) 22
    | 22 => .make .r3 (.pair .r0 .r1) 23
    | 23 => .ret .r3
    | 25 => .field .r0 .r0 true 26
    | 26 => .field .r1 .r1 true 8
    | 28 => .move .r0 .r1 29
    | 29 => .call (trimLabel 0) (trimLabel 12) .r3
    | _ => .halt
  else if pc.val=44 then .ret .r3
  else ReferenceProgramLabels.instruction trimLabel
    (BinaryTrimProgram.program ⟨pc.val-32,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 45))
    (tape : Bits) (pc : Fin 45) : NaturalState 45 := ⟨heap,heap.length,r,stack,pc,tape⟩

def canon (row : List Bits) : List Bits := row.map fun w => (trim w).1

def Output (heap : NaturalHeap) (root : ℕ) (labels weights : List Bits) : Prop :=
  ∃ targets costs,heap[root]?=some (.pair targets costs) ∧
    WordPairTableRead.Table heap targets (labels.zip (canon weights)) ∧
    WordPairTableRead.Table heap costs ((canon weights).map (·,[true]))

def bodySteps : List Bits→ℕ
  | [] => 4
  | w::ws => bodySteps ws+BinaryTrimProgram.steps w+18

def steps (weights : List Bits) : ℕ := bodySteps weights+1

theorem steps_le (weights : List Bits) (B : ℕ) (width : ∀ w∈weights,w.length≤B) :
    steps weights ≤ weights.length*(8*B+21)+5 := by
  have bound : bodySteps weights ≤ weights.length*(8*B+21)+4 := by
    induction weights with
    | nil => simp [bodySteps]
    | cons w ws ih =>
      have front := (BinaryTrimProgram.steps_bound w).trans (Nat.add_le_add_right
        (Nat.mul_le_mul_left 8 (width w List.mem_cons_self)) 3)
      have tail := ih (fun b h => width b (List.mem_cons_of_mem _ h))
      rw [bodySteps,List.length_cons,Nat.succ_mul]
      omega
  exact Nat.add_le_add_right bound 1

theorem canon_values (weights : List Bits) : canon weights=(weights.map value).map Nat.bits := by
  simp only [canon,List.map_map,Function.comp_def]
  exact List.map_congr_left fun w _ => by rw [← normal_bits (trim_spec w).1,(trim_spec w).2.1]

theorem target_fields {n : ℕ} (row : RetainedGridState.Row n) (words : List Bits)
    (values : words.map value=row.toList) (label : Fin n→Bits) :
    ((List.finRange n).map label).zip (canon words)=IntegerLevelCutProgram.fields row label (List.finRange n) := by
  rw [canon_values,values]
  apply List.ext_getElem
  · simp [IntegerLevelCutProgram.fields]
  · intro i left right
    simp [IntegerLevelCutProgram.fields,List.getElem_zip]

theorem cost_fields {n : ℕ} (row : RetainedGridState.Row n) (words : List Bits)
    (values : words.map value=row.toList) :
    (canon words).map (·,[true])=IndexedRationalRead.fields (IntegerDistanceFromPhysical.encodedRow row).toList := by
  rw [canon_values,values]
  apply List.ext_getElem
  · simp [IndexedRationalRead.fields]
  · intro i left right
    simp [IndexedRationalRead.fields,IntegerDistanceFromPhysical.encodedRow]

private theorem trim_slots (pc : Fin 13) (h : BinaryTrimProgram.program pc≠.halt) :
    program (trimLabel pc)=ReferenceProgramLabels.instruction trimLabel (BinaryTrimProgram.program pc) := by
  by_cases endPc : pc.val=12
  · have eq : pc=12 := Fin.ext endPc
    subst pc
    exact (h rfl).elim
  · simp [program,trimLabel,show ¬32+pc.val<32 by omega,show 32+pc.val≠44 by omega]

theorem extend_table {heap : NaturalHeap} {root : ℕ} {records : List (Bits×Bits)}
    (h : WordPairTableRead.Table heap root records) (ext : NaturalHeap) :
    WordPairTableRead.Table (heap++ext) root records := by
  induction h with
  | nil read => exact .nil (lookup_extend read ext)
  | cons read pair numerator denominator _ ih =>
    exact .cons (lookup_extend read ext) (lookup_extend pair ext)
      (boolList_extend numerator ext) (boolList_extend denominator ext) ih

private theorem normalize {heap : NaturalHeap} {r : Registers ℕ} {word : Bits}
    (stored : BoolList heap r.b word) (stack : List (Frame ℕ 45)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (trim word).1 ∧
      NaturalRun program (BinaryTrimProgram.steps word+4)
        (state heap r stack tape 15) [] (state (heap++ext) (r.set .r1 root) stack tape 16) := by
  let args := r.set .r0 r.b
  let frame : Frame ℕ 45 := ⟨16,.r1,r⟩
  let inner : Frame ℕ 45 := ⟨trimLabel 12,.r3,args⟩
  have enter : NaturalRun program 3 (state heap r stack tape 15) []
      (state heap args (inner::frame::stack) tape (trimLabel 0)) := by
    apply ReferenceProgramSteps.sound
    cases r
    rfl
  obtain ⟨ext,root,_,body,rep⟩ := BinaryTrimProgram.trim_return (a:=args.a) stored heap.length args.b args.c args.d
    rfl args 12 [] tape
  have lifted := ReferenceProgramLabels.run trimLabel BinaryTrimProgram.program program trim_slots body
  have lifted := ReferenceProgramStack.run program (frame::stack) lifted
  refine ⟨ext,root,rep,?_⟩
  let stop := state (heap++ext) (args.set .r3 root) (frame::stack) tape (trimLabel 12)
  have core : NaturalRun program (BinaryTrimProgram.steps word)
      (state heap args (inner::frame::stack) tape (trimLabel 0)) [] stop := by
    cases r
    simpa [state,stop,inner,args,BinaryTrimProgram.state,ReferenceProgramLabels.state,
      ReferenceProgramLabels.frame,ReferenceProgramStack.state,Registers.set] using lifted
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r1 root) stack tape 16,[],0⟩ := by
    simp [stop,state,program,trimLabel,tickNatural,frame,Registers.get,Registers.set]
  have count : 3+(BinaryTrimProgram.steps word+1)=BinaryTrimProgram.steps word+4 := by omega
  rw [← count]
  exact append_run enter (append_run core (.step ret (.done _)))

set_option maxHeartbeats 2300000 in
private theorem build_return {heap : NaturalHeap} {r : Registers ℕ} {labels weights : List Bits}
    (vertices : Vertices heap r.a labels) (stored : WordList heap r.b weights)
    (one : BoolList heap r.c [true]) (aligned : weights.length=labels.length)
    (caller : Frame ℕ 45) (stack : List (Frame ℕ 45)) (tape : Bits) :
    ∃ ext root,Output (heap++ext) root labels weights ∧
      NaturalRun program (bodySteps weights) (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction labels generalizing r heap caller stack weights with
  | nil =>
    cases weights with
    | nil =>
      cases vertices with
      | nil empty =>
        let root := heap.length
        let extra : NaturalHeap := [.nil,.pair root root]
        refine ⟨extra,root+1,?_,?_⟩
        · exact ⟨root,root,by simp [extra,root],.nil (by simp [extra,root]),.nil (by simp [extra,root])⟩
        · apply ReferenceProgramSteps.sound
          simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,empty,
            allocateNatural,Recipe.cell,bodySteps,extra,root]
    | cons w ws => simp at aligned
  | cons v vs ih =>
    cases weights with
    | nil => simp at aligned
    | cons w ws =>
      cases vertices with
      | @cons _ vertex more _ _ first vertexRep next =>
        cases stored with
        | @cons _ weight tail _ _ second weightRep remain =>
          let saved := caller::stack
          let frame : Frame ℕ 45 := ⟨13,.r3,r⟩
          let args := (r.set .r0 more).set .r1 tail
          have start : NaturalRun program 4 (state heap r saved tape 8) [] (state heap args (frame::saved) tape 8) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,tagBranch,
              first,second,args,frame]
          have len : ws.length=vs.length := Nat.succ.inj aligned
          obtain ⟨et,rest,⟨targets,costs,bundle,targetRep,costRep⟩,body⟩ := ih (r:=args) next remain one len frame saved
          let mid := heap++et
          let headArgs := (((r.set .r3 rest).set .r0 vertex).set .r1 weight)
          have left : mid[r.a]?=some (.pair vertex more) := lookup_extend first et
          have right : mid[r.b]?=some (.pair weight tail) := lookup_extend second et
          have load : NaturalRun program 2 (state mid (r.set .r3 rest) saved tape 13) []
              (state mid headArgs saved tape 15) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,left,right,headArgs]
          obtain ⟨en,normalized,numRep,trimRun⟩ := normalize (r:=headArgs) (boolList_extend weightRep et) saved tape
          let grown := mid++en
          let fresh := grown.length
          let extra : NaturalHeap := [.pair vertex normalized,.pair normalized r.c,
            .pair fresh targets,.pair (fresh+1) costs,.pair (fresh+2) (fresh+3)]
          let heads : NaturalHeap := [.pair vertex normalized,.pair normalized r.c]
          let rows : NaturalHeap := [.pair fresh targets,.pair (fresh+1) costs]
          let link : Cell ℕ := .pair (fresh+2) (fresh+3)
          let frontRegs : Registers ℕ := ⟨fresh,fresh+1,targets,rest⟩
          let backRegs : Registers ℕ := ⟨fresh+2,fresh+3,targets,costs⟩
          have tails : grown[rest]?=some (.pair targets costs) := lookup_extend bundle en
          have tails₁ : (grown++heads)[rest]?=some (.pair targets costs) := lookup_extend tails heads
          have tails₂ : (grown++[.pair vertex normalized,.pair normalized r.c,.pair fresh targets])[rest]?=
              some (.pair targets costs) := lookup_extend tails _
          have front : NaturalRun program 3 (state grown (headArgs.set .r1 normalized) saved tape 16) []
              (state (grown++heads) frontRegs saved tape 19) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,headArgs,
              allocateNatural,Recipe.cell,tails₁,heads,frontRegs,fresh]
          have back : NaturalRun program 3 (state (grown++heads) frontRegs saved tape 19) []
              (state (grown++(heads++rows)) backRegs saved tape 22) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,frontRegs,backRegs,
              allocateNatural,Recipe.cell,tails₂,heads,rows,fresh,Nat.add_assoc]
          have finish : NaturalRun program 2 (state (grown++(heads++rows)) backRegs saved tape 22) []
              (state (grown++extra) (caller.saved.set caller.destination (fresh+4)) stack tape caller.continuation) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,backRegs,saved,
              allocateNatural,Recipe.cell,heads,rows,extra,fresh,Nat.add_assoc]
          have close : NaturalRun program 8 (state grown (headArgs.set .r1 normalized) saved tape 16) []
              (state (grown++extra) (caller.saved.set caller.destination (fresh+4)) stack tape caller.continuation) :=
            append_run front (append_run back finish)
          have alloc (i : ℕ) : (grown++extra)[fresh+i]?=extra[i]? := by
            rw [List.getElem?_append_right (by dsimp [fresh]; omega)]
            have cancel : fresh+i-grown.length=i := by dsimp [fresh]; omega
            rw [cancel]
          have result : Output (grown++extra) (fresh+4) (v::vs) (w::ws) := by
            have vertexOut : BoolList (grown++extra) vertex v :=
              boolList_extend (boolList_extend (boolList_extend vertexRep et) en) extra
            have numOut : BoolList (grown++extra) normalized (trim w).1 := boolList_extend numRep extra
            have oneOut : BoolList (grown++extra) r.c [true] :=
              boolList_extend (boolList_extend (boolList_extend one et) en) extra
            refine ⟨fresh+2,fresh+3,by simpa [extra] using alloc 4,?_,?_⟩
            · exact .cons (by simpa [extra] using alloc 2)
                (by simpa [extra] using alloc 0) vertexOut numOut
                (extend_table (extend_table targetRep en) extra)
            · exact .cons (by simpa [extra] using alloc 3)
                (by simpa [extra] using alloc 1) numOut oneOut
                (extend_table (extend_table costRep en) extra)
          refine ⟨et++en++extra,fresh+4,?_,?_⟩
          · simpa only [grown,mid,List.append_assoc] using result
          · have full := append_run start (append_run body (append_run load (append_run trimRun close)))
            have count : 4+(bodySteps ws+(2+(BinaryTrimProgram.steps w+4+8)))=bodySteps (w::ws) := by
              simp only [bodySteps]
              omega
            rw [← count]
            simpa only [grown,mid,List.append_assoc,List.nil_append] using full

theorem natural_tables {heap : NaturalHeap} {r : Registers ℕ} {labels weights : List Bits}
    (vertices : Vertices heap r.a labels) (stored : WordList heap r.b weights)
    (one : BoolList heap r.c [true]) (aligned : weights.length=labels.length) (tape : Bits) :
    ∃ ext root,Output (heap++ext) root labels weights ∧
      NaturalRun program (steps weights) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  let caller : Frame ℕ 45 := ⟨1,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [caller] tape 8,[],0⟩ := rfl
  obtain ⟨ext,root,rep,body⟩ := build_return vertices stored one aligned caller [] tape
  exact ⟨ext,root,rep,.step enter body⟩

end DirectedFlowCutGap.RoundWordTablesProgram
