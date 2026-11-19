import DirectedFlowCutGap.RepeatPointerProgram
import DirectedFlowCutGap.RoundInputPackProgram
import DirectedFlowCutGap.RetainedMassTableProgram
import DirectedFlowCutGap.IntegerDistanceFromPhysical

/-! Share uniform rows during original-input preparation. -/

namespace DirectedFlowCutGap.InitialUniformTables

open BooleanTableRead (IndexSpine BoolList)
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open RetainedGridState (Family Pair row)
open BinaryPointerListRead (PointerList)
open PathCostMaterialization (WordList list_extend)
open RetainedMassTableProgram (TableAt DataRows pairOrder)

def repeatLabel (pc : Fin 16) : Fin 80 := ⟨64+pc.val,by omega⟩

def program : Program 80 := fun pc =>
  if pc.val < 64 then
    match pc.val with
    | 0 => .call 16 1 .r3
    | 1 => .call 32 2 .r1
    | 2 => .make .r3 (.pair .r3 .r1) 3
    | 16 => .make .r1 (.pair .r2 .r2) 17
    | 17 => .call (repeatLabel 0) 18 .r3
    | 18 => .ret .r3
    | 32 => .call 48 33 .r2
    | 33 => .move .r0 .r1 34
    | 34 => .move .r1 .r2 35
    | 35 => .call (repeatLabel 0) 36 .r3
    | 36 => .ret .r3
    | 48 => .move .r1 .r2 49
    | 49 => .call (repeatLabel 0) 50 .r3
    | 50 => .ret .r3
    | _ => .halt
  else if pc.val=65 then .ret .r3
  else ReferenceProgramLabels.instruction repeatLabel (RepeatPointerProgram.program ⟨pc.val-64,by have := pc.isLt; omega⟩)

abbrev state := @ReferenceProgramInvocation.state 80
abbrev uniform (n : ℕ) : Family n := Vector.replicate n (Vector.replicate n (Vector.replicate n 1))
abbrev unitWord : Bits := [true]
abbrev unitRow (n : ℕ) := List.replicate n unitWord

def words (n : ℕ) : List (List Bits) := List.replicate (n*n) (unitRow n)

def steps (n : ℕ) : ℕ := 2*RepeatPointerProgram.steps n+RepeatPointerProgram.steps (n*n)+17

theorem data_rows (n : ℕ) : DataRows (uniform n) (words n) := by
  have every (ps : List (Pair n)) :
      List.Forall₂ (fun xs p => xs.map value=(row (uniform n) p).toList) (List.replicate ps.length (unitRow n)) ps := by
    induction ps with
    | nil => exact .nil
    | cons p ps ih =>
      simp only [List.length_cons,List.replicate_succ]
      refine .cons ?_ ih
      simp [value,row]
  simpa only [DataRows,words,RetainedMassTableProgram.pairOrder_length] using every (pairOrder n)

theorem fraction_fields (n : ℕ) :
    IndexedRationalRead.fields (IntegerDistanceFromPhysical.encodedRow (Vector.replicate n 1)).toList =
      List.replicate n (unitWord,unitWord) := by
  simp [IndexedRationalRead.fields,IntegerDistanceFromPhysical.encodedRow,Vector.toList_ofFn,
    List.ofFn_const]

private theorem words_of_repeat {heap : NaturalHeap} {root payload n : ℕ} {word : Bits}
    (h : PointerList heap root (List.replicate n payload)) (rep : BoolList heap payload word) :
    WordList heap root (List.replicate n word) := by
  induction n generalizing root with
  | zero => cases h with | nil hp => exact .nil hp
  | succ n ih =>
    rw [List.replicate_succ] at h ⊢
    cases h with | cons hp rest => exact .cons hp rep (ih rest)

theorem flags_of_repeat {heap : NaturalHeap} {root payload n : ℕ} {b : Bool}
    (h : PointerList heap root (List.replicate n payload)) (rep : heap[payload]?=some (.flag b)) :
    BoolList heap root (List.replicate n b) := by
  induction n generalizing root with
  | zero => cases h with | nil hp => exact .nil hp
  | succ n ih =>
    rw [List.replicate_succ] at h ⊢
    cases h with | cons hp rest => exact .cons hp rep (ih rest)

private theorem fractions_of_repeat {heap : NaturalHeap} {root payload bit n : ℕ}
    (h : PointerList heap root (List.replicate n payload))
    (rep : heap[payload]?=some (.pair bit bit)) (word : BoolList heap bit unitWord) :
    WordPairTableRead.Table heap root (List.replicate n (unitWord,unitWord)) := by
  induction n generalizing root with
  | zero => cases h with | nil hp => exact .nil hp
  | succ n ih =>
    rw [List.replicate_succ] at h ⊢
    cases h with | cons hp rest => exact .cons hp rep word word (ih rest)

private theorem weights_of_repeat {heap : NaturalHeap} {root payload n : ℕ} {row : List Bits}
    (h : PointerList heap root (List.replicate n payload)) (rep : WordList heap payload row) :
    TableAt heap root (List.replicate n row) := by
  induction n generalizing root with
  | zero => cases h with | nil hp => exact .nil hp
  | succ n ih =>
    rw [List.replicate_succ] at h ⊢
    cases h with | cons hp rest => exact .cons hp rep (ih rest)

private theorem slots (pc : Fin 16) (h : RepeatPointerProgram.program pc≠.halt) :
    program (repeatLabel pc)=ReferenceProgramLabels.instruction repeatLabel (RepeatPointerProgram.program pc) := by
  by_cases stop : pc.val=1
  · have eq : pc=1 := Fin.ext stop
    subst pc
    exact (h rfl).elim
  · simp [program,repeatLabel,show ¬64+pc.val<64 by omega,show 64+pc.val≠65 by omega]

set_option maxHeartbeats 2300000 in
private theorem make_fractions {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (spine : IndexSpine heap r.a n) (one : BoolList heap r.c unitWord) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),
      WordPairTableRead.Table (heap++ext) root (List.replicate n (unitWord,unitWord)) ∧
      NaturalRun program (RepeatPointerProgram.steps n+5) (state heap r [] tape 0) []
        (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  let frame : Frame ℕ 80 := ⟨1,.r3,r⟩
  let cell : Cell ℕ := .pair r.c r.c
  let mid := heap++[cell]
  let args := r.set .r1 heap.length
  have beginRun : NaturalRun program 2 (state heap r [] tape 0) [] (state mid args [frame] tape 17) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,
      args,mid,cell,frame,allocateNatural,Recipe.cell]
  obtain ⟨ext,root,len,data,body⟩ := RepeatPointerProgram.natural_repeat (r:=args) (indexSpine_extend spine [cell]) tape
  have invoke := ReferenceProgramInvocation.call repeatLabel slots (caller:=17) (continuation:=18)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (mid++ext) (args.set .r3 root) [frame] tape 18
  have ret : tickNatural program stop=some ⟨state (mid++ext) (r.set .r3 root) [] tape 1,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨[cell]++ext,root,?_,?_⟩
  · have atCell : mid[heap.length]?=some (.pair r.c r.c) := by simp [mid,cell]
    have table := fractions_of_repeat data (lookup_extend atCell ext)
      (boolList_extend (boolList_extend one [cell]) ext)
    simpa only [mid,List.append_assoc] using table
  · have count : 2+(RepeatPointerProgram.steps n+2+1)=RepeatPointerProgram.steps n+5 := by omega
    rw [← count]
    simpa only [stop,mid,Registers.get,Registers.set,List.nil_append,List.append_assoc] using
      append_run beginRun (append_run invoke (.step ret (.done _)))

private theorem make_row {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (spine : IndexSpine heap r.a n) (one : BoolList heap r.c unitWord)
    (stack : List (Frame ℕ 80)) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),WordList (heap++ext) root (unitRow n) ∧
      NaturalRun program (RepeatPointerProgram.steps n+5) (state heap r stack tape 32) []
        (state (heap++ext) (r.set .r2 root) stack tape 33) := by
  let frame : Frame ℕ 80 := ⟨33,.r2,r⟩
  let args := r.set .r1 r.c
  have beginRun : NaturalRun program 2 (state heap r stack tape 32) [] (state heap args (frame::stack) tape 49) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,args,frame]
  obtain ⟨ext,root,len,data,body⟩ := RepeatPointerProgram.natural_repeat (r:=args) spine tape
  have invoke := ReferenceProgramInvocation.call repeatLabel slots (caller:=49) (continuation:=50)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) (frame::stack) body
  let stop := state (heap++ext) (args.set .r3 root) (frame::stack) tape 50
  have ret : tickNatural program stop=some ⟨state (heap++ext) (r.set .r2 root) stack tape 33,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨ext,root,words_of_repeat data (boolList_extend one ext),?_⟩
  have count : 2+(RepeatPointerProgram.steps n+2+1)=RepeatPointerProgram.steps n+5 := by omega
  rw [← count]
  simpa only [stop,Registers.get,Registers.set,List.nil_append,Nat.zero_add] using append_run beginRun (append_run invoke (.step ret (.done _)))

set_option maxHeartbeats 2300000 in
private theorem make_weights {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (spine : IndexSpine heap r.a n) (pairs : IndexSpine heap r.b (n*n)) (one : BoolList heap r.c unitWord) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root : ℕ),TableAt (heap++ext) root (words n) ∧
      NaturalRun program (RepeatPointerProgram.steps n+RepeatPointerProgram.steps (n*n)+11) (state heap r [] tape 1) []
        (state (heap++ext) (r.set .r1 root) [] tape 2) := by
  let frame : Frame ℕ 80 := ⟨2,.r1,r⟩
  have enter : tickNatural program (state heap r [] tape 1)=some ⟨state heap r [frame] tape 32,[],0⟩ := rfl
  obtain ⟨er,rowRoot,weights,rowRun⟩ := make_row spine one [frame] tape
  let mid := heap++er
  let args : Registers ℕ := ⟨r.b,rowRoot,rowRoot,r.d⟩
  have load : NaturalRun program 2 (state mid (r.set .r2 rowRoot) [frame] tape 33) []
      (state mid args [frame] tape 35) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,args]
  obtain ⟨et,root,len,data,body⟩ := RepeatPointerProgram.natural_repeat (r:=args) (indexSpine_extend pairs er) tape
  have invoke := ReferenceProgramInvocation.call repeatLabel slots (caller:=35) (continuation:=36)
    (result:=.r3) (dst:=.r3) (by rfl) (by rfl) [frame] body
  let stop := state (mid++et) (args.set .r3 root) [frame] tape 36
  have ret : tickNatural program stop=some ⟨state (mid++et) (r.set .r1 root) [] tape 2,[],0⟩ := by
    simp [stop,ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,frame]
  refine ⟨er++et,root,?_,?_⟩
  · simpa only [mid,List.append_assoc,words] using weights_of_repeat data (list_extend weights et)
  · let a := RepeatPointerProgram.steps n
    let b := RepeatPointerProgram.steps (n*n)
    have count : (a+5+(2+(b+2+1)))+1=a+b+11 := by omega
    change NaturalRun program (a+b+11) _ _ _
    rw [← count]
    simpa only [stop,mid,a,b,Registers.get,Registers.set,List.append_assoc,List.nil_append] using
      NaturalRun.step enter (append_run rowRun (append_run load (append_run invoke (.step ret (.done _)))))

theorem natural_tables {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    (spine : IndexSpine heap r.a n) (pairs : IndexSpine heap r.b (n*n))
    (one : BoolList heap r.c unitWord) (tape : Bits) :
    ∃ (ext : NaturalHeap) (root weightRoot : ℕ),
      (∃ fractions,(heap++ext)[root]?=some (.pair fractions weightRoot) ∧
        WordPairTableRead.Table (heap++ext) fractions (List.replicate n (unitWord,unitWord))) ∧
      TableAt (heap++ext) weightRoot (words n) ∧
      NaturalRun program (steps n) (state heap r [] tape 0)
        [] (state (heap++ext) ⟨r.a,weightRoot,r.c,root⟩ [] tape 3) := by
  obtain ⟨ef,fraction,stored,prepare⟩ := make_fractions spine one tape
  let mid := heap++ef
  let next := r.set .r3 fraction
  obtain ⟨ew,weights,table,work⟩ := make_weights (r:=next) (indexSpine_extend spine ef)
    (indexSpine_extend pairs ef) (boolList_extend one ef) tape
  let grown := mid++ew
  let record : Cell ℕ := .pair fraction weights
  let ext := ef++ew++[record]
  have save : tickNatural program (state grown (next.set .r1 weights) [] tape 2)=
      some ⟨state (grown++[record]) ⟨r.a,weights,r.c,grown.length⟩ [] tape 3,[],0⟩ := by
    simp [ReferenceProgramInvocation.state,program,tickNatural,Registers.get,Registers.set,next,record,allocateNatural,Recipe.cell]
  have ptr : (grown++[record])[grown.length]?=some record := by simp
  refine ⟨ext,grown.length,weights,⟨fraction,?_,?_⟩,?_,?_⟩
  · simpa only [ext,grown,mid,List.append_assoc,record] using ptr
  · simpa only [ext,grown,mid,List.append_assoc] using BinaryIndexedPairRead.table_extend
      (BinaryIndexedPairRead.table_extend stored ew) [record]
  · simpa only [ext,grown,mid,List.append_assoc] using RoundInputPackProgram.weights_extend table [record]
  · let a := RepeatPointerProgram.steps n
    let b := RepeatPointerProgram.steps (n*n)
    change NaturalRun program (2*a+b+17) _ _ _
    have calculated := append_run prepare (append_run work (.step save (.done _)))
    have actual : NaturalRun program (2*a+b+17) (state heap r [] tape 0) []
        (state (heap++ext) ⟨r.a,weights,r.c,grown.length⟩ [] tape 3) := by
      have h : (a+5)+(a+b+11+1)=2*a+b+17 := by omega
      simpa only [ext,grown,mid,a,b,h,List.append_assoc,List.nil_append] using calculated
    exact actual

end DirectedFlowCutGap.InitialUniformTables
