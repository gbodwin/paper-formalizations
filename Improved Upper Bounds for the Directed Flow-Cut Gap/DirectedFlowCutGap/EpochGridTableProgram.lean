import DirectedFlowCutGap.EpochPermutationProgram

/-! Assign grid draws to the original active order, before permutation. -/

namespace DirectedFlowCutGap.EpochGridTableProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)
open BinaryPointerListRead (PointerList pointerList_extend)
open PhysicalBoundedDrawProgram (Outcome)
open PhysicalDrawSequenceProgram (StoredBatch batch_extend)

def Entry (heap : NaturalHeap) (root key : ℕ) (word : Bits) : Prop :=
  ∃ pointer,heap[root]?=some (.pair key pointer) ∧ BoolList heap pointer word

theorem entry_extend {heap : NaturalHeap} {root key : ℕ} {word : Bits}
    (stored : Entry heap root key word) (ext : NaturalHeap) : Entry (heap++ext) root key word := by
  obtain ⟨pointer,pair,rep⟩ := stored
  exact ⟨pointer,lookup_extend pair ext,boolList_extend rep ext⟩

inductive Table (heap : NaturalHeap) : ℕ→List (ℕ×Bits)→Prop
  | nil {root} : heap[root]?=some .nil → Table heap root []
  | cons {root head tail key word rest} : heap[root]?=some (.pair head tail) →
      Entry heap head key word → Table heap tail rest → Table heap root ((key,word)::rest)

theorem table_extend {heap : NaturalHeap} {root : ℕ} {entries : List (ℕ×Bits)} (table : Table heap root entries)
    (ext : NaturalHeap) : Table (heap++ext) root entries := by
  induction table with
  | nil read => exact .nil (lookup_extend read ext)
  | cons read entry _ ih => exact .cons (lookup_extend read ext) (entry_extend entry ext) ih

def program : Program 32 := fun pc => match pc.val with
  | 0 => .call 8 1 .r3
  | 8 => .branch .r0 9 31 31 12
  | 9 => .make .r3 .nil 10
  | 10 => .ret .r3
  | 12 => .field .r2 .r0 false 13
  | 13 => .field .r3 .r1 false 14
  | 14 => .field .r3 .r3 false 15
  | 15 => .make .r2 (.pair .r2 .r3) 16
  | 16 => .field .r0 .r0 true 17
  | 17 => .field .r1 .r1 true 18
  | 18 => .call 8 19 .r3
  | 19 => .make .r3 (.pair .r2 .r3) 10
  | _ => .halt

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 32))
    (tape : Bits) (pc : Fin 32) : NaturalState 32 := ⟨heap,heap.length,r,stack,pc,tape⟩

def steps (n : ℕ) : ℕ := 10*n+4

set_option maxHeartbeats 1500000 in
private theorem zip_return {heap : NaturalHeap} {r : Registers ℕ} {keys : List ℕ} {draws : List Outcome}
    (labels : PointerList heap r.a keys) (results : StoredBatch heap r.b draws) (count : draws.length=keys.length)
    (caller : Frame ℕ 32) (stack : List (Frame ℕ 32)) (tape : Bits) :
    ∃ ext root,Table (heap++ext) root (keys.zip (draws.map Outcome.index)) ∧
      NaturalRun program (10*keys.length+3) (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction keys generalizing heap r caller stack draws with
  | nil =>
    cases labels with
    | nil empty =>
      refine ⟨[.nil],heap.length,.nil (by simp),?_⟩
      apply ReferenceProgramSteps.sound
      simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,empty,tagBranch,
        allocateNatural,Recipe.cell]
  | cons key keys ih =>
    cases draws with
    | nil => simp at count
    | cons d ds =>
      cases labels with
      | @cons _ h tail _ keyPair next =>
        cases results with
        | @cons _ draw more _ _ batch result remaining =>
          obtain ⟨word,flag,pair,value,_⟩ := result
          let saved := caller::stack
          let withWord := (r.set .r2 key).set .r3 word
          have prep : NaturalRun program 4 (state heap r saved tape 8) [] (state heap withWord saved tape 15) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,
              tagBranch,keyPair,batch,pair,withWord]
          let cell : Cell ℕ := .pair key word
          let mid := heap++[cell]
          let args := ((withWord.set .r2 heap.length).set .r0 tail).set .r1 more
          let frame : Frame ℕ 32 := ⟨19,.r3,args⟩
          have left : mid[r.a]?=some (.pair key tail) := lookup_extend keyPair [cell]
          have right : mid[r.b]?=some (.pair draw more) := lookup_extend batch [cell]
          have enter : NaturalRun program 4 (state heap withWord saved tape 15) []
              (state mid args (frame::saved) tape 8) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell,
              left,right,mid,args,frame,withWord,cell]
          have smaller : ds.length=keys.length := by simpa only [List.length_cons,Nat.succ.injEq] using count
          obtain ⟨ext,restRoot,rep,body⟩ := ih (r:=args) (pointerList_extend next [cell])
            (batch_extend remaining [cell]) smaller frame saved
          let grown := mid++ext
          let i := grown.length
          let last : Cell ℕ := .pair heap.length restRoot
          have finish : NaturalRun program 2 (state grown (args.set .r3 restRoot) saved tape 19) []
              (state (grown++[last]) (caller.saved.set caller.destination i) stack tape caller.continuation) := by
            apply ReferenceProgramSteps.sound
            simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,args,saved,
              allocateNatural,Recipe.cell,i,last]
          have link : mid[heap.length]?=some cell := by simp [mid]
          have stored : Entry (grown++[last]) heap.length key d.index :=
            ⟨word,lookup_extend (lookup_extend link ext) [last],
              boolList_extend (boolList_extend (boolList_extend value [cell]) ext) [last]⟩
          have out : Table (grown++[last]) i ((key::keys).zip ((d::ds).map Outcome.index)) :=
            .cons (by simp [i,last]) stored (table_extend rep [last])
          refine ⟨[cell]++ext++[last],i,?_,?_⟩
          · simpa only [grown,mid,List.append_assoc] using out
          · have full := append_run prep (append_run enter (append_run body finish))
            have total : 4+(4+(10*keys.length+3+2))=10*(key::keys).length+3 := by simp [Nat.mul_add]; omega
            rw [← total]
            simpa only [grown,mid,List.append_assoc,List.nil_append] using full

theorem natural_table {heap : NaturalHeap} {r : Registers ℕ} {keys : List ℕ} {draws : List Outcome}
    (labels : PointerList heap r.a keys) (results : StoredBatch heap r.b draws) (count : draws.length=keys.length) (tape : Bits) :
    ∃ ext root,Table (heap++ext) root (keys.zip (draws.map Outcome.index)) ∧
      NaturalRun program (steps keys.length) (state heap r [] tape 0) [] (state (heap++ext) (r.set .r3 root) [] tape 1) := by
  let caller : Frame ℕ 32 := ⟨1,.r3,r⟩
  have enter : tickNatural program (state heap r [] tape 0)=some ⟨state heap r [caller] tape 8,[],0⟩ := rfl
  obtain ⟨ext,root,rep,body⟩ := zip_return labels results count caller [] tape
  exact ⟨ext,root,rep,.step enter body⟩

end DirectedFlowCutGap.EpochGridTableProgram
