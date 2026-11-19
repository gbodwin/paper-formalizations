import DirectedFlowCutGap.PhysicalEpochDraws
import DirectedFlowCutGap.BinaryIncrementProgram
import DirectedFlowCutGap.FlattenDemandMaskProgram

/-!
# Preparing the epoch draw bounds from active flags

The fixed program counts only true flags. It constructs the decreasing
canonical binary permutation bounds and the list of shared grid bounds.
It then appends the two lists in the same heap and returns the schedule
used by the physical draw sequence.
-/

namespace DirectedFlowCutGap.RetainedEpochScheduleProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open PathCostMaterialization (WordList)

def incLabel (pc : Fin 16) : Fin 56 := ⟨40+pc.val,by omega⟩

def program : Program 56 := fun pc =>
  if pc.val < 40 then
    match pc.val with
    | 0 => .branch .r0 1 31 31 5
    | 1 => .make .r3 .nil 2
    | 2 => .make .r2 (.pair .r3 .r3) 3
    | 3 => .make .r3 (.pair .r3 .r2) 4
    | 4 => .ret .r3
    | 5 => .field .r2 .r0 false 6
    | 6 => .field .r0 .r0 true 7
    | 7 => .call 0 8 .r3
    | 8 => .branch .r2 31 4 10 31
    | 10 => .field .r0 .r3 false 11
    | 11 => .call (incLabel 15) 12 .r0
    | 12 => .field .r3 .r3 true 13
    | 13 => .field .r2 .r3 false 14
    | 14 => .make .r2 (.pair .r0 .r2) 15
    | 15 => .field .r3 .r3 true 16
    | 16 => .make .r3 (.pair .r1 .r3) 17
    | 17 => .make .r2 (.pair .r2 .r3) 18
    | 18 => .make .r3 (.pair .r0 .r2) 4
    | 24 => .branch .r0 25 31 31 26
    | 25 => .move .r3 .r1 4
    | 26 => .field .r2 .r0 false 27
    | 27 => .field .r0 .r0 true 28
    | 28 => .call 24 29 .r3
    | 29 => .make .r3 (.pair .r2 .r3) 4
    | 30 => .call 24 31 .r3
    | 36 => .call 0 37 .r3
    | 37 => .field .r0 .r3 true 38
    | 38 => .field .r1 .r0 true 39
    | 39 => .field .r0 .r0 false 30
    | _ => .halt
  else if pc.val=54 then .ret .r3
  else ReferenceProgramLabels.instruction incLabel
    (BinaryIncrementProgram.program ⟨pc.val-40,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (registers : Registers ℕ) (stack : List (Frame ℕ 56))
    (tape : Bits) (pc : Fin 56) : NaturalState 56 :=
  ⟨heap,heap.length,registers,stack,pc,tape⟩

def activeCount (flags : Bits) : ℕ := (flags.filter id).length

theorem activeCount_le (flags : Bits) : activeCount flags ≤ flags.length :=
  List.length_filter_le _ _

@[simp] theorem activeCount_cons (b : Bool) (flags : Bits) :
    activeCount (b::flags)=activeCount flags+b.toNat := by
  cases b <;> simp [activeCount]

def permutationWords (m : ℕ) : List Bits :=
  (PhysicalEpochDraws.permutationBounds m).map fun n => n.val.bits

theorem permutationWords_length (m : ℕ) : (permutationWords m).length=m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [permutationWords,PhysicalEpochDraws.permutationBounds] at ih ⊢; exact ih

def ScheduleAt (heap : NaturalHeap) (root L m : ℕ) : Prop :=
  ∃ count mix perm cells, heap[root]?=some (.pair count mix) ∧ heap[mix]?=some (.pair perm cells) ∧
    BoolList heap count m.bits ∧ WordList heap perm (permutationWords m) ∧
    WordList heap cells (List.replicate m L.bits)

def buildSteps : Bits → ℕ
  | [] => 5
  | b::flags =>
    buildSteps flags + (if b then 17+BinaryIncrementProgram.steps (activeCount flags).bits else 6)

private theorem inc_slots (pc : Fin 16) (h : BinaryIncrementProgram.program pc≠.halt) :
    program (incLabel pc) =
      ReferenceProgramLabels.instruction incLabel (BinaryIncrementProgram.program pc) := by
  by_cases hp : pc.val=14
  · have eq : pc=14 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,incLabel,show ¬40+pc.val<40 by omega,show 40+pc.val≠54 by omega]

private theorem join {s u v : NaturalState 56} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem inc_normal {xs : Bits} (hn : Normal xs) : Normal (increment true xs).1 := by
  induction hn with
  | nil => exact .digit .nil (fun _ => rfl)
  | @digit b xs h last ih =>
    cases b with
    | false => exact .digit h (fun _ => rfl)
    | true =>
      have nonzero : (increment true xs).1 ≠ [] := by
        intro eq
        have spec := (increment_spec true xs).1
        simp [eq,value] at spec
      exact .digit ih (fun hz => (nonzero hz).elim)

private theorem increment_bits (k : ℕ) : (increment true k.bits).1=(k+1).bits := by
  have ht := trim_spec k.bits
  have bits := normal_bits ht.1
  rw [ht.2.1,value_bits] at bits
  have h : Normal k.bits := bits ▸ ht.1
  have hv := (increment_spec true k.bits).1
  simp only [Bool.toNat_true,value_bits] at hv
  rw [← hv]
  exact (normal_bits (inc_normal h)).symm

private theorem increment_return {heap : NaturalHeap} {r : Registers ℕ} {k : ℕ}
    (data : BoolList heap r.a k.bits) (caller : Frame ℕ 56) (stack : List (Frame ℕ 56)) (tape : Bits) :
    ∃ ext root,BoolList (heap++ext) root (k+1).bits ∧
      NaturalRun program (BinaryIncrementProgram.steps k.bits+2)
        (state heap r (caller::stack) tape (incLabel 15)) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  let initial := BinaryIncrementProgram.state heap heap.length r.a r.b r.c r.d [] tape 15
  obtain ⟨out,run,rep,_,htape,hpc,hstack,ha,hb,hc,hn,⟨ext,he,_⟩,_⟩ :=
    BinaryIncrementProgram.increment_high initial rfl rfl data rfl
  have shape : out = BinaryIncrementProgram.state (heap++ext) (heap++ext).length
      r.a r.b r.c out.registers.d [] tape 14 := by
    cases out with
    | mk oh on regs frames pc src =>
      cases regs
      simp_all [initial,BinaryIncrementProgram.state]
  have lift := ReferenceProgramLabels.run incLabel BinaryIncrementProgram.program program inc_slots run
  have lift := ReferenceProgramStack.run program (caller::stack) lift
  rw [shape] at lift
  let before := state (heap++ext) ⟨r.a,r.b,r.c,out.registers.d⟩ (caller::stack) tape (incLabel 14)
  let after := state (heap++ext) (caller.saved.set caller.destination out.registers.d) stack tape caller.continuation
  have body : NaturalRun program (BinaryIncrementProgram.steps k.bits+1)
      (state heap r (caller::stack) tape (incLabel 15)) [] before := by
    cases r
    simpa [before,initial,state,ReferenceProgramLabels.state,ReferenceProgramStack.state,
      BinaryIncrementProgram.state] using lift
  have ret : tickNatural program before=some ⟨after,[],0⟩ := rfl
  rw [increment_bits k,he] at rep
  exact ⟨ext,out.registers.d,rep,join body (.step ret (.done after))⟩

private theorem add_bound {heap : NaturalHeap} {r : Registers ℕ} {L m : ℕ}
    (newCount : BoolList heap r.a (m+1).bits) (level : BoolList heap r.b L.bits)
    (prior : ScheduleAt heap r.d L m)
    (caller : Frame ℕ 56) (stack : List (Frame ℕ 56)) (tape : Bits) :
    ∃ ext root, ScheduleAt (heap++ext) root L (m+1) ∧
      NaturalRun program 8 (state heap r (caller::stack) tape 12) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  obtain ⟨_,mix,perm,cells,rootPair,mixPair,_,oldPerm,oldCells⟩ := prior
  let saved := caller::stack
  let i := heap.length
  let pCell : Cell ℕ := .pair r.a perm
  let cCell : Cell ℕ := .pair r.b cells
  let two : Cell ℕ := .pair i (i+1)
  let result : Cell ℕ := .pair r.a (i+2)
  let h1 := heap++[pCell]
  let h2 := h1++[cCell]
  let h3 := h2++[two]
  let h4 := h3++[result]
  let s13 := state heap ⟨r.a,r.b,r.c,mix⟩ saved tape 13
  let s14 := state heap ⟨r.a,r.b,perm,mix⟩ saved tape 14
  let s15 := state h1 ⟨r.a,r.b,i,mix⟩ saved tape 15
  let s16 := state h1 ⟨r.a,r.b,i,cells⟩ saved tape 16
  let s17 := state h2 ⟨r.a,r.b,i,i+1⟩ saved tape 17
  let s18 := state h3 ⟨r.a,r.b,i+2,i+1⟩ saved tape 18
  let s4 := state h4 ⟨r.a,r.b,i+2,i+3⟩ saved tape 4
  let final := state h4 (caller.saved.set caller.destination (i+3)) stack tape caller.continuation
  have readMix : tickNatural program (state heap r saved tape 12)=some ⟨s13,[],0⟩ := by
    cases r
    simp [s13,state,program,tickNatural,Registers.get,Registers.set,rootPair]
  have readPerm : tickNatural program s13=some ⟨s14,[],0⟩ := by
    simp [s13,s14,state,program,tickNatural,Registers.get,Registers.set,mixPair]
  have addPerm : tickNatural program s14=some ⟨s15,[],0⟩ := by
    simp [s14,s15,h1,pCell,i,state,program,tickNatural,Registers.get,Registers.set,Recipe.cell,allocateNatural]
  have readCells : tickNatural program s15=some ⟨s16,[],0⟩ := by
    have h : h1[mix]?=some (.pair perm cells) := lookup_extend mixPair [pCell]
    simp [s15,s16,state,program,tickNatural,Registers.get,Registers.set,h]
  have addCells : tickNatural program s16=some ⟨s17,[],0⟩ := by
    simp [s16,s17,h1,h2,cCell,i,state,program,tickNatural,Registers.get,Registers.set,Recipe.cell,allocateNatural]
  have addMix : tickNatural program s17=some ⟨s18,[],0⟩ := by
    simp [s17,s18,h1,h2,h3,two,i,state,program,tickNatural,Registers.get,Registers.set,Recipe.cell,allocateNatural,Nat.add_assoc]
  have addResult : tickNatural program s18=some ⟨s4,[],0⟩ := by
    simp [s18,s4,h1,h2,h3,h4,result,i,state,program,tickNatural,Registers.get,Registers.set,Recipe.cell,allocateNatural,Nat.add_assoc]
  have ret : tickNatural program s4=some ⟨final,[],0⟩ := rfl
  let ext := [pCell,cCell,two,result]
  have hheap : h4=heap++ext := by simp [h4,h3,h2,h1,ext,List.append_assoc]
  have hp : h4[i]?=some (.pair r.a perm) := by
    rw [hheap,List.getElem?_append_right (by simp [i])]
    simp [i,ext,pCell]
  have hc : h4[i+1]?=some (.pair r.b cells) := by
    rw [hheap,List.getElem?_append_right (by simp [i])]
    simp [i,ext,cCell]
  have hm : h4[i+2]?=some (.pair i (i+1)) := by
    rw [hheap,List.getElem?_append_right (by simp [i])]
    simp [i,ext,two]
  have hr : h4[i+3]?=some (.pair r.a (i+2)) := by
    rw [hheap,List.getElem?_append_right (by simp [i])]
    simp [i,ext,result]
  refine ⟨ext,i+3,?_,?_⟩
  · rw [← hheap]
    refine ⟨r.a,i+2,i,i+1,hr,hm,?_,?_,?_⟩
    · rw [hheap]; exact boolList_extend newCount ext
    · change WordList h4 i ((m+1).bits :: permutationWords m)
      exact .cons hp (by rw [hheap]; exact boolList_extend newCount ext)
        (by rw [hheap]; exact PathCostMaterialization.list_extend oldPerm ext)
    · rw [List.replicate_succ]
      exact .cons hc (by rw [hheap]; exact boolList_extend level ext)
        (by rw [hheap]; exact PathCostMaterialization.list_extend oldCells ext)
  · rw [← hheap]
    exact .step readMix (.step readPerm (.step addPerm (.step readCells
      (.step addCells (.step addMix (.step addResult (.step ret (.done final))))))))

private theorem schedule_extend {heap : NaturalHeap} {p L m : ℕ} (h : ScheduleAt heap p L m)
    (ext : NaturalHeap) : ScheduleAt (heap++ext) p L m := by
  obtain ⟨c,x,pr,cr,hp,hq,hc,hr,hs⟩ := h
  exact ⟨c,x,pr,cr,lookup_extend hp ext,lookup_extend hq ext,boolList_extend hc ext,
    PathCostMaterialization.list_extend hr ext,PathCostMaterialization.list_extend hs ext⟩

theorem append_return {heap : NaturalHeap} {r : Registers ℕ} {xs ys : List Bits}
    (front : WordList heap r.a xs) (tail : WordList heap r.b ys)
    (caller : Frame ℕ 56) (stack : List (Frame ℕ 56)) (tape : Bits) :
    ∃ ext root, WordList (heap++ext) root (xs++ys) ∧
      NaturalRun program (6*xs.length+3) (state heap r (caller::stack) tape 24) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction xs generalizing heap r caller stack with
  | nil =>
    cases front with
    | nil h =>
      let saved := caller::stack
      let before := state heap (r.set .r3 r.b) saved tape 4
      have test : tickNatural program (state heap r saved tape 24)=some ⟨state heap r saved tape 25,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,h]
      have move : tickNatural program (state heap r saved tape 25)=some ⟨before,[],0⟩ := rfl
      have ret : tickNatural program before=some ⟨state heap (caller.saved.set caller.destination r.b)
          stack tape caller.continuation,[],0⟩ := by
        cases r
        simp [before,saved,state,program,tickNatural,Registers.get,Registers.set]
      exact ⟨[],r.b,by simpa using tail,by simpa using NaturalRun.step test (.step move (.step ret (.done _)))⟩
  | cons x xs ih =>
    cases front with
    | @cons _ hd tl _ _ hp hw ht =>
      let saved := caller::stack
      let hargs := r.set .r2 hd
      let args := hargs.set .r0 tl
      let frame : Frame ℕ 56 := ⟨29,.r3,args⟩
      have test : tickNatural program (state heap r saved tape 24)=some ⟨state heap r saved tape 26,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      have readHead : tickNatural program (state heap r saved tape 26)=some ⟨state heap hargs saved tape 27,[],0⟩ := by
        simp [hargs,state,program,tickNatural,Registers.get,hp]
      have readTail : tickNatural program (state heap hargs saved tape 27)=some ⟨state heap args saved tape 28,[],0⟩ := by
        cases r
        simp [hargs,args,state,program,tickNatural,Registers.get,Registers.set,hp]
      have call : tickNatural program (state heap args saved tape 28)=
          some ⟨state heap args (frame::saved) tape 24,[],0⟩ := rfl
      have oldTail : WordList heap args.a xs := by cases r; exact ht
      have right : WordList heap args.b ys := by cases r; exact tail
      obtain ⟨ext,root,rep,hrun⟩ := ih oldTail right frame saved
      let mid := heap++ext
      let fresh := mid.length
      let cell : Cell ℕ := .pair hd root
      let grown := mid++[cell]
      let before := state grown (args.set .r3 fresh) saved tape 4
      have alloc : tickNatural program (state mid (args.set .r3 root) saved tape 29)=some ⟨before,[],0⟩ := by
        cases r
        simp [before,grown,cell,fresh,args,hargs,state,program,tickNatural,
          Registers.get,Registers.set,Recipe.cell,allocateNatural]
      have ret : tickNatural program before=some ⟨state grown (caller.saved.set caller.destination fresh)
          stack tape caller.continuation,[],0⟩ := by
        cases r
        simp [before,args,hargs,saved,state,program,tickNatural,Registers.get,Registers.set]
      have result : WordList grown fresh ((x::xs)++ys) :=
        .cons (by simp [grown,fresh,cell]) (boolList_extend (boolList_extend hw ext) [cell])
          (PathCostMaterialization.list_extend rep [cell])
      refine ⟨ext++[cell],fresh,?_,?_⟩
      · simpa only [grown,mid,List.append_assoc] using result
      · have trace := NaturalRun.step test (.step readHead (.step readTail (.step call
          (join hrun (.step alloc (.step ret (.done _)))))))
        simp only [List.length_cons]
        convert trace using 1 <;> first | rfl | omega | simp only [grown,mid,List.append_assoc]

theorem build_return {heap : NaturalHeap} {r : Registers ℕ} {L : ℕ} {flags : Bits}
    (input : BoolList heap r.a flags) (level : BoolList heap r.b L.bits)
    (caller : Frame ℕ 56) (stack : List (Frame ℕ 56)) (tape : Bits) :
    ∃ ext root, ScheduleAt (heap++ext) root L (activeCount flags) ∧
      NaturalRun program (buildSteps flags) (state heap r (caller::stack) tape 0) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction flags generalizing heap r caller stack with
  | nil =>
    cases input with
    | nil hnil =>
      let saved := caller::stack
      let a := heap.length
      let first := heap++[Cell.nil]
      let halves : Cell ℕ := .pair a a
      let mid := first++[halves]
      let packed : Cell ℕ := .pair a (a+1)
      let grown := mid++[packed]
      let ext : NaturalHeap := [.nil,halves,packed]
      let ra := r.set .r3 a
      let rb := ra.set .r2 (a+1)
      let result := rb.set .r3 (a+2)
      have branch : tickNatural program (state heap r saved tape 0)=some ⟨state heap r saved tape 1,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hnil]
      have makeNil : tickNatural program (state heap r saved tape 1)=some ⟨state first ra saved tape 2,[],0⟩ := by
        simp [a,first,ra,state,program,tickNatural,allocateNatural,Recipe.cell]
      have makeHalves : tickNatural program (state first ra saved tape 2)=some ⟨state mid rb saved tape 3,[],0⟩ := by
        cases r
        simp [a,first,mid,halves,ra,rb,state,program,tickNatural,Registers.get,Registers.set,allocateNatural,Recipe.cell]
      have makeResult : tickNatural program (state mid rb saved tape 3)=some ⟨state grown result saved tape 4,[],0⟩ := by
        cases r
        simp [a,first,mid,grown,packed,ra,rb,result,state,program,tickNatural,Registers.get,Registers.set,
          allocateNatural,Recipe.cell,Nat.add_assoc]
      have ret : tickNatural program (state grown result saved tape 4)=
          some ⟨state grown (caller.saved.set caller.destination (a+2)) stack tape caller.continuation,[],0⟩ := by
        cases r
        simp [ra,rb,result,saved,state,program,tickNatural,Registers.get,Registers.set]
      have shape : grown=heap++ext := by simp [first,mid,grown,ext,List.append_assoc]
      have h0 : grown[a]?=some .nil := by
        rw [shape,List.getElem?_append_right (by simp [a])]
        simp [a,ext]
      have h1 : grown[a+1]?=some (.pair a a) := by
        rw [shape,List.getElem?_append_right (by simp [a])]
        simp [a,ext,halves]
      have h2 : grown[a+2]?=some (.pair a (a+1)) := by
        rw [shape,List.getElem?_append_right (by simp [a])]
        simp [a,ext,packed]
      refine ⟨ext,a+2,?_,?_⟩
      · rw [← shape]
        exact ⟨a,a+1,a,a,h2,h1,.nil h0,.nil h0,.nil h0⟩
      · rw [← shape]
        exact .step branch (.step makeNil (.step makeHalves (.step makeResult (.step ret (.done _)))))
  | cons bit flags ih =>
    cases input with
    | @cons _ head tail _ _ hp hb ht =>
      let saved := caller::stack
      let withBit := r.set .r2 head
      let args := withBit.set .r0 tail
      let frame : Frame ℕ 56 := ⟨8,.r3,args⟩
      have branch : tickNatural program (state heap r saved tape 0)=
          some ⟨state heap r saved tape 5,[],0⟩ := by
        simp [state,program,tickNatural,Registers.get,tagBranch,hp]
      have readFlag : tickNatural program (state heap r saved tape 5)=
          some ⟨state heap withBit saved tape 6,[],0⟩ := by
        simp [withBit,state,program,tickNatural,Registers.get,hp]
      have readTail : tickNatural program (state heap withBit saved tape 6)=
          some ⟨state heap args saved tape 7,[],0⟩ := by
        cases r
        simp [withBit,args,state,program,tickNatural,Registers.get,Registers.set,hp]
      have callTail : tickNatural program (state heap args saved tape 7)=
          some ⟨state heap args (frame::saved) tape 0,[],0⟩ := rfl
      have tailRep : BoolList heap args.a flags := by cases r; exact ht
      have levelRep : BoolList heap args.b L.bits := by cases r; exact level
      obtain ⟨et,root,hprior,hrec⟩ := ih tailRep levelRep frame saved
      let mid := heap++et
      let returned := args.set .r3 root
      have pre : NaturalRun program (buildSteps flags+4) (state heap r saved tape 0) []
          (state mid returned saved tape 8) :=
        .step branch (.step readFlag (.step readTail (.step callTail hrec)))
      have htag := lookup_extend hb et
      cases bit with
      | false =>
        have test : tickNatural program (state mid returned saved tape 8)=
            some ⟨state mid returned saved tape 4,[],0⟩ := by
          cases r
          simp [returned,args,withBit,mid,state,program,tickNatural,Registers.get,Registers.set,tagBranch,htag]
        have ret : tickNatural program (state mid returned saved tape 4)=
            some ⟨state mid (caller.saved.set caller.destination root) stack tape caller.continuation,[],0⟩ := by
          cases r
          simp [returned,args,withBit,saved,state,program,tickNatural,Registers.get,Registers.set]
        exact ⟨et,root,by simpa only [activeCount_cons,Bool.toNat_false,Nat.add_zero] using hprior,
          join pre (.step test (.step ret (.done _)))⟩
      | true =>
        have test : tickNatural program (state mid returned saved tape 8)=
            some ⟨state mid returned saved tape 10,[],0⟩ := by
          cases r
          simp [returned,args,withBit,mid,state,program,tickNatural,Registers.get,Registers.set,tagBranch,htag]
        have hs := hprior
        obtain ⟨old,mix,_,_,hroot,_,hcount,_,_⟩ := hs
        let work := returned.set .r0 old
        let finc : Frame ℕ 56 := ⟨12,.r0,work⟩
        have load : tickNatural program (state mid returned saved tape 10)=
            some ⟨state mid work saved tape 11,[],0⟩ := by
          have keptPair : mid[root]?=some (.pair old mix) := hroot
          cases r
          simp [work,returned,args,withBit,state,program,tickNatural,Registers.get,Registers.set]
          rw [keptPair]
        have callInc : tickNatural program (state mid work saved tape 11)=
            some ⟨state mid work (finc::saved) tape (incLabel 15),[],0⟩ := rfl
        have counter : BoolList mid work.a (activeCount flags).bits := by
          cases r
          exact hcount
        obtain ⟨ei,nc,hnew,inc⟩ := increment_return counter finc saved tape
        let grown := mid++ei
        let next := work.set .r0 nc
        have hcounter : BoolList grown next.a (activeCount flags+1).bits := by cases r; exact hnew
        have hlevel : BoolList grown next.b L.bits := by
          cases r
          exact boolList_extend (boolList_extend level et) ei
        have hkeep : ScheduleAt grown next.d L (activeCount flags) := by
          cases r
          exact schedule_extend hprior ei
        obtain ⟨ex,answer,hrep,hf⟩ := add_bound hcounter hlevel hkeep caller stack tape
        refine ⟨et++ei++ex,answer,?_,?_⟩
        · simpa only [activeCount_cons,Bool.toNat_true,grown,mid,List.append_assoc] using hrep
        · have trace := join pre (.step test (.step load (.step callInc (join inc hf))))
          simp only [buildSteps,ite_true]
          convert trace using 1 <;> first | rfl | omega | simp only [grown,mid,List.append_assoc]

def steps (flags : Bits) : ℕ := buildSteps flags + 6*activeCount flags + 8

theorem natural_schedule {heap : NaturalHeap} {r : Registers ℕ} {L : ℕ} {flags : Bits} (positive : 0<L)
    (input : BoolList heap r.a flags) (level : BoolList heap r.b L.bits) (tape : Bits) :
    ∃ ext root regs, regs.d=root ∧
      WordList (heap++ext) root (PhysicalEpochDraws.epochBounds L positive (activeCount flags)) ∧
      NaturalRun program (steps flags) (state heap r [] tape 36) []
        (state (heap++ext) regs [] tape 31) := by
  let frame : Frame ℕ 56 := ⟨37,.r3,r⟩
  obtain ⟨eb,root,hs,hbody⟩ := build_return input level frame [] tape
  let mid := heap++eb
  let regs := r.set .r3 root
  obtain ⟨_,group,p,c,hroot,hgroup,_,hp,hc⟩ := hs
  let r38 := regs.set .r0 group
  let r39 := r38.set .r1 c
  let args := r39.set .r0 p
  let appendFrame : Frame ℕ 56 := ⟨31,.r3,args⟩
  have callBuild : tickNatural program (state heap r [] tape 36)=some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  have groupField : tickNatural program (state mid regs [] tape 37)=
      some ⟨state mid r38 [] tape 38,[],0⟩ := by
    cases r
    simp [r38,regs,mid,state,program,tickNatural,Registers.get,Registers.set,hroot]
  have rightField : tickNatural program (state mid r38 [] tape 38)=
      some ⟨state mid r39 [] tape 39,[],0⟩ := by
    cases r
    simp [r39,r38,regs,mid,state,program,tickNatural,Registers.get,Registers.set,hgroup]
  have leftField : tickNatural program (state mid r39 [] tape 39)=
      some ⟨state mid args [] tape 30,[],0⟩ := by
    cases r
    simp [args,r39,r38,regs,mid,state,program,tickNatural,Registers.get,Registers.set,hgroup]
  have callAppend : tickNatural program (state mid args [] tape 30)=
      some ⟨state mid args [appendFrame] tape 24,[],0⟩ := rfl
  have hperms : WordList mid args.a (permutationWords (activeCount flags)) := by cases r; exact hp
  have hcells : WordList mid args.b (List.replicate (activeCount flags) L.bits) := by cases r; exact hc
  obtain ⟨ea,result,hrep,hjoin⟩ := append_return hperms hcells appendFrame [] tape
  refine ⟨eb++ea,result,args.set .r3 result,rfl,?_,?_⟩
  · simpa only [PhysicalEpochDraws.epochBounds,permutationWords,PhysicalEpochDraws.cellBounds,
      List.map_append,List.map_replicate,mid,List.append_assoc] using hrep
  · have trace := NaturalRun.step callBuild (join hbody (.step groupField
        (.step rightField (.step leftField (.step callAppend hjoin)))))
    rw [permutationWords_length] at trace
    unfold steps
    convert trace using 1 <;> first | rfl | omega | simp only [mid,List.append_assoc,appendFrame]

def instructionBound (n : ℕ) : ℕ := n*(8*n+29)+13

theorem steps_le (flags : Bits) : steps flags ≤ instructionBound flags.length := by
  have aux (bs : Bits) (M : ℕ) (hM : bs.length ≤ M) : buildSteps bs ≤ bs.length*(8*M+23)+5 := by
    induction bs with
    | nil => simp [buildSteps]
    | cons b bs ih =>
      have hsub : bs.length ≤ M := by simp only [List.length_cons] at hM; omega
      have hc := (activeCount_le bs).trans hsub
      have hl : (activeCount bs).bits.length ≤ M := by
        rw [Nat.size_eq_bits_len]
        exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans hc
      have hincrement := BinaryIncrementProgram.steps_bound (activeCount bs).bits
      have htail := ih hsub
      simp only [buildSteps,List.length_cons,Nat.add_mul,Nat.one_mul]
      split <;> omega
  have h := aux flags flags.length le_rfl
  have count := activeCount_le flags
  unfold steps instructionBound
  nlinarith

theorem active_eq {n : ℕ} (a : RetainedGridState.PairFlags n) :
    activeCount ((RetainedMassTableProgram.pairOrder n).map (RetainedGridState.flag a)) =
      Fintype.card ↥(RetainedGridState.remainingSet a) := by
  let pairs := RetainedMassTableProgram.pairOrder n
  let active := pairs.filter (RetainedGridState.flag a)
  have nodup : pairs.Nodup := (List.nodup_finRange _).product (List.nodup_finRange _)
  have hset : active.toFinset=RetainedGridState.remainingSet a := by
    ext p
    rcases p with ⟨i,j⟩
    simp [active,pairs,RetainedMassTableProgram.pairOrder,List.mem_finRange]
  have hlength : activeCount (pairs.map (RetainedGridState.flag a))=active.length := by
    simp [activeCount,List.filter_map,active]
  rw [hlength,Fintype.card_coe,← hset,List.toFinset_card_of_nodup (nodup.filter _)]

private theorem at_entry (s : NaturalState 56) (hp : s.pc=36) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s = state s.heap s.registers [] s.source 36 := by
  cases s
  simp_all [state]

theorem physical_schedule {H A L : ℕ} {flags : Bits} (positive : 0<L) (initial : BitState 56)
    (bounded : initial.Bounded H A) (hp : initial.pc=36) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (input : BoolList (eraseState initial).heap (eraseState initial).registers.a flags)
    (level : BoolList (eraseState initial).heap (eraseState initial).registers.b L.bits) :
    ∃ charge out, Run program (steps flags) charge initial [] out ∧
      WordList (eraseState out).heap (eraseState out).registers.d
        (PhysicalEpochDraws.epochBounds L positive (activeCount flags)) ∧
      out.source=initial.source ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=31 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤
        completeBound 56 H A (instructionBound flags.length) := by
  let old := eraseState initial
  obtain ⟨ext,root,r,hr,hrep,hbody⟩ := natural_schedule positive input level old.source
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  let final := state (old.heap++ext) r [] old.source 31
  have trace : NaturalRun program (steps flags) old [] final := by
    rw [at_entry old hp empty hn]
    exact hbody
  have halt : tickNatural program final=none := rfl
  obtain ⟨charge,out,hactual,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace halt
  refine ⟨charge,out,hactual,?_,htape,?_,?_,⟨ext,?_⟩,hstop,hcharge.trans ?_⟩
  · rw [hout]
    change WordList (old.heap++ext) r.d _
    rw [hr]
    exact hrep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl
  · have k := steps_le flags
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.RetainedEpochScheduleProgram
