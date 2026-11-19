import DirectedFlowCutGap.ReferenceProgramSteps
import DirectedFlowCutGap.ConcreteExpressionProgram

/-!
# Count the true flags in a fixed-length cut-mask block

A unary limit controls the scan. The returned pair contains the original
suffix address and a new unary word list with one cell for each true flag.
The unary cells share a single false payload and can be counted by the
binary removal-mask counter.
-/

namespace DirectedFlowCutGap.CandidateCutBlockCountProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open ConcreteExpressionProgram (append_run)

def program : Program 32 := fun pc => match pc.val with
  | 0 => .make .r2 (.flag false) 1
  | 1 => .call 8 2 .r3
  | 8 => .branch .r1 9 31 31 12
  | 9 => .make .r3 (.pair .r0 .r1) 10
  | 10 => .ret .r3
  | 12 => .field .r3 .r0 false 13
  | 13 => .field .r0 .r0 true 14
  | 14 => .field .r1 .r1 true 15
  | 15 => .call 8 16 .r0
  | 16 => .branch .r3 31 17 18 31
  | 17 => .ret .r0
  | 18 => .field .r1 .r0 false 19
  | 19 => .field .r3 .r0 true 20
  | 20 => .make .r3 (.pair .r2 .r3) 21
  | 21 => .make .r3 (.pair .r1 .r3) 22
  | 22 => .ret .r3
  | _ => .halt

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 32))
    (tape : Bits) (pc : Fin 32) : NaturalState 32 := ⟨heap,heap.length,r,stack,pc,tape⟩

def Stored (heap : NaturalHeap) (root : ℕ) (remaining : Bits) (total : ℕ) : Prop :=
  ∃ tail units,heap[root]?=some (.pair tail units) ∧
    BoolList heap tail remaining ∧ BoolList heap units (List.replicate total false)

theorem stored_extend {heap : NaturalHeap} {root total : ℕ} {remaining : Bits}
    (h : Stored heap root remaining total) (extra : NaturalHeap) : Stored (heap++extra) root remaining total := by
  obtain ⟨tail,units,pair,rest,count⟩ := h
  exact ⟨tail,units,lookup_extend pair extra,boolList_extend rest extra,boolList_extend count extra⟩

def bodySteps : ℕ→Bits→ℕ
  | count+1,bit::bs => bodySteps count bs + if bit then 11 else 7
  | _,_ => 3

def steps (count : ℕ) (flags : Bits) : ℕ := bodySteps count flags+2

theorem steps_le (count : ℕ) (flags : Bits) : steps count flags≤11*count+5 := by
  have h (k : ℕ) (bs : Bits) : bodySteps k bs≤11*k+3 := by
    induction k generalizing bs with
    | zero => simp [bodySteps]
    | succ j ih =>
      cases bs with
      | nil => simp [bodySteps]
      | cons b bs => cases b <;> simp only [bodySteps,ite_true,ite_false,Bool.false_eq_true] <;> have h := ih bs <;> omega
  unfold steps
  have bound := h count flags
  omega

private theorem finish_true {heap : NaturalHeap} {r : Registers ℕ} {total : ℕ} {rest : Bits}
    (input : Stored heap r.a rest total) (payload : heap[r.c]?=some (.flag false))
    (caller : Frame ℕ 32) (stack : List (Frame ℕ 32)) (tape : Bits) :
    ∃ ext root,Stored (heap++ext) root rest (total+1) ∧
      NaturalRun program 5 (state heap r (caller::stack) tape 18) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  obtain ⟨tail,units,pair,mask,count⟩ := input
  let i := heap.length
  let one : Cell ℕ := .pair r.c units
  let result : Cell ℕ := .pair tail i
  let ext := [one,result]
  have out : (heap++ext)[i+1]?=some result := by
    rw [List.getElem?_append_right (show heap.length ≤ i+1 from Nat.le_succ _)]
    rw [show i+1-heap.length=1 by simp [i]]
    rfl
  have extra : BoolList (heap++ext) i (List.replicate (total+1) false) :=
    .cons (by simp [i,ext,one]) (lookup_extend payload ext) (boolList_extend count ext)
  refine ⟨ext,i+1,⟨tail,i,out,boolList_extend mask ext,extra⟩,?_⟩
  apply ReferenceProgramSteps.sound
  simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,
    allocateNatural,Recipe.cell,i,ext,one,result,pair,List.append_assoc,Nat.add_assoc]

private theorem block_return {heap : NaturalHeap} {r : Registers ℕ} {amount : ℕ} {flags : Bits}
    (input : BoolList heap r.a flags) (limit : IndexSpine heap r.b amount) (fits : amount≤flags.length)
    (payload : heap[r.c]?=some (.flag false)) (caller : Frame ℕ 32) (stack : List (Frame ℕ 32)) (tape : Bits) :
    ∃ ext root,Stored (heap++ext) root (flags.drop amount) ((flags.take amount).count true) ∧
      NaturalRun program (bodySteps amount flags) (state heap r (caller::stack) tape 8) []
        (state (heap++ext) (caller.saved.set caller.destination root) stack tape caller.continuation) := by
  induction amount generalizing heap r flags caller stack with
  | zero =>
    cases limit with
    | nil nilCount =>
      let ext : NaturalHeap := [.pair r.a r.b]
      let i := heap.length
      refine ⟨ext,i,⟨r.a,r.b,by simp [ext,i],?_,?_⟩,?_⟩
      · simpa only [List.drop_zero] using boolList_extend input ext
      · simpa using BoolList.nil (lookup_extend nilCount ext)
      · apply ReferenceProgramSteps.sound
        simp [ReferenceProgramSteps.run,state,program,bodySteps,tickNatural,Registers.get,Registers.set,
          allocateNatural,Recipe.cell,tagBranch,ext,i,nilCount]
  | succ k ih =>
    cases limit with
    | @cons _ _ next _ hnext remaining =>
      cases input with
      | nil nilInput => simp at fits
      | @cons _ head tail bit bs pair cell rest =>
        let saved := caller::stack
        let args := (((r.set .r3 head).set .r0 tail).set .r1 next)
        let recur : Frame ℕ 32 := ⟨16,.r0,args⟩
        have setup : NaturalRun program 5 (state heap r saved tape 8) [] (state heap args (recur::saved) tape 8) := by
          apply ReferenceProgramSteps.sound
          simp [ReferenceProgramSteps.run,state,program,tickNatural,Registers.get,Registers.set,
            tagBranch,args,recur,hnext,pair]
        have inside : k≤bs.length := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using fits
        obtain ⟨er,node,rep,body⟩ := ih (r:=args) rest remaining inside payload recur saved
        let mid := heap++er
        let received := args.set .r0 node
        have read : mid[head]?=some (.flag bit) := lookup_extend cell er
        have pick : tickNatural program (state mid received saved tape 16)=
            some ⟨state mid received saved tape (if bit then 18 else 17),[],0⟩ := by
          cases bit <;> simp [state,program,tickNatural,Registers.get,Registers.set,
            tagBranch,received,args,read]
        cases bit with
        | false =>
          have ret : tickNatural program (state mid received saved tape 17)=
              some ⟨state mid (caller.saved.set caller.destination node) stack tape caller.continuation,[],0⟩ := by
            simp [state,program,tickNatural,Registers.get,Registers.set,received,saved]
          refine ⟨er,node,?_,?_⟩
          · simpa [List.take_succ_cons,List.drop_succ_cons,List.count_cons] using rep
          · have trace := append_run setup (append_run body (.step pick (.step ret (.done _))))
            simp only [bodySteps,Bool.false_eq_true,ite_false]
            convert trace using 1 <;> first | rfl | omega
        | true =>
          obtain ⟨et,out,final,finish⟩ := finish_true (r:=received) rep (lookup_extend payload er) caller stack tape
          refine ⟨er++et,out,?_,?_⟩
          · simpa [mid,List.append_assoc,List.take_succ_cons,List.drop_succ_cons,List.count_cons] using final
          · have trace := append_run setup (append_run body (.step pick finish))
            simp only [bodySteps,ite_true]
            convert trace using 1 <;> first | rfl | omega | simp only [List.append_assoc]

theorem natural_block {heap : NaturalHeap} {r : Registers ℕ} {amount : ℕ} {flags : Bits}
    (input : BoolList heap r.a flags) (limit : IndexSpine heap r.b amount) (fits : amount≤flags.length)
    (tape : Bits) :
    ∃ (ext : NaturalHeap) (args : Registers ℕ) (root : ℕ),
      Stored (heap++ext) root (flags.drop amount) ((flags.take amount).count true) ∧
      NaturalRun program (steps amount flags) (state heap r [] tape 0) [] (state (heap++ext) (args.set .r3 root) [] tape 2) := by
  let extra : NaturalHeap := [.flag false]
  let mid := heap++extra
  let args := r.set .r2 heap.length
  let frame : Frame ℕ 32 := ⟨2,.r3,args⟩
  have setup : NaturalRun program 2 (state heap r [] tape 0) [] (state mid args [frame] tape 8) := by
    apply ReferenceProgramSteps.sound
    simp [ReferenceProgramSteps.run,state,program,tickNatural,allocateNatural,Recipe.cell,mid,extra,args,frame]
  have payload : mid[args.c]?=some (.flag false) := by simp [mid,extra,args,Registers.set]
  obtain ⟨ext,root,rep,body⟩ := block_return (r:=args) (boolList_extend input extra) (indexSpine_extend limit extra)
    fits payload frame [] tape
  refine ⟨extra++ext,args,root,?_,?_⟩
  · simpa only [mid,List.append_assoc] using rep
  · have trace := append_run setup body
    unfold steps
    convert trace using 1 <;> first | rfl | omega | simp only [frame,List.append_assoc]

end DirectedFlowCutGap.CandidateCutBlockCountProgram
