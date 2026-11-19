import DirectedFlowCutGap.PhysicalBoundedDrawExecution

/-!
# A finite sequence of physical bounded draws

The program shares one represented trial budget across the supplied list
of bounds. It processes the bounds in order, leaving each draw record in
the returned list. Each recursive call receives the unread tape left by
the preceding draw.
-/

namespace DirectedFlowCutGap.PhysicalDrawSequenceProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor
open PhysicalBoundedDrawProgram (Outcome outcome ResultAt)
open PathCostMaterialization (WordList)

def drawLabel (pc : Fin 78) : Fin 94 := ⟨16+pc.val,by omega⟩

def program : Program 94 := fun pc =>
  if pc.val < 16 then
    match pc.val with
    | 0 => .branch .r0 1 15 15 4
    | 1 => .make .r3 .nil 2
    | 2 => .ret .r3
    | 4 => .field .r2 .r0 false 5
    | 5 => .call 10 6 .r2
    | 6 => .field .r0 .r0 true 7
    | 7 => .call 0 8 .r3
    | 8 => .make .r3 (.pair .r2 .r3) 2
    | 10 => .move .r0 .r2 11
    | 11 => .call (drawLabel 18) 12 .r3
    | 12 => .ret .r3
    | 14 => .call 0 15 .r3
    | _ => .halt
  else if pc.val=35 then .ret .r3
  else ReferenceProgramLabels.instruction drawLabel
    (PhysicalBoundedDrawProgram.program ⟨pc.val-16,by have := pc.isLt; omega⟩)

def state (heap : NaturalHeap) (registers : Registers ℕ) (stack : List (Frame ℕ 94))
    (tape : Bits) (pc : Fin 94) : NaturalState 94 :=
  ⟨heap,heap.length,registers,stack,pc,tape⟩

structure Batch where
  draws : List Outcome
  requests : Bits
  suffix : Bits

def batch (fuel : ℕ) : List Bits → Bits → Batch
  | [],tape => ⟨[],[],tape⟩
  | bound::rest,tape =>
    let first := outcome bound fuel tape
    let later := batch fuel rest first.suffix
    ⟨first::later.draws,first.requests++later.requests,later.suffix⟩

def steps (fuel : ℕ) : List Bits → Bits → ℕ
  | [],_ => 3
  | bound::rest,tape =>
    let first := outcome bound fuel tape
    PhysicalBoundedDrawProgram.instructions bound fuel tape+steps fuel rest first.suffix+12

inductive StoredBatch (heap : NaturalHeap) : ℕ → List Outcome → Prop
  | nil {p : ℕ} : heap[p]?=some .nil → StoredBatch heap p []
  | cons {p x tail : ℕ} {first : Outcome} {rest : List Outcome} :
    heap[p]?=some (.pair x tail) → ResultAt heap x first → StoredBatch heap tail rest →
      StoredBatch heap p (first::rest)

private theorem outcome_extend {heap : NaturalHeap} {root : ℕ} {out : Outcome} (h : ResultAt heap root out)
    (ext : NaturalHeap) : ResultAt (heap++ext) root out := by
  obtain ⟨x,tag,hp,hx,ht⟩ := h
  exact ⟨x,tag,lookup_extend hp ext,boolList_extend hx ext,lookup_extend ht ext⟩

theorem batch_extend {heap : NaturalHeap} {root : ℕ} {results : List Outcome}
    (h : StoredBatch heap root results) (ext : NaturalHeap) : StoredBatch (heap++ext) root results := by
  induction h with
  | nil hp => exact .nil (lookup_extend hp ext)
  | cons hp hresult _ ih => exact .cons (lookup_extend hp ext) (outcome_extend hresult ext) ih

private theorem draw_slots (pc : Fin 78) (h : PhysicalBoundedDrawProgram.program pc≠.halt) :
    program (drawLabel pc) =
      ReferenceProgramLabels.instruction drawLabel (PhysicalBoundedDrawProgram.program pc) := by
  by_cases hp : pc.val=19
  · have eq : pc=19 := Fin.ext hp
    subst pc
    exact (h rfl).elim
  · simp [program,drawLabel,show ¬16+pc.val<16 by omega,show 16+pc.val≠35 by omega]

private theorem join {s u v : NaturalState 94} {k l : ℕ} {e f : List Event}
    (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
    NaturalRun program (k+l) s (e++f) v := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem read_one {heap : NaturalHeap} {r : Registers ℕ} {bound : Bits} {fuel : ℕ}
    (word : BoolList heap r.c bound) (trials : IndexSpine heap r.b fuel)
    (caller : Frame ℕ 94) (stack : List (Frame ℕ 94)) (tape : Bits) :
    let first := outcome bound fuel tape
    ∃ ext root,ResultAt (heap++ext) root first ∧
      NaturalRun program (PhysicalBoundedDrawProgram.instructions bound fuel tape+5)
        (state heap r (caller::stack) tape 10) (first.requests.map Event.request)
        (state (heap++ext) (caller.saved.set caller.destination root) stack first.suffix caller.continuation) := by
  let saved := caller::stack
  let args := r.set .r0 r.c
  let frame : Frame ℕ 94 := ⟨12,.r3,args⟩
  have operand : BoolList heap args.a bound := by cases r; exact word
  have count : IndexSpine heap args.b fuel := by cases r; exact trials
  obtain ⟨ext,root,hrep,hrun⟩ := PhysicalBoundedDrawProgram.natural_draw operand count tape
  let first := outcome bound fuel tape
  let before := state (heap++ext) (args.set .r3 root) (frame::saved) first.suffix (drawLabel 19)
  let after := state (heap++ext) (args.set .r3 root) saved first.suffix 12
  let final := state (heap++ext) (caller.saved.set caller.destination root) stack first.suffix caller.continuation
  have lift := ReferenceProgramLabels.run drawLabel PhysicalBoundedDrawProgram.program program draw_slots hrun
  have lift := ReferenceProgramStack.run program (frame::saved) lift
  have body : NaturalRun program (PhysicalBoundedDrawProgram.instructions bound fuel tape+1)
      (state heap args (frame::saved) tape (drawLabel 18)) (first.requests.map Event.request) before := by
    simpa [state,before,PhysicalBoundedDrawProgram.state,ReferenceProgramLabels.state,ReferenceProgramStack.state] using lift
  have move : tickNatural program (state heap r saved tape 10) = some ⟨state heap args saved tape 11,[],0⟩ := rfl
  have call : tickNatural program (state heap args saved tape 11) =
      some ⟨state heap args (frame::saved) tape (drawLabel 18),[],0⟩ := rfl
  have ret : tickNatural program before=some ⟨after,[],0⟩ := by
    cases r
    simp [before,after,state,program,drawLabel,tickNatural,frame,Registers.get,Registers.set,args]
  have endCall : tickNatural program after=some ⟨final,[],0⟩ := by
    cases r
    simp [after,final,state,program,tickNatural,saved,Registers.get,Registers.set,args]
  refine ⟨ext,root,hrep,?_⟩
  simpa only [List.append_nil,List.nil_append,first] using
    NaturalRun.step move (NaturalRun.step call (join body (.step ret (.step endCall (.done final)))))

theorem batch_return {heap : NaturalHeap} {r : Registers ℕ} {bounds : List Bits} {fuel : ℕ}
    (words : WordList heap r.a bounds) (trials : IndexSpine heap r.b fuel)
    (caller : Frame ℕ 94) (stack : List (Frame ℕ 94)) (tape : Bits) :
    let out := batch fuel bounds tape
    ∃ ext root, StoredBatch (heap++ext) root out.draws ∧
      NaturalRun program (steps fuel bounds tape) (state heap r (caller::stack) tape 0) (out.requests.map Event.request)
        (state (heap++ext) (caller.saved.set caller.destination root) stack out.suffix caller.continuation) := by
  induction bounds generalizing heap r caller stack tape with
  | nil =>
    cases words with
    | nil hn =>
      let saved := caller::stack
      let ext : NaturalHeap := [.nil]
      let fresh := heap.length
      let last := state (heap++ext) (r.set .r3 fresh) saved tape 2
      have test : tickNatural program (state heap r saved tape 0) =
          some ⟨state heap r saved tape 1,[],0⟩ := by
        simp [state,tickNatural,program,Registers.get,tagBranch,hn]
      have alloc : tickNatural program (state heap r saved tape 1) = some ⟨last,[],0⟩ := by
        simp [last,ext,fresh,state,tickNatural,program,allocateNatural,Recipe.cell]
      have ret : tickNatural program last =
          some ⟨state (heap++ext) (caller.saved.set caller.destination fresh) stack tape caller.continuation,[],0⟩ := by
        cases r
        simp [last,saved,state,tickNatural,program,Registers.get,Registers.set]
      exact ⟨ext,fresh,.nil (by simp [ext,fresh]),.step test (.step alloc (.step ret (.done _)))⟩
  | cons bound bs ih =>
    cases words with
    | @cons _ head tail _ _ hp hw htail =>
      let saved := caller::stack
      let firstArgs := r.set .r2 head
      let fdraw : Frame ℕ 94 := ⟨6,.r2,firstArgs⟩
      let first := outcome bound fuel tape
      have start : tickNatural program (state heap r saved tape 0) =
          some ⟨state heap r saved tape 4,[],0⟩ := by
        simp [state,tickNatural,program,Registers.get,tagBranch,hp]
      have field : tickNatural program (state heap r saved tape 4) =
          some ⟨state heap firstArgs saved tape 5,[],0⟩ := by
        simp [firstArgs,state,tickNatural,program,Registers.get,hp]
      have hcall : tickNatural program (state heap firstArgs saved tape 5) =
          some ⟨state heap firstArgs (fdraw::saved) tape 10,[],0⟩ := rfl
      have firstWord : BoolList heap firstArgs.c bound := by cases r; exact hw
      have firstSpine : IndexSpine heap firstArgs.b fuel := by cases r; exact trials
      obtain ⟨ef,index,hrep,hdraw⟩ := read_one firstWord firstSpine fdraw saved tape
      let mid := heap++ef
      let sampled := firstArgs.set .r2 index
      let nextArgs := sampled.set .r0 tail
      let fnext : Frame ℕ 94 := ⟨8,.r3,nextArgs⟩
      have advance : tickNatural program (state mid sampled saved first.suffix 6) =
          some ⟨state mid nextArgs saved first.suffix 7,[],0⟩ := by
        have he := lookup_extend hp ef
        cases r
        simp [nextArgs,sampled,firstArgs,mid,state,tickNatural,program,Registers.get,Registers.set,he]
      have callTail : tickNatural program (state mid nextArgs saved first.suffix 7) =
          some ⟨state mid nextArgs (fnext::saved) first.suffix 0,[],0⟩ := rfl
      have tailWords : WordList mid nextArgs.a bs := by
        cases r
        exact PathCostMaterialization.list_extend htail ef
      have tailTrials : IndexSpine mid nextArgs.b fuel := by
        cases r
        exact indexSpine_extend trials ef
      obtain ⟨et,rest,hrest,hnext⟩ := ih tailWords tailTrials fnext saved first.suffix
      let later := batch fuel bs first.suffix
      let grown := mid++et
      let fresh := grown.length
      let cell : Cell ℕ := .pair index rest
      let outHeap := grown++[cell]
      let after := nextArgs.set .r3 rest
      let last := state outHeap (nextArgs.set .r3 fresh) saved later.suffix 2
      have alloc : tickNatural program (state grown after saved later.suffix 8) =
          some ⟨last,[],0⟩ := by
        cases r
        simp [last,outHeap,cell,fresh,after,nextArgs,sampled,firstArgs,state,tickNatural,program,
          Registers.get,Registers.set,allocateNatural,Recipe.cell]
      have ret : tickNatural program last = some
          ⟨state outHeap (caller.saved.set caller.destination fresh) stack later.suffix caller.continuation,[],0⟩ := by
        cases r
        simp [last,saved,nextArgs,sampled,firstArgs,state,tickNatural,program,Registers.get,Registers.set]
      have result : StoredBatch outHeap fresh (first::later.draws) :=
        .cons (by simp [outHeap,fresh,cell]) (outcome_extend (outcome_extend hrep et) [cell])
          (batch_extend hrest [cell])
      refine ⟨ef++et++[cell],fresh,?_,?_⟩
      · simpa only [outHeap,grown,mid,batch,first,later,List.append_assoc] using result
      · have trace := NaturalRun.step start (NaturalRun.step field (NaturalRun.step hcall
          (join hdraw (NaturalRun.step advance (NaturalRun.step callTail (join hnext
            (.step alloc (.step ret (.done _)))))))))
        simp only [steps,batch,List.map_append]
        dsimp only [first,later] at trace
        convert trace using 1 <;> first | rfl | omega |
          simp only [outHeap,grown,mid,List.append_assoc,List.append_nil,List.nil_append]

theorem batch_suffix (fuel : ℕ) (bounds : List Bits) (tape : Bits) :
    let out := batch fuel bounds tape
    out.suffix=tape.drop out.requests.length := by
  induction bounds generalizing tape with
  | nil => rfl
  | cons bound rest ih =>
    let first := outcome bound fuel tape
    let later := batch fuel rest first.suffix
    have h := (PhysicalBoundedDrawProgram.exact_requests bound fuel tape).2.1
    change first.suffix=tape.drop first.requests.length at h
    change later.suffix=tape.drop (first.requests++later.requests).length
    have hl : later.suffix=first.suffix.drop later.requests.length := ih first.suffix
    rw [hl,h,List.drop_drop,List.length_append]

def instructionBound (width fuel count : ℕ) : ℕ :=
  count*(PhysicalBoundedDrawProgram.instructionBound width fuel+12)+4

theorem steps_le (fuel width : ℕ) (bounds : List Bits) (tape : Bits)
    (widths : ∀ x ∈ bounds, x.length ≤ width) :
    steps fuel bounds tape + 1 ≤ instructionBound width fuel bounds.length := by
  have h (bs : List Bits) (t : Bits) (hw : ∀ x ∈ bs, x.length ≤ width) :
      steps fuel bs t ≤ bs.length*(PhysicalBoundedDrawProgram.instructionBound width fuel+12)+3 := by
    induction bs generalizing t with
    | nil => simp [steps]
    | cons x xs ih =>
      have hwidth := hw x List.mem_cons_self
      have head := (PhysicalBoundedDrawProgram.instructions_le x fuel t).trans
        (show PhysicalBoundedDrawProgram.instructionBound x.length fuel ≤
          PhysicalBoundedDrawProgram.instructionBound width fuel by
          unfold PhysicalBoundedDrawProgram.instructionBound
          gcongr)
      have later := ih (outcome x fuel t).suffix (fun b hb => hw b (List.mem_cons_of_mem _ hb))
      simp only [steps,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  simpa only [instructionBound,Nat.add_assoc] using Nat.add_le_add_right (h bounds tape widths) 1

theorem natural_batch {heap : NaturalHeap} {r : Registers ℕ} {bounds : List Bits} {fuel : ℕ}
    (words : WordList heap r.a bounds) (trials : IndexSpine heap r.b fuel) (tape : Bits) :
    let out := batch fuel bounds tape
    ∃ ext root, StoredBatch (heap++ext) root out.draws ∧
      NaturalRun program (steps fuel bounds tape+1) (state heap r [] tape 14) (out.requests.map Event.request)
        (state (heap++ext) (r.set .r3 root) [] out.suffix 15) := by
  let frame : Frame ℕ 94 := ⟨15,.r3,r⟩
  obtain ⟨ext,root,hrep,hrun⟩ := batch_return words trials frame [] tape
  have call : tickNatural program (state heap r [] tape 14) = some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,hrep,.step call hrun⟩

private theorem at_entry (s : NaturalState 94) (hp : s.pc=14) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s = state s.heap s.registers [] s.source 14 := by
  cases s
  simp_all [state]

theorem guarded_batch {H A W fuel : ℕ} {bounds : List Bits} (initial : BitState 94)
    (bounded : initial.Bounded H A) (hp : initial.pc=14) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (words : WordList (eraseState initial).heap (eraseState initial).registers.a bounds)
    (trials : IndexSpine (eraseState initial).heap (eraseState initial).registers.b fuel)
    (widths : ∀ x ∈ bounds,x.length ≤ W) :
    let observed := batch fuel bounds initial.source
    let budget := instructionBound W fuel bounds.length
    let run := GuardedReferenceExecution.execute program (budget+1) initial 0
    if observed.requests.length ≤ initial.source.length then
      ∃ out charge, run=some (out,charge) ∧
        StoredBatch (eraseState out).heap (eraseState out).registers.d observed.draws ∧
        out.source=observed.suffix ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=15 ∧
        (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext) ∧
        charge ≤ completeBound 94 H A budget+(budget+1)*GuardedReferenceExecution.guardCost 94
    else run=none := by
  let old := eraseState initial
  let observed := batch fuel bounds initial.source
  let budget := instructionBound W fuel bounds.length
  obtain ⟨ext,root,hrep,hbody⟩ := natural_batch words trials old.source
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] observed.suffix 15
  have trace : NaturalRun program (steps fuel bounds initial.source+1) old
      (observed.requests.map Event.request) final := by
    rw [at_entry old hp empty hn]
    exact hbody
  have halt : tickNatural program final = none := rfl
  obtain ⟨q,out,hr,hout,hstop,hcharge,htape⟩ := terminating_simulation bounded trace halt
  have hsteps : steps fuel bounds initial.source+1 ≤ budget := steps_le fuel W bounds initial.source widths
  have hrun := GuardedReferenceExecution.execute_eq hr hstop (budget+1) 0 (by omega)
  rw [GuardedReferenceExecution.count_reads] at hrun
  change (if observed.requests.length ≤ initial.source.length then _ else _)
  by_cases enough : observed.requests.length ≤ initial.source.length
  · rw [ite_eq_left enough] at hrun ⊢
    refine ⟨out,_,hrun,?_,htape,?_,?_,⟨ext,?_⟩,?_⟩
    · rw [hout]; exact hrep
    · rw [hout]; rfl
    · rw [hout]; rfl
    · rw [hout]; rfl
    · have cost : q+(attempt program out).operations ≤ completeBound 94 H A budget := hcharge.trans (by
          unfold completeBound runBound stepBound
          gcongr)
      have guard := Nat.mul_le_mul_right (GuardedReferenceExecution.guardCost 94)
        (Nat.add_le_add_right hsteps 1)
      simpa only [Nat.zero_add] using Nat.add_le_add cost guard
  · rw [ite_eq_right enough] at hrun ⊢
    exact hrun

end DirectedFlowCutGap.PhysicalDrawSequenceProgram
