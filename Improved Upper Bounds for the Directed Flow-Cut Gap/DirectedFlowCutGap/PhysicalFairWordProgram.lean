import DirectedFlowCutGap.PackedBooleanConstructor
import DirectedFlowCutGap.ImmutableReferenceTerminal

/-!
# Fair word in request order

The supplied spine controls the number of requests. Each request is an
interpreter instruction. On return, the first request is the low bit of
the stored word. The trace records even the machine's default false bits
when the physical source is exhausted.
-/

namespace DirectedFlowCutGap.PhysicalFairWordProgram

open BinaryArithmetic BooleanTableRead ImmutableReferenceSimulation ImmutableReferenceTerminal
open PackedBooleanConstructor

def program : Program 10 := fun pc =>
  match pc.val with
  | 0 => .branch .r0 1 9 9 2
  | 1 => .make .r3 .nil 5
  | 2 => .request .r2 3
  | 3 => .field .r0 .r0 true 4
  | 4 => .call 0 6 .r3
  | 5 => .ret .r3
  | 6 => .make .r3 (.pair .r2 .r3) 5
  | 8 => .call 0 9 .r3
  | _ => .halt

def state (heap : NaturalHeap) (registers : Registers ℕ) (stack : List (Frame ℕ 10))
    (tape : Bits) (pc : Fin 10) : NaturalState 10 :=
  ⟨heap,heap.length,registers,stack,pc,tape⟩

def digits : ℕ → Bits → Bits
  | 0, _ => []
  | k+1, tape => tape.headD false :: digits k tape.tail

theorem digits_length (k : ℕ) (tape : Bits) : (digits k tape).length = k := by
  induction k generalizing tape with
  | zero => rfl
  | succ k ih => simp [digits,ih]

theorem digits_eq_take (k : ℕ) (tape : Bits) (enough : k ≤ tape.length) :
    digits k tape = tape.take k := by
  induction k generalizing tape with
  | zero => rfl
  | succ k ih =>
    cases tape with
    | nil => simp at enough
    | cons bit tail =>
      have ht : k ≤ tail.length := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using enough
      simp only [digits,List.headD_cons,List.tail_cons,List.take_succ_cons,ih tail ht]

def instructions (k : ℕ) : ℕ := 6*k+3

theorem word_return {heap : NaturalHeap} {r : Registers ℕ} {k : ℕ}
    (width : IndexSpine heap r.a k) (caller : Frame ℕ 10) (stack : List (Frame ℕ 10)) (tape : Bits) :
    ∃ ext root, BoolList (heap++ext) root (digits k tape) ∧ ext.length=2*k+1 ∧
      NaturalRun program (instructions k) (state heap r (caller::stack) tape 0)
        ((digits k tape).map Event.request)
        (state (heap++ext) (caller.saved.set caller.destination root) stack (tape.drop k) caller.continuation) := by
  induction k generalizing heap r caller stack tape with
  | zero =>
    cases width with
    | nil hn =>
      let saved := caller::stack
      let ext : NaturalHeap := [.nil]
      let result := heap.length
      let finish := state (heap++ext) (r.set .r3 result) saved tape 5
      have test : tickNatural program (state heap r saved tape 0) =
          some ⟨state heap r saved tape 1,[],0⟩ := by
        simp [state,tickNatural,program,Registers.get,tagBranch,hn]
      have alloc : tickNatural program (state heap r saved tape 1) = some ⟨finish,[],0⟩ := by
        simp [finish,ext,result,state,tickNatural,program,allocateNatural,Recipe.cell]
      have ret : tickNatural program finish = some
          ⟨state (heap++ext) (caller.saved.set caller.destination result) stack tape caller.continuation,[],0⟩ := by
        cases r
        simp [finish,saved,state,tickNatural,program,Registers.get,Registers.set]
      exact ⟨ext,result,.nil (by simp [ext,result]),rfl,.step test (.step alloc (.step ret (.done _)))⟩
  | succ k ih =>
    cases width with
    | @cons _ payload tail _ hp htail =>
      let saved := caller::stack
      let bit := tape.headD false
      let extra : NaturalHeap := [.flag bit]
      let grown := heap++extra
      let fresh := heap.length
      let r1 := r.set .r2 fresh
      let args := r1.set .r0 tail
      let frame : Frame ℕ 10 := ⟨6,.r3,args⟩
      have test : tickNatural program (state heap r saved tape 0) =
          some ⟨state heap r saved tape 2,[],0⟩ := by
        simp [state,tickNatural,program,Registers.get,tagBranch,hp]
      have request : tickNatural program (state heap r saved tape 2) =
          some ⟨state grown r1 saved tape.tail 3,[.request bit],0⟩ := by
        simp [grown,extra,bit,r1,fresh,state,tickNatural,program,allocateNatural]
      have advance : tickNatural program (state grown r1 saved tape.tail 3) =
          some ⟨state grown args saved tape.tail 4,[],0⟩ := by
        have kept := lookup_extend hp extra
        cases r
        simp [r1,args,grown,state,tickNatural,program,Registers.get,Registers.set,kept]
      have call : tickNatural program (state grown args saved tape.tail 4) =
          some ⟨state grown args (frame::saved) tape.tail 0,[],0⟩ := rfl
      have tailSpine : IndexSpine grown args.a k := by
        cases r
        exact indexSpine_extend htail extra
      obtain ⟨next,low,hbits,hlen,hwork⟩ := ih tailSpine frame saved tape.tail
      let mid := grown++next
      let suffix := tape.tail.drop k
      let lastCell : Cell ℕ := .pair fresh low
      let root := mid.length
      let finish := state (mid++[lastCell]) (args.set .r3 root) saved suffix 5
      have alloc : tickNatural program (state mid (args.set .r3 low) saved suffix 6) =
          some ⟨finish,[],0⟩ := by
        cases r
        simp [finish,lastCell,root,args,r1,state,tickNatural,program,Registers.get,Registers.set,allocateNatural,Recipe.cell]
      have ret : tickNatural program finish =
          some ⟨state (mid++[lastCell]) (caller.saved.set caller.destination root) stack suffix caller.continuation,[],0⟩ := by
        cases r
        simp [finish,args,r1,saved,state,tickNatural,program,Registers.get,Registers.set]
      have mark : (mid++[lastCell])[fresh]? = some (.flag bit) :=
        lookup_extend (lookup_extend (by simp [grown,extra,fresh]) next) [lastCell]
      have hresult : BoolList (mid++[lastCell]) root (digits (k+1) tape) := by
        exact .cons (by simp [root,lastCell]) mark (boolList_extend hbits [lastCell])
      refine ⟨extra++next++[lastCell],root,?_,?_,?_⟩
      · simpa only [mid,grown,List.append_assoc] using hresult
      · simp only [List.length_append,List.length_singleton,extra,hlen]
        omega
      · have work := NaturalRun.step test (NaturalRun.step request (NaturalRun.step advance
            (NaturalRun.step call (join hwork (.step alloc (.step ret (.done _)))))))
        simp only [digits,List.map_cons,instructions] at work ⊢
        rw [← List.drop_tail]
        convert work using 1 <;> first | rfl | omega |
          (simp only [mid,grown,List.append_assoc,List.append_nil,List.nil_append]; rfl)
where
  join {s u v : NaturalState 10} {k l : ℕ} {e f : List Event}
      (h : NaturalRun program k s e u) (hg : NaturalRun program l u f v) :
      NaturalRun program (k+l) s (e++f) v := by
    induction h with
    | done _ => simpa using hg
    | step ht _ ih =>
      simpa only [List.append_assoc,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm 1] using NaturalRun.step ht (ih hg)

theorem natural_word {heap : NaturalHeap} {r : Registers ℕ} {k : ℕ}
    (width : IndexSpine heap r.a k) (tape : Bits) :
    ∃ ext root, BoolList (heap++ext) root (digits k tape) ∧ ext.length=2*k+1 ∧
      NaturalRun program (instructions k+1) (state heap r [] tape 8)
        ((digits k tape).map Event.request) (state (heap++ext) (r.set .r3 root) [] (tape.drop k) 9) := by
  let frame : Frame ℕ 10 := ⟨9,.r3,r⟩
  obtain ⟨ext,root,rep,hlen,hbody⟩ := word_return width frame [] tape
  have call : tickNatural program (state heap r [] tape 8) =
      some ⟨state heap r [frame] tape 0,[],0⟩ := rfl
  exact ⟨ext,root,rep,hlen,.step call hbody⟩

private theorem at_entry (s : NaturalState 10) (hp : s.pc=8) (hc : s.stack=[])
    (hn : s.next=s.heap.length) : s = state s.heap s.registers [] s.source 8 := by
  cases s
  simp_all [state]

theorem physical_word {k H A : ℕ} (initial : BitState 10) (bound : initial.Bounded H A)
    (hp : initial.pc=8) (hc : initial.stack=[])
    (hn : (eraseState initial).next=(eraseState initial).heap.length)
    (width : IndexSpine (eraseState initial).heap (eraseState initial).registers.a k) :
    ∃ charge out, Run program (instructions k+1) charge initial ((digits k initial.source).map Event.request) out ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (digits k initial.source) ∧
      out.source=initial.source.drop k ∧ (eraseState out).stack=[] ∧ (eraseState out).pc=9 ∧
      (∃ ext,(eraseState out).heap=(eraseState initial).heap++ext ∧ ext.length=2*k+1) ∧
      (attempt program out).result=none ∧ charge+(attempt program out).operations ≤ completeBound 10 H A (6*k+4) := by
  let old := eraseState initial
  obtain ⟨ext,root,rep,hlen,hbody⟩ := natural_word width old.source
  have empty : old.stack=[] := by simp [old,eraseState,State.map,hc]
  let final := state (old.heap++ext) (old.registers.set .r3 root) [] (old.source.drop k) 9
  have trace : NaturalRun program (instructions k+1) old ((digits k initial.source).map Event.request) final := by
    rw [at_entry old hp empty hn]
    exact hbody
  have halt : tickNatural program final = none := rfl
  obtain ⟨charge,out,hactual,hout,hstop,hcharge,htape⟩ := terminating_simulation bound trace halt
  refine ⟨charge,out,hactual,?_,htape,?_,?_,⟨ext,?_,hlen⟩,hstop,hcharge⟩
  · rw [hout]; exact rep
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; rfl

end DirectedFlowCutGap.PhysicalFairWordProgram
