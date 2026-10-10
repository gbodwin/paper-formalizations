import DirectedFlowCutGap.EncodedSequenceAccess

/-!
# One fixed immutable-reference copy procedure

This is the first structural anchor for the assessed finite-list model. The
seven-instruction program is fixed before every word, heap and caller. Its
interpreter has only tag/field reads, reference movement, a fixed recursive
call, fresh cons allocation and return. Heap lookup and fresh addresses are
high-level primitives here; their sequential bit implementation is NOT proved
in this module. In particular these are high steps, not native Lean timings.

The procedure copies every cons cell, preserves arbitrary valid old nodes and
caller frames, and never requests a bit. The source charge is an annotation
of the same instruction derivation. It is not an executed natural counter or
a reconstruction from the final word alone. A local call begins after its
caller has pushed its return frame; every callee return is counted, including
the final return. The explicit caller-side invoke is one additional step.
-/
namespace DirectedFlowCutGap.ImmutableWordCopy
open BinaryArithmetic EncodedSequenceAccess

inductive Cell where
  | nil
  | cons (head : Bool) (tail : ℕ)
  deriving DecidableEq, Repr

abbrev Heap := List Cell

/-- Dense addresses are list positions; all cell edges point backwards. -/
def Heap.Valid (h : Heap) : Prop :=
  ∀ (i : ℕ) (b : Bool) (tail : ℕ), h[i]? = some (Cell.cons b tail) → tail < i

inductive Word (h : Heap) : ℕ → Bits → Prop
  | nil {root : ℕ} : h[root]? = some Cell.nil → Word h root []
  | cons {root tail : ℕ} {b : Bool} {bs : Bits} :
      h[root]? = some (Cell.cons b tail) → Word h tail bs → Word h root (b::bs)

theorem Word.root_lt {h : Heap} {root : ℕ} {bs : Bits} (w : Word h root bs) :
    root < h.length := by
  cases w with
  | nil hr => exact (List.getElem?_eq_some_iff.mp hr).choose
  | cons hr _ => exact (List.getElem?_eq_some_iff.mp hr).choose

theorem Word.extend {h : Heap} {root : ℕ} {bs : Bits} (w : Word h root bs)
    (fresh : Heap) : Word (h++fresh) root bs := by
  induction w with
  | nil hr =>
      apply Word.nil
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hr).choose]
      exact hr
  | cons hr _ ih =>
      apply Word.cons _ ih
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hr).choose]
      exact hr

theorem Heap.valid_cons {h : Heap} (hh : h.Valid) (b : Bool) (tail : ℕ)
    (ht : tail < h.length) : (h++[Cell.cons b tail]).Valid := by
  intro i c next hi
  by_cases hlt : i < h.length
  · rw [List.getElem?_append_left hlt] at hi
    exact hh i c next hi
  · have hi' := (List.getElem?_eq_some_iff.mp hi).choose
    have he : i = h.length := by simp only [List.length_append,List.length_singleton] at hi'; omega
    subst i
    rw [List.getElem?_append_right (Nat.le_refl _)] at hi
    simp only [Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq,Cell.cons.injEq] at hi
    simpa only [hi.2] using ht

/-- Every nonempty output cell is fresh above the entering heap baseline.
The terminal nil is an existing node; no copied cons aliases an input cons. -/
inductive Copied (baseline : ℕ) (h : Heap) : ℕ → Bits → Prop
  | nil {root : ℕ} : root < baseline → h[root]? = some Cell.nil → Copied baseline h root []
  | cons {root tail : ℕ} {b : Bool} {bs : Bits} : baseline ≤ root →
      h[root]? = some (Cell.cons b tail) → Copied baseline h tail bs →
      Copied baseline h root (b::bs)

theorem Copied.word {baseline : ℕ} {h : Heap} {root : ℕ} {bs : Bits}
    (hc : Copied baseline h root bs) : Word h root bs := by
  induction hc with
  | nil _ hr => exact .nil hr
  | cons _ hr _ ih => exact .cons hr ih

theorem Copied.extend {baseline : ℕ} {h : Heap} {root : ℕ} {bs : Bits}
    (hc : Copied baseline h root bs) (fresh : Heap) : Copied baseline (h++fresh) root bs := by
  induction hc with
  | nil hb hr =>
      apply Copied.nil hb
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hr).choose]
      exact hr
  | cons hb hr _ ih =>
      apply Copied.cons hb _ ih
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hr).choose]
      exact hr

inductive PC where
  | inspect | base | head | tail | call | allocate | ret
  deriving DecidableEq, Repr

inductive Instruction where
  | caseList | move | readHead | readTail | invoke | cons | returnValue
  deriving DecidableEq, Repr

/-- The same finite code table serves every dimension and represented word. -/
def program : PC → Instruction
  | .inspect => .caseList
  | .base => .move
  | .head => .readHead
  | .tail => .readTail
  | .call => .invoke
  | .allocate => .cons
  | .ret => .returnValue

structure Frame where
  continuation : PC
  argument : ℕ
  head : Bool
  tail : ℕ
  deriving DecidableEq, Repr

def Frame.Valid (h : Heap) (f : Frame) : Prop :=
  f.argument < h.length ∧ f.tail < h.length

structure State where
  heap : Heap
  pc : PC
  argument : ℕ
  head : Bool
  tail : ℕ
  result : ℕ
  stack : List Frame
  source : Bits
  deriving DecidableEq, Repr

def State.Valid (s : State) : Prop := s.heap.Valid ∧
  s.argument < s.heap.length ∧ s.tail < s.heap.length ∧ s.result < s.heap.length ∧
  ∀ f ∈ s.stack, f.Valid s.heap

/-- Actual fixed instruction semantics. No host body/callback is an opcode. -/
def tick (s : State) : Option State :=
  match program s.pc with
  | .caseList =>
      match s.heap[s.argument]? with
      | none => none
      | some Cell.nil => some {s with pc := .base}
      | some (Cell.cons _ _) => some {s with pc := .head}
  | .move => some {s with pc := .ret, result := s.argument}
  | .readHead =>
      match s.heap[s.argument]? with
      | some (Cell.cons b _) => some {s with pc := .tail, head := b}
      | _ => none
  | .readTail =>
      match s.heap[s.argument]? with
      | some (Cell.cons _ t) => some {s with pc := .call, tail := t}
      | _ => none
  | .invoke =>
      some {s with pc := .inspect, argument := s.tail, stack := ⟨.allocate,s.argument,s.head,s.tail⟩::s.stack}
  | .cons =>
      some {s with heap := s.heap++[Cell.cons s.head s.result], pc := .ret, result := s.heap.length}
  | .returnValue =>
      match s.stack with
      | [] => none
      | f::fs => some {s with pc := f.continuation, argument := f.argument, head := f.head, tail := f.tail, stack := fs}

/-- Ghost accounting attached to the instruction which was actually taken. -/
def annotation : PC → ℕ
  | .inspect | .head | .tail | .call => 1
  | .base | .allocate | .ret => 0

/-- One fixed-size frame record on call, one value record on cons. The
eventual binary encoding expands each such bounded-arity record by a fixed
constant; this is not a claim that a record is one bit. -/
def freshRecords : PC → ℕ
  | .call | .allocate => 1
  | _ => 0

inductive Steps : ℕ → State → State → Prop
  | done (s : State) : Steps 0 s s
  | step {s u v : State} {t : ℕ} : tick s = some u → Steps t u v → Steps (t+1) s v

/-- The depth cap covers every reached state; annotations fold this very run.
They are not stored fields of the executing state. -/
inductive Run (depth : ℕ) : ℕ → ℕ → State → State → Prop
  | done (s : State) : s.stack.length ≤ depth → Run depth 0 0 s s
  | step {s u v : State} {t q : ℕ} : s.stack.length ≤ depth →
      tick s = some u → Run depth t q u v → Run depth (t+1) (annotation s.pc+q) s v

/-- Allocation annotations accompany the same instruction transitions. -/
inductive AllocationRun (depth : ℕ) : ℕ → ℕ → ℕ → State → State → Prop
  | done (s : State) : s.stack.length ≤ depth → AllocationRun depth 0 0 0 s s
  | step {s u v : State} {t q a : ℕ} : s.stack.length ≤ depth →
      tick s = some u → AllocationRun depth t q a u v →
      AllocationRun depth (t+1) (annotation s.pc+q) (freshRecords s.pc+a) s v

theorem AllocationRun.erase {depth t q a : ℕ} {s u : State}
    (h : AllocationRun depth t q a s u) : Run depth t q s u := by
  induction h with
  | done s hs => exact .done s hs
  | step hs ht _ ih => exact .step hs ht ih

theorem Run.with_allocations {depth t q : ℕ} {s u : State} (h : Run depth t q s u) :
    ∃ a ≤ t, AllocationRun depth t q a s u := by
  induction h with
  | done s hs => exact ⟨0,le_rfl,.done s hs⟩
  | @step s u v t q hs ht _ ih =>
      obtain ⟨a,ha,hr⟩ := ih
      have hf : freshRecords s.pc ≤ 1 := by cases s.pc <;> simp [freshRecords]
      exact ⟨freshRecords s.pc+a,by omega,.step hs ht hr⟩

theorem Run.erase {depth t q : ℕ} {s u : State} (h : Run depth t q s u) : Steps t s u := by
  induction h with
  | done s _ => exact .done s
  | step _ hs _ ih => exact .step hs ih

theorem Run.single {depth : ℕ} {s u : State} (hs : s.stack.length ≤ depth)
    (hu : u.stack.length ≤ depth) (h : tick s = some u) :
    Run depth 1 (annotation s.pc) s u := by
  simpa only [Nat.add_zero] using Run.step hs h (Run.done u hu)

theorem Run.append {depth t q r c : ℕ} {s u v : State}
    (h : Run depth t q s u) (k : Run depth r c u v) : Run depth (t+r) (q+c) s v := by
  induction h with
  | done s _ => simpa only [Nat.zero_add] using k
  | step hs hstep _ ih =>
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Run.step hs hstep (ih k)

theorem tick_source {s u : State} (h : tick s = some u) : u.source = s.source := by
  unfold tick at h
  split at h <;> first | (split at h <;> simp_all) | simp_all
  all_goals (cases h; rfl)

theorem Run.source {depth t q : ℕ} {s u : State} (h : Run depth t q s u) :
    u.source = s.source := by
  induction h with
  | done s _ => rfl
  | step _ hs _ ih => exact ih.trans (tick_source hs)

/-- The instruction semantics preserves the concrete live-register and
frame invariants. This includes frames belonging to an arbitrary caller. -/
theorem tick_valid {s u : State} (hs : s.Valid) (step : tick s = some u) : u.Valid := by
  cases hp : s.pc with
  | inspect =>
      cases hr : s.heap[s.argument]? with
      | none => simp [tick,program,hp,hr] at step
      | some cell =>
          cases cell <;> simp only [tick,program,hp,hr,Option.some.injEq] at step
            <;> subst u <;> exact hs
  | base =>
      simp only [tick,program,hp,Option.some.injEq] at step
      subst u
      exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.1,hs.2.2.2.2⟩
  | head =>
      cases hr : s.heap[s.argument]? with
      | none => simp [tick,program,hp,hr] at step
      | some cell =>
          cases cell with
          | nil => simp [tick,program,hp,hr] at step
          | cons b next =>
              simp only [tick,program,hp,hr,Option.some.injEq] at step
              subst u
              exact hs
  | tail =>
      cases hr : s.heap[s.argument]? with
      | none => simp [tick,program,hp,hr] at step
      | some cell =>
          cases cell with
          | nil => simp [tick,program,hp,hr] at step
          | cons b next =>
              have hn := (hs.1 s.argument b next hr).trans hs.2.1
              simp only [tick,program,hp,hr,Option.some.injEq] at step
              subst u
              exact ⟨hs.1,hs.2.1,hn,hs.2.2.2.1,hs.2.2.2.2⟩
  | call =>
      simp only [tick,program,hp,Option.some.injEq] at step
      subst u
      refine ⟨hs.1,hs.2.2.1,hs.2.2.1,hs.2.2.2.1,?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨hs.2.1,hs.2.2.1⟩
      · exact hs.2.2.2.2 f hf
  | allocate =>
      simp only [tick,program,hp,Option.some.injEq] at step
      subst u
      refine ⟨Heap.valid_cons hs.1 s.head s.result hs.2.2.2.1,?_,?_,?_,?_⟩
      · exact hs.2.1.trans_le (by simp)
      · exact hs.2.2.1.trans_le (by simp)
      · simp
      · intro f hf
        have h := hs.2.2.2.2 f hf
        exact ⟨h.1.trans_le (by simp),h.2.trans_le (by simp)⟩
  | ret =>
      cases ht : s.stack with
      | nil => simp [tick,program,hp,ht] at step
      | cons f fs =>
          have hf := hs.2.2.2.2 f (by simp [ht])
          simp only [tick,program,hp,ht,Option.some.injEq] at step
          subst u
          refine ⟨hs.1,hf.1,hf.2,hs.2.2.2.1,?_⟩
          intro g hg
          exact hs.2.2.2.2 g (by simp [ht,hg])

theorem Run.valid {depth t q : ℕ} {s u : State} (h : Run depth t q s u)
    (hs : s.Valid) : u.Valid := by
  induction h with
  | done _ _ => exact hs
  | step _ hstep _ ih => exact ih (tick_valid hs hstep)

def entry (h : Heap) (root : ℕ) (head : Bool) (tail result : ℕ)
    (stack : List Frame) (source : Bits) : State :=
  ⟨h,.inspect,root,head,tail,result,stack,source⟩

def returned (h : Heap) (caller : Frame) (stack : List Frame) (root : ℕ)
    (source : Bits) : State :=
  ⟨h,caller.continuation,caller.argument,caller.head,caller.tail,root,stack,source⟩

/-- The fixed calling convention restores every saved non-result register,
the exact continuation and the complete caller stack. It does not execute
that continuation. The result register carries only the new word root. -/
theorem returned_context (h : Heap) (caller : Frame) (stack : List Frame)
    (root : ℕ) (source : Bits) :
    (returned h caller stack root source).pc=caller.continuation ∧
    (returned h caller stack root source).argument=caller.argument ∧
    (returned h caller stack root source).head=caller.head ∧
    (returned h caller stack root source).tail=caller.tail ∧
    (returned h caller stack root source).stack=stack ∧
    (returned h caller stack root source).result=root := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem nil_run (h : Heap) (root : ℕ) (head : Bool) (tail result : ℕ)
    (caller : Frame) (stack : List Frame) (source : Bits) (depth : ℕ)
    (hd : stack.length+1 ≤ depth) (hr : h[root]? = some Cell.nil) :
    Run depth 3 1 (entry h root head tail result (caller::stack) source)
      (returned h caller stack root source) := by
  let a := entry h root head tail result (caller::stack) source
  let b := {a with pc := PC.base}
  let c := {b with pc := PC.ret,result := root}
  have r₁ : Run depth 1 1 a b := Run.single (depth := depth) (s := a) (u := b)
    (by change stack.length+1 ≤ depth; exact hd)
    (by change stack.length+1 ≤ depth; exact hd)
    (by dsimp only [a,b,entry,tick,program]; rw [hr])
  have r₂ : Run depth 1 0 b c := Run.single (depth := depth) (s := b) (u := c)
    (by change stack.length+1 ≤ depth; exact hd)
    (by change stack.length+1 ≤ depth; exact hd) rfl
  have r₃ : Run depth 1 0 c (returned h caller stack root source) :=
    Run.single (depth := depth) (s := c) (u := returned h caller stack root source)
      (by change stack.length+1 ≤ depth; exact hd)
      (by change stack.length ≤ depth; omega) rfl
  exact (r₁.append r₂).append r₃

private theorem cons_prefix (h : Heap) (root next : ℕ) (b head : Bool) (tail result : ℕ)
    (caller : Frame) (stack : List Frame) (source : Bits) (depth : ℕ)
    (hd : stack.length+2 ≤ depth) (hr : h[root]? = some (Cell.cons b next)) :
    Run depth 4 4 (entry h root head tail result (caller::stack) source)
      (entry h next b next result (⟨.allocate,root,b,next⟩::caller::stack) source) := by
  let a := entry h root head tail result (caller::stack) source
  let s₁ := {a with pc := PC.head}
  let s₂ := {s₁ with pc := PC.tail,head := b}
  let s₃ := {s₂ with pc := PC.call,tail := next}
  have r₁ : Run depth 1 1 a s₁ := Run.single (depth := depth) (s := a) (u := s₁)
    (by change stack.length+1 ≤ depth; omega)
    (by change stack.length+1 ≤ depth; omega)
    (by dsimp only [a,s₁,entry,tick,program]; rw [hr])
  have r₂ : Run depth 1 1 s₁ s₂ := Run.single (depth := depth) (s := s₁) (u := s₂)
    (by change stack.length+1 ≤ depth; omega)
    (by change stack.length+1 ≤ depth; omega)
    (by dsimp only [s₂,s₁,a,entry,tick,program]; rw [hr])
  have r₃ : Run depth 1 1 s₂ s₃ := Run.single (depth := depth) (s := s₂) (u := s₃)
    (by change stack.length+1 ≤ depth; omega)
    (by change stack.length+1 ≤ depth; omega)
    (by dsimp only [s₃,s₂,s₁,a,entry,tick,program]; rw [hr])
  have r₄ : Run depth 1 1 s₃
      (entry h next b next result (⟨.allocate,root,b,next⟩::caller::stack) source) :=
    Run.single (depth := depth) (s := s₃)
      (u := entry h next b next result (⟨.allocate,root,b,next⟩::caller::stack) source)
      (by change stack.length+1 ≤ depth; omega)
      (by change (stack.length+1)+1 ≤ depth; omega) rfl
  exact ((r₁.append r₂).append r₃).append r₄

private theorem cons_suffix (h : Heap) (root next out : ℕ) (b : Bool)
    (caller : Frame) (stack : List Frame) (source : Bits) (depth : ℕ)
    (hd : stack.length+1 ≤ depth) :
    Run depth 2 0 (returned h ⟨.allocate,root,b,next⟩ (caller::stack) out source)
      (returned (h++[Cell.cons b out]) caller stack h.length source) := by
  let a := returned h ⟨.allocate,root,b,next⟩ (caller::stack) out source
  let c := {a with heap := h++[Cell.cons b out], pc := PC.ret,result := h.length}
  have r₁ : Run depth 1 0 a c := Run.single (depth := depth) (s := a) (u := c)
    (by change stack.length+1 ≤ depth; exact hd)
    (by change stack.length+1 ≤ depth; exact hd) rfl
  have r₂ : Run depth 1 0 c (returned (h++[Cell.cons b out]) caller stack h.length source) :=
    Run.single (depth := depth) (s := c)
      (u := returned (h++[Cell.cons b out]) caller stack h.length source)
      (by change stack.length+1 ≤ depth; exact hd)
      (by change stack.length ≤ depth; omega) rfl
  exact r₁.append r₂

/-- The actual instruction derivation, exact annotation and literal fresh
copy. Counts are derived from 3 nil instructions and 6 additional cons
instructions, including internal call and return-frame handling. -/
theorem copy_call {h : Heap} {root : ℕ} {bits : Bits}
    (hw : h.Valid) (word : Word h root bits) (head : Bool) (tail result : ℕ)
    (caller : Frame) (stack : List Frame) (source : Bits) :
    ∃ fresh out,
      fresh.length=bits.length ∧ (h++fresh).Valid ∧ Copied h.length (h++fresh) out bits ∧
      Run (stack.length+bits.length+1) (6*bits.length+3) (4*bits.length+1)
        (entry h root head tail result (caller::stack) source)
        (returned (h++fresh) caller stack out source) := by
  induction word generalizing head tail result caller stack with
  | @nil root hr =>
      refine ⟨[],root,rfl,by simpa using hw,?_,?_⟩
      · simpa only [List.append_nil] using Copied.nil
          (List.getElem?_eq_some_iff.mp hr).choose hr
      · simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero,List.append_nil] using
          nil_run h root head tail result caller stack source (stack.length+1) le_rfl hr
  | @cons root next b bs hr htail ih =>
      let inner : Frame := ⟨.allocate,root,b,next⟩
      obtain ⟨fresh,out,hlen,hvalid,hcopy,hrun⟩ :=
        ih b next result inner (caller::stack)
      refine ⟨fresh++[Cell.cons b out],(h++fresh).length,?_,?_,?_,?_⟩
      · simp only [List.length_append,List.length_cons,List.length_nil,hlen]
      · rw [← List.append_assoc]
        exact Heap.valid_cons hvalid b out hcopy.word.root_lt
      · rw [← List.append_assoc]
        apply Copied.cons (tail := out) (by simp only [List.length_append]; omega)
        · simp only [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero]
        · exact hcopy.extend [Cell.cons b out]
      · have pre := cons_prefix h root next b head tail result caller stack source
          (stack.length+bs.length+2) (by omega) hr
        have middle : Run (stack.length+bs.length+2) (6*bs.length+3) (4*bs.length+1)
            (entry h next b next result (inner::caller::stack) source)
            (returned (h++fresh) inner (caller::stack) out source) := by
          simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hrun
        have post := cons_suffix (h++fresh) root next out b caller stack source
          (stack.length+bs.length+2) (by omega)
        have total := (pre.append middle).append post
        convert total using 1 <;> simp only [List.length_cons,Nat.mul_add,Nat.mul_one,
          Nat.add_assoc,List.append_assoc] <;> omega

/-- The actual caller-side invoke adds one instruction and one frame to the
callee certificate. The return restores the caller registers and stops at
the fixed continuation; it does not execute the caller after that boundary. -/
theorem invoke_copy (s : State) (hpc : s.pc=.call) (hs : s.Valid)
    {bits : Bits} (word : Word s.heap s.tail bits) :
    ∃ fresh out,
      fresh.length=bits.length ∧ Copied s.heap.length (s.heap++fresh) out bits ∧
      Run (s.stack.length+bits.length+1) (6*bits.length+4) (4*bits.length+2) s
        (returned (s.heap++fresh) ⟨.allocate,s.argument,s.head,s.tail⟩ s.stack out s.source) := by
  obtain ⟨fresh,out,hlen,_,hcopy,hrun⟩ := copy_call hs.1 word s.head s.tail s.result
    ⟨.allocate,s.argument,s.head,s.tail⟩ s.stack s.source
  have call : Run (s.stack.length+bits.length+1) 1 1 s
      (entry s.heap s.tail s.head s.tail s.result
        (⟨.allocate,s.argument,s.head,s.tail⟩::s.stack) s.source) := by
    have hc := Run.single (depth := s.stack.length+bits.length+1)
      (s := s) (u := entry s.heap s.tail s.head s.tail s.result
        (⟨.allocate,s.argument,s.head,s.tail⟩::s.stack) s.source)
      (by omega) (by simp only [entry,List.length_cons]; omega)
      (by simp only [tick,program,hpc,entry])
    simpa only [hpc,annotation] using hc
  refine ⟨fresh,out,hlen,hcopy,?_⟩
  convert call.append hrun using 1 <;> omega

/-- The same fixed code realizes the existing source execution relation.
The caller's heap/continuation may be arbitrary; fresh cells and maximum frame
depth are measured above that baseline. All represented caller references
remain valid because the old heap prefix is unchanged. -/
theorem copy_source_certificate {h : Heap} {root : ℕ} {bits copied : Bits} {q : ℕ}
    (hw : h.Valid) (word : Word h root bits) (sourceRun : BitsCopyExec bits copied q)
    (head : Bool) (tail result : ℕ) (caller : Frame) (stack : List Frame) (source : Bits)
    (htail : tail < h.length) (hresult : result < h.length)
    (hcaller : caller.Valid h) (hstack : ∀ f ∈ stack, f.Valid h) :
    ∃ fresh out t,
      fresh.length=bits.length ∧ (h++fresh).Valid ∧
      Copied h.length (h++fresh) out copied ∧
      Run (stack.length+bits.length+1) t q
        (entry h root head tail result (caller::stack) source)
        (returned (h++fresh) caller stack out source) ∧
      (∃ a ≤ t, AllocationRun (stack.length+bits.length+1) t q a
        (entry h root head tail result (caller::stack) source)
        (returned (h++fresh) caller stack out source)) ∧
      t ≤ 2*(q+1) ∧
      (entry h root head tail result (caller::stack) source).Valid ∧
      (returned (h++fresh) caller stack out source).Valid ∧
      (returned (h++fresh) caller stack out source).source=source := by
  have hs := sourceRun.result
  have hv := copyBits_spec bits
  have hcopied : copied=bits := hs.1.trans hv.1
  have hq : q=4*bits.length+1 := hs.2.trans hv.2
  subst copied
  subst q
  obtain ⟨fresh,out,hlen,hvalid,hcopy,hrun⟩ := copy_call hw word head tail result caller stack source
  have hentry : (entry h root head tail result (caller::stack) source).Valid := by
    refine ⟨hw,word.root_lt,htail,hresult,?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hcaller
    · exact hstack f hf
  exact ⟨fresh,out,6*bits.length+3,hlen,hvalid,hcopy,hrun,hrun.with_allocations,by omega,
    hentry,hrun.valid hentry,rfl⟩

end DirectedFlowCutGap.ImmutableWordCopy
