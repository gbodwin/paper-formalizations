import DirectedFlowCutGap.ImmutableReferenceSimulation

/-!
# Terminal attempts of the immutable-reference interpreter

The successful-prefix model discards the charge when its next instruction
halts or fails. This literal extension retains that final attempt's charge,
including the same copied source register and sequential lookup on failure.
Success results are unchanged. It closes terminal accounting for this model;
it does not supply a native allocator interpretation or a graph-program
embedding, and its input is still an already represented finite store.
-/
namespace DirectedFlowCutGap.ImmutableReferenceTerminal
open ImmutableReferenceSimulation BinaryArithmetic EncodedSequenceAccess

structure Attempt (C : ℕ) where
  result : Option (Result Bits C)
  operations : ℕ
  deriving DecidableEq, Repr

def success {C : ℕ} (r : Result Bits C) : Attempt C := ⟨some r,r.cost⟩
def stopped {C : ℕ} (operations : ℕ) : Attempt C := ⟨none,operations⟩

/-- The next instruction is executed once; failed reads keep their work. -/
def attempt {C : ℕ} (p : Program C) (s : BitState C) : Attempt C :=
  match p s.pc with
  | .halt => stopped (controlCost C)
  | .move dst src pc =>
      let a := copyBits (s.registers.get src)
      success ⟨{s with registers := s.registers.set dst a.1,pc := pc},[],a.2+controlCost C⟩
  | .make dst recipe pc => success (allocate s dst (recipe.cell s.registers) pc)
  | .branch src n f t pair =>
      let a := copyBits (s.registers.get src)
      let r := lookup a.1 s.heap
      match r.1 with
      | none => stopped (a.2+r.2+controlCost C)
      | some c => success ⟨{s with pc := tagBranch n f t pair c},[],a.2+r.2+controlCost C⟩
  | .field dst src right pc =>
      let a := copyBits (s.registers.get src)
      let r := lookup a.1 s.heap
      match r.1 with
      | some (.pair l r') =>
          let b := copyBits (if right then r' else l)
          success ⟨{s with registers := s.registers.set dst b.1,pc := pc},[],
            a.2+r.2+b.2+controlCost C⟩
      | _ => stopped (a.2+r.2+controlCost C)
  | .call entry continuation dst =>
      let saved := copyRegisters s.registers
      let args := copyRegisters s.registers
      success ⟨{s with registers := args.1,stack := ⟨continuation,dst,saved.1⟩::s.stack,pc := entry},[],
        saved.2+args.2+controlCost C⟩
  | .ret result =>
      match s.stack with
      | [] => stopped (controlCost C)
      | f::fs =>
          let saved := copyRegisters f.saved
          let a := copyBits (s.registers.get result)
          success ⟨{s with registers := saved.1.set f.destination a.1,stack := fs,pc := f.continuation},[],
            saved.2+a.2+controlCost C⟩
  | .request dst pc =>
      let b := s.source.headD false
      success (allocate {s with source := s.source.tail} dst (.flag b) pc [.request b])
  | .emit src pc =>
      let a := copyBits (s.registers.get src)
      let r := lookup a.1 s.heap
      match r.1 with
      | some (.flag b) => success ⟨{s with pc := pc},[.emit b],a.2+r.2+controlCost C⟩
      | _ => stopped (a.2+r.2+controlCost C)

/-- The extra terminal charge changes no state, source suffix or emitted event. -/
theorem attempt_result {C : ℕ} (p : Program C) (s : BitState C) :
    (attempt p s).result = tick p s := by
  cases hi : p s.pc with
  | halt => simp [attempt,tick,hi,stopped]
  | move dst src pc => simp [attempt,tick,hi,success]
  | make dst recipe pc => simp [attempt,tick,hi,success]
  | branch src n f t pair =>
      simp only [attempt,tick,hi]
      cases (lookup (copyBits (s.registers.get src)).1 s.heap).1 <;> rfl
  | field dst src right pc =>
      simp only [attempt,tick,hi]
      cases (lookup (copyBits (s.registers.get src)).1 s.heap).1 with
      | none => rfl
      | some c => cases c <;> rfl
  | call entry continuation dst => simp [attempt,tick,hi,success]
  | ret result => simp only [attempt,tick,hi]; cases s.stack <;> rfl
  | request dst pc => simp [attempt,tick,hi,success]
  | emit src pc =>
      simp only [attempt,tick,hi]
      cases (lookup (copyBits (s.registers.get src)).1 s.heap).1 with
      | none => rfl
      | some c => cases c <;> rfl

/-- Successful instructions keep exactly the original instruction charge. -/
theorem success_cost {C : ℕ} {p : Program C} {s : BitState C} {r : Result Bits C}
    (h : (attempt p s).result = some r) : (attempt p s).operations = r.cost := by
  cases hi : p s.pc <;> simp only [attempt,hi] at h ⊢
  all_goals first
    | (simp only [success,Option.some.injEq] at h; subst r; rfl)
    | (simp [stopped] at h)
    | skip
  all_goals split at h ⊢ <;> simp_all [success,stopped]

/-- Halts and unsuccessful lookups are charged under the same reached bound. -/
theorem stopped_bound {C H B : ℕ} {p : Program C} {s : BitState C}
    (hs : s.Bounded H B) (h : (attempt p s).result = none) :
    (attempt p s).operations ≤ stepBound C H B := by
  have control : controlCost C ≤ stepBound C H B := cost_absorb (by omega)
  have read (i : Reg) :
      (copyBits (s.registers.get i)).2 +
        (lookup (copyBits (s.registers.get i)).1 s.heap).2 + controlCost C ≤ stepBound C H B := by
    have hw := Registers.get_all hs.2.2.2.1 i
    have hr := lookup_bound hw hs.2.2.1
    have hh : s.heap.length+1 ≤ H+1 := by
      have := hs.1
      simp only [State.records] at this
      omega
    have hm := Nat.mul_le_mul_right (B+1) hh
    have hb : B+1 ≤ (H+1)*(B+1) := by nlinarith
    apply cost_absorb
    simp only [copiedWord,copiedWordCost]
    nlinarith
  cases hi : p s.pc <;> simp only [attempt,hi] at h ⊢
  all_goals first
    | exact control
    | (simp [success] at h)
    | skip
  all_goals split at h ⊢ <;> simp_all [success,stopped]

/-- One total bound applies whether this actual attempt succeeds or stops. -/
theorem attempt_bound {C H B : ℕ} {p : Program C} {s : BitState C}
    (hs : s.Bounded H B) : (attempt p s).operations ≤ stepBound C H B := by
  cases h : (attempt p s).result with
  | none => exact stopped_bound hs h
  | some r =>
      rw [success_cost h]
      exact (tick_controlled hs (by rwa [attempt_result] at h)).2

/-- The failed/halt outcome agrees with the high reference semantics too. -/
theorem stopped_refines {C : ℕ} {p : Program C} {s : BitState C}
    (h : (attempt p s).result = none) : tickNatural p (eraseState s) = none := by
  have hr := tick_refines p s
  rw [← attempt_result p s,h] at hr
  exact hr.symm

def completeBound (C H B t : ℕ) : ℕ := runBound C H B t+stepBound C (H+t) (B+t)

/-- The terminating instruction is an additional paid attempt after the same
successful prefix. No output or source is reconstructed from the final state. -/
theorem terminal_accounting {C H B t q : ℕ} {p : Program C}
    {s u : BitState C} {events : List Event}
    (h : Run p t q s events u) (hs : s.Bounded H B)
    (halted : (attempt p u).result = none) :
    tickNatural p (eraseState u) = none ∧
      q+(attempt p u).operations ≤ completeBound C H B t := by
  have hc := h.controlled hs
  exact ⟨stopped_refines halted,Nat.add_le_add hc.2 (attempt_bound hc.1)⟩

end DirectedFlowCutGap.ImmutableReferenceTerminal
