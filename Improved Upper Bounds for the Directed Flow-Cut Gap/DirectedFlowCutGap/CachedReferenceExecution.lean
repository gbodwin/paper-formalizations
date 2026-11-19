import DirectedFlowCutGap.CachedReferenceHeap

/-!
# Cached execution of the terminal-inclusive reference machine

The finite instruction table is unchanged. The cached heap avoids
recopying shared payloads in the host evaluator. Its projection preserves
each reference transition, event, operation charge, and stopped attempt.
-/

namespace DirectedFlowCutGap.CachedReferenceExecution

open BinaryArithmetic ImmutableReferenceSimulation EncodedSequenceAccess
open ImmutableReferenceTerminal

structure FastState (C : ℕ) where
  store : CachedReferenceHeap.Store
  next : Bits
  registers : Registers Bits
  stack : List (Frame Bits C)
  pc : Fin C
  source : Bits

def FastState.freeze {C : ℕ} (s : FastState C) : BitState C :=
  ⟨s.store.cells.toList, s.next, s.registers, s.stack, s.pc, s.source⟩

private def FastState.withoutHeap {C : ℕ} (s : FastState C) : BitState C :=
  ⟨[], s.next, s.registers, s.stack, s.pc, s.source⟩

private def restore {C : ℕ} (heap : CachedReferenceHeap.Store) (s : BitState C) : FastState C :=
  ⟨heap, s.next, s.registers, s.stack, s.pc, s.source⟩

def FastState.ofReference {C : ℕ} (s : BitState C) : FastState C :=
  restore (CachedReferenceHeap.ofList s.heap) s

@[simp] theorem freeze_ofReference {C : ℕ} (s : BitState C) : (FastState.ofReference s).freeze = s := by
  cases s
  simp [FastState.ofReference, FastState.freeze, restore]

structure FastResult (C : ℕ) where
  state : FastState C
  events : List Event
  cost : ℕ

def FastResult.freeze {C : ℕ} (r : FastResult C) : Result Bits C :=
  ⟨r.state.freeze, r.events, r.cost⟩

inductive FastAttempt (C : ℕ) where
  | stopped (state : FastState C) (operations : ℕ)
  | completed (result : FastResult C)

def FastAttempt.freeze {C : ℕ} : FastAttempt C → ImmutableReferenceTerminal.Attempt C
  | .stopped _ operations => ImmutableReferenceTerminal.stopped operations
  | .completed result => success result.freeze

private def lift {C : ℕ} (s : FastState C)
    (a : ImmutableReferenceTerminal.Attempt C) : FastAttempt C :=
  match a.result with
  | none => .stopped s a.operations
  | some r => .completed ⟨restore s.store r.state, r.events, r.cost⟩

private def allocate {C : ℕ} (s : FastState C) (dst : Reg) (c : Cell Bits)
    (pc : Fin C) (events : List Event) : FastResult C :=
  match s with
  | ⟨store, next, registers, stack, _, source⟩ =>
    let n := increment true next
    let a := copyBits next
    let h := CachedReferenceHeap.append store c
    ⟨⟨h.1, n.1, registers.set dst a.1, stack, pc, source⟩,
      events, h.2 + n.2 + a.2 + controlCost C⟩

private theorem allocate_eq {C : ℕ} (s : FastState C) (dst : Reg) (c : Cell Bits)
    (pc : Fin C) (events : List Event) :
    (allocate s dst c pc events).freeze =
      ImmutableReferenceSimulation.allocate s.freeze dst c pc events := by
  have h := CachedReferenceHeap.append_eq s.store c
  have hh := congrArg Prod.fst h
  have hc := congrArg Prod.snd h
  change (CachedReferenceHeap.append s.store c).1.cells.toList =
    (appendCell s.store.cells.toList c).1 at hh
  change (CachedReferenceHeap.append s.store c).2 = (appendCell s.store.cells.toList c).2 at hc
  cases s
  simp only [allocate, FastResult.freeze, FastState.freeze, ImmutableReferenceSimulation.allocate]
  rw [hh, hc]

def attempt {C : ℕ} (p : Program C) (s : FastState C) : FastAttempt C :=
  match p s.pc with
  | .make dst recipe pc => .completed (allocate s dst (recipe.cell s.registers) pc [])
  | .request dst pc =>
      let bit := s.source.headD false
      .completed (allocate {s with source := s.source.tail} dst (.flag bit) pc [.request bit])
  | .branch src n f t pair =>
      let a := copyBits (s.registers.get src)
      let r := CachedReferenceHeap.read s.store a.1
      let charge := a.2 + r.2 + controlCost C
      match r.1 with
      | none => .stopped s charge
      | some c => .completed ⟨{s with pc := tagBranch n f t pair c}, [], charge⟩
  | .field dst src right pc =>
      let a := copyBits (s.registers.get src)
      let r := CachedReferenceHeap.read s.store a.1
      match r.1 with
      | some (.pair l r') =>
          let b := copyBits (if right then r' else l)
          .completed ⟨{s with registers := s.registers.set dst b.1, pc := pc}, [],
            a.2 + r.2 + b.2 + controlCost C⟩
      | _ => .stopped s (a.2 + r.2 + controlCost C)
  | .emit src pc =>
      let a := copyBits (s.registers.get src)
      let r := CachedReferenceHeap.read s.store a.1
      let charge := a.2 + r.2 + controlCost C
      match r.1 with
      | some (.flag b) => .completed ⟨{s with pc := pc}, [.emit b], charge⟩
      | _ => .stopped s charge
  | _ => lift s (ImmutableReferenceTerminal.attempt p s.withoutHeap)

theorem attempt_eq {C : ℕ} (p : Program C) (s : FastState C) :
    (attempt p s).freeze = ImmutableReferenceTerminal.attempt p s.freeze := by
  cases hi : p s.pc with
  | halt => simp [attempt, hi, FastState.freeze, FastState.withoutHeap,
      ImmutableReferenceTerminal.attempt, stopped, lift, FastAttempt.freeze]
  | move dst src pc => simp [attempt, hi, FastState.freeze, FastState.withoutHeap,
      ImmutableReferenceTerminal.attempt, success, lift, FastAttempt.freeze, FastResult.freeze, restore]
  | call entry continuation dst => simp [attempt, hi, FastState.freeze, FastState.withoutHeap,
      ImmutableReferenceTerminal.attempt, success, lift, FastAttempt.freeze, FastResult.freeze, restore]
  | ret result =>
      cases hs : s.stack <;>
        simp [attempt, hi, hs, FastState.freeze, FastState.withoutHeap,
          ImmutableReferenceTerminal.attempt, success, stopped, lift, FastAttempt.freeze, FastResult.freeze, restore]
  | make dst recipe pc =>
      have hpc : p s.freeze.pc = .make dst recipe pc := hi
      simp only [attempt, ImmutableReferenceTerminal.attempt, hi, hpc, FastAttempt.freeze, allocate_eq]
      rfl
  | request dst pc =>
      have hpc : p s.freeze.pc = .request dst pc := hi
      simp only [attempt, ImmutableReferenceTerminal.attempt, hi, hpc, FastAttempt.freeze, allocate_eq]
      rfl
  | branch src n f t pair =>
      simp only [attempt, ImmutableReferenceTerminal.attempt, FastState.freeze, hi, CachedReferenceHeap.read_eq]
      cases (lookup (copyBits (s.registers.get src)).1 s.store.cells.toList).1 <;> rfl
  | field dst src right pc =>
      simp only [attempt, ImmutableReferenceTerminal.attempt, FastState.freeze, hi, CachedReferenceHeap.read_eq]
      cases (lookup (copyBits (s.registers.get src)).1 s.store.cells.toList).1 with
      | none => rfl
      | some c => cases c <;> rfl
  | emit src pc =>
      simp only [attempt, ImmutableReferenceTerminal.attempt, FastState.freeze, hi, CachedReferenceHeap.read_eq]
      cases (lookup (copyBits (s.registers.get src)).1 s.store.cells.toList).1 with
      | none => rfl
      | some c => cases c <;> rfl

theorem stopped_state {C : ℕ} (p : Program C) {s u : FastState C} {q : ℕ}
    (h : attempt p s = .stopped u q) : u = s := by
  have lift_stop (a : ImmutableReferenceTerminal.Attempt C) (ha : lift s a = .stopped u q) : u = s := by
    unfold lift at ha
    split at ha <;> simp_all
  cases hi : p s.pc with
  | halt | move | call | ret => exact lift_stop _ (by simpa only [attempt, hi] using h)
  | make | request => simp [attempt, hi] at h
  | branch | field | emit =>
    simp only [attempt, hi] at h
    split at h <;> simp_all

def execute {C : ℕ} (p : Program C) : ℕ → FastState C → ℕ → Option (FastState C × ℕ)
  | 0, _, _ => none
  | fuel + 1, s, paid =>
    match attempt p s with
    | .stopped u q => some (u, paid + q)
    | .completed r => execute p fuel r.state (paid + r.cost)

end DirectedFlowCutGap.CachedReferenceExecution
