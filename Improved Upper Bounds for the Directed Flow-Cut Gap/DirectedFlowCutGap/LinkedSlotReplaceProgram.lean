import DirectedFlowCutGap.BinaryPointerListRead
import DirectedFlowCutGap.PhysicalCoverReader

/-!
# Fixed-instruction replacement in a retained linked row

The stored index spine and row are traversed together. The new prefix
reuses all unchanged payload references, and the suffix after the
replaced slot is shared. No random bit is read.
-/

namespace DirectedFlowCutGap.LinkedSlotReplaceProgram

open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open BinaryPointerListRead PackedBooleanConstructor BinaryArithmetic

def program : Program 14 := fun pc =>
  match pc.val with
  | 0 => .call 1 13 .r3
  | 1 => .branch .r1 8 12 12 2
  | 2 => .field .r3 .r0 false 3
  | 3 => .field .r0 .r0 true 4
  | 4 => .field .r1 .r1 true 5
  | 5 => .call 1 6 .r0
  | 6 => .make .r0 (.pair .r3 .r0) 10
  | 8 => .field .r0 .r0 true 9
  | 9 => .make .r0 (.pair .r2 .r0) 10
  | 10 => .ret .r0
  | _ => .halt

def state (heap : NaturalHeap) (regs : Registers ℕ) (stack : List (Frame ℕ 14))
    (tape : Bits) (pc : Fin 14) : NaturalState 14 :=
  ⟨heap, heap.length, regs, stack, pc, tape⟩

private theorem append_run {a b c : NaturalState 14} {m n : ℕ} {es fs : List Event}
    (h : NaturalRun program m a es b) (hg : NaturalRun program n b fs c) :
    NaturalRun program (m + n) a (es ++ fs) c := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm 1] using
      NaturalRun.step ht (ih hg)

theorem replace_subroutine {heap : NaturalHeap} {root index i : ℕ} {xs : List ℕ}
    (hr : PointerList heap root xs) (hi : IndexSpine heap index i) (inRange : i < xs.length)
    (new scratch : ℕ) (caller : Frame ℕ 14) (stack : List (Frame ℕ 14)) (tape : Bits) :
    ∃ extra out, extra.length = i + 1 ∧ PointerList (heap ++ extra) out (xs.set i new) ∧
      NaturalRun program (7 * i + 4) (state heap ⟨root, index, new, scratch⟩ (caller :: stack) tape 1) []
        (state (heap ++ extra) (caller.saved.set caller.destination out) stack tape caller.continuation) := by
  induction i generalizing root index xs scratch caller stack with
  | zero =>
    cases hi with
    | nil hnil =>
      cases hr with
      | nil _ => simp at inRange
      | @cons root head tail rest hp ht =>
        let saved := caller :: stack
        let regs : Registers ℕ := ⟨root, index, new, scratch⟩
        let s1 := state heap regs saved tape 1
        let s8 := state heap regs saved tape 8
        let s9 := state heap ⟨tail, index, new, scratch⟩ saved tape 9
        let cell : Cell ℕ := .pair new tail
        let updated := heap ++ [cell]
        let fresh := heap.length
        let s10 := state updated ⟨fresh, index, new, scratch⟩ saved tape 10
        let quit := state updated (caller.saved.set caller.destination fresh) stack tape caller.continuation
        have h1 : tickNatural program s1 = some ⟨s8, [], 0⟩ := by
          simp [tickNatural, program, state, Registers.get, tagBranch, s1, s8, regs, hnil]
        have h8 : tickNatural program s8 = some ⟨s9, [], 0⟩ := by
          simp [tickNatural, program, state, Registers.get, Registers.set, s8, s9, regs, hp]
        have h9 : tickNatural program s9 = some ⟨s10, [], 0⟩ := by
          simp [tickNatural, program, state, allocateNatural, Recipe.cell, Registers.get, Registers.set,
            s9, s10, cell, updated, fresh]
        have h10 : tickNatural program s10 = some ⟨quit, [], 0⟩ := by
          simp [tickNatural, program, state, Registers.get, s10, quit, saved]
        have hout : PointerList updated fresh (new :: rest) :=
          .cons (by simp [updated, fresh, cell]) (pointerList_extend ht [cell])
        exact ⟨[cell], fresh, rfl, hout, NaturalRun.step h1 (.step h8 (.step h9 (.step h10 (.done quit))))⟩
  | succ i ih =>
    cases hi with
    | @cons index ignore small _ hindex htail =>
      cases hr with
      | nil _ => simp at inRange
      | @cons root head tail rest hp ht =>
        let saved := caller :: stack
        let s1 := state heap ⟨root, index, new, scratch⟩ saved tape 1
        let s2 := state heap ⟨root, index, new, scratch⟩ saved tape 2
        let s3 := state heap ⟨root, index, new, head⟩ saved tape 3
        let s4 := state heap ⟨tail, index, new, head⟩ saved tape 4
        let regs : Registers ℕ := ⟨tail, small, new, head⟩
        let s5 := state heap regs saved tape 5
        let frame : Frame ℕ 14 := ⟨6, .r0, regs⟩
        have h1 : tickNatural program s1 = some ⟨s2, [], 0⟩ := by
          simp [tickNatural, program, state, Registers.get, tagBranch, hindex, s1, s2]
        have h2 : tickNatural program s2 = some ⟨s3, [], 0⟩ := by
          simp [tickNatural, program, state, Registers.get, Registers.set, hp, s2, s3]
        have h3 : tickNatural program s3 = some ⟨s4, [], 0⟩ := by
          simp [tickNatural, program, state, Registers.get, Registers.set, hp, s3, s4]
        have h4 : tickNatural program s4 = some ⟨s5, [], 0⟩ := by
          simp [tickNatural, program, state, Registers.get, Registers.set, hindex, s4, s5, regs]
        have h5 : tickNatural program s5 =
            some ⟨state heap regs (frame :: saved) tape 1, [], 0⟩ := rfl
        obtain ⟨ext, replaced, hext, hrep, hrun⟩ := ih ht htail (by simpa using inRange) head frame saved
        let grown := heap ++ ext
        let s6 := state grown ⟨replaced, small, new, head⟩ saved tape 6
        change NaturalRun program (7 * i + 4) (state heap regs (frame :: saved) tape 1) [] s6 at hrun
        let cell : Cell ℕ := .pair head replaced
        let updated := grown ++ [cell]
        let fresh := grown.length
        let s10 := state updated ⟨fresh, small, new, head⟩ saved tape 10
        let quit := state updated (caller.saved.set caller.destination fresh) stack tape caller.continuation
        have h6 : tickNatural program s6 = some ⟨s10, [], 0⟩ := by
          simp [tickNatural, program, state, allocateNatural, Recipe.cell, Registers.get, Registers.set,
            s6, s10, cell, updated, fresh]
        have h10 : tickNatural program s10 = some ⟨quit, [], 0⟩ := by
          simp [tickNatural, program, state, Registers.get, s10, quit, saved]
        have joined := append_run hrun (NaturalRun.step h6 (.step h10 (.done quit)))
        have full := NaturalRun.step h1 (.step h2 (.step h3 (.step h4 (.step h5 joined))))
        have hout : PointerList updated fresh (head :: rest.set i new) :=
          .cons (by simp [updated, cell, fresh]) (pointerList_extend hrep [cell])
        refine ⟨ext ++ [cell], fresh, by simp [hext], ?_, ?_⟩
        · simpa only [List.set_cons_succ, updated, grown, List.append_assoc] using hout
        · have hcount : 7 * (i + 1) + 4 = 7 * i + 4 + 2 + 5 := by omega
          rw [hcount]
          convert full using 1 <;> simp [quit, updated, grown, List.append_assoc]

private theorem start (s : NaturalState 14) (hp : s.pc = 0) (hc : s.stack = [])
    (hn : s.next = s.heap.length) :
    tickNatural program s = some ⟨state s.heap s.registers [⟨13, .r3, s.registers⟩] s.source 1, [], 0⟩ := by
  cases s
  simp_all [tickNatural, program, state]

theorem replaced_slot {i H B : ℕ} {initial : BitState 14} {xs : List ℕ}
    (hs : initial.Bounded H B) (hp : initial.pc = 0) (hc : initial.stack = [])
    (hn : (eraseState initial).next = (eraseState initial).heap.length)
    (hr : PointerList (eraseState initial).heap (eraseState initial).registers.a xs)
    (hi : IndexSpine (eraseState initial).heap (eraseState initial).registers.b i)
    (inRange : i < xs.length) :
    ∃ q out, Run program (7 * i + 5) q initial [] out ∧
      (attempt program out).result = none ∧
      (eraseState out).pc = 13 ∧ (eraseState out).stack = [] ∧ out.source = initial.source ∧
      PointerList (eraseState out).heap (eraseState out).registers.d (xs.set i (eraseState initial).registers.c) ∧
      (∃ extra, extra.length = i + 1 ∧ (eraseState out).heap = (eraseState initial).heap ++ extra) ∧
      q + (attempt program out).operations ≤ completeBound 14 H B (7 * H + 5) := by
  let init := eraseState initial
  let caller : Frame ℕ 14 := ⟨13, .r3, init.registers⟩
  have hnil : init.stack = [] := by simp [init, eraseState, State.map, hc]
  obtain ⟨ext, root, hlen, hrep, htrace⟩ :=
    replace_subroutine hr hi inRange init.registers.c init.registers.d caller [] init.source
  let final := state (init.heap ++ ext) (init.registers.set .r3 root) [] init.source 13
  have h0 : tickNatural program init = some ⟨state init.heap init.registers [caller] init.source 1, [], 0⟩ :=
    start init hp hnil hn
  change NaturalRun program (7 * i + 4) (state init.heap init.registers [caller] init.source 1) [] final at htrace
  have hrun : NaturalRun program (7 * i + 5) init [] final := NaturalRun.step h0 htrace
  have halt : tickNatural program final = none := rfl
  obtain ⟨q, out, hmodel, he, hterminal, hcost, htape⟩ := terminating_simulation hs hrun halt
  have hH : init.heap.length ≤ H := by
    have hheap := hs.1
    unfold State.records at hheap
    have : initial.heap.length ≤ H := by omega
    simpa [init, eraseState, State.map] using this
  have hsize := (PhysicalCoverReader.spine_short hi).le.trans hH
  refine ⟨q, out, hmodel, hterminal, ?_, ?_, htape, ?_, ⟨ext, hlen, ?_⟩, hcost.trans ?_⟩
  · rw [he]; rfl
  · rw [he]; rfl
  · rw [he]; exact hrep
  · rw [he]; rfl
  · unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.LinkedSlotReplaceProgram
