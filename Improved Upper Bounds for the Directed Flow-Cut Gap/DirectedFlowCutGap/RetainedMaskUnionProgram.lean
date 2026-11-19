import DirectedFlowCutGap.EncodedRoundingState
import DirectedFlowCutGap.PhysicalCoverReader
import DirectedFlowCutGap.ImmutableReferenceTerminal

/-!
# The retained cut union on the fixed reference machine

The two cut arrays are represented as linked Boolean rows. The program
walks them in lockstep and reuses a Boolean cell from the selected input
at each position. Only the pair cells of the result are allocated. It
preserves the input heap and random tape and charges the terminal attempt.
-/

namespace DirectedFlowCutGap.RetainedMaskUnionProgram

open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic RetainedGridState

def program : Program 13 := fun pc =>
  match pc.val with
  | 0 => .call 1 12 .r3
  | 1 => .branch .r0 10 11 11 2
  | 2 => .field .r2 .r0 false 3
  | 3 => .field .r0 .r0 true 4
  | 4 => .field .r3 .r1 false 5
  | 5 => .field .r1 .r1 true 6
  | 6 => .branch .r2 11 7 8 11
  | 7 => .move .r2 .r3 8
  | 8 => .call 1 9 .r3
  | 9 => .make .r0 (.pair .r2 .r3) 10
  | 10 => .ret .r0
  | _ => .halt

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 13))
    (source : Bits) (pc : Fin 13) : NaturalState 13 :=
  ⟨heap, heap.length, r, stack, pc, source⟩

def steps : List Bool → ℕ
  | [] => 2
  | b :: bs => steps bs + (if b then 9 else 10)

theorem steps_le (xs : List Bool) : steps xs ≤ 10 * xs.length + 2 := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [steps, List.length_cons, Bool.false_eq_true, ite_false, ite_true] <;> omega

private theorem join {a b c : NaturalState 13} {m n : ℕ} {es fs : List Event}
    (h : NaturalRun program m a es b) (hg : NaturalRun program n b fs c) :
    NaturalRun program (m + n) a (es ++ fs) c := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm 1] using NaturalRun.step ht (ih hg)

theorem union_subroutine {heap : NaturalHeap} {left right : ℕ} {xs ys : Bits}
    (hx : BoolList heap left xs) (hy : BoolList heap right ys) (sameLength : xs.length = ys.length)
    (c d : ℕ) (caller : Frame ℕ 13) (stack : List (Frame ℕ 13)) (source : Bits) :
    ∃ extra root, extra.length = xs.length ∧
      BoolList (heap ++ extra) root (List.zipWith (· || ·) xs ys) ∧
      NaturalRun program (steps xs)
        (state heap ⟨left, right, c, d⟩ (caller :: stack) source 1) []
        (state (heap ++ extra) (caller.saved.set caller.destination root) stack source caller.continuation) := by
  induction hx generalizing right ys c d caller stack with
  | @nil left hp =>
    have hy0 : ys = [] := List.length_eq_zero_iff.mp sameLength.symm
    subst ys
    let saved := caller :: stack
    let regs : Registers ℕ := ⟨left, right, c, d⟩
    let ret := state heap regs saved source 10
    let stop := state heap (caller.saved.set caller.destination left) stack source caller.continuation
    have h1 : tickNatural program (state heap regs saved source 1) = some ⟨ret, [], 0⟩ := by
      simp [tickNatural, program, state, regs, Registers.get, hp, tagBranch, ret]
    have h10 : tickNatural program ret = some ⟨stop, [], 0⟩ := by
      simp [tickNatural, program, state, regs, Registers.get, saved, ret, stop]
    exact ⟨[], left, rfl, by simpa using BoolList.nil hp,
      by simpa [state, steps, stop] using NaturalRun.step h1 (NaturalRun.step h10 (NaturalRun.done stop))⟩
  | @cons left headA tailA a xs hpairA hbitA _ ih =>
    cases hy with
    | nil => simp at sameLength
    | @cons right headB tailB b ys hpairB hbitB restB =>
      let saved := caller :: stack
      let pick := if a then headA else headB
      let s1 := state heap ⟨left, right, c, d⟩ saved source 1
      let s2 := state heap ⟨left, right, c, d⟩ saved source 2
      let s3 := state heap ⟨left, right, headA, d⟩ saved source 3
      let s4 := state heap ⟨tailA, right, headA, d⟩ saved source 4
      let s5 := state heap ⟨tailA, right, headA, headB⟩ saved source 5
      let s6 := state heap ⟨tailA, tailB, headA, headB⟩ saved source 6
      let regs : Registers ℕ := ⟨tailA, tailB, pick, headB⟩
      let s8 := state heap regs saved source 8
      let frame : Frame ℕ 13 := ⟨9, .r3, regs⟩
      have h1 : tickNatural program s1 = some ⟨s2, [], 0⟩ := by
        simp [tickNatural, program, state, Registers.get, tagBranch, hpairA, s1, s2]
      have h2 : tickNatural program s2 = some ⟨s3, [], 0⟩ := by
        simp [tickNatural, program, state, Registers.get, Registers.set, hpairA, s2, s3]
      have h3 : tickNatural program s3 = some ⟨s4, [], 0⟩ := by
        simp [tickNatural, program, state, Registers.get, Registers.set, hpairA, s3, s4]
      have h4 : tickNatural program s4 = some ⟨s5, [], 0⟩ := by
        simp [tickNatural, program, state, Registers.get, Registers.set, hpairB, s4, s5]
      have h5 : tickNatural program s5 = some ⟨s6, [], 0⟩ := by
        simp [tickNatural, program, state, Registers.get, Registers.set, hpairB, s5, s6]
      have hchoose : NaturalRun program (if a then 1 else 2) s6 [] s8 := by
        cases a with
        | false =>
          let s7 := state heap ⟨tailA, tailB, headA, headB⟩ saved source 7
          have h6 : tickNatural program s6 = some ⟨s7, [], 0⟩ := by
            simp [tickNatural, program, state, Registers.get, hbitA, tagBranch, s6, s7]
          have h7 : tickNatural program s7 = some ⟨s8, [], 0⟩ := by
            simp [tickNatural, program, state, Registers.get, Registers.set, s7, s8, regs, pick]
          exact NaturalRun.step h6 (NaturalRun.step h7 (.done s8))
        | true =>
          have h6 : tickNatural program s6 = some ⟨s8, [], 0⟩ := by
            simp [tickNatural, program, state, Registers.get, hbitA, tagBranch, s6, s8, regs, pick]
          exact NaturalRun.step h6 (.done s8)
      have h8 : tickNatural program s8 =
          some ⟨state heap regs (frame :: saved) source 1, [], 0⟩ := rfl
      obtain ⟨extra, tail, hlen, htail, hrun⟩ := ih restB (by simpa using sameLength) pick headB frame saved
      let grown := heap ++ extra
      let s9 := state grown ⟨tailA, tailB, pick, tail⟩ saved source 9
      change NaturalRun program (steps xs) (state heap regs (frame :: saved) source 1) [] s9 at hrun
      let cell : Cell ℕ := .pair pick tail
      let appended := grown ++ [cell]
      let newRoot := grown.length
      let s10 := state appended ⟨newRoot, tailB, pick, tail⟩ saved source 10
      let stop := state appended (caller.saved.set caller.destination newRoot) stack source caller.continuation
      have h9 : tickNatural program s9 = some ⟨s10, [], 0⟩ := by
        simp [tickNatural, program, state, allocateNatural, Recipe.cell, Registers.get, Registers.set,
          s9, s10, cell, appended, newRoot]
      have h10 : tickNatural program s10 = some ⟨stop, [], 0⟩ := by
        simp [tickNatural, program, state, Registers.get, s10, stop, saved]
      have hfinish := NaturalRun.step h9 (NaturalRun.step h10 (.done stop))
      have hrest := NaturalRun.step h8 (join hrun hfinish)
      have hfull := NaturalRun.step h1 (NaturalRun.step h2 (NaturalRun.step h3
        (NaturalRun.step h4 (NaturalRun.step h5 (join hchoose hrest)))))
      have hpick : heap[pick]? = some (.flag (a || b)) := by
        cases a
        · simpa [pick] using hbitB
        · simpa [pick] using hbitA
      have hout : BoolList appended newRoot ((a || b) :: List.zipWith (· || ·) xs ys) := by
        exact .cons (by simp [appended, newRoot, cell])
          (lookup_extend (lookup_extend hpick extra) [cell]) (boolList_extend htail [cell])
      refine ⟨extra ++ [cell], newRoot, by simp [hlen], ?_, ?_⟩
      · simpa only [appended, grown, List.append_assoc, List.zipWith_cons_cons] using hout
      · let count := (if a then 1 else 2) + (steps xs + (0 + 1 + 1) + 1) + 1 + 1 + 1 + 1 + 1
        change NaturalRun program count s1 [] stop at hfull
        have he : count = steps (a :: xs) := by
          cases a
          · simp only [count, steps, Bool.false_eq_true, ite_false]
            omega
          · simp only [count, steps, ite_true]
            omega
        rw [he] at hfull
        simpa only [s1, stop, appended, grown, List.append_assoc] using hfull

private theorem union_toList {n : ℕ} (x y : Flags n) :
    List.zipWith (· || ·) x.toList y.toList = (EncodedRoundingState.union x y).1.toList := by
  rw [EncodedRoundingState.union_value]
  apply List.ext_getElem
  · simp [List.length_zipWith]
  · intro i hi hj
    simp only [List.getElem_zipWith, Vector.getElem_toList, unionFlags, Vector.getElem_ofFn]

private theorem entry (s : NaturalState 13) (hp : s.pc = 0) (hc : s.stack = [])
    (hn : s.next = s.heap.length) :
    s = state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem natural_trace {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {x y : Flags n}
    (hx : BoolList heap r.a x.toList) (hy : BoolList heap r.b y.toList) (tape : Bits) :
    ∃ ext root, ext.length = n ∧
      BoolList (heap ++ ext) root (EncodedRoundingState.union x y).1.toList ∧
      NaturalRun program (steps x.toList + 1) (state heap r [] tape 0) []
        (state (heap ++ ext) (r.set .r3 root) [] tape 12) := by
  let caller : Frame ℕ 13 := ⟨12, .r3, r⟩
  obtain ⟨ext, root, hlen, hout, hrun⟩ :=
    union_subroutine hx hy (by simp) r.c r.d caller [] tape
  have call : tickNatural program (state heap r [] tape 0) =
      some ⟨state heap r [caller] tape 1, [], 0⟩ := rfl
  rw [union_toList] at hout
  exact ⟨ext, root, by simpa using hlen, hout, NaturalRun.step call hrun⟩

theorem retained_union {n H B : ℕ} {initial : BitState 13} {x y : Flags n}
    (hs : initial.Bounded H B) (hp : initial.pc = 0) (hc : initial.stack = [])
    (hd : (eraseState initial).next = (eraseState initial).heap.length)
    (hx : BoolList (eraseState initial).heap (eraseState initial).registers.a x.toList)
    (hy : BoolList (eraseState initial).heap (eraseState initial).registers.b y.toList) :
    ∃ q out, Run program (steps x.toList + 1) q initial [] out ∧
      (attempt program out).result = none ∧
      (eraseState out).pc = 12 ∧ (eraseState out).stack = [] ∧ out.source = initial.source ∧
      BoolList (eraseState out).heap (eraseState out).registers.d (EncodedRoundingState.union x y).1.toList ∧
      (∃ extra, extra.length = n ∧ (eraseState out).heap = (eraseState initial).heap ++ extra) ∧
      q + (attempt program out).operations ≤ completeBound 13 H B (10 * n + 3) := by
  let input := eraseState initial
  have hin : input.stack = [] := by simp [input, eraseState, State.map, hc]
  obtain ⟨ext, root, hlen, hout, hrun⟩ := natural_trace hx hy input.source
  let final := state (input.heap ++ ext) (input.registers.set .r3 root) [] input.source 12
  have start := entry input hp hin hd
  have run : NaturalRun program (steps x.toList + 1) input [] final := start ▸ hrun
  have halt : tickNatural program final = none := rfl
  obtain ⟨q, out, hf, he, ht, hcost, hsupply⟩ := terminating_simulation hs run halt
  refine ⟨q, out, hf, ht, ?_, ?_, hsupply, ?_, ⟨ext, hlen, ?_⟩, hcost.trans ?_⟩
  · rw [he]; rfl
  · rw [he]; rfl
  · rw [he]; exact hout
  · rw [he]; rfl
  · have hsteps : steps x.toList + 1 ≤ 10 * n + 3 := by simpa using Nat.add_le_add_right (steps_le x.toList) 1
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.RetainedMaskUnionProgram
