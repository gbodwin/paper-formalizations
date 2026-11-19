import DirectedFlowCutGap.RetainedMaskUnionProgram
import DirectedFlowCutGap.RetainedDemandEraseProgram

/-!
# Physical update of the two masks in a rounding state

The input retains the demand table and old cut as one pair. A second pair
supplies the row and column index spines. The program clears the demand,
unions the old and sampled cuts, and returns one pair of new roots.
Mass recomputation is a separate part of the rounding step.
-/

namespace DirectedFlowCutGap.RoundMaskUpdateProgram

open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open PackedBooleanConstructor BinaryArithmetic RetainedGridState
open RetainedDemandEraseProgram (RowsAt)

private def eraseLabel (pc : Fin 64) : Fin 92 := ⟨15 + pc.val, by omega⟩
private def unionLabel (pc : Fin 13) : Fin 92 := ⟨79 + pc.val, by omega⟩

def program : Program 92 := fun pc =>
  if pc.val < 15 then
    match pc.val with
    | 0 => .call 10 1 .r1
    | 1 => .field .r0 .r0 true 2
    | 2 => .move .r3 .r1 3
    | 3 => .move .r1 .r2 4
    | 4 => .call (unionLabel 0) 5 .r2
    | 5 => .make .r3 (.pair .r3 .r2) 6
    | 10 => .field .r0 .r0 false 11
    | 11 => .field .r2 .r1 true 12
    | 12 => .field .r1 .r1 false 13
    | 13 => .call (eraseLabel 0) 14 .r3
    | 14 => .ret .r3
    | _ => .halt
  else if pc.val = 17 ∨ pc.val = 91 then .ret .r3
  else if h : pc.val < 79 then
    ReferenceProgramLabels.instruction eraseLabel (RetainedDemandEraseProgram.program ⟨pc.val-15,by omega⟩)
  else
    ReferenceProgramLabels.instruction unionLabel (RetainedMaskUnionProgram.program ⟨pc.val-79,by omega⟩)

private theorem erase_slots (pc : Fin 64) (h : RetainedDemandEraseProgram.program pc ≠ .halt) :
    program (eraseLabel pc) =
      ReferenceProgramLabels.instruction eraseLabel (RetainedDemandEraseProgram.program pc) := by
  fin_cases pc <;> first | rfl | exact (h rfl).elim

private theorem union_slots (pc : Fin 13) (h : RetainedMaskUnionProgram.program pc ≠ .halt) :
    program (unionLabel pc) =
      ReferenceProgramLabels.instruction unionLabel (RetainedMaskUnionProgram.program pc) := by
  fin_cases pc <;> first | rfl | exact (h rfl).elim

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 92))
    (tape : Bits) (pc : Fin 92) : NaturalState 92 :=
  ⟨heap, heap.length, r, stack, pc, tape⟩

private theorem join {a b c : NaturalState 92} {m n : ℕ} {es fs : List Event}
    (h : NaturalRun program m a es b) (hg : NaturalRun program n b fs c) :
    NaturalRun program (m + n) a (es ++ fs) c := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm 1] using NaturalRun.step ht (ih hg)

inductive MaskPairAt {n : ℕ} (heap : NaturalHeap) (root : ℕ) (remaining : PairFlags n)
    (cut : Flags n) : Prop where
  | mk (d x : ℕ) (record : heap[root]? = some (.pair d x))
      (demands : RowsAt heap d remaining) (cutFlags : BoolList heap x cut.toList)

theorem natural_trace {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ}
    {remaining : PairFlags n} {oldCut sample : Flags n} (p : Pair n) (tape : Bits)
    (hm : MaskPairAt heap r.a remaining oldCut)
    (hi : ∃ b c, heap[r.b]? = some (.pair b c) ∧ IndexSpine heap b p.1.val ∧ IndexSpine heap c p.2.val)
    (hsample : BoolList heap r.c sample.toList) (hf : heap[r.d]? = some (.flag false)) :
    ∃ ext root outRegs,
      ext.length = n + p.1.val + p.2.val + 3 ∧ outRegs.d = root ∧
      MaskPairAt (heap ++ ext) root (EncodedRoundingState.erase remaining p).1
        (EncodedRoundingState.union oldCut sample).1 ∧
      NaturalRun program (10*p.1.val + 7*p.2.val + RetainedMaskUnionProgram.steps oldCut.toList + 32)
        (state heap r [] tape 0) [] (state (heap ++ ext) outRegs [] tape 6) := by
  obtain ⟨demands, old, hpair, hdemands, hold⟩ := hm
  obtain ⟨row, col, hindex, hrow, hcol⟩ := hi
  let eraseRegs : Registers ℕ := ⟨demands, row, col, r.d⟩
  obtain ⟨erased, rowRoot, tableRoot, herased, hnewDemands, hErase⟩ :=
    RetainedDemandEraseProgram.natural_trace (r := eraseRegs) p hdemands hrow hcol hf tape
  let grown := heap ++ erased
  let outer : Frame ℕ 92 := ⟨1,.r1,r⟩
  let enterErase : Frame ℕ 92 := ⟨14,.r3,eraseRegs⟩
  let s0 := state heap r [] tape 0
  let s10 := state heap r [outer] tape 10
  let s11 := state heap ⟨demands,r.b,r.c,r.d⟩ [outer] tape 11
  let s12 := state heap ⟨demands,r.b,col,r.d⟩ [outer] tape 12
  let s13 := state heap eraseRegs [outer] tape 13
  let erStart := state heap eraseRegs [enterErase,outer] tape (eraseLabel 0)
  let erStop := state grown ⟨demands,row,rowRoot,tableRoot⟩ [enterErase,outer] tape (eraseLabel 2)
  let s14 := state grown ⟨demands,row,col,tableRoot⟩ [outer] tape 14
  let s1 := state grown (r.set .r1 tableRoot) [] tape 1
  have h0 : tickNatural program s0 = some ⟨s10,[],0⟩ := rfl
  have h10 : tickNatural program s10 = some ⟨s11,[],0⟩ := by
    cases r
    simp [s10, s11, tickNatural, state, program, Registers.get, Registers.set, hpair]
  have h11 : tickNatural program s11 = some ⟨s12,[],0⟩ := by
    simp [s11, s12, tickNatural, state, program, Registers.get, Registers.set, hindex]
  have h12 : tickNatural program s12 = some ⟨s13,[],0⟩ := by
    simp [s12, s13, tickNatural, state, program, Registers.get, Registers.set, eraseRegs, hindex]
  have h13 : tickNatural program s13 = some ⟨erStart,[],0⟩ := rfl
  have lifted := ReferenceProgramLabels.run eraseLabel RetainedDemandEraseProgram.program program erase_slots hErase
  have eraseRun : NaturalRun program (10*p.1.val+7*p.2.val+18) erStart [] erStop :=
    ReferenceProgramStack.run program [enterErase,outer] lifted
  have erReturn : tickNatural program erStop = some ⟨s14,[],0⟩ := rfl
  have h14 : tickNatural program s14 = some ⟨s1,[],0⟩ := rfl
  let s2 := state grown ⟨old,tableRoot,r.c,r.d⟩ [] tape 2
  let s3 := state grown ⟨old,tableRoot,r.c,tableRoot⟩ [] tape 3
  let unionRegs : Registers ℕ := ⟨old,r.c,r.c,tableRoot⟩
  let s4 := state grown unionRegs [] tape 4
  let frame : Frame ℕ 92 := ⟨5,.r2,unionRegs⟩
  let unStart := state grown unionRegs [frame] tape (unionLabel 0)
  have h1 : tickNatural program s1 = some ⟨s2,[],0⟩ := by
    have hp := lookup_extend hpair erased
    cases r
    simp [s1, s2, grown, tickNatural, state, program, Registers.get, Registers.set, hp]
  have h2 : tickNatural program s2 = some ⟨s3,[],0⟩ := rfl
  have h3 : tickNatural program s3 = some ⟨s4,[],0⟩ := rfl
  have h4 : tickNatural program s4 = some ⟨unStart,[],0⟩ := rfl
  obtain ⟨unionCells, unionRoot, hunion, hnewCut, hUnion⟩ :=
    RetainedMaskUnionProgram.natural_trace (r := unionRegs)
      (boolList_extend hold erased) (boolList_extend hsample erased) tape
  let afterUnion := grown ++ unionCells
  let unStop := state afterUnion (unionRegs.set .r3 unionRoot) [frame] tape (unionLabel 12)
  let s5 := state afterUnion ⟨old,r.c,unionRoot,tableRoot⟩ [] tape 5
  have lifted := ReferenceProgramLabels.run unionLabel RetainedMaskUnionProgram.program program union_slots hUnion
  have unionRun : NaturalRun program (RetainedMaskUnionProgram.steps oldCut.toList+1) unStart [] unStop :=
    ReferenceProgramStack.run program [frame] lifted
  have unReturn : tickNatural program unStop = some ⟨s5,[],0⟩ := rfl
  let cell : Cell ℕ := .pair tableRoot unionRoot
  let root := afterUnion.length
  let outRegs : Registers ℕ := ⟨old,r.c,unionRoot,root⟩
  let finalHeap := afterUnion ++ [cell]
  let s6 := state finalHeap outRegs [] tape 6
  have h5 : tickNatural program s5 = some ⟨s6,[],0⟩ := by
    simp [tickNatural, program, state, Registers.get, Registers.set, allocateNatural, Recipe.cell,
      s5, s6, finalHeap, cell, root, outRegs]
  let newCells := erased ++ unionCells ++ [cell]
  have hpair' : finalHeap[root]? = some (.pair tableRoot unionRoot) := by simp [finalHeap, root, cell]
  obtain ⟨refs, hptr, hrows⟩ := hnewDemands
  have hdemands' : RowsAt finalHeap tableRoot (EncodedRoundingState.erase remaining p).1 :=
    ⟨refs, BinaryPointerListRead.pointerList_extend (BinaryPointerListRead.pointerList_extend hptr unionCells) [cell],
      hrows.imp (fun _ _ h => boolList_extend (boolList_extend h unionCells) [cell])⟩
  have hrep : MaskPairAt finalHeap root (EncodedRoundingState.erase remaining p).1
      (EncodedRoundingState.union oldCut sample).1 :=
    ⟨tableRoot,unionRoot,hpair',hdemands',boolList_extend hnewCut [cell]⟩
  have unSuffix := join unionRun (.step unReturn (.step h5 (.done s6)))
  have unPrefix := NaturalRun.step h1 (.step h2 (.step h3 (.step h4 unSuffix)))
  have erSuffix := join eraseRun (.step erReturn (.step h14 unPrefix))
  have full := NaturalRun.step h0 (.step h10 (.step h11 (.step h12 (.step h13 erSuffix))))
  let count := (10*p.1.val+7*p.2.val+18) +
    (RetainedMaskUnionProgram.steps oldCut.toList+1 + (0+1+1)+1+1+1+1+1+1) + 1+1+1+1+1
  change NaturalRun program count s0 [] s6 at full
  have hcount : count = 10*p.1.val+7*p.2.val+RetainedMaskUnionProgram.steps oldCut.toList+32 := by
    unfold count
    omega
  rw [hcount] at full
  refine ⟨newCells, root, outRegs, by simp [newCells, herased, hunion]; omega, rfl, ?_, ?_⟩
  · simpa only [newCells, finalHeap, afterUnion, grown, List.append_assoc] using hrep
  · simpa only [s0, s6, newCells, finalHeap, afterUnion, grown, List.append_assoc] using full

private theorem at_entry (s : NaturalState 92) (hp : s.pc = 0) (hc : s.stack = [])
    (hn : s.next = s.heap.length) :
    s = state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem update_masks {n H B : ℕ} {initial : BitState 92} (d : Data n) (p : Pair n) (y : Flags n)
    (hs : initial.Bounded H B) (hp : initial.pc = 0) (hc : initial.stack = [])
    (hn : (eraseState initial).next = (eraseState initial).heap.length)
    (hm : MaskPairAt (eraseState initial).heap (eraseState initial).registers.a d.remaining d.cut)
    (hi : ∃ b c, (eraseState initial).heap[(eraseState initial).registers.b]? = some (.pair b c) ∧
      IndexSpine (eraseState initial).heap b p.1.val ∧ IndexSpine (eraseState initial).heap c p.2.val)
    (hy : BoolList (eraseState initial).heap (eraseState initial).registers.c y.toList)
    (hf : (eraseState initial).heap[(eraseState initial).registers.d]? = some (.flag false)) :
    let expected := (EncodedRoundingState.roundData d p y).1
    ∃ q out,
      Run program (10*p.1.val + 7*p.2.val + RetainedMaskUnionProgram.steps d.cut.toList + 32) q initial [] out ∧
      (attempt program out).result = none ∧ (eraseState out).pc = 6 ∧
      (eraseState out).stack = [] ∧ out.source = initial.source ∧
      MaskPairAt (eraseState out).heap (eraseState out).registers.d expected.remaining expected.cut ∧
      (∃ ext, ext.length = n + p.1.val + p.2.val + 3 ∧ (eraseState out).heap = (eraseState initial).heap ++ ext) ∧
      q + (attempt program out).operations ≤ completeBound 92 H B (27*n+34) := by
  let input := eraseState initial
  obtain ⟨ext, root, regs, hlen, hd, hmask, htrace⟩ := natural_trace p input.source hm hi hy hf
  have hnil : input.stack = [] := by simp [input, eraseState, State.map, hc]
  have he := at_entry input hp hnil hn
  let final := state (input.heap ++ ext) regs [] input.source 6
  change NaturalRun program _ (state input.heap input.registers [] input.source 0) [] final at htrace
  have hrun : NaturalRun program (10*p.1.val + 7*p.2.val + RetainedMaskUnionProgram.steps d.cut.toList + 32)
      input [] final := by
    rw [he]
    exact htrace
  have hhalt : tickNatural program final = none := rfl
  obtain ⟨q, out, hr, hout, hstop, hwork, htape⟩ := terminating_simulation hs hrun hhalt
  refine ⟨q,out,hr,hstop,?_,?_,htape,?_,⟨ext,hlen,?_⟩,hwork.trans ?_⟩
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]
    change MaskPairAt (input.heap ++ ext) regs.d (EncodedRoundingState.erase d.remaining p).1
      (EncodedRoundingState.union d.cut y).1
    rwa [hd]
  · rw [hout]; rfl
  · have hsteps := RetainedMaskUnionProgram.steps_le d.cut.toList
    have ha := p.1.isLt.le
    have hb := p.2.isLt.le
    have hk : 10*p.1.val + 7*p.2.val + RetainedMaskUnionProgram.steps d.cut.toList + 32 ≤ 27*n+34 := by
      simp only [Vector.length_toList] at hsteps
      omega
    unfold completeBound runBound stepBound
    gcongr

end DirectedFlowCutGap.RoundMaskUpdateProgram
