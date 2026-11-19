import DirectedFlowCutGap.LinkedSlotReplaceProgram
import DirectedFlowCutGap.EncodedRoundingState
import Mathlib.Data.List.Forall2

/-!
# Clearing one demand in a retained Boolean matrix

The literal calls locate the chosen row, replace the chosen flag, and
install the new row reference in the matrix. Both index spines are
retained inputs. Immutable storage shares each untouched suffix.
-/

namespace DirectedFlowCutGap.RetainedDemandEraseProgram

open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead
open BinaryPointerListRead PackedBooleanConstructor BinaryArithmetic RetainedGridState

private def innerLabel (pc : Fin 14) : Fin 64 :=
  if pc.val = 13 then 7 else ⟨8 + pc.val, by omega⟩

private def outerLabel (pc : Fin 14) : Fin 64 :=
  if pc.val = 13 then 2 else ⟨22 + pc.val, by omega⟩

private def readLabel (pc : Fin 27) : Fin 64 := ⟨36 + pc.val, by omega⟩

def program : Program 64 := fun pc =>
  if pc.val < 8 then
    match pc.val with
    | 0 => .call 3 1 .r2
    | 1 => .call (outerLabel 1) 2 .r3
    | 3 => .call (readLabel 18) 4 .r0
    | 4 => .move .r1 .r2 5
    | 5 => .move .r2 .r3 6
    | 6 => .call (innerLabel 1) 7 .r0
    | 7 => .ret .r0
    | _ => .halt
  else if h : pc.val < 22 then
    ReferenceProgramLabels.instruction innerLabel (LinkedSlotReplaceProgram.program ⟨pc.val-8, by omega⟩)
  else if h : pc.val < 36 then
    ReferenceProgramLabels.instruction outerLabel (LinkedSlotReplaceProgram.program ⟨pc.val-22, by omega⟩)
  else if h : pc.val < 63 then
    ReferenceProgramLabels.instruction readLabel (BinaryPointerListRead.program ⟨pc.val-36, by omega⟩)
  else .halt

private theorem inner_slots (pc : Fin 14) (h : LinkedSlotReplaceProgram.program pc ≠ .halt) :
    program (innerLabel pc) =
      ReferenceProgramLabels.instruction innerLabel (LinkedSlotReplaceProgram.program pc) := by
  fin_cases pc <;> first | rfl | exact (h rfl).elim

private theorem outer_slots (pc : Fin 14) (_ : LinkedSlotReplaceProgram.program pc ≠ .halt) :
    program (outerLabel pc) =
      ReferenceProgramLabels.instruction outerLabel (LinkedSlotReplaceProgram.program pc) := by
  fin_cases pc <;> rfl

private theorem read_slots (pc : Fin 27) (_ : BinaryPointerListRead.program pc ≠ .halt) :
    program (readLabel pc) =
      ReferenceProgramLabels.instruction readLabel (BinaryPointerListRead.program pc) := by
  fin_cases pc <;> rfl

def state (heap : NaturalHeap) (r : Registers ℕ) (stack : List (Frame ℕ 64))
    (tape : Bits) (pc : Fin 64) : NaturalState 64 :=
  ⟨heap, heap.length, r, stack, pc, tape⟩

private theorem join {a b c : NaturalState 64} {m n : ℕ} {es fs : List Event}
    (h : NaturalRun program m a es b) (hg : NaturalRun program n b fs c) :
    NaturalRun program (m + n) a (es ++ fs) c := by
  induction h with
  | done _ => simpa using hg
  | step ht _ ih =>
    simpa only [List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm 1] using NaturalRun.step ht (ih hg)

private theorem replace_return (label : Fin 14 → Fin 64)
    (slots : ∀ pc, LinkedSlotReplaceProgram.program pc ≠ .halt →
      program (label pc) = ReferenceProgramLabels.instruction label (LinkedSlotReplaceProgram.program pc))
    {heap : NaturalHeap} {a b i : ℕ} {xs : List ℕ}
    (row : PointerList heap a xs) (index : IndexSpine heap b i) (hi : i < xs.length)
    (new scratch : ℕ) (saved : Registers ℕ) (dest : Reg) (stack : List (Frame ℕ 64)) (tape : Bits) :
    ∃ ext root, ext.length = i + 1 ∧ PointerList (heap ++ ext) root (xs.set i new) ∧
      NaturalRun program (7*i+4)
        (state heap ⟨a,b,new,scratch⟩ (⟨label 13,dest,saved⟩ :: stack) tape (label 1)) []
        (state (heap ++ ext) (saved.set dest root) stack tape (label 13)) := by
  obtain ⟨ext, root, hlen, hrep, hr⟩ :=
    LinkedSlotReplaceProgram.replace_subroutine row index hi new scratch ⟨13, dest, saved⟩ [] tape
  have lift := ReferenceProgramLabels.run label LinkedSlotReplaceProgram.program program slots hr
  have lift := ReferenceProgramStack.run program stack lift
  refine ⟨ext, root, hlen, hrep, ?_⟩
  simpa only [ReferenceProgramLabels.state, ReferenceProgramLabels.frame, ReferenceProgramStack.state,
    LinkedSlotReplaceProgram.state, state, List.map_cons, List.map_nil, List.cons_append, List.nil_append] using lift

private theorem lookup_return {heap : NaturalHeap} {a b i : ℕ} {rows : List ℕ}
    (row : PointerList heap a rows) (idx : IndexSpine heap b i) (hi : i < rows.length)
    (c d : ℕ) (stack : List (Frame ℕ 64)) (tape : Bits) :
    let saved : Registers ℕ := ⟨a,b,c,d⟩
    NaturalRun program (3*i+3)
      (state heap saved (⟨4,.r0,saved⟩ :: stack) tape (readLabel 18)) []
      (state heap ⟨rows[i],b,c,d⟩ stack tape 4) := by
  let saved : Registers ℕ := ⟨a,b,c,d⟩
  let caller : Frame ℕ 64 := ⟨4,.r0,saved⟩
  obtain ⟨a', b', h⟩ := BinaryPointerListRead.loop row idx hi heap.length c d [] tape
  have lift := ReferenceProgramLabels.run readLabel BinaryPointerListRead.program program read_slots h
  have lift := ReferenceProgramStack.run program (caller :: stack) lift
  let before := state heap ⟨a',b',c,rows[i]⟩ (caller :: stack) tape (readLabel 22)
  let after := state heap ⟨rows[i],b,c,d⟩ stack tape 4
  have walk : NaturalRun program (3*i+2)
      (state heap saved (caller :: stack) tape (readLabel 18)) [] before := lift
  have ret : tickNatural program before = some ⟨after, [], 0⟩ := rfl
  exact join walk (NaturalRun.step ret (.done after))

theorem pointer_update {heap : NaturalHeap} {a s t f i j : ℕ} {rows cells : List ℕ}
    (matrix : PointerList heap a rows) (rowIndex : IndexSpine heap s i) (hi : i < rows.length)
    (chosen : PointerList heap rows[i] cells) (columnIndex : IndexSpine heap t j) (hj : j < cells.length)
    (tape : Bits) :
    ∃ eRow eMatrix newRow out,
      eRow.length = j+1 ∧ eMatrix.length = i+1 ∧
      PointerList (heap ++ eRow ++ eMatrix) newRow (cells.set j f) ∧
      PointerList (heap ++ eRow ++ eMatrix) out (rows.set i newRow) ∧
      NaturalRun program (10*i+7*j+18) (state heap ⟨a,s,t,f⟩ [] tape 0) []
        (state (heap ++ eRow ++ eMatrix) ⟨a,s,newRow,out⟩ [] tape 2) := by
  let r0 : Registers ℕ := ⟨a,s,t,f⟩
  let frame : Frame ℕ 64 := ⟨1,.r2,r0⟩
  let s0 := state heap r0 [] tape 0
  let s3 := state heap r0 [frame] tape 3
  let r4 : Registers ℕ := ⟨rows[i],s,t,f⟩
  let r5 : Registers ℕ := ⟨rows[i],t,t,f⟩
  let r6 : Registers ℕ := ⟨rows[i],t,f,f⟩
  let s4 := state heap r4 [frame] tape 4
  let s5 := state heap r5 [frame] tape 5
  let s6 := state heap r6 [frame] tape 6
  have h0 : tickNatural program s0 = some ⟨s3, [], 0⟩ := rfl
  have h3 : tickNatural program s3 =
      some ⟨state heap r0 (⟨4,.r0,r0⟩ :: [frame]) tape (readLabel 18), [], 0⟩ := rfl
  have hlook := lookup_return matrix rowIndex hi t f [frame] tape
  change NaturalRun program (3*i+3) (state heap r0 (⟨4,.r0,r0⟩ :: [frame]) tape (readLabel 18)) [] s4 at hlook
  have h4 : tickNatural program s4 = some ⟨s5, [], 0⟩ := rfl
  have h5 : tickNatural program s5 = some ⟨s6, [], 0⟩ := rfl
  have h6 : tickNatural program s6 =
      some ⟨state heap r6 (⟨innerLabel 13,.r0,r6⟩ :: [frame]) tape (innerLabel 1), [], 0⟩ := rfl
  obtain ⟨eRow, newRow, hre, hrow, hinner⟩ :=
    replace_return innerLabel inner_slots chosen columnIndex hj f f r6 .r0 [frame] tape
  let grown := heap ++ eRow
  let s7 := state grown ⟨newRow,t,f,f⟩ [frame] tape 7
  change NaturalRun program (7*j+4)
    (state heap r6 (⟨innerLabel 13,.r0,r6⟩ :: [frame]) tape (innerLabel 1)) [] s7 at hinner
  let r1 : Registers ℕ := ⟨a,s,newRow,f⟩
  let s1 := state grown r1 [] tape 1
  have h7 : tickNatural program s7 = some ⟨s1, [], 0⟩ := rfl
  have h1 : tickNatural program s1 =
      some ⟨state grown r1 [⟨outerLabel 13,.r3,r1⟩] tape (outerLabel 1), [], 0⟩ := rfl
  obtain ⟨eMatrix, out, hme, hout, houter⟩ :=
    replace_return outerLabel outer_slots (pointerList_extend matrix eRow)
      (indexSpine_extend rowIndex eRow) hi newRow f r1 .r3 [] tape
  let finish := state (grown ++ eMatrix) ⟨a,s,newRow,out⟩ [] tape 2
  change NaturalRun program (7*i+4) (state grown r1 [⟨outerLabel 13,.r3,r1⟩] tape (outerLabel 1)) [] finish at houter
  have endRun := NaturalRun.step h7 (.step h1 houter)
  have middle := NaturalRun.step h4 (.step h5 (.step h6 (join hinner endRun)))
  have full := NaturalRun.step h0 (.step h3 (join hlook middle))
  refine ⟨eRow, eMatrix, newRow, out, hre, hme, pointerList_extend hrow eMatrix, hout, ?_⟩
  let count := 3*i+3 + (7*j+4 + (7*i+4+1+1)+1+1+1)+1+1
  change NaturalRun program count s0 [] finish at full
  have hcount : count = 10*i+7*j+18 := by unfold count; omega
  rw [hcount] at full
  exact full

def RowsAt {n : ℕ} (heap : NaturalHeap) (root : ℕ) (mask : PairFlags n) : Prop :=
  ∃ refs, PointerList heap root refs ∧
    List.Forall₂ (fun ref (row : Flags n) => BoolList heap ref row.toList) refs mask.toList

private theorem flag_refs {heap : NaturalHeap} {root : ℕ} {flags : Bits}
    (h : BoolList heap root flags) :
    ∃ refs, PointerList heap root refs ∧
      List.Forall₂ (fun p b => heap[p]? = some (.flag b)) refs flags := by
  induction h with
  | nil hn => exact ⟨[], .nil hn, .nil⟩
  | @cons root head tail flag flags hp hf _ ih =>
    obtain ⟨refs, hr, hrel⟩ := ih
    exact ⟨head :: refs, .cons hp hr, .cons hf hrel⟩

private theorem flags_of_refs {heap : NaturalHeap} {root : ℕ} {refs : List ℕ} {flags : Bits}
    (h : PointerList heap root refs) (hr : List.Forall₂ (fun p b => heap[p]? = some (.flag b)) refs flags) :
    BoolList heap root flags := by
  induction h generalizing flags with
  | nil hn =>
    cases hr
    exact .nil hn
  | cons hp _ ih =>
    cases hr with
    | cons hf ht => exact .cons hp hf (ih ht)

private theorem set_related {A B : Type} {R : A → B → Prop} {xs : List A} {ys : List B}
    (h : List.Forall₂ R xs ys) (i : ℕ) {a : A} {b : B} (hab : R a b) :
    List.Forall₂ R (xs.set i a) (ys.set i b) := by
  induction h generalizing i with
  | nil => exact .nil
  | cons hh ht ih =>
    cases i with
    | zero => exact .cons hab ht
    | succ k => exact .cons hh (ih k)

private theorem erase_value {n : ℕ} (mask : PairFlags n) (p : Pair n) :
    mask.set p.1.val (mask[p.1.val].set p.2.val false p.2.isLt) p.1.isLt =
      (EncodedRoundingState.erase mask p).1 := by
  rw [EncodedRoundingState.erase_value]
  rcases p with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_set, eraseFlag, Vector.getElem_ofFn, flag, Prod.mk.injEq, Fin.mk.injEq]
  by_cases hrow : s = i
  · subst i
    by_cases hcol : t = j
    · subst j
      simp
    · simp [hcol, Ne.symm hcol]
  · simp [hrow, Ne.symm hrow]

private theorem at_entry (s : NaturalState 64) (hp : s.pc = 0) (hd : s.next = s.heap.length)
    (hs : s.stack = []) :
    s = state s.heap s.registers [] s.source 0 := by
  cases s
  simp_all [state]

theorem natural_trace {n : ℕ} {heap : NaturalHeap} {r : Registers ℕ} {mask : PairFlags n}
    (p : Pair n) (hm : RowsAt heap r.a mask)
    (hi : IndexSpine heap r.b p.1.val) (hj : IndexSpine heap r.c p.2.val)
    (hf : heap[r.d]? = some (.flag false)) (tape : Bits) :
    ∃ ext rowRoot matrixRoot,
      ext.length = p.1.val + p.2.val + 2 ∧
      RowsAt (heap ++ ext) matrixRoot (EncodedRoundingState.erase mask p).1 ∧
      NaturalRun program (10*p.1.val + 7*p.2.val + 18) (state heap r [] tape 0) []
        (state (heap ++ ext) ⟨r.a,r.b,rowRoot,matrixRoot⟩ [] tape 2) := by
  obtain ⟨refs, hmatrix, hrows⟩ := hm
  have hi' : p.1.val < refs.length := by simp [hrows.length_eq, p.1.isLt]
  have hs' : p.1.val < mask.toList.length := by simp [p.1.isLt]
  have chosen : BoolList heap refs[p.1.val] mask[p.1.val].toList := by
    simpa only [List.get_eq_getElem, Vector.getElem_toList] using hrows.get hi' hs'
  obtain ⟨cells, hrow, hflags⟩ := flag_refs chosen
  have hj' : p.2.val < cells.length := by simp [hflags.length_eq, p.2.isLt]
  obtain ⟨inner, outer, rowRoot, matrixRoot, hinner, houter, hrow', hmatrix', htrace⟩ :=
    pointer_update (f := r.d) hmatrix hi hi' hrow hj hj' tape
  let ext := inner ++ outer
  let grown := heap ++ ext
  have hflags' : List.Forall₂ (fun q b => grown[q]? = some (.flag b)) cells mask[p.1.val].toList :=
    hflags.imp (fun _ _ h => lookup_extend h ext)
  have hrow'' : BoolList grown rowRoot ((mask[p.1.val].set p.2.val false p.2.isLt).toList) := by
    rw [Vector.toList_set]
    exact flags_of_refs (by simpa only [grown, ext, List.append_assoc] using hrow')
      (set_related hflags' p.2.val (lookup_extend hf ext))
  have hrows' : List.Forall₂ (fun ref (row : Flags n) => BoolList grown ref row.toList) refs mask.toList :=
    hrows.imp (fun _ _ h => boolList_extend h ext)
  have hmatrix'' : RowsAt grown matrixRoot (EncodedRoundingState.erase mask p).1 := by
    rw [← erase_value, RowsAt, Vector.toList_set]
    exact ⟨refs.set p.1.val rowRoot, by simpa only [grown, ext, List.append_assoc] using hmatrix',
      set_related hrows' p.1.val hrow''⟩
  exact ⟨ext, rowRoot, matrixRoot, by simp [ext, hinner, houter]; omega, hmatrix'',
    by simpa only [ext, List.append_assoc] using htrace⟩

theorem retained_erase {n H B : ℕ} {initial : BitState 64} {mask : PairFlags n} (p : Pair n)
    (hs : initial.Bounded H B) (hp : initial.pc = 0) (hc : initial.stack = [])
    (hd : (eraseState initial).next = (eraseState initial).heap.length)
    (hm : RowsAt (eraseState initial).heap (eraseState initial).registers.a mask)
    (hi : IndexSpine (eraseState initial).heap (eraseState initial).registers.b p.1.val)
    (hj : IndexSpine (eraseState initial).heap (eraseState initial).registers.c p.2.val)
    (hf : (eraseState initial).heap[(eraseState initial).registers.d]? = some (.flag false)) :
    ∃ q out, Run program (10*p.1.val + 7*p.2.val + 18) q initial [] out ∧
      (attempt program out).result = none ∧ (eraseState out).pc = 2 ∧
      (eraseState out).stack = [] ∧ out.source = initial.source ∧
      RowsAt (eraseState out).heap (eraseState out).registers.d (EncodedRoundingState.erase mask p).1 ∧
      (∃ ext, ext.length = p.1.val + p.2.val + 2 ∧ (eraseState out).heap = (eraseState initial).heap ++ ext) ∧
      q + (attempt program out).operations ≤ completeBound 64 H B (17*n+18) := by
  let input := eraseState initial
  obtain ⟨ext, rowRoot, matrixRoot, hext, hmatrix, htrace⟩ := natural_trace p hm hi hj hf input.source
  let heap := input.heap ++ ext
  let final := state heap ⟨input.registers.a,input.registers.b,rowRoot,matrixRoot⟩ [] input.source 2
  have hnil : input.stack = [] := by simp [input, eraseState, State.map, hc]
  have he : input = state input.heap input.registers [] input.source 0 :=
    at_entry input hp hd hnil
  have hrun : NaturalRun program (10*p.1.val + 7*p.2.val + 18) input [] final := by
    rw [he]
    exact htrace
  have halt : tickNatural program final = none := rfl
  obtain ⟨q, out, hrun', hout, hstop, hpays, htape⟩ := terminating_simulation hs hrun halt
  refine ⟨q, out, hrun', hstop, ?_, ?_, htape, ?_, ⟨ext, hext, ?_⟩, hpays.trans ?_⟩
  · rw [hout]; rfl
  · rw [hout]; rfl
  · rw [hout]; exact hmatrix
  · rw [hout]; rfl
  · unfold completeBound runBound stepBound
    have ha := p.1.isLt.le
    have hb := p.2.isLt.le
    have hs : 10 * p.1.val + 7 * p.2.val + 18 ≤ 17 * n + 18 := by omega
    gcongr

end DirectedFlowCutGap.RetainedDemandEraseProgram
