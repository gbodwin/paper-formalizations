import DirectedFlowCutGap.CachedHeapWidths
import DirectedFlowCutGap.CachedHeapCopies

/-! The scalar operands of a cached allocation are taken from the actual
heap, payload-counter and address-counter appends. -/
namespace DirectedFlowCutGap.CachedControllerStorage

open BinaryArithmetic ImmutableReferenceSimulation EncodedArrayStorage
open CachedReferenceExecution (FastState)
open CachedReferenceHeap (Store)
open CachedHeapWidths (payload_counter address_counter readerWidth)
open CachedHeapCopies (payloadAfter addressAfter)

private theorem appended_size (s : Store) (c : Cell Bits) :
    (CachedReferenceHeap.append s c).1.cells.size=s.cells.size+1 :=
  Array.size_push c

private theorem last_values (s : Store) (c : Cell Bits) :
    let out := (CachedReferenceHeap.append s c).1
    out.cellPrefix[out.cells.size]?.getD 0=payloadAfter s c ∧
      out.countPrefix[out.cells.size]?.getD 0=addressAfter s := by
  dsimp only
  rw [appended_size]
  constructor
  · change (s.cellPrefix.push (payloadAfter s c))[s.cells.size+1]?.getD 0=_
    rw [← s.cell_size,Array.getElem?_push_size,Option.getD_some]
  · change (s.countPrefix.push (addressAfter s))[s.cells.size+1]?.getD 0=_
    rw [← s.count_size,Array.getElem?_push_size,Option.getD_some]

def AppendOperands (s : Store) (c : Cell Bits) (W : ℕ) : Prop :=
  s.cells.size.size ≤ W ∧ (s.cells.size+1).size ≤ W ∧
    (payloadAfter s c).size ≤ W ∧ (addressAfter s).size ≤ W ∧
    (CachedReferenceHeap.append s c).2.size ≤ W

theorem append_operands {s : Store} {c : Cell Bits} {H B : ℕ} (cells : s.cells.size≤H)
    (bounded : Heap.Bounded B s.cells.toList) (valueFits : c.Bounded B) :
    AppendOperands s c (readerWidth (H+1) B) := by
  let out := (CachedReferenceHeap.append s c).1
  let N := H+2
  let M := max B N.size
  let Q := 64*N*(M+1)
  have outSize : out.cells.size=s.cells.size+1 := appended_size s c
  obtain ⟨payloadEq,addressEq⟩ := last_values s c
  change out.cellPrefix[out.cells.size]?.getD 0=payloadAfter s c at payloadEq
  change out.countPrefix[out.cells.size]?.getD 0=addressAfter s at addressEq
  have heapEq : out.cells.toList=s.cells.toList++[c] := by
    change ((CachedReferenceHeap.push s c).cells.toList)=_
    exact CachedReferenceHeap.push_value s c
  have good : Heap.Bounded B out.cells.toList := by
    intro cell mem
    rw [heapEq,List.mem_append,List.mem_singleton] at mem
    rcases mem with h|rfl
    · exact bounded cell h
    · exact valueFits
  have cardinal : out.cells.size≤N := by dsimp only [N]; omega
  have p := payload_counter out B out.cells.size good le_rfl
  have q := address_counter out out.cells.size le_rfl
  rw [payloadEq] at p
  rw [addressEq] at q
  have maxB : B ≤ M := le_max_left ..
  have maxSize : out.cells.size.size ≤ M := (Nat.size_le_size cardinal).trans (le_max_right ..)
  have pCap : payloadAfter s c≤Q := p.trans (by
    calc
      _ ≤ N*(64*(M+1)) := Nat.mul_le_mul cardinal (Nat.mul_le_mul (by decide) (Nat.add_le_add_right maxB 1))
      _ = Q := by unfold Q; ring)
  have qCap : addressAfter s≤Q := q.trans (Nat.mul_le_mul (Nat.mul_le_mul (by decide) cardinal)
    (Nat.add_le_add_right maxSize 1))
  have same := congrArg Prod.snd (CachedReferenceHeap.append_eq s c)
  change (CachedReferenceHeap.append s c).2=(appendCell s.cells.toList c).2 at same
  have charged := appendCell_bound bounded valueFits
  rw [← same,Array.length_toList] at charged
  have chargeCap : (CachedReferenceHeap.append s c).2≤Q := charged.trans
    (Nat.mul_le_mul (Nat.mul_le_mul (by decide) (by dsimp only [N]; omega)) (Nat.add_le_add_right maxB 1))
  have sizeCap : N≤Q := by
    dsimp only [Q]
    calc
      N ≤ 64*N := by omega
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  have toWidth {v : ℕ} (le : v≤Q) : v.size ≤ readerWidth (H+1) B :=
    (Nat.size_le_size le).trans (le_max_right B Q.size)
  exact ⟨toWidth (show s.cells.size≤N by dsimp only [N];omega |>.trans sizeCap),
    toWidth (show s.cells.size+1≤N by dsimp only [N];omega |>.trans sizeCap),
    toWidth pCap,toWidth qCap,toWidth chargeCap⟩

/-- The original evaluator uses these two cases to append to the cached heap. -/
theorem attempt_append_width {C H B : ℕ} (p : Program C) (s : FastState C) (fits : s.freeze.Bounded H B) :
    match p s.pc with
    | .make _ recipe _ => AppendOperands s.store (recipe.cell s.registers) (readerWidth (H+1) B)
    | .request _ _ => AppendOperands s.store (.flag (s.source.headD false)) (readerWidth (H+1) B)
    | _ => True := by
  have records := fits.1
  simp only [State.records,FastState.freeze,Array.length_toList] at records
  have size : s.store.cells.size≤H := by omega
  have heap : Heap.Bounded B s.store.cells.toList := fits.2.2.1
  have registers : s.registers.All (fun a => a.length≤B) := fits.2.2.2.1
  cases p s.pc with
  | make dst recipe pc => exact append_operands size heap (recipe.bounded registers)
  | request dst pc => exact append_operands size heap trivial
  | _ => exact True.intro

end DirectedFlowCutGap.CachedControllerStorage
