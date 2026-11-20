import DirectedFlowCutGap.CachedReferenceExecution

/-! Bounds for the actual natural-number metadata and indexes in the cached
reference reader. The storage and reference read operations are unchanged. -/
namespace DirectedFlowCutGap.CachedHeapWidths

open BinaryArithmetic ImmutableReferenceSimulation EncodedSequenceAccess
open CachedReferenceHeap (Store push)

private theorem cell_sum (B : ℕ) (heap : Heap) (bounded : heap.Bounded B) :
    (heap.map fun c => (copyCell c).2).sum ≤ heap.length*(8*(B+1)) := by
  induction heap with
  | nil => simp
  | cons cell rest ih =>
      have first := copyCell_bound (bounded cell (List.mem_cons_self ..))
      have later := ih (fun c member => bounded c (List.mem_cons_of_mem _ member))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem payload_counter (s : Store) (B i : ℕ) (bounded : Heap.Bounded B s.cells.toList)
    (inside : i≤s.cells.size) : s.cellPrefix[i]?.getD 0 ≤ i*(8*(B+1)) := by
  have found := s.cell_spec i inside
  change s.cellPrefix[i]?=some (((s.cells.toList.take i).map fun c => (copyCell c).2).sum) at found
  rw [found,Option.getD_some]
  have readers : Heap.Bounded B (s.cells.toList.take i) := fun c found =>
    bounded c (List.mem_of_mem_take found)
  exact (cell_sum B _ readers).trans (Nat.mul_le_mul_right _ (by simp))

private def sample : ℕ → Store
  | 0 => CachedReferenceHeap.empty
  | n+1 => push (sample n) .nil

private theorem sample_size (n : ℕ) : (sample n).cells.size=n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((sample n).cells.push .nil).size=n+1
      rw [Array.size_push,ih]

private theorem skip_work (word : Bits) : (isZero word).2+(predecessor word).2+6≤42*(word.length+1) := by
  have a := (isZero_spec word).2
  have b := (predecessor_spec word).2.2
  omega

private theorem next_count (s : Store) :
    (push s .nil).countPrefix[s.cells.size+1]?.getD 0 =
      s.countPrefix[s.cells.size]?.getD 0+(isZero (s.cells.size+1).bits).2+
        (predecessor (s.cells.size+1).bits).2+6 := by
  let word := (s.cells.size+1).bits
  let q := s.countPrefix[s.cells.size]?.getD 0 + ((isZero word).2+(predecessor word).2+6)
  change (s.countPrefix.push q)[s.cells.size+1]?.getD 0 = _
  have next : (s.countPrefix.push q)[s.cells.size+1]?=some q := by
    rw [← s.count_size]
    exact Array.getElem?_push_size
  rw [next,Option.getD_some]
  unfold q word
  omega

private theorem sample_counter (n : ℕ) :
    (sample n).countPrefix[n]?.getD 0 ≤ 42*n*(n.size+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      change (push (sample n) .nil).countPrefix[n+1]?.getD 0≤42*(n+1)*((n+1).size+1)
      have step_work := next_count (sample n)
      rw [sample_size n] at step_work
      rw [step_work]
      have step := skip_work (n+1).bits
      rw [Nat.size_eq_bits_len] at step
      have width : n.size≤(n+1).size := Nat.size_le_size (Nat.le_succ n)
      have prior : (sample n).countPrefix[n]?.getD 0≤42*n*((n+1).size+1) :=
        ih.trans (Nat.mul_le_mul_left (42*n) (Nat.add_le_add_right width 1))
      rw [show 42*(n+1)*((n+1).size+1)=42*n*((n+1).size+1)+42*((n+1).size+1) by ring]
      omega

theorem address_counter (s : Store) (i : ℕ) (inside : i≤s.cells.size) :
    s.countPrefix[i]?.getD 0 ≤ 42*i*(i.size+1) := by
  have isSample := (sample i).count_spec i (by rw [sample_size])
  rw [(s.count_spec i inside).trans isSample.symm]
  exact sample_counter i

/-- The actual read computes its numeric address, selects two prefix counters,
and adds their charges. This bounds the involved operand widths whenever the
cached heap fits its cell and stored pointer bounds. -/
def readerWidth (H B : ℕ) : ℕ := max B (64*(H+1)*(max B (H+1).size+1)).size

def ReadOperands (s : Store) (a : Bits) (W : ℕ) : Prop :=
    let i := value a
    s.cells.size.size ≤ W ∧ i.size ≤ W ∧ (CachedReferenceHeap.read s a).2.size ≤ W ∧
    (i<s.cells.size → (i+1).size ≤ W ∧ (i-1).size ≤ W ∧
      (s.cellPrefix[i+1]?.getD 0).size ≤ W ∧ (s.countPrefix[i-1]?.getD 0).size ≤ W)

theorem read_width {s : Store} {H B : ℕ} (cells : s.cells.size≤H)
    (bounded : Heap.Bounded B s.cells.toList) (a : Bits) (address : a.length≤B) :
    ReadOperands s a (readerWidth H B) := by
  let i := value a
  let C := 64*(H+1)*(max B (H+1).size+1)
  let W := readerWidth H B
  have base : (H+1).size≤W := by
    apply le_trans _ (le_max_right B C.size)
    apply Nat.size_le_size
    dsimp only [C]
    calc
      H+1 ≤ (64*(H+1))*1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have addressSize : i.size≤W := (Nat.size_le.mpr (value_lt a)).trans (address.trans (le_max_left B C.size))
  have paid := lookup_bound address bounded
  rw [← CachedReferenceHeap.read_eq s a,Array.length_toList] at paid
  have paidCap : (CachedReferenceHeap.read s a).2≤C := by
    exact paid.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (by omega)) (Nat.add_le_add_right (le_max_left _ _) 1))
  refine ⟨(Nat.size_le_size (cells.trans (Nat.le_succ H))).trans base,addressSize,
    (Nat.size_le_size paidCap).trans (le_max_right B C.size),?_⟩
  intro inside
  have hplus : i+1≤s.cells.size := by omega
  have hminus : i-1≤s.cells.size := by omega
  have p := payload_counter s B (i+1) bounded hplus
  have q := address_counter s (i-1) hminus
  have indexSize (j : ℕ) (hj : j≤H+1) : j.size≤W := (Nat.size_le_size hj).trans base
  have pCap : s.cellPrefix[i+1]?.getD 0≤C := by
    refine p.trans ?_
    calc
      (i+1)*(8*(B+1)) ≤ (H+1)*(64*(max B (H+1).size+1)) := by
        exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by decide) (Nat.add_le_add_right (le_max_left _ _) 1))
      _=C := by dsimp only [C]; ring
  have qCap : s.countPrefix[i-1]?.getD 0≤C := by
    refine q.trans ?_
    rw [show C=64*(H+1)*(max B (H+1).size+1) from rfl]
    have j : i-1≤H+1 := by omega
    exact Nat.mul_le_mul (Nat.mul_le_mul (by decide) j)
      (Nat.add_le_add_right ((Nat.size_le_size j).trans (le_max_right _ _)) 1)
  exact ⟨indexSize _ (by omega),indexSize _ (by omega),
    (Nat.size_le_size pCap).trans (le_max_right B C.size),
    (Nat.size_le_size qCap).trans (le_max_right B C.size)⟩

open CachedReferenceExecution (FastState FastResult)

/-- These are the three executed instruction branches that read the cached
heap. The operands are those of `CachedReferenceExecution.attempt`. -/
theorem attempt_read_width {C H B : ℕ} (p : Program C) (s : FastState C) (fits : s.freeze.Bounded H B) :
    let addr (src : Reg) := (copyBits (s.registers.get src)).1
    match p s.pc with
    | .branch src _ _ _ _ | .field _ src _ _ | .emit src _ =>
        ReadOperands s.store (addr src) (readerWidth H B)
    | _ => True := by
  have records := fits.1
  simp only [State.records,FastState.freeze,Array.length_toList] at records
  have size : s.store.cells.size≤H := by omega
  have hh : Heap.Bounded B s.store.cells.toList := fits.2.2.1
  have each (src : Reg) : ReadOperands s.store (copyBits (s.registers.get src)).1 (readerWidth H B) := by
    have all : s.registers.All (fun a => a.length≤B) := fits.2.2.2.1
    apply read_width size hh
    rw [(copyBits_spec _).1]
    exact Registers.get_all all src
  cases p s.pc <;> first | exact True.intro | exact each _

theorem returned_address {s : Store} {a : Bits} {c : Cell Bits}
    (found : (CachedReferenceHeap.read s a).1=some c) : value a<s.cells.size := by
  rw [CachedReferenceHeap.read_eq,lookup_value] at found
  by_contra absent
  have far : s.cells.toList.length ≤ value a := by simpa only [Array.length_toList,Nat.not_lt] using absent
  rw [List.getElem?_eq_none far] at found
  cases found

private theorem inbounds_of_read {s : Store} {a : Bits} (found : (CachedReferenceHeap.read s a).1 ≠ none) :
    value a<s.cells.size := by
  cases read : (CachedReferenceHeap.read s a).1 with
  | none => exact (found read).elim
  | some c => exact returned_address read

/-- After a successful instruction, any cached read took its indexed-array
branch. The out-of-bounds list reader is never entered for such a step. -/
theorem attempt_read_inbounds {C : ℕ} (p : Program C) (s : FastState C) {result : FastResult C}
    (done : CachedReferenceExecution.attempt p s=.completed result) :
    let addr (src : Reg) := (copyBits (s.registers.get src)).1
    match p s.pc with
    | .branch src _ _ _ _ | .field _ src _ _ | .emit src _ => value (addr src)<s.store.cells.size
    | _ => True := by
  cases step : p s.pc <;> first | exact True.intro | skip
  all_goals
    apply inbounds_of_read
    intro read
    rw [CachedReferenceExecution.attempt,step] at done
    simp only [read,reduceCtorEq] at done

end DirectedFlowCutGap.CachedHeapWidths
