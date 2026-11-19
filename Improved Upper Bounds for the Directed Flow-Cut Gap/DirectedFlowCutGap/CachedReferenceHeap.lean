import DirectedFlowCutGap.ImmutableReferenceTerminal

/-!
# Exact charge with a cached physical store

This evaluator supports testing large reference traces. The sequential
store's copied payload and countdown charges are accumulated separately.
The returned cells and operation counts equal the reference evaluator.
-/

namespace DirectedFlowCutGap.CachedReferenceHeap

open BinaryArithmetic ImmutableReferenceSimulation EncodedSequenceAccess

private def cellCharges (heap : Heap) : ℕ :=
  (heap.map fun c => (copyCell c).2).sum

private theorem cellCharges_append (a b : Heap) :
    cellCharges (a ++ b) = cellCharges a + cellCharges b := by
  simp [cellCharges]

private theorem appendCharge (heap : Heap) (c : Cell Bits) :
    (appendCell heap c).2 = cellCharges heap + (copyCell c).2 + 2 * (heap.length + 1) := by
  induction heap with
  | nil => simp [appendCell, cellCharges]
  | cons a as ih =>
    simp only [appendCell, ih, cellCharges, List.map_cons, List.sum_cons, List.length_cons]
    omega

private theorem predecessor_bits (a : Bits) :
    (predecessor a).1 = (value a - 1).bits := by
  have hn : Normal (predecessor a).1 := by
    unfold predecessor
    dsimp only
    split
    · exact .nil
    · exact (trim_spec _).1
  rw [← (predecessor_spec a).1, normal_bits hn]

private def skipCharge (a : Bits) : ℕ := (isZero a).2 + (predecessor a).2 + 6

private def addressPrefix : ℕ → ℕ
  | 0 => 0
  | k + 1 => addressPrefix k + skipCharge (k + 1).bits

private theorem nonzero {a : Bits} (h : value a ≠ 0) : (isZero a).1 = false := by
  exact Bool.eq_false_of_not_eq_true (h ∘ (isZero_spec a).1.mp)

private theorem canonical_lookup (heap : Heap) {k : ℕ} (hk : k < heap.length) :
    lookup k.bits heap =
      (heap[k]?, cellCharges (heap.take (k + 1)) + addressPrefix k + 5) := by
  induction heap generalizing k with
  | nil => simp at hk
  | cons c cs ih =>
    cases k with
    | zero =>
      simp [lookup, isZero, (copyCell_spec c).1, cellCharges, addressPrefix]
      omega
    | succ k =>
      have h := ih (k := k) (by simpa using hk)
      have hz : (isZero (k + 1).bits).1 = false := nonzero (by simp [value_bits])
      have hp : (predecessor (k + 1).bits).1 = k.bits := by
        rw [predecessor_bits, value_bits, Nat.add_sub_cancel]
      simp only [lookup, hz, Bool.false_eq_true, ite_false, hp, h, List.getElem?_cons_succ,
        List.take_succ_cons, cellCharges, List.map_cons, List.sum_cons, addressPrefix, skipCharge]
      congr 1
      omega

private def addressCharge (a : Bits) (earlier : ℕ) : ℕ :=
  if value a = 0 then (isZero a).2 + 4 else skipCharge a + earlier + 5

private theorem inbounds_lookup (heap : Heap) (a : Bits) (h : value a < heap.length) :
    lookup a heap = (heap[value a]?,
      cellCharges (heap.take (value a + 1)) + addressCharge a (addressPrefix (value a - 1))) := by
  cases heap with
  | nil => simp at h
  | cons c cs =>
    cases hval : value a with
    | zero =>
      have hz := (isZero_spec a).1.mpr hval
      simp [lookup, hz, (copyCell_spec c).1, addressCharge, hval, cellCharges]
      omega
    | succ k =>
      have hk : k < cs.length := by simpa [hval] using h
      have hz := nonzero (a := a) (by simp [hval])
      have hp : (predecessor a).1 = k.bits := by rw [predecessor_bits, hval, Nat.succ_sub_one]
      have hc := canonical_lookup cs hk
      simp only [lookup, hz, Bool.false_eq_true, ite_false, hp, hc, hval, Nat.succ_sub_one,
        List.getElem?_cons_succ, List.take_succ_cons, cellCharges, List.map_cons, List.sum_cons,
        addressCharge, Nat.succ_ne_zero, skipCharge]
      congr 1
      omega

structure Store where
  cells : Array (Cell Bits)
  cellPrefix : Array ℕ
  countPrefix : Array ℕ
  cell_size : cellPrefix.size = cells.size + 1
  count_size : countPrefix.size = cells.size + 1
  cell_spec : ∀ i ≤ cells.size, cellPrefix[i]? = some (cellCharges (cells.toList.take i))
  count_spec : ∀ i ≤ cells.size, countPrefix[i]? = some (addressPrefix i)

def empty : Store := ⟨#[], #[0], #[0], rfl, rfl, by
  intro i hi
  have he : i = 0 := Nat.eq_zero_of_le_zero hi
  subst i
  rfl, by
  intro i hi
  have he : i = 0 := Nat.eq_zero_of_le_zero hi
  subst i
  rfl⟩

private def pushArrays (heap : Array (Cell Bits)) (cells counts : Array ℕ) (c : Cell Bits) :
    Array (Cell Bits) × Array ℕ × Array ℕ :=
  let n := heap.size
  let cellCost := cells[n]?.getD 0 + (copyCell c).2
  let addressCost := counts[n]?.getD 0 + skipCharge (n + 1).bits
  (heap.push c, cells.push cellCost, counts.push addressCost)

def push (s : Store) (c : Cell Bits) : Store :=
  let next := pushArrays s.cells s.cellPrefix s.countPrefix c
  ⟨next.1, next.2.1, next.2.2, by simp [next, pushArrays, s.cell_size],
  by simp [next, pushArrays, s.count_size], by
    intro i hi
    simp only [next, pushArrays, Array.size_push] at hi
    simp only [next, pushArrays, Array.toList_push]
    by_cases hn : i ≤ s.cells.size
    · have hlt : i < s.cellPrefix.size := by rw [s.cell_size]; omega
      have hspec := s.cell_spec i hn
      rw [Array.getElem?_eq_getElem hlt] at hspec
      rw [Array.getElem?_push_lt hlt, hspec, List.take_append_of_le_length (by simpa using hn)]
    · have he : i = s.cells.size + 1 := by omega
      subst i
      have hlast := Array.getElem?_push_size
        (xs := s.cellPrefix) (x := s.cellPrefix[s.cells.size]?.getD 0 + (copyCell c).2)
      rw [s.cell_size] at hlast
      rw [hlast,
        s.cell_spec _ le_rfl, List.take_of_length_le (by simp),
        List.take_of_length_le (by simp), cellCharges_append]
      rfl, by
    intro i hi
    simp only [next, pushArrays, Array.size_push] at hi
    simp only [next, pushArrays]
    by_cases hn : i ≤ s.cells.size
    · have hlt : i < s.countPrefix.size := by rw [s.count_size]; omega
      have hspec := s.count_spec i hn
      rw [Array.getElem?_eq_getElem hlt] at hspec
      rw [Array.getElem?_push_lt hlt, hspec]
    · have he : i = s.cells.size + 1 := by omega
      subst i
      have hlast := Array.getElem?_push_size (xs := s.countPrefix)
        (x := s.countPrefix[s.cells.size]?.getD 0 + skipCharge (s.cells.size + 1).bits)
      rw [s.count_size] at hlast
      rw [hlast, s.count_spec _ le_rfl]
      rfl⟩

def ofList (heap : Heap) : Store := heap.foldl push empty

@[simp] theorem push_value (s : Store) (c : Cell Bits) :
    (push s c).cells.toList = s.cells.toList ++ [c] := Array.toList_push

@[simp] theorem ofList_value (heap : Heap) : (ofList heap).cells.toList = heap := by
  have go (s : Store) : (heap.foldl push s).cells.toList = s.cells.toList ++ heap := by
    induction heap generalizing s with
    | nil => simp
    | cons c cs ih => simp [ih, List.append_assoc]
  simpa [ofList, empty] using go empty

def append (s : Store) (c : Cell Bits) : Store × ℕ :=
  let charge := s.cellPrefix[s.cells.size]?.getD 0 + (copyCell c).2 + 2 * (s.cells.size + 1)
  (push s c, charge)

theorem append_eq (s : Store) (c : Cell Bits) :
    ((append s c).1.cells.toList, (append s c).2) = appendCell s.cells.toList c := by
  rw [← Prod.eta (appendCell s.cells.toList c), appendCell_value, appendCharge]
  have htake : s.cells.toList.take s.cells.size = s.cells.toList :=
    List.take_of_length_le (by simp)
  simp [append, s.cell_spec _ le_rfl, htake]

def read (s : Store) (a : Bits) : Option (Cell Bits) × ℕ :=
  let i := value a
  if i < s.cells.size then
    (s.cells[i]?, s.cellPrefix[i + 1]?.getD 0 + addressCharge a (s.countPrefix[i - 1]?.getD 0))
  else lookup a s.cells.toList

theorem read_eq (s : Store) (a : Bits) : read s a = lookup a s.cells.toList := by
  unfold read
  dsimp only
  split
  · rename_i h
    have hcell := s.cell_spec (value a + 1) (by omega)
    have haddr := s.count_spec (value a - 1) (by omega)
    rw [inbounds_lookup _ _ (by simpa using h), hcell, haddr, Array.getElem?_toList]
    rfl
  · rfl

end DirectedFlowCutGap.CachedReferenceHeap
