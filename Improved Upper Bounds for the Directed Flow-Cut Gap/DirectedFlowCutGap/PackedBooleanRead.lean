import DirectedFlowCutGap.PackedBooleanConstructor

/-!
# Paid index-pointer preparation and the existing fixed table read

An incoming binary word encodes a valid table index. Its pointer is produced
by the actual `add false word word` routine, with that routine's charge plus
12 units of fixed state/record overhead. Acquisition and encoding of the
incoming word and Boolean list remain input boundaries. No `Nat.bits` call
or separately allocated unary list occurs in this executable preparation.
-/
namespace DirectedFlowCutGap.PackedBooleanConstructor
open BinaryArithmetic ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead

/-- The pure notation-level state record retains the constructed heap. -/
def readerState (s : Prepared) (index source : Bits) : BitState 6 :=
  ⟨s.heap, s.next, ⟨s.root, (add false index index).1, [], []⟩, [], 0, source⟩

/-- All preparation charges, including the actual binary index doubling. -/
def prepareRead (xs : List Bool) (index source : Bits) : BitState 6 × ℕ :=
  let s := construct xs
  (readerState s index source, s.operations + (add false index index).2 + 12)

/-- This discharges the representation and bounded-state premises of the
six-instruction read from the actual prepared heap and paid pointer routine. -/
theorem prepareRead_spec (xs : List Bool) (i : Fin xs.length) (index source : Bits)
    (encoded : value index = i.val) (width : index.length ≤ 2 * xs.length + 1) :
    (prepareRead xs index source).1.Bounded (2 * xs.length + 2) (2 * xs.length + 2) ∧
    (prepareRead xs index source).1.pc = 0 ∧
    BoolList (eraseState (prepareRead xs index source).1).heap
      (eraseState (prepareRead xs index source).1).registers.a xs ∧
    IndexSpine (eraseState (prepareRead xs index source).1).heap
      (eraseState (prepareRead xs index source).1).registers.b i.val ∧
    (prepareRead xs index source).2 ≤
      128 * (xs.length + 1)^3 + 32 * (xs.length + 1) + 12 := by
  have h := construct_valid xs
  have arithmetic := add_spec false index index
  have doubled : value (add false index index).1 = 2 * i.val := by
    simpa [encoded, two_mul] using arithmetic.1
  have doubleWidth : (add false index index).1.length ≤ 2 * xs.length + 2 := by
    have hw := arithmetic.2.1
    simp only [max_self] at hw
    omega
  have doubleCharge : (add false index index).2 ≤ 32 * (xs.length + 1) := by
    have hc := arithmetic.2.2
    simp only [max_self] at hc
    omega
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp only [prepareRead, readerState, State.Bounded, State.records,
      List.length_nil, Nat.add_zero, Registers.All, List.not_mem_nil, false_implies]
    exact ⟨by rw [h.heap_length],
      h.next_width.trans (by omega), heapBound_mono h.heap_bound (by omega),
      ⟨h.root_width.trans (by omega), doubleWidth, by omega, by omega⟩, fun _ => trivial⟩
  · exact h.table
  · change IndexSpine (eraseHeap (construct xs).heap)
      (value (add false index index).1) i.val
    rw [doubled]
    exact h.suffix i.val (Nat.le_of_lt i.isLt)
  · change (construct xs).operations + (add false index index).2 + 12 ≤ _
    have := construct_charge xs
    omega

/-- Natural execution uses the prepared table and shared suffix spine, with
exactly the existing `3*i+3` successful instructions and the selected bit. -/
theorem read_constructed_high {m : ℕ} (table : Vector Bool m) (i : Fin m)
    (index source : Bits) (encoded : value index = i.val)
    (width : index.length ≤ 2 * m + 1) :
    ∃ final, NaturalRun program (3 * i.val + 3)
      (eraseState (prepareRead table.toList index source).1) [.emit table[i.val]] final ∧
      final.pc = 5 ∧ final.heap[final.registers.c]? = some (.flag table[i.val]) ∧
      tickNatural program final = none := by
  let j : Fin table.toList.length := ⟨i.val, by simpa only [Vector.length_toList] using i.isLt⟩
  have ready := prepareRead_spec table.toList j index source encoded (by simpa using width)
  obtain ⟨final, run, _, _, _, _, _, pc, flag, halt, _⟩ :=
    read_table_high table i (eraseState (prepareRead table.toList index source).1)
      ready.2.1 ready.2.2.1 ready.2.2.2.1
  exact ⟨final, run, pc, flag, halt⟩

/-- Actual lower execution, unchanged source, flag result, and charged halt.
The preparation budget and the read budget are explicitly added; the incoming
list/index encoding and whole-graph algorithm remain outside this theorem. -/
theorem read_constructed_bit {m : ℕ} (table : Vector Bool m) (i : Fin m)
    (index source : Bits) (encoded : value index = i.val)
    (width : index.length ≤ 2 * m + 1) :
    ∃ q out, Run program (3 * i.val + 3) q
      (prepareRead table.toList index source).1 [.emit table[i.val]] out ∧
      out.Bounded ((2 * m + 2) + (3 * i.val + 3)) ((2 * m + 2) + (3 * i.val + 3)) ∧
      q ≤ runBound 6 (2 * m + 2) (2 * m + 2) (3 * i.val + 3) ∧
      out.source = source ∧ out.pc = 5 ∧
      (eraseState out).heap[(eraseState out).registers.c]? = some (.flag table[i.val]) ∧
      (attempt program out).result = none ∧
      (prepareRead table.toList index source).2 + q + (attempt program out).operations ≤
        128 * (m + 1)^3 + 32 * (m + 1) + 12 +
          completeBound 6 (2 * m + 2) (2 * m + 2) (3 * i.val + 3) := by
  let j : Fin table.toList.length := ⟨i.val, by simpa only [Vector.length_toList] using i.isLt⟩
  have ready := prepareRead_spec table.toList j index source encoded (by simpa using width)
  have bounded : (prepareRead table.toList index source).1.Bounded (2*m+2) (2*m+2) := by
    simpa using ready.1
  obtain ⟨q, out, run, bound, cost, sourceEq, pc, flag, halt, total⟩ :=
    read_table_bit table i (prepareRead table.toList index source).1 bounded
      ready.2.1 ready.2.2.1 ready.2.2.2.1
  refine ⟨q, out, run, bound, cost, sourceEq, pc, flag, halt, ?_⟩
  have prep : (prepareRead table.toList index source).2 ≤
      128 * (m + 1)^3 + 32 * (m + 1) + 12 := by simpa using ready.2.2.2.2
  omega

end DirectedFlowCutGap.PackedBooleanConstructor
