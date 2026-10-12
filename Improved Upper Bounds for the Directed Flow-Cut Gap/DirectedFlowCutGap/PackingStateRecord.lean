import DirectedFlowCutGap.PackingStartInput

namespace DirectedFlowCutGap.PackingStart
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

inductive EventList {n : ℕ} (heap : NaturalHeap) (label : Fin n → Bits) :
    ℕ → List (BinaryFractionalCore.Event n) → Prop
  | nil {root} : heap[root]?=some .nil → EventList heap label root []
  | cons {root entry tail choice amount e es} : heap[root]?=some (.pair entry tail) →
      heap[entry]?=some (.pair choice amount) → OracleChoice.StoredChoice heap choice label e.choice →
      Stored heap amount e.amount → EventList heap label tail es → EventList heap label root (e::es)

def StateRecord {n : ℕ} (heap : NaturalHeap) (root : ℕ) (label : Fin n → Bits)
    (s : BinaryFractionalCore.State n) : Prop :=
  ∃ weights best cost total loads events k1 k2 k3 k4,
    heap[root]?=some (.pair weights k1) ∧ heap[k1]?=some (.pair best k2) ∧
    heap[k2]?=some (.pair cost k3) ∧ heap[k3]?=some (.pair total k4) ∧
    heap[k4]?=some (.pair loads events) ∧
    StoredList heap weights s.weights.toList ∧ StoredList heap best s.best.toList ∧
    Stored heap cost s.bestCost ∧ Stored heap total s.total ∧
    StoredList heap loads s.loads.toList ∧ EventList heap label events s.events
end DirectedFlowCutGap.PackingStart
