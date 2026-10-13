import DirectedFlowCutGap.AdaptivePackingOriginalData

namespace DirectedFlowCutGap.AdaptivePackingState
open BinaryArithmetic BinaryRational BinaryFractionalRows
open ImmutableReferenceSimulation ImmutableReferenceTerminal BooleanTableRead PackedBooleanConstructor
open RationalComparisonProgram
open CanonicalRationalSum (StoredList list_extend)

def selectedRow {n : ℕ} (capacity : Row n) (s : BinaryFractionalCore.State n) (q : BinaryFractionalCore.Choice n) : Row n :=
  if (BinaryRational.le s.bestCost (objective capacity (normalized s.weights q.mask).1).1).1 then
    s.best else (normalized s.weights q.mask).1

def selectedCost {n : ℕ} (capacity : Row n) (s : BinaryFractionalCore.State n) (q : BinaryFractionalCore.Choice n) : Fraction :=
  if (BinaryRational.le s.bestCost (objective capacity (normalized s.weights q.mask).1).1).1 then
    s.bestCost else (objective capacity (normalized s.weights q.mask).1).1

structure SelectedData {n : ℕ} (heap : NaturalHeap) (frame cap original input : ℕ)
    (label : Fin n → Bits) (capacity : Row n) (s : BinaryFractionalCore.State n) (q : BinaryFractionalCore.Choice n) where
  choice : ℕ
  amount : ℕ
  normalized : ℕ
  candidate : ℕ
  best : ℕ
  cost : ℕ
  old : OriginalData heap original label s
  capacityRep : StoredList heap cap capacity.toList
  frameRep : CandidateFrame heap frame candidate normalized amount choice cap original input
  choiceRep : OracleChoice.StoredChoice heap choice label q
  amountRep : Stored heap amount (get capacity q.bottleneck)
  normalizedRep : StoredList heap normalized (BinaryFractionalRows.normalized s.weights q.mask).1.toList
  candidateRep : Stored heap candidate (objective capacity (BinaryFractionalRows.normalized s.weights q.mask).1).1
  bestRep : StoredList heap best (selectedRow capacity s q).toList
  costRep : Stored heap cost (selectedCost capacity s q)

def SelectedData.extend {n : ℕ} {heap : NaturalHeap} {frame cap original input : ℕ}
    {label : Fin n → Bits} {capacity : Row n} {s : BinaryFractionalCore.State n} {q : BinaryFractionalCore.Choice n}
    (d : SelectedData heap frame cap original input label capacity s q) (ext : NaturalHeap) :
    SelectedData (heap++ext) frame cap original input label capacity s q :=
  ⟨d.choice,d.amount,d.normalized,d.candidate,d.best,d.cost,d.old.extend ext,list_extend d.capacityRep ext,
    candidate_frame_extend d.frameRep ext,choice_extend d.choiceRep ext,stored_extend d.amountRep ext,
    list_extend d.normalizedRep ext,stored_extend d.candidateRep ext,list_extend d.bestRep ext,stored_extend d.costRep ext⟩
end DirectedFlowCutGap.AdaptivePackingState
