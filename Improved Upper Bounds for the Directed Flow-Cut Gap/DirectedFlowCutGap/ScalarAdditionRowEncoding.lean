import DirectedFlowCutGap.ScalarAdditionRowRefinement
import DirectedFlowCutGap.IndexedRationalRead

namespace DirectedFlowCutGap.ScalarAdditionRow
open BinaryArithmetic BinaryRational ImmutableReferenceSimulation BooleanTableRead
open RationalComparisonProgram CanonicalRationalSum

theorem stored_of_table {heap : NaturalHeap} {root : ℕ} {xs : List Fraction}
    (table : WordPairTableRead.Table heap root (IndexedRationalRead.fields xs)) :
    StoredList heap root xs := by
  induction xs generalizing root with
  | nil =>
    cases table with
    | nil hp => exact .nil hp
  | cons x xs ih =>
    cases table with
    | @cons root item tail num den a b rest hp record hn hd ht =>
      exact .cons hp ⟨num,den,record,hn,hd⟩ (ih ht)

theorem table_of_stored {heap : NaturalHeap} {root : ℕ} {xs : List Fraction}
    (stored : StoredList heap root xs) :
    WordPairTableRead.Table heap root (IndexedRationalRead.fields xs) := by
  induction stored with
  | nil hp => exact .nil hp
  | cons hp hx _ ih =>
    obtain ⟨num,den,record,hn,hd⟩ := hx
    exact .cons hp record hn hd ih
end DirectedFlowCutGap.ScalarAdditionRow
