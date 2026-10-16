import LightEFTSpanners.StoredZeroWeights

namespace LightEFTSpanners.StoredGraphMatrix
open Controller

def lists (edges : List StoredEdges.Edge) : StoredSample.EdgeLists := ⟨[],[],edges,[]⟩
inductive State where
  | zero : StoredZeroWeights.State → State
  | records : StoredRecords.State → State
  | matrix : SampleRecords.State → State
  | halt : LinkedDistance.Matrix → State
  deriving DecidableEq, Repr

def transition (n : ℕ) (edges : List StoredEdges.Edge) : State → Option State
  | .zero (.halt W) => some (.records (.row 0 W []))
  | .zero s => (StoredZeroWeights.transition n s).map State.zero
  | .records (.halt R) => some (.matrix (.row 0 R []))
  | .records s => (StoredRecords.transition (lists edges) s).map State.records
  | .matrix (.halt M) => some (.halt M)
  | .matrix s => (SampleRecords.transition s).map State.matrix
  | .halt _ => none

theorem zero_lift (n : ℕ) (edges : List StoredEdges.Edge)
    {k : ℕ} {s t : StoredZeroWeights.State} (h : Trace (StoredZeroWeights.transition n) k s t) :
    Trace (transition n edges) k (.zero s) (.zero t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [StoredZeroWeights.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map State.zero) he

theorem records_lift (n : ℕ) (edges : List StoredEdges.Edge)
    {k : ℕ} {s t : StoredRecords.State} (h : Trace (StoredRecords.transition (lists edges)) k s t) :
    Trace (transition n edges) k (.records s) (.records t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [StoredRecords.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map State.records) he

theorem matrix_lift (n : ℕ) (edges : List StoredEdges.Edge)
    {k : ℕ} {s t : SampleRecords.State} (h : Trace SampleRecords.transition k s t) :
    Trace (transition n edges) k (.matrix s) (.matrix t) := by
  induction h with
  | refl => exact .refl _
  | @cons k s t u he _ ih =>
    apply Trace.cons _ ih
    cases s <;> try {simp [SampleRecords.transition] at he}
    all_goals simpa only [transition,Option.map_some] using congrArg (Option.map State.matrix) he

def value (n : ℕ) (edges : List StoredEdges.Edge) : LinkedDistance.Matrix :=
  SampleRecords.values 0 (StoredRecords.values (lists edges) 0 (StoredZeroWeights.matrix n))

def steps (n : ℕ) (edges : List StoredEdges.Edge) : ℕ :=
  2*n+2+1+StoredRecords.matrixSteps (lists edges) (StoredZeroWeights.matrix n)+1+
    (2*SampleRecords.cellCount (StoredRecords.values (lists edges) 0 (StoredZeroWeights.matrix n))+4*n+2)+1

theorem constructed_trace (n : ℕ) (edges : List StoredEdges.Edge) :
    Trace (transition n edges) (steps n edges) (.zero (.row n [])) (.halt (value n edges)) := by
  let W := StoredZeroWeights.matrix n
  let R := StoredRecords.values (lists edges) 0 W
  have a := zero_lift n edges (StoredZeroWeights.construct_trace n)
  have b := records_lift n edges (StoredRecords.materialize_trace (lists edges) W)
  have c := matrix_lift n edges (SampleRecords.materialize_trace R)
  have hR : R.length=n := by simp [R,W,StoredZeroWeights.matrix]
  rw [hR] at c
  have x := Trace.one (show transition n edges (.zero (.halt W))=some (.records (.row 0 W [])) from rfl)
  have y := Trace.one (show transition n edges (.records (.halt R))=some (.matrix (.row 0 R [])) from rfl)
  have z := Trace.one (show transition n edges (.matrix (.halt (SampleRecords.values 0 R)))=
    some (.halt (value n edges)) from rfl)
  simpa only [steps,Nat.add_assoc] using a.trans (x.trans (b.trans (y.trans (c.trans z))))
end LightEFTSpanners.StoredGraphMatrix
