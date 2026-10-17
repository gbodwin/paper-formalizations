import LightEFTSpanners.StoredRecordEncoding

/-! The bounded interpreter reaches the same constructed records. The bound is
an external fuel bound on the actual controller trace, not a claim that list
lengths or rational/natural arithmetic have unit bit complexity. -/
namespace LightEFTSpanners.StoredRecords
open Controller

def bound (es : StoredSample.EdgeLists) (W : Weights) : ℕ :=
  cellCount W*(listSize es+11)+4*W.length+2

def execute (es : StoredSample.EdgeLists) (W : Weights) : SampleRecords.Records :=
  match Controller.run (transition es) (bound es W) (.row 0 W []) with
  | .halt R => R
  | _ => []

theorem run_materialize (es : StoredSample.EdgeLists) (W : Weights) :
    Controller.run (transition es) (bound es W) (.row 0 W [])=.halt (values es 0 W) := by
  have hb : matrixSteps es W≤bound es W := matrixSteps_le es W
  have he : bound es W=matrixSteps es W+(bound es W-matrixSteps es W) := by omega
  rw [he,Controller.run_add,(materialize_trace es W).run_eq]
  exact Controller.run_terminal (transition es) (.halt (values es 0 W)) rfl _

theorem execute_eq (es : StoredSample.EdgeLists) (W : Weights) :
    execute es W=values es 0 W := by simp only [execute,run_materialize]

theorem execute_encode {n : ℕ} (Q E T S : List (Fin n × Fin n)) (w : Sym2 (Fin n) → ℚ) :
    execute (StoredSample.encodeLists Q E T S) (encodeWeights w)=
      SampleRecords.encode (StoredSample.edgeSet Q) (StoredSample.edgeSet E)
        (StoredSample.edgeSet T) (StoredSample.edgeSet S) w := by
  rw [execute_eq,values_encode]
end LightEFTSpanners.StoredRecords
