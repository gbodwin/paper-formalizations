import LightEFTSpanners.StoredRecordMachine

namespace LightEFTSpanners.StoredRecords
open Controller

theorem reverse_row_trace (es : StoredSample.EdgeLists) (i : ℕ) (rs : Weights)
    (out : SampleRecords.Records) (r acc : List SampleRecords.Entry) :
    Trace (transition es) (r.length+1) (.revRow i rs out r acc)
      (.row (i+1) rs ((r.reverse++acc)::out)) := by
  induction r generalizing acc with
  | nil => exact Trace.one rfl
  | cons a as ih =>
    simpa [List.reverse_cons,List.append_assoc] using
      Trace.cons (show transition es (.revRow i rs out (a::as) acc)=
        some (.revRow i rs out as (a::acc)) from rfl) (ih (a::acc))

theorem reverse_matrix_trace (es : StoredSample.EdgeLists) (R acc : SampleRecords.Records) :
    Trace (transition es) (R.length+1) (.revMatrix R acc) (.halt (R.reverse++acc)) := by
  induction R generalizing acc with
  | nil => exact Trace.one rfl
  | cons r rs ih =>
    simpa [List.reverse_cons,List.append_assoc] using
      Trace.cons (show transition es (.revMatrix (r::rs) acc)=some (.revMatrix rs (r::acc)) from rfl)
        (ih (r::acc))

def rowsSteps (es : StoredSample.EdgeLists) : ℕ → Weights → ℕ :=
  fun i W => List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun r _ next i => rowSteps es i 0 r+r.length+2+next (i+1)) W i

theorem rowsSteps_nil (es : StoredSample.EdgeLists) (i : ℕ) : rowsSteps es i [] = 0 := rfl

theorem rowsSteps_cons (es : StoredSample.EdgeLists) (i : ℕ) (r : List ℚ) (rs : Weights) :
    rowsSteps es i (r::rs) = rowSteps es i 0 r+r.length+2+rowsSteps es (i+1) rs := rfl

-- Let arithmetic normalization identify the exact unfolded tail count.
attribute [reducible] rowsSteps

theorem rows_trace (es : StoredSample.EdgeLists) (i : ℕ) (W : Weights)
    (out : SampleRecords.Records) :
    Trace (transition es) (rowsSteps es i W) (.row i W out)
      (.row (i+W.length) [] ((values es i W).reverse++out)) := by
  induction W generalizing i out with
  | nil => simpa [rowsSteps,values] using Trace.refl (step:=transition es) (.row i [] out)
  | cons r rs ih =>
    have h0 := Trace.one (show transition es (.row i (r::rs) out)=some (.cell i 0 r [] rs out) from rfl)
    have h1 := cell_trace es i 0 r [] rs out
    have h2 := reverse_row_trace es i rs out (rowValues es i 0 r).reverse []
    simp only [List.append_nil] at h1
    simp only [List.length_reverse,rowValues_length,List.reverse_reverse,List.append_nil] at h2
    have h3 := ih (i+1) (rowValues es i 0 r::out)
    convert h0.trans (h1.trans (h2.trans h3)) using 1 <;>
      simp [rowsSteps,values,List.reverse_cons,List.append_assoc] <;> omega

def matrixSteps (es : StoredSample.EdgeLists) (W : Weights) : ℕ := rowsSteps es 0 W+W.length+2

theorem materialize_trace (es : StoredSample.EdgeLists) (W : Weights) :
    Trace (transition es) (matrixSteps es W) (.row 0 W []) (.halt (values es 0 W)) := by
  have h1 := rows_trace es 0 W []
  simp only [zero_add,List.append_nil] at h1
  have h2 := Trace.one (show transition es (.row W.length [] (values es 0 W).reverse)=
    some (.revMatrix (values es 0 W).reverse []) from rfl)
  have h3 := reverse_matrix_trace es (values es 0 W).reverse []
  simp only [List.length_reverse,values_length,List.reverse_reverse,List.append_nil] at h3
  convert h1.trans (h2.trans h3) using 1
  unfold matrixSteps
  omega

def listSize (es : StoredSample.EdgeLists) : ℕ :=
  es.seed.length+es.selected.length+es.host.length+es.drawn.length
def cellCount (W : Weights) : ℕ := (W.map List.length).sum

theorem rowSteps_le (es : StoredSample.EdgeLists) (i j : ℕ) (r : List ℚ) :
    rowSteps es i j r ≤ r.length*(listSize es+10)+1 := by
  induction r generalizing j with
  | nil => simp [rowSteps]
  | cons w ws ih =>
    have he := StoredSample.entrySteps_le (i,j) es
    have ht := ih (j+1)
    simp only [rowSteps,List.length_cons]
    unfold listSize at *
    nlinarith

theorem rowsSteps_le (es : StoredSample.EdgeLists) (i : ℕ) (W : Weights) :
    rowsSteps es i W ≤ cellCount W*(listSize es+11)+3*W.length := by
  induction W generalizing i with
  | nil => simp [rowsSteps,cellCount]
  | cons r rs ih =>
    have hr := rowSteps_le es i 0 r
    have ht := ih (i+1)
    simp only [rowsSteps,cellCount,List.map_cons,List.sum_cons,List.length_cons]
    unfold cellCount at ht
    nlinarith

theorem matrixSteps_le (es : StoredSample.EdgeLists) (W : Weights) :
    matrixSteps es W ≤ cellCount W*(listSize es+11)+4*W.length+2 := by
  have h := rowsSteps_le es 0 W
  unfold matrixSteps
  omega
end LightEFTSpanners.StoredRecords
