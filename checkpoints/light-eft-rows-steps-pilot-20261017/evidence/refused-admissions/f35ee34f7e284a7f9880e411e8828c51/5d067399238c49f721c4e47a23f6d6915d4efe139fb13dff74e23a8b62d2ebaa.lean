import LightEFTSpanners.StoredRecordTrace
open LightEFTSpanners.StoredRecords
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredRecords.rowsSteps
  let some c := env.find? name | throwError "rowsSteps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "rowsSteps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: rowsSteps safe, total, computable, explicit List.rec, no partial companion"
example (es : LightEFTSpanners.StoredSample.EdgeLists) (i : ℕ) : rowsSteps es i [] = 0 := rfl
example (es : LightEFTSpanners.StoredSample.EdgeLists) (i : ℕ) (r : List ℚ) (rs : Weights) :
    rowsSteps es i (r::rs) = rowSteps es i 0 r+r.length+2+rowsSteps es (i+1) rs := rfl
example (es : LightEFTSpanners.StoredSample.EdgeLists) (i : ℕ) (r t : List ℚ) :
    rowsSteps es i [r,t] = rowSteps es i 0 r+r.length+2+(rowSteps es (i+1) 0 t+t.length+2+0) := rfl
namespace RowsStepsCases
open LightEFTSpanners
def empty : StoredSample.EdgeLists := ⟨[],[],[],[]⟩
def single : StoredSample.EdgeLists := ⟨[(0,0)],[(0,0)],[(0,0)],[(0,0)]⟩
def mixed : StoredSample.EdgeLists := ⟨[(3,0),(3,1),(4,0)],[(9,9),(0,3),(3,0)],[(0,4),(1,3)],[(3,0),(3,0),(4,1)]⟩
def huge : StoredSample.EdgeLists := ⟨[(100000000000000000000,0),(100000000000000000001,1)],[(0,100000000000000000000)],[],[(100000000000000000002,0)]⟩
example : rowsSteps empty 0 [] = 0 := by decide
example : rowsSteps empty 7 [] = 0 := by decide
example : rowsSteps empty 100000000000000000000 [] = 0 := by decide
example : rowsSteps empty 0 [[]] = 3 := by decide
example : rowsSteps empty 8 [[],[],[]] = 9 := by decide
example : rowsSteps empty 0 [[0]] = 14 := by decide
example : rowsSteps empty 5 [[-3/2,0,5/7]] = 36 := by decide
example : rowsSteps empty 100000000000000000000 [[],[2],[],[-3,4]] = 45 := by decide
example : rowsSteps single 0 [[7]] = 14 := by decide
example : rowsSteps single 1 [[7]] = 18 := by decide
example : rowsSteps single 0 [[7,7]] = 29 := by decide
example : rowsSteps single 0 [[],[7]] = 21 := by decide
example : rowsSteps single 0 [[7],[],[7,7]] = 50 := by decide
example : rowsSteps single 100000000000000000000 [[-1,0,1]] = 48 := by decide
example : rowsSteps mixed 3 [[1,2],[3,4]] = 79 := by decide
example : rowsSteps mixed 2 [[],[1,2],[3],[]] = 64 := by decide
example : rowsSteps mixed 3 [[0],[],[-7/3,8]] = 67 := by decide
example : rowsSteps mixed 0 [[1,2,3],[4]] = 94 := by decide
example : rowsSteps mixed 4 [[1,2],[1,2],[1,2]] = 137 := by decide
example : rowsSteps huge 100000000000000000000 [[0,1],[2,3],[4]] = 79 := by decide
example : rowsSteps huge 100000000000000000001 [[],[4]] = 20 := by decide
example : rowsSteps huge 99999999999999999999 [[2],[3],[4]] = 51 := by decide
example : rowsSteps mixed 3 [[1],[],[],[],[2]] = 51 := by decide
example : rowsSteps single 0 [[7],[7],[7],[7]] = 68 := by decide
end RowsStepsCases
run_cmd Lean.logInfo "PASS: 24 kernel-checked full-count fixtures and 3 exact equations; arbitrary start indices, empty/ragged matrices, duplicate/reversed edge membership, signed rational payloads, row index advancement and exact additive term order"
