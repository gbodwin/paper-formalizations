import LightEFTSpanners.StoredRecordMachine
open LightEFTSpanners.StoredRecords
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredRecords.rowSteps
  let some c := env.find? name | throwError "rowSteps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "rowSteps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: rowSteps safe, total, computable, explicit List.rec, no partial companion"
example (es : LightEFTSpanners.StoredSample.EdgeLists) (i j : ℕ) : rowSteps es i j [] = 1 := rfl
example (es : LightEFTSpanners.StoredSample.EdgeLists) (i j : ℕ) (w : ℚ) (ws : List ℚ) :
    rowSteps es i j (w::ws) = LightEFTSpanners.StoredSample.entrySteps (i,j) es+2+rowSteps es i (j+1) ws := rfl
example (es : LightEFTSpanners.StoredSample.EdgeLists) (i j : ℕ) (a b : ℚ) :
    rowSteps es i j [a,b] = LightEFTSpanners.StoredSample.entrySteps (i,j) es+2+
      (LightEFTSpanners.StoredSample.entrySteps (i,j+1) es+2+1) := rfl
namespace RowStepsCases
open LightEFTSpanners
def empty : StoredSample.EdgeLists := ⟨[],[],[],[]⟩
def single : StoredSample.EdgeLists := ⟨[(0,0)],[(0,0)],[(0,0)],[(0,0)]⟩
def mixed : StoredSample.EdgeLists := ⟨[(3,2),(3,3),(3,4)],[(9,9),(2,3),(3,2)],[(4,3),(3,3)],[(3,2),(3,2),(3,5)]⟩
def huge : StoredSample.EdgeLists := ⟨[(100000000000000000000,100000000000000000000),(100000000000000000000,100000000000000000001)],[(100000000000000000001,100000000000000000000)],[],[(100000000000000000000,100000000000000000002)]⟩
example : rowSteps empty 0 0 [] = 1 := by decide
example : rowSteps empty 7 99 [] = 1 := by decide
example : rowSteps empty 100000000000000000000 100000000000000000000 [] = 1 := by decide
example : rowSteps empty 0 0 [0] = 11 := by decide
example : rowSteps empty 4 8 [-3/2,0,5/7] = 31 := by decide
example : rowSteps empty 100000000000000000000 100000000000000000000 [-1,0,1] = 31 := by decide
example : rowSteps single 0 0 [7] = 11 := by decide
example : rowSteps single 0 1 [7] = 15 := by decide
example : rowSteps single 1 0 [7] = 15 := by decide
example : rowSteps single 0 0 [7,7] = 25 := by decide
example : rowSteps single 0 1 [-7,7] = 29 := by decide
example : rowSteps single 100000000000000000000 0 [-1,0,1] = 43 := by decide
example : rowSteps mixed 3 0 [1,2,3,4,5] = 92 := by decide
example : rowSteps mixed 3 2 [1,2,3,4] = 70 := by decide
example : rowSteps mixed 3 3 [1,2,3] = 57 := by decide
example : rowSteps mixed 2 3 [1] = 14 := by decide
example : rowSteps mixed 4 3 [1] = 19 := by decide
example : rowSteps mixed 3 5 [1,2] = 42 := by decide
example : rowSteps mixed 3 2 [-1/7,0,2/3,-99] = 70 := by decide
example : rowSteps huge 100000000000000000000 100000000000000000000 [0,1,2,3] = 52 := by decide
example : rowSteps huge 100000000000000000000 100000000000000000001 [2,3] = 26 := by decide
example : rowSteps huge 100000000000000000001 100000000000000000000 [2] = 13 := by decide
example : rowSteps single 0 0 [-7] = 11 := by decide
example : rowSteps mixed 0 0 [0,0,0,0,0,0] = 127 := by decide
end RowStepsCases
run_cmd Lean.logInfo "PASS: 24 kernel-checked row full-count fixtures and 3 exact equations; arbitrary fixed row and starting column, nil one, duplicate/reversed membership scans, signed payloads, column increment and exact entrySteps plus two plus tail order"
