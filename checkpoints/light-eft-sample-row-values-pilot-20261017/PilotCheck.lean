import LightEFTSpanners.SampleRecordMatrix
open LightEFTSpanners.SampleRecords
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.SampleRecords.rowValues
  let some c := env.find? name | throwError "rowValues missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "rowValues not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: rowValues safe, total, computable, explicit List.rec, no partial companion"
example (i j : ℕ) : rowValues i j [] = [] := rfl
example (i j : ℕ) (a : LightEFTSpanners.SampleRecords.Entry) (as : List LightEFTSpanners.SampleRecords.Entry) :
    rowValues i j (a::as) = value i j a :: rowValues i (j+1) as := rfl
example (i j : ℕ) (a b : LightEFTSpanners.SampleRecords.Entry) :
    rowValues i j [a,b] = [value i j a,value i (j+1) b] := rfl
namespace SampleRowValuesCases
example : rowValues 0 0 [⟨-8/3,false,false,false,false⟩] = [none] := by rfl
example : rowValues 3 3 [⟨-8/3,false,false,false,false⟩] = [none] := by rfl
example : rowValues 0 1 [⟨-8/3,false,false,false,false⟩] = [none] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨-8/3,false,false,false,false⟩] = [none] := by rfl
example : rowValues 0 0 [⟨-7/3,true,false,false,false⟩] = [none] := by rfl
example : rowValues 3 3 [⟨-7/3,true,false,false,false⟩] = [none] := by rfl
example : rowValues 0 1 [⟨-7/3,true,false,false,false⟩] = [none] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨-7/3,true,false,false,false⟩] = [none] := by rfl
example : rowValues 0 0 [⟨-6/3,false,true,false,false⟩] = [none] := by rfl
example : rowValues 3 3 [⟨-6/3,false,true,false,false⟩] = [none] := by rfl
example : rowValues 0 1 [⟨-6/3,false,true,false,false⟩] = [none] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨-6/3,false,true,false,false⟩] = [none] := by rfl
example : rowValues 0 0 [⟨-5/3,true,true,false,false⟩] = [none] := by rfl
example : rowValues 3 3 [⟨-5/3,true,true,false,false⟩] = [none] := by rfl
example : rowValues 0 1 [⟨-5/3,true,true,false,false⟩] = [none] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨-5/3,true,true,false,false⟩] = [none] := by rfl
example : rowValues 0 0 [⟨-4/3,false,false,true,false⟩] = [none] := by rfl
example : rowValues 3 3 [⟨-4/3,false,false,true,false⟩] = [none] := by rfl
example : rowValues 0 1 [⟨-4/3,false,false,true,false⟩] = [some (-4/3)] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨-4/3,false,false,true,false⟩] = [some (-4/3)] := by rfl
example : rowValues 0 0 [⟨-3/3,true,false,true,false⟩] = [none] := by rfl
example : rowValues 3 3 [⟨-3/3,true,false,true,false⟩] = [none] := by rfl
example : rowValues 0 1 [⟨-3/3,true,false,true,false⟩] = [some (-3/3)] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨-3/3,true,false,true,false⟩] = [some (-3/3)] := by rfl
example : rowValues 0 0 [⟨-2/3,false,true,true,false⟩] = [none] := by rfl
example : rowValues 3 3 [⟨-2/3,false,true,true,false⟩] = [none] := by rfl
example : rowValues 0 1 [⟨-2/3,false,true,true,false⟩] = [some (-2/3)] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨-2/3,false,true,true,false⟩] = [some (-2/3)] := by rfl
example : rowValues 0 0 [⟨-1/3,true,true,true,false⟩] = [none] := by rfl
example : rowValues 3 3 [⟨-1/3,true,true,true,false⟩] = [none] := by rfl
example : rowValues 0 1 [⟨-1/3,true,true,true,false⟩] = [some (-1/3)] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨-1/3,true,true,true,false⟩] = [some (-1/3)] := by rfl
example : rowValues 0 0 [⟨0/3,false,false,false,true⟩] = [none] := by rfl
example : rowValues 3 3 [⟨0/3,false,false,false,true⟩] = [none] := by rfl
example : rowValues 0 1 [⟨0/3,false,false,false,true⟩] = [none] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨0/3,false,false,false,true⟩] = [none] := by rfl
example : rowValues 0 0 [⟨1/3,true,false,false,true⟩] = [none] := by rfl
example : rowValues 3 3 [⟨1/3,true,false,false,true⟩] = [none] := by rfl
example : rowValues 0 1 [⟨1/3,true,false,false,true⟩] = [none] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨1/3,true,false,false,true⟩] = [none] := by rfl
example : rowValues 0 0 [⟨2/3,false,true,false,true⟩] = [none] := by rfl
example : rowValues 3 3 [⟨2/3,false,true,false,true⟩] = [none] := by rfl
example : rowValues 0 1 [⟨2/3,false,true,false,true⟩] = [some (2/3)] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨2/3,false,true,false,true⟩] = [some (2/3)] := by rfl
example : rowValues 0 0 [⟨3/3,true,true,false,true⟩] = [none] := by rfl
example : rowValues 3 3 [⟨3/3,true,true,false,true⟩] = [none] := by rfl
example : rowValues 0 1 [⟨3/3,true,true,false,true⟩] = [none] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨3/3,true,true,false,true⟩] = [none] := by rfl
example : rowValues 0 0 [⟨4/3,false,false,true,true⟩] = [none] := by rfl
example : rowValues 3 3 [⟨4/3,false,false,true,true⟩] = [none] := by rfl
example : rowValues 0 1 [⟨4/3,false,false,true,true⟩] = [some (4/3)] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨4/3,false,false,true,true⟩] = [some (4/3)] := by rfl
example : rowValues 0 0 [⟨5/3,true,false,true,true⟩] = [none] := by rfl
example : rowValues 3 3 [⟨5/3,true,false,true,true⟩] = [none] := by rfl
example : rowValues 0 1 [⟨5/3,true,false,true,true⟩] = [some (5/3)] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨5/3,true,false,true,true⟩] = [some (5/3)] := by rfl
example : rowValues 0 0 [⟨6/3,false,true,true,true⟩] = [none] := by rfl
example : rowValues 3 3 [⟨6/3,false,true,true,true⟩] = [none] := by rfl
example : rowValues 0 1 [⟨6/3,false,true,true,true⟩] = [some (6/3)] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨6/3,false,true,true,true⟩] = [some (6/3)] := by rfl
example : rowValues 0 0 [⟨7/3,true,true,true,true⟩] = [none] := by rfl
example : rowValues 3 3 [⟨7/3,true,true,true,true⟩] = [none] := by rfl
example : rowValues 0 1 [⟨7/3,true,true,true,true⟩] = [some (7/3)] := by rfl
example : rowValues 100000000000000000000 100000000000000000001 [⟨7/3,true,true,true,true⟩] = [some (7/3)] := by rfl
example : rowValues 0 0 [] = [] := by rfl
example : rowValues 100000000000000000000 100000000000000000000 [] = [] := by rfl
example : rowValues 0 100000000000000000000 [] = [] := by rfl
example : rowValues 2 0 [⟨-2/3,false,false,true,false⟩,⟨0,false,false,true,false⟩,⟨7,false,false,true,false⟩,⟨5/11,false,false,true,false⟩,⟨-9,false,false,true,false⟩] = [some (-2/3),some (0),none,some (5/11),some (-9)] := by rfl
example : rowValues 2 1 [⟨1,false,true,false,true⟩,⟨2,false,true,false,true⟩,⟨3,false,true,false,true⟩,⟨4,false,true,false,true⟩] = [some (1),none,some (3),some (4)] := by rfl
example : rowValues 2 3 [⟨1,false,true,false,true⟩,⟨1,false,true,false,true⟩,⟨-1,false,true,false,true⟩] = [some (1),some (1),some (-1)] := by rfl
example : rowValues 100000000000000000000 99999999999999999999 [⟨1,false,false,true,false⟩,⟨2,false,false,true,false⟩,⟨3,false,false,true,false⟩] = [some (1),none,some (3)] := by rfl
example : rowValues 100000000000000000000 100000000000000000000 [⟨0,true,true,true,true⟩,⟨0,true,true,true,true⟩,⟨0,true,true,true,true⟩] = [none,some (0),some (0)] := by rfl
example : rowValues 7 0 [⟨-8,false,false,false,false⟩,⟨-7,true,false,false,false⟩,⟨-6,false,true,false,false⟩,⟨-5,true,true,false,false⟩,⟨-4,false,false,true,false⟩,⟨-3,true,false,true,false⟩,⟨-2,false,true,true,false⟩,⟨-1,true,true,true,false⟩,⟨0,false,false,false,true⟩,⟨1,true,false,false,true⟩,⟨2,false,true,false,true⟩,⟨3,true,true,false,true⟩,⟨4,false,false,true,true⟩,⟨5,true,false,true,true⟩,⟨6,false,true,true,true⟩,⟨7,true,true,true,true⟩] = [none,none,none,none,some (-4),some (-3),some (-2),none,none,none,some (2),none,some (4),some (5),some (6),some (7)] := by rfl
example : rowValues 7 8 [⟨-1/7,false,false,false,false⟩,⟨-1/7,true,false,false,false⟩,⟨-1/7,false,true,false,false⟩,⟨-1/7,true,true,false,false⟩,⟨-1/7,false,false,true,false⟩,⟨-1/7,true,false,true,false⟩,⟨-1/7,false,true,true,false⟩,⟨-1/7,true,true,true,false⟩,⟨-1/7,false,false,false,true⟩,⟨-1/7,true,false,false,true⟩,⟨-1/7,false,true,false,true⟩,⟨-1/7,true,true,false,true⟩,⟨-1/7,false,false,true,true⟩,⟨-1/7,true,false,true,true⟩,⟨-1/7,false,true,true,true⟩,⟨-1/7,true,true,true,true⟩] = [none,none,none,none,some (-1/7),some (-1/7),some (-1/7),some (-1/7),none,none,some (-1/7),none,some (-1/7),some (-1/7),some (-1/7),some (-1/7)] := by rfl
example : rowValues 0 0 [⟨7,false,false,false,false⟩,⟨7,false,false,true,false⟩,⟨7,false,false,false,false⟩,⟨7,false,true,false,true⟩] = [none,some (7),none,some (7)] := by rfl
example : rowValues 9 0 [⟨7,true,true,false,true⟩,⟨7,true,true,true,true⟩,⟨7,false,true,false,false⟩,⟨7,false,false,false,true⟩] = [none,some (7),none,none] := by rfl
end SampleRowValuesCases
run_cmd Lean.logInfo "PASS: 76 kernel-checked complete Option Rational list fixtures and 3 exact equations; all sixteen fields on and off diagonal, host override, seed suppression, arbitrary columns, ordered duplicates and signed weights"
