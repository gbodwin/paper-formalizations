import LightEFTSpanners.SampleRecordMatrix
open LightEFTSpanners.SampleRecords
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.SampleRecords.values
  let some c := env.find? name | throwError "values missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "values not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: values safe, total, computable, explicit List.rec, no partial companion"
example (i : ℕ) : values i [] = [] := rfl
example (i : ℕ) (row : List LightEFTSpanners.SampleRecords.Entry) (rows : LightEFTSpanners.SampleRecords.Records) :
    values i (row::rows) = rowValues i 0 row :: values (i+1) rows := rfl
example (i : ℕ) (a b : LightEFTSpanners.SampleRecords.Entry) :
    values i [[],[a,b],[],[b]] = [[],[value (i+1) 0 a,value (i+1) 1 b],[],[value (i+3) 0 b]] := rfl
namespace SampleValuesCases
example : values 0 [[⟨-8/3,false,false,false,false⟩,⟨-8/3,false,false,false,false⟩],[⟨-7/11,false,false,false,false⟩],[]] = [[none,none],[none],[]] := by rfl
example : values 1 [[⟨-8/3,false,false,false,false⟩,⟨-7/11,false,false,false,false⟩],[],[⟨-8/3,false,false,false,false⟩]] = [[none,none],[],[none]] := by rfl
example : values 0 [[],[⟨-8/3,false,false,false,false⟩,⟨-7/11,false,false,false,false⟩],[],[⟨-7/11,false,false,false,false⟩]] = [[],[none,none],[],[none]] := by rfl
example : values 100000000000000000000 [[⟨-8/3,false,false,false,false⟩],[],[⟨-8/3,false,false,false,false⟩,⟨-7/11,false,false,false,false⟩,⟨-7/11,false,false,false,false⟩]] = [[none],[],[none,none,none]] := by rfl
example : values 0 [[⟨-7/3,true,false,false,false⟩,⟨-7/3,true,false,false,false⟩],[⟨-7/11,true,false,false,false⟩],[]] = [[none,none],[none],[]] := by rfl
example : values 1 [[⟨-7/3,true,false,false,false⟩,⟨-7/11,true,false,false,false⟩],[],[⟨-7/3,true,false,false,false⟩]] = [[none,none],[],[none]] := by rfl
example : values 0 [[],[⟨-7/3,true,false,false,false⟩,⟨-7/11,true,false,false,false⟩],[],[⟨-7/11,true,false,false,false⟩]] = [[],[none,none],[],[none]] := by rfl
example : values 100000000000000000000 [[⟨-7/3,true,false,false,false⟩],[],[⟨-7/3,true,false,false,false⟩,⟨-7/11,true,false,false,false⟩,⟨-7/11,true,false,false,false⟩]] = [[none],[],[none,none,none]] := by rfl
example : values 0 [[⟨-6/3,false,true,false,false⟩,⟨-6/3,false,true,false,false⟩],[⟨-7/11,false,true,false,false⟩],[]] = [[none,none],[none],[]] := by rfl
example : values 1 [[⟨-6/3,false,true,false,false⟩,⟨-7/11,false,true,false,false⟩],[],[⟨-6/3,false,true,false,false⟩]] = [[none,none],[],[none]] := by rfl
example : values 0 [[],[⟨-6/3,false,true,false,false⟩,⟨-7/11,false,true,false,false⟩],[],[⟨-7/11,false,true,false,false⟩]] = [[],[none,none],[],[none]] := by rfl
example : values 100000000000000000000 [[⟨-6/3,false,true,false,false⟩],[],[⟨-6/3,false,true,false,false⟩,⟨-7/11,false,true,false,false⟩,⟨-7/11,false,true,false,false⟩]] = [[none],[],[none,none,none]] := by rfl
example : values 0 [[⟨-5/3,true,true,false,false⟩,⟨-5/3,true,true,false,false⟩],[⟨-7/11,true,true,false,false⟩],[]] = [[none,none],[none],[]] := by rfl
example : values 1 [[⟨-5/3,true,true,false,false⟩,⟨-7/11,true,true,false,false⟩],[],[⟨-5/3,true,true,false,false⟩]] = [[none,none],[],[none]] := by rfl
example : values 0 [[],[⟨-5/3,true,true,false,false⟩,⟨-7/11,true,true,false,false⟩],[],[⟨-7/11,true,true,false,false⟩]] = [[],[none,none],[],[none]] := by rfl
example : values 100000000000000000000 [[⟨-5/3,true,true,false,false⟩],[],[⟨-5/3,true,true,false,false⟩,⟨-7/11,true,true,false,false⟩,⟨-7/11,true,true,false,false⟩]] = [[none],[],[none,none,none]] := by rfl
example : values 0 [[⟨-4/3,false,false,true,false⟩,⟨-4/3,false,false,true,false⟩],[⟨-7/11,false,false,true,false⟩],[]] = [[none,some (-4/3)],[some (-7/11)],[]] := by rfl
example : values 1 [[⟨-4/3,false,false,true,false⟩,⟨-7/11,false,false,true,false⟩],[],[⟨-4/3,false,false,true,false⟩]] = [[some (-4/3),none],[],[some (-4/3)]] := by rfl
example : values 0 [[],[⟨-4/3,false,false,true,false⟩,⟨-7/11,false,false,true,false⟩],[],[⟨-7/11,false,false,true,false⟩]] = [[],[some (-4/3),none],[],[some (-7/11)]] := by rfl
example : values 100000000000000000000 [[⟨-4/3,false,false,true,false⟩],[],[⟨-4/3,false,false,true,false⟩,⟨-7/11,false,false,true,false⟩,⟨-7/11,false,false,true,false⟩]] = [[some (-4/3)],[],[some (-4/3),some (-7/11),some (-7/11)]] := by rfl
example : values 0 [[⟨-3/3,true,false,true,false⟩,⟨-3/3,true,false,true,false⟩],[⟨-7/11,true,false,true,false⟩],[]] = [[none,some (-3/3)],[some (-7/11)],[]] := by rfl
example : values 1 [[⟨-3/3,true,false,true,false⟩,⟨-7/11,true,false,true,false⟩],[],[⟨-3/3,true,false,true,false⟩]] = [[some (-3/3),none],[],[some (-3/3)]] := by rfl
example : values 0 [[],[⟨-3/3,true,false,true,false⟩,⟨-7/11,true,false,true,false⟩],[],[⟨-7/11,true,false,true,false⟩]] = [[],[some (-3/3),none],[],[some (-7/11)]] := by rfl
example : values 100000000000000000000 [[⟨-3/3,true,false,true,false⟩],[],[⟨-3/3,true,false,true,false⟩,⟨-7/11,true,false,true,false⟩,⟨-7/11,true,false,true,false⟩]] = [[some (-3/3)],[],[some (-3/3),some (-7/11),some (-7/11)]] := by rfl
example : values 0 [[⟨-2/3,false,true,true,false⟩,⟨-2/3,false,true,true,false⟩],[⟨-7/11,false,true,true,false⟩],[]] = [[none,some (-2/3)],[some (-7/11)],[]] := by rfl
example : values 1 [[⟨-2/3,false,true,true,false⟩,⟨-7/11,false,true,true,false⟩],[],[⟨-2/3,false,true,true,false⟩]] = [[some (-2/3),none],[],[some (-2/3)]] := by rfl
example : values 0 [[],[⟨-2/3,false,true,true,false⟩,⟨-7/11,false,true,true,false⟩],[],[⟨-7/11,false,true,true,false⟩]] = [[],[some (-2/3),none],[],[some (-7/11)]] := by rfl
example : values 100000000000000000000 [[⟨-2/3,false,true,true,false⟩],[],[⟨-2/3,false,true,true,false⟩,⟨-7/11,false,true,true,false⟩,⟨-7/11,false,true,true,false⟩]] = [[some (-2/3)],[],[some (-2/3),some (-7/11),some (-7/11)]] := by rfl
example : values 0 [[⟨-1/3,true,true,true,false⟩,⟨-1/3,true,true,true,false⟩],[⟨-7/11,true,true,true,false⟩],[]] = [[none,some (-1/3)],[some (-7/11)],[]] := by rfl
example : values 1 [[⟨-1/3,true,true,true,false⟩,⟨-7/11,true,true,true,false⟩],[],[⟨-1/3,true,true,true,false⟩]] = [[some (-1/3),none],[],[some (-1/3)]] := by rfl
example : values 0 [[],[⟨-1/3,true,true,true,false⟩,⟨-7/11,true,true,true,false⟩],[],[⟨-7/11,true,true,true,false⟩]] = [[],[some (-1/3),none],[],[some (-7/11)]] := by rfl
example : values 100000000000000000000 [[⟨-1/3,true,true,true,false⟩],[],[⟨-1/3,true,true,true,false⟩,⟨-7/11,true,true,true,false⟩,⟨-7/11,true,true,true,false⟩]] = [[some (-1/3)],[],[some (-1/3),some (-7/11),some (-7/11)]] := by rfl
example : values 0 [[⟨0/3,false,false,false,true⟩,⟨0/3,false,false,false,true⟩],[⟨-7/11,false,false,false,true⟩],[]] = [[none,none],[none],[]] := by rfl
example : values 1 [[⟨0/3,false,false,false,true⟩,⟨-7/11,false,false,false,true⟩],[],[⟨0/3,false,false,false,true⟩]] = [[none,none],[],[none]] := by rfl
example : values 0 [[],[⟨0/3,false,false,false,true⟩,⟨-7/11,false,false,false,true⟩],[],[⟨-7/11,false,false,false,true⟩]] = [[],[none,none],[],[none]] := by rfl
example : values 100000000000000000000 [[⟨0/3,false,false,false,true⟩],[],[⟨0/3,false,false,false,true⟩,⟨-7/11,false,false,false,true⟩,⟨-7/11,false,false,false,true⟩]] = [[none],[],[none,none,none]] := by rfl
example : values 0 [[⟨1/3,true,false,false,true⟩,⟨1/3,true,false,false,true⟩],[⟨-7/11,true,false,false,true⟩],[]] = [[none,none],[none],[]] := by rfl
example : values 1 [[⟨1/3,true,false,false,true⟩,⟨-7/11,true,false,false,true⟩],[],[⟨1/3,true,false,false,true⟩]] = [[none,none],[],[none]] := by rfl
example : values 0 [[],[⟨1/3,true,false,false,true⟩,⟨-7/11,true,false,false,true⟩],[],[⟨-7/11,true,false,false,true⟩]] = [[],[none,none],[],[none]] := by rfl
example : values 100000000000000000000 [[⟨1/3,true,false,false,true⟩],[],[⟨1/3,true,false,false,true⟩,⟨-7/11,true,false,false,true⟩,⟨-7/11,true,false,false,true⟩]] = [[none],[],[none,none,none]] := by rfl
example : values 0 [[⟨2/3,false,true,false,true⟩,⟨2/3,false,true,false,true⟩],[⟨-7/11,false,true,false,true⟩],[]] = [[none,some (2/3)],[some (-7/11)],[]] := by rfl
example : values 1 [[⟨2/3,false,true,false,true⟩,⟨-7/11,false,true,false,true⟩],[],[⟨2/3,false,true,false,true⟩]] = [[some (2/3),none],[],[some (2/3)]] := by rfl
example : values 0 [[],[⟨2/3,false,true,false,true⟩,⟨-7/11,false,true,false,true⟩],[],[⟨-7/11,false,true,false,true⟩]] = [[],[some (2/3),none],[],[some (-7/11)]] := by rfl
example : values 100000000000000000000 [[⟨2/3,false,true,false,true⟩],[],[⟨2/3,false,true,false,true⟩,⟨-7/11,false,true,false,true⟩,⟨-7/11,false,true,false,true⟩]] = [[some (2/3)],[],[some (2/3),some (-7/11),some (-7/11)]] := by rfl
example : values 0 [[⟨3/3,true,true,false,true⟩,⟨3/3,true,true,false,true⟩],[⟨-7/11,true,true,false,true⟩],[]] = [[none,none],[none],[]] := by rfl
example : values 1 [[⟨3/3,true,true,false,true⟩,⟨-7/11,true,true,false,true⟩],[],[⟨3/3,true,true,false,true⟩]] = [[none,none],[],[none]] := by rfl
example : values 0 [[],[⟨3/3,true,true,false,true⟩,⟨-7/11,true,true,false,true⟩],[],[⟨-7/11,true,true,false,true⟩]] = [[],[none,none],[],[none]] := by rfl
example : values 100000000000000000000 [[⟨3/3,true,true,false,true⟩],[],[⟨3/3,true,true,false,true⟩,⟨-7/11,true,true,false,true⟩,⟨-7/11,true,true,false,true⟩]] = [[none],[],[none,none,none]] := by rfl
example : values 0 [[⟨4/3,false,false,true,true⟩,⟨4/3,false,false,true,true⟩],[⟨-7/11,false,false,true,true⟩],[]] = [[none,some (4/3)],[some (-7/11)],[]] := by rfl
example : values 1 [[⟨4/3,false,false,true,true⟩,⟨-7/11,false,false,true,true⟩],[],[⟨4/3,false,false,true,true⟩]] = [[some (4/3),none],[],[some (4/3)]] := by rfl
example : values 0 [[],[⟨4/3,false,false,true,true⟩,⟨-7/11,false,false,true,true⟩],[],[⟨-7/11,false,false,true,true⟩]] = [[],[some (4/3),none],[],[some (-7/11)]] := by rfl
example : values 100000000000000000000 [[⟨4/3,false,false,true,true⟩],[],[⟨4/3,false,false,true,true⟩,⟨-7/11,false,false,true,true⟩,⟨-7/11,false,false,true,true⟩]] = [[some (4/3)],[],[some (4/3),some (-7/11),some (-7/11)]] := by rfl
example : values 0 [[⟨5/3,true,false,true,true⟩,⟨5/3,true,false,true,true⟩],[⟨-7/11,true,false,true,true⟩],[]] = [[none,some (5/3)],[some (-7/11)],[]] := by rfl
example : values 1 [[⟨5/3,true,false,true,true⟩,⟨-7/11,true,false,true,true⟩],[],[⟨5/3,true,false,true,true⟩]] = [[some (5/3),none],[],[some (5/3)]] := by rfl
example : values 0 [[],[⟨5/3,true,false,true,true⟩,⟨-7/11,true,false,true,true⟩],[],[⟨-7/11,true,false,true,true⟩]] = [[],[some (5/3),none],[],[some (-7/11)]] := by rfl
example : values 100000000000000000000 [[⟨5/3,true,false,true,true⟩],[],[⟨5/3,true,false,true,true⟩,⟨-7/11,true,false,true,true⟩,⟨-7/11,true,false,true,true⟩]] = [[some (5/3)],[],[some (5/3),some (-7/11),some (-7/11)]] := by rfl
example : values 0 [[⟨6/3,false,true,true,true⟩,⟨6/3,false,true,true,true⟩],[⟨-7/11,false,true,true,true⟩],[]] = [[none,some (6/3)],[some (-7/11)],[]] := by rfl
example : values 1 [[⟨6/3,false,true,true,true⟩,⟨-7/11,false,true,true,true⟩],[],[⟨6/3,false,true,true,true⟩]] = [[some (6/3),none],[],[some (6/3)]] := by rfl
example : values 0 [[],[⟨6/3,false,true,true,true⟩,⟨-7/11,false,true,true,true⟩],[],[⟨-7/11,false,true,true,true⟩]] = [[],[some (6/3),none],[],[some (-7/11)]] := by rfl
example : values 100000000000000000000 [[⟨6/3,false,true,true,true⟩],[],[⟨6/3,false,true,true,true⟩,⟨-7/11,false,true,true,true⟩,⟨-7/11,false,true,true,true⟩]] = [[some (6/3)],[],[some (6/3),some (-7/11),some (-7/11)]] := by rfl
example : values 0 [[⟨7/3,true,true,true,true⟩,⟨7/3,true,true,true,true⟩],[⟨-7/11,true,true,true,true⟩],[]] = [[none,some (7/3)],[some (-7/11)],[]] := by rfl
example : values 1 [[⟨7/3,true,true,true,true⟩,⟨-7/11,true,true,true,true⟩],[],[⟨7/3,true,true,true,true⟩]] = [[some (7/3),none],[],[some (7/3)]] := by rfl
example : values 0 [[],[⟨7/3,true,true,true,true⟩,⟨-7/11,true,true,true,true⟩],[],[⟨-7/11,true,true,true,true⟩]] = [[],[some (7/3),none],[],[some (-7/11)]] := by rfl
example : values 100000000000000000000 [[⟨7/3,true,true,true,true⟩],[],[⟨7/3,true,true,true,true⟩,⟨-7/11,true,true,true,true⟩,⟨-7/11,true,true,true,true⟩]] = [[some (7/3)],[],[some (7/3),some (-7/11),some (-7/11)]] := by rfl
example : values 0 [] = [] := by rfl
example : values 100000000000000000000 [] = [] := by rfl
example : values 0 [[]] = [[]] := by rfl
example : values 7 [[],[],[]] = [[],[],[]] := by rfl
example : values 0 [[⟨1,false,false,true,false⟩],[⟨2,false,false,true,false⟩],[⟨3,false,false,true,false⟩]] = [[none],[some (2)],[some (3)]] := by rfl
example : values 2 [[⟨-2/3,false,false,true,false⟩,⟨0,false,false,true,false⟩,⟨7,false,false,true,false⟩,⟨5/11,false,false,true,false⟩,⟨-9,false,false,true,false⟩],[],[⟨1,false,true,false,true⟩]] = [[some (-2/3),some (0),none,some (5/11),some (-9)],[],[some (1)]] := by rfl
example : values 0 [[⟨7,false,false,false,false⟩,⟨7,false,false,true,false⟩,⟨7,false,false,false,false⟩,⟨7,false,true,false,true⟩]] = [[none,some (7),none,some (7)]] := by rfl
example : values 7 [[⟨-8,false,false,false,false⟩,⟨-7,true,false,false,false⟩,⟨-6,false,true,false,false⟩,⟨-5,true,true,false,false⟩,⟨-4,false,false,true,false⟩,⟨-3,true,false,true,false⟩,⟨-2,false,true,true,false⟩,⟨-1,true,true,true,false⟩,⟨0,false,false,false,true⟩,⟨1,true,false,false,true⟩,⟨2,false,true,false,true⟩,⟨3,true,true,false,true⟩,⟨4,false,false,true,true⟩,⟨5,true,false,true,true⟩,⟨6,false,true,true,true⟩,⟨7,true,true,true,true⟩],[],[⟨-1/7,false,false,false,false⟩,⟨-1/7,true,false,false,false⟩,⟨-1/7,false,true,false,false⟩,⟨-1/7,true,true,false,false⟩,⟨-1/7,false,false,true,false⟩,⟨-1/7,true,false,true,false⟩,⟨-1/7,false,true,true,false⟩,⟨-1/7,true,true,true,false⟩,⟨-1/7,false,false,false,true⟩,⟨-1/7,true,false,false,true⟩,⟨-1/7,false,true,false,true⟩,⟨-1/7,true,true,false,true⟩,⟨-1/7,false,false,true,true⟩,⟨-1/7,true,false,true,true⟩,⟨-1/7,false,true,true,true⟩,⟨-1/7,true,true,true,true⟩]] = [[none,none,none,none,some (-4),some (-3),some (-2),none,none,none,some (2),none,some (4),some (5),some (6),some (7)],[],[none,none,none,none,some (-1/7),some (-1/7),some (-1/7),some (-1/7),none,none,some (-1/7),none,some (-1/7),some (-1/7),some (-1/7),some (-1/7)]] := by rfl
example : values 0 [[],[],[⟨0,true,true,true,true⟩],[]] = [[],[],[some (0)],[]] := by rfl
example : values 100000000000000000000 [[],[⟨7,true,true,false,true⟩,⟨7,true,true,true,true⟩,⟨7,false,true,false,false⟩,⟨7,false,false,false,true⟩]] = [[],[none,some (7),none,none]] := by rfl
example : values 1 [[⟨7,false,false,true,false⟩,⟨7,false,false,true,false⟩],[],[⟨7,false,false,true,false⟩]] = [[some (7),none],[],[some (7)]] := by rfl
example : values 3 [[⟨1,false,true,false,true⟩],[⟨1,true,true,false,true⟩,⟨1,true,true,true,true⟩],[]] = [[some (1)],[none,some (1)],[]] := by rfl
end SampleValuesCases
run_cmd Lean.logInfo "PASS: 76 kernel-checked complete nested Option Rational fixtures and 3 exact equations; ragged records, empty rows, row advancement, column reset, all sixteen fields and diagonal suppression"
