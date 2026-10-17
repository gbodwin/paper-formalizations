import LightEFTSpanners.StoredRecordMachine
open LightEFTSpanners.StoredRecords
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredRecords.rowValues
  let some c := env.find? name | throwError "rowValues missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "rowValues not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: rowValues safe, total, computable, explicit List.rec, no partial companion"
example (es : LightEFTSpanners.StoredSample.EdgeLists) (i j : ℕ) : rowValues es i j [] = [] := rfl
example (es : LightEFTSpanners.StoredSample.EdgeLists) (i j : ℕ) (w : ℚ) (ws : List ℚ) :
    rowValues es i j (w::ws) = LightEFTSpanners.StoredSample.entry (i,j) w es::rowValues es i (j+1) ws := rfl
example (es : LightEFTSpanners.StoredSample.EdgeLists) (i j : ℕ) (a b : ℚ) :
    rowValues es i j [a,b] = [LightEFTSpanners.StoredSample.entry (i,j) a es,
      LightEFTSpanners.StoredSample.entry (i,j+1) b es] := rfl
namespace RowValuesCases
open LightEFTSpanners
def empty : StoredSample.EdgeLists := ⟨[],[],[],[]⟩
def single : StoredSample.EdgeLists := ⟨[(0,0)],[(0,0)],[(0,0)],[(0,0)]⟩
def mixed : StoredSample.EdgeLists := ⟨[(3,2),(3,3),(3,4)],[(9,9),(2,3),(3,2)],[(4,3),(3,3)],[(3,2),(3,2),(3,5)]⟩
def huge : StoredSample.EdgeLists := ⟨[(100000000000000000000,100000000000000000000),(100000000000000000000,100000000000000000001)],[(100000000000000000001,100000000000000000000)],[],[(100000000000000000000,100000000000000000002)]⟩
def isolated : StoredSample.EdgeLists := ⟨[(2,0)],[(2,1)],[(2,2)],[(2,3)]⟩
def allbits : StoredSample.EdgeLists := ⟨[(7,1),(7,3),(7,5),(7,7),(7,9),(7,11),(7,13),(7,15)],[(7,2),(7,3),(7,6),(7,7),(7,10),(7,11),(7,14),(7,15)],[(7,4),(7,5),(7,6),(7,7),(7,12),(7,13),(7,14),(7,15)],[(7,8),(7,9),(7,10),(7,11),(7,12),(7,13),(7,14),(7,15)]⟩
example : rowValues empty 0 0 [] = [] := by rfl
example : rowValues empty 7 99 [] = [] := by rfl
example : rowValues empty 100000000000000000000 100000000000000000000 [] = [] := by rfl
example : rowValues empty 0 0 [0] = [⟨0,false,false,false,false⟩] := by rfl
example : rowValues empty 4 8 [-3/2,0,5/7] = [⟨-3/2,false,false,false,false⟩,⟨0,false,false,false,false⟩,⟨5/7,false,false,false,false⟩] := by rfl
example : rowValues empty 100000000000000000000 100000000000000000000 [-1,0,1] = [⟨-1,false,false,false,false⟩,⟨0,false,false,false,false⟩,⟨1,false,false,false,false⟩] := by rfl
example : rowValues single 0 0 [7] = [⟨7,true,true,true,true⟩] := by rfl
example : rowValues single 0 1 [7] = [⟨7,false,false,false,false⟩] := by rfl
example : rowValues single 1 0 [7] = [⟨7,false,false,false,false⟩] := by rfl
example : rowValues single 0 0 [7,7] = [⟨7,true,true,true,true⟩,⟨7,false,false,false,false⟩] := by rfl
example : rowValues single 0 1 [-7,7] = [⟨-7,false,false,false,false⟩,⟨7,false,false,false,false⟩] := by rfl
example : rowValues single 100000000000000000000 0 [-1,0,1] = [⟨-1,false,false,false,false⟩,⟨0,false,false,false,false⟩,⟨1,false,false,false,false⟩] := by rfl
example : rowValues mixed 3 0 [1,2,3,4,5] = [⟨1,false,false,false,false⟩,⟨2,false,false,false,false⟩,⟨3,true,true,false,true⟩,⟨4,true,false,true,false⟩,⟨5,true,false,true,false⟩] := by rfl
example : rowValues mixed 3 2 [1,2,3,4] = [⟨1,true,true,false,true⟩,⟨2,true,false,true,false⟩,⟨3,true,false,true,false⟩,⟨4,false,false,false,true⟩] := by rfl
example : rowValues mixed 3 3 [1,2,3] = [⟨1,true,false,true,false⟩,⟨2,true,false,true,false⟩,⟨3,false,false,false,true⟩] := by rfl
example : rowValues mixed 2 3 [1] = [⟨1,true,true,false,true⟩] := by rfl
example : rowValues mixed 4 3 [1] = [⟨1,true,false,true,false⟩] := by rfl
example : rowValues mixed 3 5 [1,2] = [⟨1,false,false,false,true⟩,⟨2,false,false,false,false⟩] := by rfl
example : rowValues mixed 3 2 [-1/7,0,2/3,-99] = [⟨-1/7,true,true,false,true⟩,⟨0,true,false,true,false⟩,⟨2/3,true,false,true,false⟩,⟨-99,false,false,false,true⟩] := by rfl
example : rowValues huge 100000000000000000000 100000000000000000000 [0,1,2,3] = [⟨0,true,false,false,false⟩,⟨1,true,true,false,false⟩,⟨2,false,false,false,true⟩,⟨3,false,false,false,false⟩] := by rfl
example : rowValues huge 100000000000000000000 100000000000000000001 [2,3] = [⟨2,true,true,false,false⟩,⟨3,false,false,false,true⟩] := by rfl
example : rowValues huge 100000000000000000001 100000000000000000000 [2] = [⟨2,true,true,false,false⟩] := by rfl
example : rowValues isolated 2 0 [1,-1,0,2/3] = [⟨1,true,false,false,false⟩,⟨-1,false,true,false,false⟩,⟨0,false,false,true,false⟩,⟨2/3,false,false,false,true⟩] := by rfl
example : rowValues allbits 7 0 [-8/3,-7/3,-6/3,-5/3,-4/3,-3/3,-2/3,-1/3,0/3,1/3,2/3,3/3,4/3,5/3,6/3,7/3] = [⟨-8/3,false,false,false,false⟩,⟨-7/3,true,false,false,false⟩,⟨-6/3,false,true,false,false⟩,⟨-5/3,true,true,false,false⟩,⟨-4/3,false,false,true,false⟩,⟨-3/3,true,false,true,false⟩,⟨-2/3,false,true,true,false⟩,⟨-1/3,true,true,true,false⟩,⟨0/3,false,false,false,true⟩,⟨1/3,true,false,false,true⟩,⟨2/3,false,true,false,true⟩,⟨3/3,true,true,false,true⟩,⟨4/3,false,false,true,true⟩,⟨5/3,true,false,true,true⟩,⟨6/3,false,true,true,true⟩,⟨7/3,true,true,true,true⟩] := by rfl
end RowValuesCases
run_cmd Lean.logInfo "PASS: 24 kernel-checked complete Entry-list fixtures and 3 exact equations; arbitrary fixed row and starting column, exact ordered weights and all sixteen membership-bit combinations, duplicates, reversals, signed rational payloads, empty rows and huge indices"
