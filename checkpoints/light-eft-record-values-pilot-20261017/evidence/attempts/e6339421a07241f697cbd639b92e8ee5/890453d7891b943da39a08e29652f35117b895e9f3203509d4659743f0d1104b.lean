import LightEFTSpanners.StoredRecordMachine
open LightEFTSpanners.StoredRecords
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredRecords.values
  let some c := env.find? name | throwError "values missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "values not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: values safe, total, computable, explicit List.rec, no partial companion"
example (es : LightEFTSpanners.StoredSample.EdgeLists) (i : ℕ) : values es i [] = [] := rfl
example (es : LightEFTSpanners.StoredSample.EdgeLists) (i : ℕ) (row : List ℚ) (rows : Weights) :
    values es i (row::rows) = rowValues es i 0 row::values es (i+1) rows := rfl
example (es : LightEFTSpanners.StoredSample.EdgeLists) (i : ℕ) (a b : ℚ) :
    values es i [[],[a,b],[],[b]] = [[],[LightEFTSpanners.StoredSample.entry (i+1,0) a es,
      LightEFTSpanners.StoredSample.entry (i+1,1) b es],[],[LightEFTSpanners.StoredSample.entry (i+3,0) b es]] := rfl
namespace ValuesCases
open LightEFTSpanners
def empty : StoredSample.EdgeLists := ⟨[],[],[],[]⟩
def single : StoredSample.EdgeLists := ⟨[(0,0)],[(0,0)],[(0,0)],[(0,0)]⟩
def mixed : StoredSample.EdgeLists := ⟨[(3,0),(4,0),(4,1),(6,2)],[(0,3),(1,4),(4,1)],[(3,1),(5,0)],[(4,0),(4,0),(0,6)]⟩
def huge : StoredSample.EdgeLists := ⟨[(100000000000000000000,0),(100000000000000000002,1)],[(0,100000000000000000001)],[(100000000000000000003,0)],[(100000000000000000000,1),(100000000000000000002,0)]⟩
def isolated : StoredSample.EdgeLists := ⟨[(2,0)],[(2,1)],[(2,2)],[(2,3)]⟩
def allbits : StoredSample.EdgeLists := ⟨[(20,1),(20,3),(20,5),(20,7),(20,9),(20,11),(20,13),(20,15)],[(20,2),(20,3),(20,6),(20,7),(20,10),(20,11),(20,14),(20,15)],[(20,4),(20,5),(20,6),(20,7),(20,12),(20,13),(20,14),(20,15)],[(20,8),(20,9),(20,10),(20,11),(20,12),(20,13),(20,14),(20,15)]⟩
example : values empty 0 [] = [] := by rfl
example : values empty 100000000000000000000 [] = [] := by rfl
example : values empty 0 [[]] = [[]] := by rfl
example : values empty 7 [[],[],[]] = [[],[],[]] := by rfl
example : values empty 0 [[0]] = [[⟨0,false,false,false,false⟩]] := by rfl
example : values empty 4 [[-3/2,0],[],[5/7]] = [[⟨-3/2,false,false,false,false⟩,⟨0,false,false,false,false⟩],[],[⟨5/7,false,false,false,false⟩]] := by rfl
example : values empty 100000000000000000000 [[-1,0,1],[],[]] = [[⟨-1,false,false,false,false⟩,⟨0,false,false,false,false⟩,⟨1,false,false,false,false⟩],[],[]] := by rfl
example : values single 0 [[7]] = [[⟨7,true,true,true,true⟩]] := by rfl
example : values single 0 [[7,7],[7]] = [[⟨7,true,true,true,true⟩,⟨7,false,false,false,false⟩],[⟨7,false,false,false,false⟩]] := by rfl
example : values single 0 [[],[7]] = [[],[⟨7,false,false,false,false⟩]] := by rfl
example : values single 1 [[7],[7,7]] = [[⟨7,false,false,false,false⟩],[⟨7,false,false,false,false⟩,⟨7,false,false,false,false⟩]] := by rfl
example : values single 100000000000000000000 [[],[-7,7]] = [[],[⟨-7,false,false,false,false⟩,⟨7,false,false,false,false⟩]] := by rfl
example : values mixed 3 [[1,2,3],[4,5],[],[6,7,8]] = [[⟨1,true,true,false,false⟩,⟨2,false,false,true,false⟩,⟨3,false,false,false,false⟩],[⟨4,true,false,false,true⟩,⟨5,true,true,false,false⟩],[],[⟨6,false,false,false,true⟩,⟨7,false,false,false,false⟩,⟨8,true,false,false,false⟩]] := by rfl
example : values mixed 2 [[],[1,2],[3,4],[],[5]] = [[],[⟨1,true,true,false,false⟩,⟨2,false,false,true,false⟩],[⟨3,true,false,false,true⟩,⟨4,true,true,false,false⟩],[],[⟨5,false,false,false,true⟩]] := by rfl
example : values mixed 3 [[1],[],[2]] = [[⟨1,true,true,false,false⟩],[],[⟨2,false,false,true,false⟩]] := by rfl
example : values mixed 4 [[1,2,3,4],[5]] = [[⟨1,true,false,false,true⟩,⟨2,true,true,false,false⟩,⟨3,false,false,false,false⟩,⟨4,false,false,false,false⟩],[⟨5,false,false,true,false⟩]] := by rfl
example : values mixed 3 [[-1/7],[0,2/3],[-99]] = [[⟨-1/7,true,true,false,false⟩],[⟨0,true,false,false,true⟩,⟨2/3,true,true,false,false⟩],[⟨-99,false,false,true,false⟩]] := by rfl
example : values huge 100000000000000000000 [[0,1],[2],[],[3,4]] = [[⟨0,true,false,false,false⟩,⟨1,false,false,false,true⟩],[⟨2,false,true,false,false⟩],[],[⟨3,false,false,true,false⟩,⟨4,false,false,false,false⟩]] := by rfl
example : values huge 100000000000000000000 [[],[],[0,1]] = [[],[],[⟨0,false,false,false,true⟩,⟨1,true,false,false,false⟩]] := by rfl
example : values huge 100000000000000000001 [[1],[2,3]] = [[⟨1,false,true,false,false⟩],[⟨2,false,false,false,true⟩,⟨3,true,false,false,false⟩]] := by rfl
example : values isolated 2 [[1,-1,0,2/3],[1]] = [[⟨1,true,false,false,false⟩,⟨-1,false,true,false,false⟩,⟨0,false,false,true,false⟩,⟨2/3,false,false,false,true⟩],[⟨1,false,false,false,false⟩]] := by rfl
example : values allbits 20 [[-8/3,-7/3,-6/3,-5/3,-4/3,-3/3,-2/3,-1/3,0/3,1/3,2/3,3/3,4/3,5/3,6/3,7/3]] = [[⟨-8/3,false,false,false,false⟩,⟨-7/3,true,false,false,false⟩,⟨-6/3,false,true,false,false⟩,⟨-5/3,true,true,false,false⟩,⟨-4/3,false,false,true,false⟩,⟨-3/3,true,false,true,false⟩,⟨-2/3,false,true,true,false⟩,⟨-1/3,true,true,true,false⟩,⟨0/3,false,false,false,true⟩,⟨1/3,true,false,false,true⟩,⟨2/3,false,true,false,true⟩,⟨3/3,true,true,false,true⟩,⟨4/3,false,false,true,true⟩,⟨5/3,true,false,true,true⟩,⟨6/3,false,true,true,true⟩,⟨7/3,true,true,true,true⟩]] := by rfl
example : values allbits 19 [[],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[]] = [[],[⟨0,false,false,false,false⟩,⟨1,true,false,false,false⟩,⟨2,false,true,false,false⟩,⟨3,true,true,false,false⟩,⟨4,false,false,true,false⟩,⟨5,true,false,true,false⟩,⟨6,false,true,true,false⟩,⟨7,true,true,true,false⟩,⟨8,false,false,false,true⟩,⟨9,true,false,false,true⟩,⟨10,false,true,false,true⟩,⟨11,true,true,false,true⟩,⟨12,false,false,true,true⟩,⟨13,true,false,true,true⟩,⟨14,false,true,true,true⟩,⟨15,true,true,true,true⟩],[]] := by rfl
example : values mixed 3 [[9,9],[],[9],[],[]] = [[⟨9,true,true,false,false⟩,⟨9,false,false,true,false⟩],[],[⟨9,false,false,true,false⟩],[],[]] := by rfl
end ValuesCases
run_cmd Lean.logInfo "PASS: 24 kernel-checked complete nested Entry-list fixtures and 3 exact equations; arbitrary starting row, ragged matrices, empty rows, row advancement and column reset, all sixteen membership patterns"
