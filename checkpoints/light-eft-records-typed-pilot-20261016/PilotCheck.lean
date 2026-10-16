import LightEFTSpanners.StoredCandidateDrawEncoding
open LightEFTSpanners
open StoredOriginalCandidateRecords
-- Test-only structural equality checks both fields of every output record.
deriving instance DecidableEq for StoredForestBank.TypedInput
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredOriginalCandidateRecords.typedValue
  let some c := env.find? name | throwError "typedValue missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "typedValue not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: typedValue safe, total, computable, explicit List.rec, no partial companion"
example {n : ℕ} (Q : List (Fin n × Fin n)) (bank : StoredCandidateDrawLookup.TypedBank n) :
    typedValue Q bank [] = [] := rfl
example {n : ℕ} (Q : List (Fin n × Fin n)) (bank : StoredCandidateDrawLookup.TypedBank n)
    (x : Fin n × Fin n) (xs : List (Fin n × Fin n)) :
    typedValue Q bank (x::xs) = if s(x.1,x.2)∈StoredSample.edgeSet Q then typedValue Q bank xs
      else ⟨x,StoredCandidateDrawLookup.typedValue s(x.1,x.2) bank⟩::typedValue Q bank xs := rfl
private def a : StoredDrawLookup.TypedBank 3 :=
  [(7,[[],[(0,1),(1,0),(2,2),(0,1)]]),(7,[]),(100000000000000000000,[[(2,0)],[]])]
private def b : StoredDrawLookup.TypedBank 3 := [(0,[[(2,0)]])]
private def bank : StoredCandidateDrawLookup.TypedBank 3 := [((1,0),a),((0,1),b),((2,2),b)]
#eval do
  let checks := [
    decide (typedValue [] bank [] = []),
    decide (typedValue (n:=3) [] [] [(0,1)] = [(StoredForestBank.TypedInput.mk (n:=3) (0,1) [])]),
    decide (typedValue [(0,1)] bank [(0,1)] = []),
    decide (typedValue [(1,0)] bank [(0,1),(1,0),(0,1)] = []),
    decide (typedValue [(0,1),(1,0),(0,1)] bank [(0,1),(2,2),(1,0)] = [(StoredForestBank.TypedInput.mk (n:=3) (2,2) b)]),
    decide (typedValue [] bank [(1,0)] = [(StoredForestBank.TypedInput.mk (n:=3) (1,0) a)]),
    decide (typedValue [] bank [(0,1),(0,1)] = [(StoredForestBank.TypedInput.mk (n:=3) (0,1) a),(StoredForestBank.TypedInput.mk (n:=3) (0,1) a)]),
    decide (typedValue [] bank [(2,2)] = [(StoredForestBank.TypedInput.mk (n:=3) (2,2) b)]),
    decide (typedValue [(2,2)] bank [(2,2),(0,1)] = [(StoredForestBank.TypedInput.mk (n:=3) (0,1) a)]),
    decide (typedValue [] bank [(0,2),(1,0),(2,0)] = [(StoredForestBank.TypedInput.mk (n:=3) (0,2) []),(StoredForestBank.TypedInput.mk (n:=3) (1,0) a),(StoredForestBank.TypedInput.mk (n:=3) (2,0) [])]),
    decide (typedValue [] [((0,1),[]),((1,0),a)] [(1,0)] = [(StoredForestBank.TypedInput.mk (n:=3) (1,0) [])]),
    decide (typedValue [] [((0,1),b),((1,0),a)] [(0,1),(1,0)] = [(StoredForestBank.TypedInput.mk (n:=3) (0,1) b),(StoredForestBank.TypedInput.mk (n:=3) (1,0) b)]),
    decide (typedValue [(0,2)] bank [(2,2),(2,0),(1,0),(0,1),(2,2)] =
      [(StoredForestBank.TypedInput.mk (n:=3) (2,2) b),(StoredForestBank.TypedInput.mk (n:=3) (1,0) a),(StoredForestBank.TypedInput.mk (n:=3) (0,1) a),(StoredForestBank.TypedInput.mk (n:=3) (2,2) b)]),
    decide (typedValue [(1,1)] bank [(0,1),(1,0)] = [(StoredForestBank.TypedInput.mk (n:=3) (0,1) a),(StoredForestBank.TypedInput.mk (n:=3) (1,0) a)]),
    decide (typedValue (n:=1) [] [] [(0,0),(0,0)] = [(StoredForestBank.TypedInput.mk (n:=1) (0,0) []),(StoredForestBank.TypedInput.mk (n:=1) (0,0) [])]),
    decide (typedValue (n:=1) [(0,0)] [] [(0,0),(0,0)] = []),
    decide (typedValue (n:=0) [] [] [] = [])]
  unless checks.all id do throw (IO.userError "Complete ordered record fixtures failed")
  IO.println s!"PASS: {checks.length} full-record fixtures: zero/singleton vertices, empty/missing payloads, undirected Q membership, duplicates, orientation, survivor order, first-match lookup and unrestricted nested payloads"
