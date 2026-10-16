import LightEFTSpanners.StoredOriginalCandidateRecords
open LightEFTSpanners
open StoredOriginalCandidateRecords
-- Existing structural equality checks both fields of every output record.
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredOriginalCandidateRecords.value
  let some c := env.find? name | throwError "value missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "value not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: value safe, total, computable, explicit List.rec, no partial companion"
example (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank) :
    value Q bank [] = [] := rfl
example (Q : List StoredEdges.Edge) (bank : StoredCandidateDrawLookup.Bank)
    (x : StoredEdges.Edge) (xs : List StoredEdges.Edge) :
    value Q bank (x::xs) = if StoredEdges.contains x Q then value Q bank xs
      else ⟨x,StoredCandidateDrawLookup.value x bank⟩::value Q bank xs := rfl
private def a : StoredDrawLookup.Bank :=
  [(7,[[],[(0,1),(1,0),(2,2),(0,1)]]),(7,[]),(100000000000000000000,[[(2,0)],[]])]
private def b : StoredDrawLookup.Bank := [(0,[[(2,0)]])]
private def bank : StoredCandidateDrawLookup.Bank := [((1,0),a),((0,1),b),((2,2),b)]
#eval do
  let checks := [
    decide (value [] bank [] = []),
    decide (value [] [] [(0,1)] = [(StoredForestBank.Input.mk (0,1) [])]),
    decide (value [(0,1)] bank [(0,1)] = []),
    decide (value [(1,0)] bank [(0,1),(1,0),(0,1)] = []),
    decide (value [(0,1),(1,0),(0,1)] bank [(0,1),(2,2),(1,0)] = [(StoredForestBank.Input.mk (2,2) b)]),
    decide (value [] bank [(1,0)] = [(StoredForestBank.Input.mk (1,0) a)]),
    decide (value [] bank [(0,1),(0,1)] = [(StoredForestBank.Input.mk (0,1) a),(StoredForestBank.Input.mk (0,1) a)]),
    decide (value [] bank [(2,2)] = [(StoredForestBank.Input.mk (2,2) b)]),
    decide (value [(2,2)] bank [(2,2),(0,1)] = [(StoredForestBank.Input.mk (0,1) a)]),
    decide (value [] bank [(0,2),(1,0),(2,0)] = [(StoredForestBank.Input.mk (0,2) []),(StoredForestBank.Input.mk (1,0) a),(StoredForestBank.Input.mk (2,0) [])]),
    decide (value [] [((0,1),[]),((1,0),a)] [(1,0)] = [(StoredForestBank.Input.mk (1,0) [])]),
    decide (value [] [((0,1),b),((1,0),a)] [(0,1),(1,0)] = [(StoredForestBank.Input.mk (0,1) b),(StoredForestBank.Input.mk (1,0) b)]),
    decide (value [(0,2)] bank [(2,2),(2,0),(1,0),(0,1),(2,2)] =
      [(StoredForestBank.Input.mk (2,2) b),(StoredForestBank.Input.mk (1,0) a),(StoredForestBank.Input.mk (0,1) a),(StoredForestBank.Input.mk (2,2) b)]),
    decide (value [(1,1)] bank [(0,1),(1,0)] = [(StoredForestBank.Input.mk (0,1) a),(StoredForestBank.Input.mk (1,0) a)]),
    decide (value [] [] [(0,0),(0,0)] = [(StoredForestBank.Input.mk (0,0) []),(StoredForestBank.Input.mk (0,0) [])]),
    decide (value [(0,0)] [] [(0,0),(0,0)] = []),
    decide (value [] [] [] = []),
    decide (value [] [((100000000000000000000,7),a)] [(7,100000000000000000000)] =
      [StoredForestBank.Input.mk (7,100000000000000000000) a]),
    decide (value [(7,100000000000000000000)] [] [(100000000000000000000,7),(7,7)] =
      [StoredForestBank.Input.mk (7,7) []])]
  unless checks.all id do throw (IO.userError "Complete ordered record fixtures failed")
  IO.println s!"PASS: {checks.length} full-record fixtures: empty lists, loops, arbitrary large natural endpoints, empty/missing payloads, undirected Q membership, duplicates, orientation, survivor order, first-match lookup and unrestricted nested payloads"
