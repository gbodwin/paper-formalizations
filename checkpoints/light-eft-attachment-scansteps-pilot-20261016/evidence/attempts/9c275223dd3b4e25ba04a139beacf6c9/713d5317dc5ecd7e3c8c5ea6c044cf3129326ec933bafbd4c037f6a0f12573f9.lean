import LightEFTSpanners.StoredForestDrawAttachment
open LightEFTSpanners.StoredForestDrawAttachment
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  let name := `LightEFTSpanners.StoredForestDrawAttachment.scanSteps
  let some c := env.find? name | throwError "scanSteps missing"
  if c.isUnsafe || c.isPartial || isNoncomputable env name then throwError "scanSteps not safe, total and computable"
  if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains"
  let .defnInfo d := c | throwError "Not a definition"
  unless d.value.getUsedConstants.contains `List.rec do throwError "List.rec absent"
  if d.value.getUsedConstants.contains name then throwError "Self-reference remains"
  logInfo "PASS: scanSteps safe, total, computable, explicit List.rec, no partial companion"
example (n : ℕ) (bank : LightEFTSpanners.StoredDrawLookup.Bank) : scanSteps n bank [] = 1 := rfl
example (n : ℕ) (bank : LightEFTSpanners.StoredDrawLookup.Bank) (r : Record) (rs : List Record) :
    scanSteps n bank (r::rs) = LightEFTSpanners.StoredDrawLookup.steps (key n r) bank+2+scanSteps n bank rs := rfl
private def r (i root : ℕ) (vs : List ℕ) (es : List (ℕ × ℕ)) : Record := (i,((root,vs),es))
private def a : Record := r 2 3 [99,3,3] [(999,1),(1,1)]
private def b : Record := r 0 1 [] []
private def c : Record := r 5 3 [0] [(0,0)]
private def bank : LightEFTSpanners.StoredDrawLookup.Bank := [(13,[]),(1,[[(9,9)]]),(28,[[]])]
#eval do
  let checks := [
    decide (scanSteps 0 [] [] = 1),
    decide (scanSteps 999 bank [] = 1),
    decide (scanSteps 5 [] [a] = 4),
    decide (scanSteps 5 [] [a,b,c] = 10),
    decide (scanSteps 5 [(13,[])] [a] = 4),
    decide (scanSteps 5 [(1,[])] [a] = 5),
    decide (scanSteps 5 bank [a] = 4),
    decide (scanSteps 5 bank [b] = 5),
    decide (scanSteps 5 bank [c] = 6),
    decide (scanSteps 5 bank [r 0 99 [] []] = 7),
    decide (scanSteps 5 bank [a,b,c] = 13),
    decide (scanSteps 5 bank [c,a,b] = 13),
    decide (scanSteps 5 bank [a,a] = 7),
    decide (scanSteps 5 [(13,[]),(13,[[(1,2)]])] [a] = 4),
    decide (scanSteps 5 [(99,[]),(13,[]),(13,[[(1,2)]])] [a] = 5),
    decide (scanSteps 0 [(3,[])] [r 0 3 [] [],r 999 3 [99] [(100,200)]] = 7),
    decide (scanSteps 100000000000000000000 [(200000000000000000003,[])] [a] = 4),
    decide (scanSteps 5 (List.replicate 16 (99,[])) [a] = 20),
    decide (scanSteps 5 (List.replicate 16 (99,[]) ++ [(13,[])]) [a] = 20),
    decide (scanSteps 5 [] (List.replicate 16 a) = 49)]
  unless checks.all id do throw (IO.userError "Exact attachment scan-count fixtures failed")
  IO.println s!"PASS: {checks.length} complete natural scan-count fixtures; empty input, lookup plus two plus tail, first-match empty payload, misses, arbitrary records and n, label collisions, repeated records, huge labels and long banks"
