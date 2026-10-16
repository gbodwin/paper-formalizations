import LightEFTSpanners.ExecutableVotingWork
open LightEFTSpanners.ExecutableVoting
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  for name in [`LightEFTSpanners.ExecutableVoting.sampleWork,
      `LightEFTSpanners.ExecutableVoting.hostWork, `LightEFTSpanners.ExecutableVoting.edgesWork] do
    let some c := env.find? name | throwError "Missing {name}"
    if c.isUnsafe || c.isPartial || isNoncomputable env name then
      throwError "{name} is not safe, total and computable"
    if (env.find? (name ++ `_unsafe_rec)).isSome then throwError "Partial companion remains for {name}"
    let .defnInfo d := c | throwError "Not a definition: {name}"
    unless d.value.getUsedConstants.contains `List.rec do throwError "No explicit List.rec: {name}"
    if d.value.getUsedConstants.contains name then throwError "Self-reference: {name}"
    logInfo m!"PASS: {name} is safe, total, computable, explicit List.rec, without partial companion"

private def sw (e : Sym2 (Fin 2)) (l : List (Finset (Sym2 (Fin 2)))) :=
  sampleWork ∅ ∅ ∅ (fun _ => 0) (by simp) 1 e l
private def hw (eligible : Finset (Fin 1)) (draws : List (Finset (Sym2 (Fin 2))))
    (hosts : List (Fin 1)) :=
  hostWork ∅ (fun _ => 0) (by simp) 1 (fun _ => eligible) (fun _ => ∅)
    (fun _ _ _ => draws) ∅ s(0,1) hosts
private def ew (h : ℕ) (l : List (Sym2 (Fin 2))) :=
  edgesWork (j:=1) ∅ (fun _ => 0) (by simp) 1 (fun _ => Finset.univ) (fun _ => ∅)
    (fun _ _ _ => [∅]) h l
#eval do
  unless decide (sw s(0,1) [] = (0,1)) && decide (sw s(0,1) [∅] = (1,63)) &&
      decide (sw s(0,0) [∅] = (0,63)) && decide (sw s(0,1) [∅,∅] = (2,125)) do
    throw (IO.userError "sampleWork full-pair fixtures failed")
  unless decide (hw ∅ [] [] = (∅,1)) && decide (hw ∅ [] [0] = (∅,2)) &&
      decide (hw Finset.univ [] [0] = (∅,6)) &&
      decide (hw Finset.univ [∅] [0] = ({0},68)) &&
      decide (hw Finset.univ [∅] [0,0] = ({0},135)) do
    throw (IO.userError "hostWork full-pair fixtures failed")
  unless decide (ew 1 [] = (∅,1)) && decide (ew 1 [s(0,1)] = ({s(0,1)},72)) &&
      decide (ew 2 [s(0,1)] = (∅,72)) &&
      decide (ew 1 [s(0,1),s(0,1)] = ({s(0,1)},143)) do
    throw (IO.userError "edgesWork full-pair fixtures failed")
  IO.println "PASS: 13 full-pair fixtures, including work counters, empty inputs, admission/rejection and repetitions"
