import DirectedFlowCutGap.EncodedAmplification

open DirectedFlowCutGap

private def bit (n : ℕ) (hp : 0 < n) : StateM (List Bool × ℕ × Bool) (Fin n) := do
  let (bits, calls, legal) ← get
  match bits with
  | [] =>
    set (([] : List Bool), calls + 1, false)
    pure ⟨0, hp⟩
  | b :: rest =>
    set (rest, calls + 1, legal && (n == 2))
    if h : n = 2 then
      let value : Fin 2 := if b then 1 else 0
      pure (h.symm ▸ value)
    else pure ⟨0, hp⟩

private def program : FiniteDrawTrees.Tree (Fin 3) :=
  EncodedAmplification.bitTree (fun x => RawNonnegativeRational.Code.ofNat x.val)
    (FiniteDrawTrees.pick 3 (by decide)) 1 1 2

def main : IO Unit := do
  let (out, rest, calls, legal) := (FiniteDrawTrees.execute bit program).run
    ([true, true, false, true, true, false, false], 0, true)
  unless out.val == 1 && rest == [false] && calls == 6 && legal do
    throw (IO.userError "amplification did not reject once and choose the cheaper actual sample")
  let (defaulted, rest, calls, legal) := (FiniteDrawTrees.execute bit program).run
    (List.replicate 16 true, 0, true)
  unless defaulted.val == 0 && rest.isEmpty && calls == 16 && legal do
    throw (IO.userError "bounded rejection did not use the legal default on each repeated sample")
  IO.println "PASS fair-bit amplification: actual rejection, minimum, retained suffix, and defaults"
