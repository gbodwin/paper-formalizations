import DirectedFlowCutGap.RetainedFairBitLaw
import DirectedFlowCutGap.FairBitConfidence
open DirectedFlowCutGap
open FiniteDrawTrees LazyFairBitTrees FairBitWords BitSamplerCoupling

private def bitsFromCode (n : ℕ) (hn : 0 < n) : StateM (ℕ × ℕ) (Fin n) := do
  let (code,used) ← get
  set (code / n,used+1)
  pure ⟨code % n,Nat.mod_lt _ hn⟩

private def mkWord : (b : ℕ) → ℕ → Bits b
  | 0, _ => ()
  | b+1, x => (⟨x%2,Nat.mod_lt _ (by decide)⟩,mkWord b (x/2))

private def tape3 (x : ℕ) : BoundedBitRejection.Tape 3 2 :=
  (mkWord (width 3) (x%4),mkWord (width 3) (x/4),())

#eval do
  for b in [0:10] do
    for x in [0:2^b] do
      let (w,(_,used)) := (execute bitsFromCode (word b)).run (x,0)
      unless (FairBitWords.run b w).1 == x && used == b do
        throw <| IO.userError "lazy word state/counter mismatch"
  let mut counts := #[0,0,0]
  for code in [0:16] do
    let (r,(_,used)) := (execute bitsFromCode (rejection 3 (by decide) 2)).run (code,0)
    let old := fallbackRun 3 2 (tape3 code)
    unless r.value == old.value && r.failed == old.failed &&
        r.trials == old.trials && r.bits == old.bits && used == r.bits do
      throw <| IO.userError "lazy rejection output or actual bit-state mismatch"
    counts := counts.modify r.value.val (·+1)
  unless counts == #[6,5,5] do throw <| IO.userError "bounded-default exact frequencies mismatch"
  let (early,(_,earlyUsed)) := (execute bitsFromCode (rejection 3 (by decide) 2)).run (14,0)
  unless early.value == 2 && earlyUsed == 2 do throw <| IO.userError "unreached rejection tail was consumed"
  let (defaultTrial,(_,noUsed)) := (execute bitsFromCode (rejection 7 (by decide) 0)).run (999,0)
  unless defaultTrial.failed && defaultTrial.value == 0 && noUsed == 0 do throw <| IO.userError "zero-trial default mismatch"
  IO.println s!"PASS lazy words, exact rejection/refinement/state consumption; frequencies {counts}"

private def adaptive : FiniteDrawTrees.Tree ℕ := .draw 3 (by decide) fun a =>
  if a.val == 0 then .draw 7 (by decide) (fun b => .pure (10+b.val)) else .pure a.val

#eval do
  for code in [0:256] do
    let (x,(_,used)) := (execute bitsFromCode (lower 2 adaptive)).run (code,0)
    unless (x == 1 || x == 2 || (10 ≤ x && x ≤ 16)) && used ≤ 12 do
      throw <| IO.userError "adaptive lowered changing-bound execution mismatch"
  let (defaultValue,(_,zeroUsed)) := (execute bitsFromCode (lower 0 adaptive)).run (12,0)
  unless defaultValue == 10 && zeroUsed == 0 do throw <| IO.userError "default-induced adaptive branch mismatch"
  for q in [0:20] do
    for k in [0:10] do
      unless q * 2^k ≤ 2^(FairBitConfidence.trials q k) do
        throw <| IO.userError "confidence budget arithmetic mismatch"
  IO.println "PASS adaptive legal-default histories and confidence arithmetic"

private def active : RetainedGridState.PairFlags 2 :=
  #v[#v[false,true],#v[true,false]]

#eval do
  let (t,(_,used)) := (execute bitsFromCode
    (lower 2 (RetainedDrawTrees.sampleTape (by decide : 0<3) active))).run (0,0)
  let i := RetainedTapeInput.materialize (by decide : 0<3) active t
  unless i.order.length == 2 && i.order.toFinset == ({(0,1),(1,0)} : Finset (Fin 2 × Fin 2)) do
    throw <| IO.userError "actual retained active-label tape mismatch"
  unless i.cell (0,1) == 0 && i.cell (1,0) == 0 && used == 7 do
    throw <| IO.userError "actual retained permutation/cell bit consumption mismatch"
  IO.println "PASS retained active-mask tape materialization from seven actually consumed fair bits"
