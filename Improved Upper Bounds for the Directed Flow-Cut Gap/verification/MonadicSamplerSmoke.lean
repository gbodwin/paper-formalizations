import DirectedFlowCutGap.MonadicBitSampler
open DirectedFlowCutGap FiniteDrawTrees LazyFairBitTrees MonadicBitSampler

private def nextBit : StateM (Nat × Nat) (Fin 2) := do
  let (code,used) ← get
  set (code/2,used+1)
  pure ⟨code%2,Nat.mod_lt _ (by decide)⟩

private def adaptive : FiniteDrawTrees.Tree Nat := .draw 3 (by decide) fun a =>
  if a.val == 0 then .draw 7 (by decide) (fun b => .pure (10+b.val)) else .pure a.val

#eval do
  for b in [0:10] do
    for code in [0:2^b] do
      let (w,(_,used)) := (wordValue nextBit b).run (code,0)
      unless w.val == code && used == b do
        throw <| IO.userError "fused word decoding or actual state mismatch"
  let mut counts := #[0,0,0]
  for code in [0:16] do
    let (r,state) := (MonadicBitSampler.draw nextBit 3 (by decide) 2).run (code,0)
    let (s,other) := (execute (liftBit nextBit) (rejection 3 (by decide) 2)).run (code,0)
    unless r.value == s.value && r.failed == s.failed && r.trials == s.trials &&
        r.bits == s.bits && state == other && state.2 == r.bits do
      throw <| IO.userError "fused rejection full output/state refinement mismatch"
    counts := counts.modify r.value.val (·+1)
  unless counts == #[6,5,5] do throw <| IO.userError "fused biased-default frequency mismatch"
  for code in [0:256] do
    let direct : Nat × (Nat × Nat) := (execute (sample nextBit 2) adaptive).run (code,0)
    let lowered : Nat × (Nat × Nat) := (execute (liftBit nextBit) (lower 2 adaptive)).run (code,0)
    unless direct == lowered do throw <| IO.userError "adaptive lawful-monad state refinement mismatch"
  let (d,(_,used)) := (MonadicBitSampler.draw nextBit 7 (by decide) 0).run (999,0)
  unless d.failed && d.value == 0 && used == 0 do
    throw <| IO.userError "fused zero-trial branch consumed a bit"
  IO.println "PASS fused bit decoding/rejection, full counters/state, adaptive changing bounds and legal zero-trial default"
