import DirectedFlowCutGap.BoundedDrawPrograms
open DirectedFlowCutGap
open FairBitWords BoundedBitRejection BitSamplerCoupling BoundedDrawPrograms

def mkWord : (b : ℕ) → ℕ → Bits b
  | 0, _ => ()
  | b + 1, x => (⟨x % 2, Nat.mod_lt _ (by decide)⟩, mkWord b (x / 2))

def tape3 (code : ℕ) : BoundedBitRejection.Tape 3 2 :=
  (mkWord (width 3) (code % 4), mkWord (width 3) (code / 4), ())

#eval do
  for b in [0:12] do
    for x in [0:2^b] do
      let r := FairBitWords.run b (mkWord b x)
      unless r == (x,b) do throw <| IO.userError "binary word interpreter mismatch"
  let rejectThenAccept := BoundedBitRejection.run 3 2 (tape3 11)
  unless decide (rejectThenAccept = (⟨some 2,2,4⟩ : BoundedBitRejection.Output 3)) do
    throw <| IO.userError "reject then accept mismatch"
  let allReject := BoundedBitRejection.run 3 2 (tape3 15)
  unless decide (allReject = (⟨none,2,4⟩ : BoundedBitRejection.Output 3)) do throw <| IO.userError "bounded rejection mismatch"
  let fallback := fallbackRun 3 2 (tape3 15)
  unless fallback.value == 0 && fallback.failed && fallback.bits == 4 do
    throw <| IO.userError "legal fallback mismatch"
  let immediate := BoundedBitRejection.run 3 2 (tape3 14)
  unless decide (immediate = (⟨some 2,1,2⟩ : BoundedBitRejection.Output 3)) do throw <| IO.userError "early exit mismatch"
  let noTrials := BoundedBitRejection.run 3 0 ()
  unless decide (noTrials = (⟨none,0,0⟩ : BoundedBitRejection.Output 3)) do throw <| IO.userError "zero trial mismatch"
  let emptyBound := BoundedBitRejection.run 0 2
    (mkWord (width 0) 0, mkWord (width 0) 1, ())
  unless decide (emptyBound = (⟨none,2,2⟩ : BoundedBitRejection.Output 0)) do throw <| IO.userError "zero bound mismatch"
  let mut counts := #[0,0,0,0]
  for code in [0:16] do
    let outcome := (BoundedBitRejection.run 3 2 (tape3 code)).value
    let index := match outcome with | none => 0 | some x => x.val + 1
    counts := counts.modify index (· + 1)
  unless counts == #[1,5,5,5] do throw <| IO.userError "exact bounded law frequencies mismatch"
  IO.println s!"PASS fair-bit interpreter, rejection/default boundaries; exact frequencies {counts}"

def adaptiveExample : Program ℕ 2 := .draw 3 (by decide) fun a =>
  if a.val == 0 then .draw 7 (by decide) (fun b => .pure (10 + b.val))
  else .pure a.val

#eval do
  let x : ℕ := Id.run <| execute (m := Id) (fun _ hn => ⟨0, hn⟩) adaptiveExample
  unless x == 10 do throw <| IO.userError "adaptive zero branch mismatch"
  let y : ℕ := Id.run <| execute (m := Id) (fun n hn => ⟨n-1, by omega⟩) adaptiveExample
  unless y == 2 do throw <| IO.userError "adaptive changing bound mismatch"
  IO.println "PASS finite adaptive interpreter with history-dependent draw bound"
