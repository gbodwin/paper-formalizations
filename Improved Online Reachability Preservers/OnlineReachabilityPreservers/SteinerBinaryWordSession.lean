import OnlineReachabilityPreservers.SteinerBinaryArrivalWordInput
import OnlineReachabilityPreservers.SteinerBinaryRawOnline

/-! Start the sampled online solver from binary arc words and retain its seed. -/

namespace OnlineReachabilityPreservers

set_option maxHeartbeats 1200000 in
/-- The decoded fixed graph, one sampled seed, and the current prefix state. -/
structure FinSteinerBinaryWordSession (n height : ℕ) where
  width : ℕ
  raw : List (Fin n × Fin n)
  graph : Arcs (Fin n)
  graphExact : raw.toFinset = graph
  seed : Vector Bool (steinerBitBudget graph height)
  state : FinSteinerBinaryArrivalState n

/-- Validate the binary graph before drawing any bits. The extra tally
accounts for input decoding and graph preparation. -/
def finSteinerBinaryStartFromWords {n : ℕ} {m : Type → Type} [Monad m]
    (arcWords : List (List Bool × List Bool)) (height width : ℕ) (nextBit : m Bool) :
    m (Option (FinSteinerBinaryWordSession n height) × ℕ) := do
  let decoded := decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords
  match decoded.1 with
  | none => pure (none,decoded.2+2)
  | some raw =>
    let prepared := prepareSteinerBinaryArcRowsWithWork raw
    let same := (prepareSteinerBinaryArcRowsWithWork_spec raw).1
    let (seed,state) ← finSteinerBinaryArrivalStartFromBitSource prepared.1 raw same height nextBit
    pure (some ⟨width,raw,prepared.1,same,seed,state⟩,decoded.2+prepared.2+5)

/-- A rejected graph leaves the stream position at its starting point. -/
theorem finSteinerBinaryStartFromWords_rejects {n : ℕ}
    (arcWords : List (List Bool × List Bool)) (height width : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (bad : (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).1 = none) :
    (finSteinerBinaryStartFromWords (n := n) arcWords height width (steinerBitStreamSource stream)).run start =
      ((none,(decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).2+2),start) := by
  unfold finSteinerBinaryStartFromWords
  dsimp only
  rw [bad]
  rfl

/-- On acceptance the stored graph and seed are those of the existing
initializer on the decoded arcs, with the same stream position. -/
theorem finSteinerBinaryStartFromWords_accepts {n : ℕ}
    (arcWords : List (List Bool × List Bool)) (height width : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (raw : List (Fin n × Fin n)) (good : (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).1 = some raw) :
    let prepared := prepareSteinerBinaryArcRowsWithWork raw
    let same := (prepareSteinerBinaryArcRowsWithWork_spec raw).1
    let seeded := (finSteinerBinaryArrivalStartFromBitSource prepared.1 raw same height (steinerBitStreamSource stream)).run start
    (finSteinerBinaryStartFromWords (n := n) arcWords height width (steinerBitStreamSource stream)).run start =
      ((some ⟨width,raw,prepared.1,same,seeded.1.1,seeded.1.2⟩,
        (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).2+prepared.2+5),seeded.2) := by
  unfold finSteinerBinaryStartFromWords
  dsimp only
  rw [good]
  rfl

/-- An accepted graph consumes exactly the input-dependent seed length. -/
theorem finSteinerBinaryStartFromWords_bits {n : ℕ}
    (arcWords : List (List Bool × List Bool)) (height width : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (raw : List (Fin n × Fin n)) (good : (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).1 = some raw) :
    ((finSteinerBinaryStartFromWords (n := n) arcWords height width (steinerBitStreamSource stream)).run start).2 =
      start + steinerBitBudget raw.toFinset height := by
  let prepared := prepareSteinerBinaryArcRowsWithWork raw
  let same := (prepareSteinerBinaryArcRowsWithWork_spec raw).1
  have exactBits := congrArg Prod.snd
    (finSteinerBinaryServeFromBitSource_stream prepared.1 raw same height stream start [])
  change ((finSteinerBinaryArrivalStartFromBitSource prepared.1 raw same height
    (steinerBitStreamSource stream)).run start).2 = start + steinerBitBudget prepared.1 height at exactBits
  rw [finSteinerBinaryStartFromWords_accepts arcWords height width stream start raw good]
  change ((finSteinerBinaryArrivalStartFromBitSource prepared.1 raw same height
    (steinerBitStreamSource stream)).run start).2 = start + steinerBitBudget raw.toFinset height
  exact exactBits.trans (congrArg (fun G => start + steinerBitBudget G height) same.symm)

/-- Advance the stored session from one encoded demand using its saved seed. -/
def finSteinerBinaryWordSessionStep {n height : ℕ} (session : FinSteinerBinaryWordSession n height)
    (words : List Bool × List Bool) : Option (FinSteinerBinaryWordSession n height) × ℕ :=
  let step := finSteinerBinaryArrivalStepFromWords session.graph session.raw session.graphExact
    height session.width session.seed session.state words
  (step.1.map (fun state => {session with state}),step.2+3)

/-- Canonically encoded demands give the same next prefix state while
reusing every field other than that state. -/
theorem finSteinerBinaryWordSessionStep_refines {n height : ℕ} (session : FinSteinerBinaryWordSession n height)
    (fits : n ≤ 2^session.width) (demand : Fin n × Fin n) :
    (finSteinerBinaryWordSessionStep session
      (binaryFinLabel session.width demand.1,binaryFinLabel session.width demand.2)).1 =
      some { session with
        state := finSteinerBinaryArrivalStepFromSeed session.graph session.raw session.graphExact
          height session.seed session.state demand } := by
  unfold finSteinerBinaryWordSessionStep
  dsimp only
  rw [finSteinerBinaryArrivalStepFromWords_refines _ _ _ _ _ fits]
  rfl

/-- Charge only the current input's width scan and numerical decoding
in the word-session step's extra tally. -/
theorem finSteinerBinaryWordSessionStep_work_le {n height : ℕ} (session : FinSteinerBinaryWordSession n height)
    (words : List Bool × List Bool) : (finSteinerBinaryWordSessionStep session words).2 ≤
      binaryEndpointWidthCheckBudget session.width [words] + binaryFinArcDecodingWorkBudget 1 session.width + 10 := by
  have measured := finSteinerBinaryArrivalStepFromWords_work_le session.graph session.raw session.graphExact
    height session.width session.seed session.state words
  unfold finSteinerBinaryWordSessionStep
  dsimp only
  omega

end OnlineReachabilityPreservers
