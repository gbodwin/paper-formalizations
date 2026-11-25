import OnlineReachabilityPreservers.SteinerBitBudget
import OnlineReachabilityPreservers.SteinerHeightIndexWork

/-! Word work for the fixed-budget seed decoder, including its arithmetic setup. -/

namespace OnlineReachabilityPreservers

/-- Compute bit length by halving, with word work for every division and step. -/
def bitLengthWithWork (n : ℕ) : ℕ × ℕ :=
  if n = 0 then (0,3) else
    let tail := bitLengthWithWork (n/2)
    (tail.1+1,tail.2+7)
termination_by n
decreasing_by omega

theorem bitLengthWithWork_spec (n : ℕ) :
    let result := bitLengthWithWork n
    result.1 = n.size ∧ result.2 = 7*n.size+3 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    dsimp only
    rw [bitLengthWithWork]
    by_cases zero : n = 0
    · simp [zero]
    · have small : n/2 < n := by omega
      obtain ⟨same,work⟩ := ih (n/2) small
      have nonzero : Nat.bit n.bodd n.div2 ≠ 0 := by rwa [Nat.bit_bodd_div2]
      have size := Nat.size_bit nonzero
      rw [Nat.bit_bodd_div2, Nat.div2_val] at size
      rw [ite_eq_right zero]
      exact ⟨by simpa only [same, Nat.succ_eq_add_one] using size.symm,
        by simp only [work, size, Nat.succ_eq_add_one]; omega⟩

theorem bitLengthWork_le (n : ℕ) : (bitLengthWithWork n).2 ≤ 7*n+3 := by
  rw [(bitLengthWithWork_spec n).2]
  have bound := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  omega

theorem max_size_eq_log2_add_one (n : ℕ) : max 1 n.size = n.log2+1 := by
  by_cases zero : n = 0
  · simp [zero, Nat.log2_zero]
  · have size : n.size = n.log2+1 := by
      apply le_antisymm
      · exact Nat.size_le.mpr ((Nat.log2_lt zero).mp (Nat.lt_succ_self _))
      · exact Nat.succ_le_of_lt (Nat.lt_size.mpr (Nat.log2_self_le zero))
    rw [size, max_eq_right (by omega)]

/-- Search the supplied interval for the integer fifth root, with a
word-work tally for the power tests. -/
def fifthRootWithWork (value : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0,2)
  | k+1 =>
    let square := (k+1)*(k+1)
    if square*square*(k+1) ≤ value then (k+1,16) else
      let tail := fifthRootWithWork value k
      (tail.1,tail.2+16)

theorem fifthRootWithWork_spec (value cap : ℕ) :
    let result := fifthRootWithWork value cap
    result.1 = Nat.findGreatest (fun j => j^5 ≤ value) cap ∧ result.2 ≤ 16*cap+2 := by
  induction cap with
  | zero => simp [fifthRootWithWork]
  | succ cap ih =>
    obtain ⟨same,work⟩ := ih
    have power : (cap+1)*(cap+1)*((cap+1)*(cap+1))*(cap+1) = (cap+1)^5 := by ring
    by_cases fits : (cap+1)^5 ≤ value
    · simp only [fifthRootWithWork, power, Nat.findGreatest_succ, ite_eq_left fits]
      exact ⟨trivial,by omega⟩
    · simp only [fifthRootWithWork, power, Nat.findGreatest_succ, ite_eq_right fits, same]
      exact ⟨trivial,by omega⟩

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Compute the sizes used by the decoder from the input cardinalities and
the already prepared forest width. The recurrence for histories does not
enumerate any history or use the vertex or arc index maps. -/
def prepareSteinerSeedDecoderSizesWithWork (G : Arcs V) (height width n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) : SteinerSeedDecoderSizes G height width × ℕ :=
  let bits := bitLengthWithWork n
  let vertexWidth := bitLengthWithWork (n-1)
  let arcWidth := bitLengthWithWork (m-1)
  let root := fifthRootWithWork (n*n*n) n
  let histories := heightLexBlockCountWithWordWork n height
  let logBound := max 1 bits.1
  let levels := height+1
  let trials := 16*levels*levels*logBound
  let earlyCount := trials*(n*(width*(2*histories.1+1)))
  let hubs := if n = 0 then 0 else 4*logBound*n/(root.1+1)+1
  have logEq : logBound = n.log2+1 := by
    dsimp only [logBound,bits]
    rw [(bitLengthWithWork_spec n).1, max_size_eq_log2_add_one]
  have rootEq : root.1 = steinerThinThreshold n := by
    have cube : n*n*n = n^3 := by ring
    dsimp only [root]
    rw [cube, (fifthRootWithWork_spec (n^3) n).1]
    rfl
  have trialEq : trials = earlyTrialCount V height := by
    dsimp only [trials,levels]
    rw [logEq, hn, earlyTrialCount]
    ring
  let sizes : SteinerSeedDecoderSizes G height width :=
    { vertexCount := n
      arcCount := m
      earlyCount := earlyCount
      hubCount := hubs
      vertexWidth := vertexWidth.1
      arcWidth := arcWidth.1
      vertexCount_eq := hn
      arcCount_eq := hm
      earlyCount_eq := by
        dsimp only [earlyCount, histories, earlySeedCoordinateCountByWidth]
        rw [trialEq, (heightLexBlockCountWithWordWork_spec n height).1, hn,
          heightLexBlockCount_card, heightNode_card]
      hubCount_eq := by
        dsimp only [hubs]
        rw [logEq, rootEq, hn]
        rfl
      vertexWidth_eq := (bitLengthWithWork_spec (n-1)).1
      arcWidth_eq := (bitLengthWithWork_spec (m-1)).1 }
  (sizes,bits.2+vertexWidth.2+arcWidth.2+root.2+histories.2+45)

theorem prepareSteinerSeedDecoderSizesWithWork_le (G : Arcs V) (height width n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) :
    (prepareSteinerSeedDecoderSizesWithWork G height width n m hn hm).2 ≤
      30*n+7*m+5*height+57 := by
  have bits := bitLengthWork_le n
  have vertex := bitLengthWork_le (n-1)
  have arc := bitLengthWork_le (m-1)
  have root := (fifthRootWithWork_spec (n*n*n) n).2
  have histories := (heightLexBlockCountWithWordWork_spec n height).2
  dsimp only [prepareSteinerSeedDecoderSizesWithWork]
  omega

/-- Run the metered decoder with one shared arithmetic setup. The input
cardinalities, forest width, bit access and key-index maps are supplied. -/
def decodeCompleteSteinerSeedFromPreparedWidthWithWork (G : Arcs V) (height width n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) :=
  let setup := prepareSteinerSeedDecoderSizesWithWork G height width n m hn hm
  let out := decodeCompleteSteinerSeedCursorWithWork G height width width_eq setup.1 coordinates vertices arcs bits cursor
  (out.1, setup.2+out.2+4)

theorem decodeCompleteSteinerSeedFromPreparedWidthWithWork_eq (G : Arcs V) (height width n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    {budget : ℕ} (bits : Fin budget → Bool) (cursor : BitCursor budget) :
    (decodeCompleteSteinerSeedFromPreparedWidthWithWork G height width n m hn hm width_eq
      coordinates vertices arcs bits cursor).1 =
      decodeCompleteSteinerSeedCursorWithEndAtWidth G height width width_eq coordinates vertices arcs bits cursor :=
  (decodeCompleteSteinerSeedCursorWithWork_spec G height width width_eq _ coordinates vertices arcs bits cursor).1

/-- The arithmetic budget uses the same counts as the reader. -/
def steinerBitBudgetFromDecoderSizes {G : Arcs V} {height width : ℕ} (sizes : SteinerSeedDecoderSizes G height width) : ℕ :=
  (sizes.earlyCount*width + sizes.hubCount*(2*sizes.vertexWidth) + sizes.arcCount*(2*sizes.arcWidth))*sizes.arcCount

theorem steinerBitBudgetFromDecoderSizes_eq {G : Arcs V} {height width : ℕ}
    (width_eq : width = (forestScale G height).log2+1) (sizes : SteinerSeedDecoderSizes G height width) :
    steinerBitBudgetFromDecoderSizes sizes = steinerBitBudget G height := by
  unfold steinerBitBudgetFromDecoderSizes steinerBitBudget
  rw [sizes.earlyCount_eq, sizes.hubCount_eq, sizes.vertexWidth_eq, sizes.arcWidth_eq,
    sizes.vertexCount_eq, sizes.arcCount_eq, ← completeSteinerSeedBitBoundAtWidth_eq G height width width_eq]
  rfl

/-- An explicit bound on the work at the graph's fixed fair-bit budget. -/
def completeSteinerSeedDecodeWorkPolynomial (n m height : ℕ) : ℕ :=
  let B := completeSteinerSeedPolynomial n m height
  24*(B*m) + 29*(B+4*(n+1)*n+1+m) + 30*n+7*m+5*height+116

theorem decodeCompleteSteinerSeedCursorWithWork_fixed_budget (G : Arcs V) (height width : ℕ)
    (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (cursor : BitCursor (steinerBitBudget G height)) :
    (decodeCompleteSteinerSeedFromPreparedWidthWithWork G height width (Fintype.card V) G.card rfl rfl width_eq
      coordinates vertices arcs bits cursor).2 ≤
      completeSteinerSeedDecodeWorkPolynomial (Fintype.card V) G.card height := by
  let n := Fintype.card V
  let m := G.card
  let B := completeSteinerSeedPolynomial n m height
  let setup := prepareSteinerSeedDecoderSizesWithWork G height width n m rfl rfl
  let out := decodeCompleteSteinerSeedCursorWithWork G height width width_eq setup.1 coordinates vertices arcs bits cursor
  change setup.2+out.2+4 ≤ _
  have setupBound := prepareSteinerSeedDecoderSizesWithWork_le G height width n m rfl rfl
  have decodeBound := (decodeCompleteSteinerSeedCursorWithWork_spec G height width width_eq
    setup.1 coordinates vertices arcs bits cursor).2.2
  have endBound := out.1.2.bounded.trans (steinerBitBudget_polynomial G height)
  have early : setup.1.earlyCount ≤ B := by
    rw [setup.1.earlyCount_eq]
    have sum := completeSteinerSeedBitBound_polynomial G height
    rw [← completeSteinerSeedBitBoundAtWidth_eq G height width width_eq] at sum
    have positive : 1 ≤ width := by omega
    have step := Nat.mul_le_mul_left (earlySeedCoordinateCountByWidth V height width) positive
    unfold completeSteinerSeedBitBoundAtWidth at sum
    change _ ≤ B at sum
    have first : earlySeedCoordinateCountByWidth V height width ≤
        earlySeedCoordinateCountByWidth V height width*width := by simpa only [Nat.mul_one] using step
    exact first.trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans sum))
  have hub : setup.1.hubCount ≤ 4*(n+1)*n+1 := by
    rw [setup.1.hubCount_eq]
    exact (completeSteinerHubCount_le V).trans (by
      have log := Nat.log2_le_self n
      gcongr)
  have counts : setup.1.earlyCount+setup.1.hubCount+setup.1.arcCount ≤ B+4*(n+1)*n+1+m := by
    rw [setup.1.arcCount_eq]
    omega
  change out.1.2.position ≤ B*m at endBound
  change setup.2 ≤ 30*n+7*m+5*height+57 at setupBound
  change out.2 ≤ 24*(out.1.2.position-cursor.position)+29*(setup.1.earlyCount+setup.1.hubCount+setup.1.arcCount)+55 at decodeBound
  change setup.2+out.2+4 ≤ 24*(B*m)+29*(B+4*(n+1)*n+1+m)+30*n+7*m+5*height+116
  omega

private theorem castDecoderBudget {G : Arcs V} {height width a b : ℕ}
    (width_eq : width = (forestScale G height).log2+1) (sizes : SteinerSeedDecoderSizes G height width)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (same : a = b) (bits : Fin b → Bool) :
    let left := decodeCompleteSteinerSeedCursorWithWork G height width width_eq sizes coordinates vertices arcs
      (fun i : Fin a => bits (Fin.cast same i)) ⟨0,Nat.zero_le a⟩
    let right := decodeCompleteSteinerSeedCursorWithWork G height width width_eq sizes coordinates vertices arcs
      bits ⟨0,Nat.zero_le b⟩
    (left.1.1,left.1.2.position,left.2) = (right.1.1,right.1.2.position,right.2) := by
  subst a
  rfl

@[inline] private def decodeFixedSteinerBudgetUsing {Result : Type*} (G : Arcs V) (height width n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (width_eq : width = (forestScale G height).log2+1)
    (bits : Fin (steinerBitBudget G height) → Bool)
    (decode : SteinerSeedDecoderSizes G height width → {b : ℕ} → (Fin b → Bool) →
      BitCursor b → (Option Result × BitCursor b) × ℕ) :=
  let setup := prepareSteinerSeedDecoderSizesWithWork G height width n m hn hm
  let budget := steinerBitBudgetFromDecoderSizes setup.1
  let same := steinerBitBudgetFromDecoderSizes_eq width_eq setup.1
  let out := decode setup.1 (fun i : Fin budget => bits (Fin.cast same i)) ⟨0,Nat.zero_le budget⟩
  ((out.1.1,out.1.2.position),setup.2+out.2+20)

/-- Compute the fixed budget from the same arithmetic setup used by the
metered reader. Return the seed and counts if present, the final bit
position on either branch, and the work of setup and decoding together. -/
def decodeCompleteSteinerSeedWithFixedBudgetWork (G : Arcs V) (height width n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) :=
  decodeFixedSteinerBudgetUsing G height width n m hn hm width_eq bits
    (fun sizes {_} reader cursor => decodeCompleteSteinerSeedCursorWithWork G height width width_eq sizes
      coordinates vertices arcs reader cursor)

private def decodeFixedSteinerBudgetWithIndexedThin (G : Arcs V) (height width n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) :=
  decodeFixedSteinerBudgetUsing G height width n m hn hm width_eq bits
    (fun sizes {_} reader cursor => decodeSteinerSeedCursorWithIndexedThin G height width width_eq sizes
      coordinates vertices arcs reader cursor)

private theorem decodeFixedSteinerBudgetWithIndexedThin_spec (G : Arcs V) (height width n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) :
    let out := decodeFixedSteinerBudgetWithIndexedThin G height width n m hn hm width_eq coordinates vertices arcs bits
    ((out.1.1.map Prod.fst,out.1.2),out.2) =
      decodeCompleteSteinerSeedWithFixedBudgetWork G height width n m hn hm width_eq coordinates vertices arcs bits ∧
      ∀ packet, out.1.1 = some packet → ∀ e, packet.2 (arcs e) = packet.1.1.2.2 e := by
  let setup := prepareSteinerSeedDecoderSizesWithWork G height width n m hn hm
  let budget := steinerBitBudgetFromDecoderSizes setup.1
  let same := steinerBitBudgetFromDecoderSizes_eq width_eq setup.1
  obtain ⟨agreement,view⟩ := decodeSteinerSeedCursorWithIndexedThin_spec G height width width_eq setup.1
    coordinates vertices arcs (fun i : Fin budget => bits (Fin.cast same i)) ⟨0,Nat.zero_le budget⟩
  refine ⟨congrArg (fun v => ((v.1.1,v.1.2.position),setup.2+v.2+20)) agreement,view⟩

theorem decodeCompleteSteinerSeedWithFixedBudgetWork_spec (G : Arcs V) (height width n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) :
    let out := decodeCompleteSteinerSeedWithFixedBudgetWork G height width n m hn hm width_eq coordinates vertices arcs bits
    let reference := decodeCompleteSteinerSeedCursorWithEndAtWidth G height width width_eq coordinates vertices arcs
      bits ⟨0,Nat.zero_le _⟩
    out.1 = (reference.1,reference.2.position) ∧
      out.2 ≤ completeSteinerSeedDecodeWorkPolynomial n m height+16 := by
  subst n m
  let n := Fintype.card V
  let m := G.card
  let setup := prepareSteinerSeedDecoderSizesWithWork G height width n m rfl rfl
  let same := steinerBitBudgetFromDecoderSizes_eq width_eq setup.1
  let reference := decodeCompleteSteinerSeedFromPreparedWidthWithWork G height width n m rfl rfl width_eq
      coordinates vertices arcs bits ⟨0,Nat.zero_le _⟩
  have agreement := decodeCompleteSteinerSeedFromPreparedWidthWithWork_eq G height width n m rfl rfl width_eq
    coordinates vertices arcs bits ⟨0,Nat.zero_le _⟩
  have work := decodeCompleteSteinerSeedCursorWithWork_fixed_budget G height width width_eq coordinates vertices arcs
    bits ⟨0,Nat.zero_le _⟩
  have casted := castDecoderBudget width_eq setup.1 coordinates vertices arcs same bits
  have result := congrArg Prod.fst casted
  have position := congrArg (fun outcome => outcome.2.1) casted
  have tally := congrArg (fun outcome => outcome.2.2) casted
  dsimp only at result position tally
  refine ⟨?_,?_⟩
  · apply Prod.ext
    · exact result.trans (congrArg Prod.fst agreement)
    · exact position.trans (congrArg (fun state => state.2.position) agreement)
  · dsimp only [decodeCompleteSteinerSeedWithFixedBudgetWork,decodeFixedSteinerBudgetUsing]
    rw [tally]
    change reference.2+16 ≤ _
    exact Nat.add_le_add_right work 16

private theorem cursorSeedAtBudget {G : Arcs V} {height width a b : ℕ}
    (width_eq : width = (forestScale G height).log2+1)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (same : a = b) (bits : Fin b → Bool) :
    (decodeCompleteSteinerSeedCursorAtWidth G height width width_eq coordinates vertices arcs
      (fun i : Fin a => bits (Fin.cast same i)) ⟨0,Nat.zero_le a⟩).map Prod.fst =
    (decodeCompleteSteinerSeedCursorAtWidth G height width width_eq coordinates vertices arcs
      bits ⟨0,Nat.zero_le b⟩).map Prod.fst := by
  subst a
  rfl

private def steinerDecoderScaleCap (n height : ℕ) : ℕ := 1+n*((n*2)*((height+1)*n^height))^2

private theorem forestScale_le_decoderCap (G : Arcs V) (height : ℕ) :
    forestScale G height ≤ steinerDecoderScaleCap (Fintype.card V) height := by
  apply (forestNetworkScale_le G height).trans
  have vertices : Fintype.card (HeightForestVertex V height) ≤
      (Fintype.card V*2)*((height+1)*Fintype.card V^height) := by
    cases isEmpty_or_nonempty V with
    | inl empty => simp [HeightForestVertex]
    | inr nonempty => exact heightForestVertex_card_le V height
  unfold steinerDecoderScaleCap
  exact max_le (Nat.le_add_right _ _)
    ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left vertices 2)).trans (Nat.le_add_left _ _))

/-- The three index orders consumed by the fixed-budget seed decoder. -/
structure SteinerReplaySeedIndexes (G : Arcs V) (height : ℕ) where
  vertices : V ≃ Fin (Fintype.card V)
  arcs : G ≃ Fin G.card
  coordinates : {w : ℕ // w = (forestScale G height).log2+1} →
    EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height))

/-- Canonical seed index orders for a general ordered vertex type. -/
def steinerReplaySeedIndexes (G : Arcs V) (height : ℕ) : SteinerReplaySeedIndexes G height :=
  let vertices := steinerUniverseArrayIndex V
  ⟨vertices,steinerArcArrayIndex G,fun width => steinerEarlyCoordinateIndexLex G height width.val width.property vertices⟩

private def decodeSteinerFixedBudgetAtIndex (G : Arcs V) (height n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (indexes : SteinerReplaySeedIndexes G height)
    (width : {w : ℕ // w = (forestScale G height).log2+1})
    (bits : Fin (steinerBitBudget G height) → Bool) :=
  decodeCompleteSteinerSeedWithFixedBudgetWork G height width.val n m hn hm width.property
    (indexes.coordinates width) indexes.vertices indexes.arcs bits

/-- The fixed-budget decoder work, including the forest's word-width calculation. -/
def completeSteinerCachedDecoderWorkPolynomial (n m height : ℕ) : ℕ :=
  completeSteinerSeedDecodeWorkPolynomial n m height+7*steinerDecoderScaleCap n height+27

private def preparedSteinerWidthWithWork (G : Arcs V) (height : ℕ)
    (scale : {s : ℕ // s = forestScale G height}) : {w : ℕ // w = (forestScale G height).log2+1} × ℕ :=
  let scaleWidth := bitLengthWithWork scale.val
  let width := max 1 scaleWidth.1
  have widthEq : width = (forestScale G height).log2+1 := by
    dsimp only [width, scaleWidth]
    rw [(bitLengthWithWork_spec _).1,max_size_eq_log2_add_one,scale.property]
  (⟨width,widthEq⟩,scaleWidth.2)

/-- Decode one bit word using the width from the supplied forest preparation. -/
def decodeSteinerSeedFromPreparedScale (G : Arcs V) (height n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (scale : {s : ℕ // s = forestScale G height})
    (indexes : SteinerReplaySeedIndexes G height) (bits : Fin (steinerBitBudget G height) → Bool) :=
  let width := preparedSteinerWidthWithWork G height scale
  let decoded := decodeSteinerFixedBudgetAtIndex G height n m hn hm indexes width.1 bits
  (decoded.1.1.map Prod.fst,decoded.2+width.2+8)

/-- Retain a direct indexed view of the thin thresholds from the same bit read. -/
def decodeSteinerSeedWithIndexedThinFromPreparedScale (G : Arcs V) (height n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (scale : {s : ℕ // s = forestScale G height})
    (indexes : SteinerReplaySeedIndexes G height) (bits : Fin (steinerBitBudget G height) → Bool) :=
  let width := preparedSteinerWidthWithWork G height scale
  let decoded := decodeFixedSteinerBudgetWithIndexedThin G height width.1.val n m hn hm width.1.property
    (indexes.coordinates width.1) indexes.vertices indexes.arcs bits
  (decoded.1.1.map (fun entry => (entry.1.1,entry.2)),decoded.2+width.2+8)

theorem decodeSteinerSeedWithIndexedThinFromPreparedScale_spec (G : Arcs V) (height n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (scale : {s : ℕ // s = forestScale G height})
    (indexes : SteinerReplaySeedIndexes G height) (bits : Fin (steinerBitBudget G height) → Bool) :
    let out := decodeSteinerSeedWithIndexedThinFromPreparedScale G height n m hn hm scale indexes bits
    let old := decodeSteinerSeedFromPreparedScale G height n m hn hm scale indexes bits
    (out.1.map Prod.fst,out.2) = old ∧
      ∀ entry, out.1 = some entry → ∀ e, entry.2 (indexes.arcs e) = entry.1.2.2 e := by
  let width := preparedSteinerWidthWithWork G height scale
  let codes := decodeFixedSteinerBudgetWithIndexedThin G height width.1.val n m hn hm width.1.property
    (indexes.coordinates width.1) indexes.vertices indexes.arcs bits
  obtain ⟨matchOld,view⟩ := decodeFixedSteinerBudgetWithIndexedThin_spec G height width.1.val n m hn hm width.1.property
    (indexes.coordinates width.1) indexes.vertices indexes.arcs bits
  refine ⟨?_,?_⟩
  · have compare := congrArg (fun v => (v.1.1.map Prod.fst,v.2+width.2+8)) matchOld
    simpa only [decodeSteinerSeedWithIndexedThinFromPreparedScale, decodeSteinerSeedFromPreparedScale,
      decodeSteinerFixedBudgetAtIndex, width, Option.map_map, Function.comp_def] using compare
  · intro entry same e
    change (codes.1.1.map fun packet => (packet.1.1,packet.2)) = some entry at same
    obtain ⟨packet,present,packetEq⟩ := Option.map_eq_some_iff.mp same
    subst entry
    exact view packet present e

/-- Reuse one prepared forest and one set of seed indexes at every prefix. -/
def completeSteinerReplayWithDecoderWorkUsingIndexes (G : Arcs V) (height n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (prepared : SteinerSeedPreparation G height)
    (indexes : SteinerReplaySeedIndexes G height)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (V × V)) :=
  let decoded := decodeSteinerSeedFromPreparedScale G height n m hn hm prepared.1 indexes bits
  let rounds := match decoded.1 with
    | none => steinerFallbackPrefixScan G D
    | some seed => D.inits.map (completeSteinerDrawRunWithSearchWorkFromEarly G
        (prepared.2.1 seed.1) seed.2.1 seed.2.2)
  ((rounds,prepared.2.2),decoded.2)

/-- Decode once and use the supplied initial forest plan at every prefix. -/
def completeSteinerReplayWithDecoderWorkFromPreparation (G : Arcs V) (height n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (prepared : SteinerSeedPreparation G height)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (V × V)) :=
  completeSteinerReplayWithDecoderWorkUsingIndexes G height n m hn hm prepared
    (steinerReplaySeedIndexes G height) bits D

/-- Use the measured fixed-budget sampler once in the existing cached prefix
replay. Report its work separately from the established search and table
counts. Bit access is a unit operation. Construction and application of
the key-index maps and native execution costs are separate. -/
def completeSteinerReplayWithCachedDecoderWork (G : Arcs V) (height n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (V × V)) :=
  completeSteinerReplayWithDecoderWorkFromPreparation G height n m hn hm
    (prepareEarlyDistanceTableForSeed G height) bits D

theorem completeSteinerReplayWithDecoderWorkFromPreparation_eq (G : Arcs V) (height n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card) (prepared : SteinerSeedPreparation G height)
    (distanceWork templateWork : ℕ)
    (same : let old := prepareEarlyDistanceTableForSeed G height
      prepared = (old.1,old.2.1,distanceWork,templateWork,old.2.2.2.2))
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (V × V)) :
    let out := completeSteinerReplayWithDecoderWorkFromPreparation G height n m hn hm prepared bits D
    let old := completeSteinerReplayWithCachedDecoderWork G height n m hn hm bits D
    out = ((old.1.1,distanceWork,templateWork,old.1.2.2.2),old.2) := by
  dsimp only at same
  subst prepared
  rfl

theorem completeSteinerReplayWithCachedDecoderWork_spec (G : Arcs V) (height n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (V × V)) :
    let out := completeSteinerReplayWithCachedDecoderWork G height n m hn hm bits D
    out.1 = completeSteinerReplayWithCachedBitBudget G height bits D ∧
      out.2 ≤ completeSteinerCachedDecoderWorkPolynomial n m height := by
  subst n m
  let prepared := prepareEarlyDistanceTableForSeed G height
  let scaleWidth := bitLengthWithWork prepared.1.val
  have exactWidth : max 1 scaleWidth.1 = (prepared.1.val).log2+1 := by
    dsimp only [scaleWidth]
    rw [(bitLengthWithWork_spec _).1,max_size_eq_log2_add_one]
  let width := prepared.1.val.log2+1
  let widthEq := congrArg (fun scale : ℕ => scale.log2+1) prepared.1.property
  have sameWidth : (⟨max 1 scaleWidth.1,exactWidth.trans widthEq⟩ : {w : ℕ // w = (forestScale G height).log2+1}) =
      ⟨width,widthEq⟩ := Subtype.ext exactWidth
  unfold completeSteinerReplayWithCachedDecoderWork completeSteinerReplayWithDecoderWorkFromPreparation
    completeSteinerReplayWithDecoderWorkUsingIndexes decodeSteinerSeedFromPreparedScale preparedSteinerWidthWithWork
  dsimp only
  rw [sameWidth]
  dsimp only [decodeSteinerFixedBudgetAtIndex,steinerReplaySeedIndexes]
  let vertices := steinerUniverseArrayIndex V
  let coordinates := steinerEarlyCoordinateIndexLex G height width widthEq vertices
  let arcs := steinerArcArrayIndex G
  let decoded := decodeCompleteSteinerSeedWithFixedBudgetWork G height width (Fintype.card V) G.card rfl rfl
    widthEq coordinates vertices arcs bits
  let start : BitCursor (steinerBitBudget G height) := ⟨0,Nat.zero_le _⟩
  have sample := congrArg Prod.fst (decodeCompleteSteinerSeedWithFixedBudgetWork_spec G height width
    (Fintype.card V) G.card rfl rfl widthEq coordinates vertices arcs bits).1
  have ordinary := congrArg (Option.map Prod.fst) (decodeCompleteSteinerSeedCursorWithEndAtWidth_spec G height
    width widthEq coordinates vertices arcs bits start).1
  have sameSeed : decoded.1.1.map Prod.fst =
      (decodeCompleteSteinerSeedCursorAtWidth G height width widthEq coordinates vertices arcs bits start).map Prod.fst := by
    change decoded.1.1 = (decodeCompleteSteinerSeedCursorWithEndAtWidth G height width widthEq coordinates vertices arcs bits start).1 at sample
    rw [sample, ← ordinary, Option.map_map]
    rfl
  let limit := completeSteinerSeedBitBoundAtWidth G height width * G.card
  let limitEq : limit = steinerBitBudget G height :=
    congrArg (· * G.card) (completeSteinerSeedBitBoundAtWidth_eq G height width widthEq)
  have cast := cursorSeedAtBudget widthEq coordinates vertices arcs limitEq bits
  refine ⟨?_,?_⟩
  · unfold completeSteinerReplayWithCachedBitBudget
    dsimp only
    rw [sameSeed, cast]
    rfl
  · have widthWork : scaleWidth.2 ≤ 7*steinerDecoderScaleCap (Fintype.card V) height+3 := by
      apply (bitLengthWork_le prepared.1.val).trans
      rw [prepared.1.property]
      gcongr
      exact forestScale_le_decoderCap G height
    have decodeWork := (decodeCompleteSteinerSeedWithFixedBudgetWork_spec G height width (Fintype.card V) G.card
      rfl rfl widthEq coordinates vertices arcs bits).2
    change decoded.2 ≤ _ at decodeWork
    change decoded.2+scaleWidth.2+8 ≤
      completeSteinerSeedDecodeWorkPolynomial (Fintype.card V) G.card height+7*steinerDecoderScaleCap (Fintype.card V) height+27
    omega

/-- The metered replay returns the usual graph at every demand prefix.
The bound composes the previously measured work with the decoder. -/
theorem completeSteinerReplayWithCachedDecoderWork_prefixes (G : Arcs V) (height n m : ℕ)
    (hn : n = Fintype.card V) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeSteinerReplayWithCachedDecoderWork G height n m hn hm bits D
    out.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (out.1.1.map Prod.snd).sum+out.1.2.1+out.1.2.2.1+out.1.2.2.2+out.2 ≤
        completeSteinerWeightWorkPolynomial n m height D.length+completeSteinerCachedDecoderWorkPolynomial n m height := by
  subst n m
  obtain ⟨output,decoder⟩ := completeSteinerReplayWithCachedDecoderWork_spec G height _ _ rfl rfl bits D
  obtain ⟨prefixes,search⟩ := completeSteinerReplayWithCachedBitBudget_spec G height bits D feasible
  dsimp only
  rw [output]
  exact ⟨prefixes,Nat.add_le_add search decoder⟩

end OnlineReachabilityPreservers
