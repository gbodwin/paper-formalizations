import OnlineReachabilityPreservers.SteinerBinaryWordOnline

/-! Theorem 21 for accepted binary words with the exact sampled trace. -/

namespace OnlineReachabilityPreservers

/-- The total input tally is bounded on both success and rejection. -/
def binaryWordOnlineInputWorkBudget (n width : ℕ) (arcWords demands : List (List Bool × List Bool)) : ℕ :=
  binaryEndpointWidthCheckBudget width arcWords + binaryFinArcDecodingWorkBudget arcWords.length width +
    steinerBinaryArcRowsWorkBudget n arcWords.length + binaryWordSessionTraceInputWorkBudget width demands + 13

private theorem decodedBinaryRowsLength {n width : ℕ} {words : List (List Bool × List Bool)}
    {rows : List (Fin n × Fin n)} (accepted : (decodeCheckedBinaryFinArcRowsWithWork width words).1 = some rows) :
    rows.length = words.length := by
  have values := (decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff width words rows).mp accepted
  simpa only [List.length_map] using congrArg List.length values.2

theorem finSteinerBinaryServeFromWords_input_work_le {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height width : ℕ) (stream : ℕ → Bool) (start : ℕ) :
    ((finSteinerBinaryServeFromWords (n := n) arcWords demands height width (steinerBitStreamSource stream)).run start).1.2 ≤
      binaryWordOnlineInputWorkBudget n width arcWords demands := by
  have decodeCost := decodeCheckedBinaryFinArcRowsWithWork_work_le (n := n) width arcWords
  unfold binaryWordOnlineInputWorkBudget
  cases accepted : (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).1 with
  | none =>
    rw [finSteinerBinaryServeFromWords_rejects_graph arcWords demands height width stream start accepted]
    change (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).2+2+2 ≤ _
    omega
  | some raw =>
    let prepared := prepareSteinerBinaryArcRowsWithWork raw
    let same := (prepareSteinerBinaryArcRowsWithWork_spec raw).1
    let initial := (finSteinerBinaryArrivalStartFromBitSource prepared.1 raw same height
      (steinerBitStreamSource stream)).run start
    let session : FinSteinerBinaryWordSession n height := ⟨width,raw,prepared.1,same,initial.1.1,initial.1.2⟩
    have count := decodedBinaryRowsLength accepted
    have prepCost : prepared.2 ≤ steinerBinaryArcRowsWorkBudget n arcWords.length := by
      rw [← count]
      exact (prepareSteinerBinaryArcRowsWithWork_spec raw).2.2
    have traceCost := finSteinerBinaryWordSessionServe_work_le session demands
    change (finSteinerBinaryWordSessionServe session demands).2 ≤ binaryWordSessionTraceInputWorkBudget width demands at traceCost
    unfold finSteinerBinaryServeFromWords
    rw [StateT.run_bind,finSteinerBinaryStartFromWords_accepts arcWords height width stream start raw accepted]
    change (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).2+prepared.2+5+
      (finSteinerBinaryWordSessionServe session demands).2+5 ≤ _
    omega

/-- Count vertices, supplied rows, declared width and actual endpoint bits. -/
def binaryWordOnlineInputSize (n width : ℕ) (arcWords demands : List (List Bool × List Bool)) : ℕ :=
  n + width + arcWords.length + demands.length + binaryEndpointBits arcWords + binaryEndpointBits demands + 1

/-- The entire input overhead is cubic in these supplied dimensions. -/
theorem binaryWordOnlineInputWorkBudget_cubic (n width : ℕ) (arcWords demands : List (List Bool × List Bool)) :
    binaryWordOnlineInputWorkBudget n width arcWords demands ≤
      256*(binaryWordOnlineInputSize n width arcWords demands)^3 := by
  let s := binaryWordOnlineInputSize n width arcWords demands
  have one : 1 ≤ s := by dsimp [s,binaryWordOnlineInputSize]; omega
  have widthBound : width+1 ≤ s := by dsimp [s,binaryWordOnlineInputSize]; omega
  have arcRows : arcWords.length ≤ s := by dsimp [s,binaryWordOnlineInputSize]; omega
  have demandRows : demands.length ≤ s := by dsimp [s,binaryWordOnlineInputSize]; omega
  have arcBits : binaryEndpointBits arcWords ≤ s := by dsimp [s,binaryWordOnlineInputSize]; omega
  have demandBits : binaryEndpointBits demands ≤ s := by dsimp [s,binaryWordOnlineInputSize]; omega
  have squareAsc : s ≤ s^2 := by nlinarith [Nat.mul_le_mul_left s one]
  have cubeAsc : s^2 ≤ s^3 := by nlinarith [Nat.mul_le_mul_left (s^2) one]
  have checkRow : 4*(width+1)+7 ≤ 11*s := by omega
  have decodeRow : 2*(2+width*(2*(width+1)+5))+4*(width+1)+7 ≤ 29*s^2 := by
    have inner : 2*(width+1)+5 ≤ 7*s := by omega
    nlinarith [Nat.mul_le_mul (show width ≤ s by omega) inner,checkRow]
  have graphCheck : binaryEndpointWidthCheckBudget width arcWords ≤ 14*s^3 := by
    unfold binaryEndpointWidthCheckBudget
    nlinarith [Nat.mul_le_mul arcRows checkRow]
  have graphDecode : binaryFinArcDecodingWorkBudget arcWords.length width ≤ 31*s^3 := by
    unfold binaryFinArcDecodingWorkBudget
    nlinarith [Nat.mul_le_mul arcRows decodeRow]
  have singleDecode : binaryFinArcDecodingWorkBudget 1 width ≤ 31*s^2 := by
    unfold binaryFinArcDecodingWorkBudget
    omega
  have oneArrival : 2+4*(width+1)+7+binaryFinArcDecodingWorkBudget 1 width+14 ≤ 58*s^2 := by
    omega
  have demandCheck : binaryWordSessionTraceInputWorkBudget width demands ≤ 61*s^3 := by
    unfold binaryWordSessionTraceInputWorkBudget
    nlinarith [Nat.mul_le_mul demandRows oneArrival]
  have graphBase : n+arcWords.length+1 ≤ s := by dsimp [s,binaryWordOnlineInputSize]; omega
  have graphPrep := (steinerBinaryArcRowsWorkBudget_cubic n arcWords.length).trans
    (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left graphBase 3))
  change binaryWordOnlineInputWorkBudget n width arcWords demands ≤ 256*s^3
  unfold binaryWordOnlineInputWorkBudget
  omega

/-- The empty graph is used only when this observation has no final state. -/
def finSteinerBinaryWordResultGraph {n : ℕ} (out : Option (FinSteinerBinaryArrivalState n)) : Arcs (Fin n) :=
  (out.map FinSteinerBinaryArrivalState.graph).getD ∅

private theorem finSteinerBinaryServeFromWords_graph_of_decoded {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height width : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (raw D : List (Fin n × Fin n))
    (goodGraph : (decodeCheckedBinaryFinArcRowsWithWork width arcWords).1 = some raw)
    (goodDemands : (decodeCheckedBinaryFinArcRowsWithWork width demands).1 = some D) :
    finSteinerBinaryWordResultGraph ((finSteinerBinaryServeFromWords (n := n) arcWords demands height width
      (steinerBitStreamSource stream)).run start).1.1 =
      ((finSteinerBinaryServeFromBinaryArcRowsWithWork raw height (steinerBitStreamSource stream) D).run start).1.graph := by
  obtain ⟨state,success,graph,_,_,_⟩ :=
    finSteinerBinaryServeFromWords_refines_decoded arcWords demands height width stream start raw D goodGraph goodDemands
  rw [success]
  exact graph

private theorem decodedDemandPrefix {n : ℕ} {width : ℕ} {words extension : List (List Bool × List Bool)}
    {D E : List (Fin n × Fin n)} (prefixOf : words <+: extension)
    (goodD : (decodeCheckedBinaryFinArcRowsWithWork width words).1 = some D)
    (goodE : (decodeCheckedBinaryFinArcRowsWithWork width extension).1 = some E) : D <+: E := by
  let values (row : Fin n × Fin n) := (row.1.val,row.2.val)
  have injective : Function.Injective values := fun _ _ equal =>
    Prod.ext (Fin.ext (congrArg Prod.fst equal)) (Fin.ext (congrArg Prod.snd equal))
  have a := (decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff width words D).mp goodD
  have b := (decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff width extension E).mp goodE
  apply (List.prefix_map_iff_of_injective injective).mp
  rw [show D.map values = _ from a.2,show E.map values = _ from b.2]
  exact prefixOf.map _

open MeasureTheory
open scoped ENNReal

/-- Theorem 21 for fixed feasible traces supplied as checked binary words.
The input overhead is separate from the sampled typed computation.
The graph is monotone on accepted word prefixes, and the expectation
uses the same fair stream and comparator as the typed solver. -/
theorem theorem21_online_steiner_sampled_binary_words {ε : ℝ} (epsilon : 0 < ε) :
    ∃ (height : ℕ) (K : ℝ) (C k : ℕ), 0 < height ∧ 0 < K ∧
      (∀ {n : ℕ} (width : ℕ) (arcWords demands : List (List Bool × List Bool))
        (raw D : List (Fin n × Fin n)) (stream : ℕ → Bool),
        (decodeCheckedBinaryFinArcRowsWithWork width arcWords).1 = some raw →
        (decodeCheckedBinaryFinArcRowsWithWork width demands).1 = some D →
        (∀ d ∈ D, Reach raw.toFinset d.1 d.2) →
        let out := (finSteinerBinaryServeFromWords (n := n) arcWords demands height width
          (steinerBitStreamSource stream)).run 0
        ∃ state, out.1.1 = some state ∧ out.2 = steinerBitBudget raw.toFinset height ∧
          state.history.reverse = D ∧ state.graph ⊆ raw.toFinset ∧ Preserves raw.toFinset state.graph D ∧
          state.work + out.1.2 ≤ C*(binaryWordOnlineInputSize n width arcWords demands)^k) ∧
      (∀ {n : ℕ} (width : ℕ) (arcWords demands extension : List (List Bool × List Bool))
        (raw D E : List (Fin n × Fin n)) (stream : ℕ → Bool),
        (decodeCheckedBinaryFinArcRowsWithWork width arcWords).1 = some raw →
        (decodeCheckedBinaryFinArcRowsWithWork width demands).1 = some D →
        (decodeCheckedBinaryFinArcRowsWithWork width extension).1 = some E →
        demands <+: extension → (∀ d ∈ E, Reach raw.toFinset d.1 d.2) →
        let graph (words : List (List Bool × List Bool)) :=
          finSteinerBinaryWordResultGraph ((finSteinerBinaryServeFromWords (n := n) arcWords words height width
            (steinerBitStreamSource stream)).run 0).1.1
        graph demands ⊆ graph extension) ∧
      (∀ {n : ℕ} {Z : Arcs (Fin n)} (width : ℕ) (arcWords demands : List (List Bool × List Bool))
        (raw D : List (Fin n × Fin n)),
        (decodeCheckedBinaryFinArcRowsWithWork width arcWords).1 = some raw →
        (decodeCheckedBinaryFinArcRowsWithWork width demands).1 = some D →
        Z ⊆ raw.toFinset → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∫⁻ stream, ((finSteinerBinaryWordResultGraph ((finSteinerBinaryServeFromWords (n := n)
          arcWords demands height width (steinerBitStreamSource stream)).run 0).1.1).card : ℝ≥0∞) ∂fairBitMeasure) ≤
            ENNReal.ofReal (K*(n:ℝ)^(3/5+ε)*Z.card)) := by
  obtain ⟨height,K,C,k,heightPos,constantPos,correct,monotone,expected⟩ :=
    theorem21_online_steiner_sampled_binary_arc_rows epsilon
  refine ⟨height,K,C+256,max k 3,heightPos,constantPos,?_,?_,?_⟩
  · intro n width arcWords demands raw D stream goodGraph goodDemands feasible
    obtain ⟨state,success,graph,history,work,position⟩ :=
      finSteinerBinaryServeFromWords_refines_decoded arcWords demands height width stream 0 raw D goodGraph goodDemands
    obtain ⟨bits,trace,sub,preserves,servingCost⟩ := correct raw stream D feasible
    have inputCost := finSteinerBinaryServeFromWords_input_work_le (n := n) arcWords demands height width stream 0
    refine ⟨state,success,position.trans bits,?_,?_,?_,?_⟩
    · rw [history]
      exact trace
    · rw [graph]
      exact sub
    · rw [graph]
      exact preserves
    · have solverCost : state.work ≤ C*(n+raw.length+D.length+1)^k := by
        calc
          _ ≤ state.work+(prepareSteinerBinaryArcRowsWithWork raw).2+4 := by omega
          _ = _ := work
          _ ≤ _ := servingCost
      let size := binaryWordOnlineInputSize n width arcWords demands
      have positive : 0 < size := by dsimp [size,binaryWordOnlineInputSize]; omega
      have leSize : n+raw.length+D.length+1 ≤ size := by
        rw [decodedBinaryRowsLength goodGraph,decodedBinaryRowsLength goodDemands]
        dsimp [size,binaryWordOnlineInputSize]
        omega
      have serve : state.work ≤ C*size^(max k 3) :=
        (solverCost.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left leSize k))).trans
          (Nat.mul_le_mul_left C (Nat.pow_le_pow_right positive (le_max_left k 3)))
      have input := (inputCost.trans (binaryWordOnlineInputWorkBudget_cubic n width arcWords demands)).trans
        (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_right positive (le_max_right k 3)))
      change _ ≤ (C+256)*size^(max k 3)
      rw [Nat.add_mul]
      exact Nat.add_le_add serve input
  · intro n width arcWords demands extension raw D E stream goodGraph goodD goodE prefixOf feasible
    dsimp only
    rw [finSteinerBinaryServeFromWords_graph_of_decoded arcWords demands height width stream 0 raw D goodGraph goodD,
      finSteinerBinaryServeFromWords_graph_of_decoded arcWords extension height width stream 0 raw E goodGraph goodE]
    exact monotone raw stream (decodedDemandPrefix prefixOf goodD goodE) feasible
  · intro n Z width arcWords demands raw D goodGraph goodDemands sub feasible
    simp_rw [fun stream => finSteinerBinaryServeFromWords_graph_of_decoded arcWords demands height width stream 0
      raw D goodGraph goodDemands]
    exact expected raw D sub feasible

end OnlineReachabilityPreservers
