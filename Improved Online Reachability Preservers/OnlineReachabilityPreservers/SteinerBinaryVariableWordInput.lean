import OnlineReachabilityPreservers.SteinerBinaryWordGuarantee

/-! Size the decoder using the fixed graph and the current encoded demand. -/

namespace OnlineReachabilityPreservers

private theorem binaryEndpointBits_cons (word : List Bool × List Bool)
    (rest : List (List Bool × List Bool)) :
    binaryEndpointBits (word::rest) = word.1.length+word.2.length+binaryEndpointBits rest := by
  simp only [binaryEndpointBits,List.map_cons,List.sum_cons]

private theorem binaryEndpointBits_le_of_member {word : List Bool × List Bool}
    {rows : List (List Bool × List Bool)} (present : word ∈ rows) :
    word.1.length+word.2.length ≤ binaryEndpointBits rows := by
  induction rows with
  | nil => simp at present
  | cons head tail ih =>
    rw [List.mem_cons] at present
    rw [binaryEndpointBits_cons]
    rcases present with rfl | on
    · omega
    · exact (ih on).trans (Nat.le_add_left _ _)

/-- Allowances derived from the supplied graph words admit exactly the
same decoded arcs as the value decoder. This includes leading zeros and
empty words that encode zero. -/
theorem decodeCheckedBinaryFinArcRowsWithWork_of_actual_bits {n : ℕ}
    (words : List (List Bool × List Bool)) (rows : List (Fin n × Fin n)) :
    (decodeCheckedBinaryFinArcRowsWithWork (n+binaryEndpointBits words) words).1 = some rows ↔
      (decodeBinaryFinArcRowsWithWork 0 words).1 = some rows := by
  rw [decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff,decodeBinaryFinArcRowsWithWork_eq_some_iff]
  have fits (word) (on : word ∈ words) : word.1.length ≤ n+binaryEndpointBits words ∧
      word.2.length ≤ n+binaryEndpointBits words := by
    have := binaryEndpointBits_le_of_member on
    omega
  exact and_iff_right (fun word on => fits word on)

/-- Derive the width before drawing the graph's single seed. The tally
also records the extra traversal to compute the supplied lengths. -/
def finSteinerBinaryStartFromVariableWords {n : ℕ} {m : Type → Type} [Monad m]
    (arcWords : List (List Bool × List Bool)) (height : ℕ) (nextBit : m Bool) :
    m (Option (FinSteinerBinaryWordSession n height) × ℕ) := do
  let bits := binaryEndpointBits arcWords
  let (initial,charge) ← finSteinerBinaryStartFromWords (n := n) arcWords height (n+bits) nextBit
  pure (initial,charge+bits+8*arcWords.length+7)

/-- Decode just this demand, giving it an allowance determined by its
two supplied words. Reuse the graph and seed and keep the stored graph width. -/
def finSteinerBinaryVariableWordStep {n height : ℕ} (session : FinSteinerBinaryWordSession n height)
    (word : List Bool × List Bool) : Option (FinSteinerBinaryWordSession n height) × ℕ :=
  let bits := word.1.length + word.2.length
  let step := finSteinerBinaryArrivalStepFromWords session.graph session.raw session.graphExact
    height (n+bits) session.seed session.state word
  (step.1.map (fun state => {session with state}),step.2+bits+8)

/-- Each row has precisely the typed step at its two decoded values,
with no numerical width required from the caller. -/
theorem finSteinerBinaryVariableWordStep_result {n height : ℕ} (session : FinSteinerBinaryWordSession n height)
    (word : List Bool × List Bool) :
    (finSteinerBinaryVariableWordStep session word).1 =
      if valid : binaryWordValue word.1 < n ∧ binaryWordValue word.2 < n then
        some {session with state := (finSteinerBinaryArrivalStepFromSeed session.graph session.raw
          session.graphExact height session.seed session.state
          (⟨binaryWordValue word.1,valid.1⟩,⟨binaryWordValue word.2,valid.2⟩))}
      else none := by
  let width := n+(word.1.length+word.2.length)
  let step := finSteinerBinaryArrivalStepFromWords session.graph session.raw session.graphExact
    height width session.seed session.state word
  change step.1.map _ = _
  by_cases valid : binaryWordValue word.1 < n ∧ binaryWordValue word.2 < n
  · rw [dite_eq_left valid]
    let demand : Fin n × Fin n := (⟨binaryWordValue word.1,valid.1⟩,⟨binaryWordValue word.2,valid.2⟩)
    let updated := finSteinerBinaryArrivalStepFromSeed session.graph session.raw session.graphExact
      height session.seed session.state demand
    have accepted : step.1 = some updated :=
      (finSteinerBinaryArrivalStepFromWords_eq_some_iff session.graph session.raw session.graphExact
        height width session.seed session.state updated word).mpr
        ⟨demand,by dsimp [width]; omega,by dsimp [width]; omega,rfl,rfl,rfl⟩
    rw [accepted]
    rfl
  · rw [dite_eq_right valid]
    cases out : step.1 with
    | none => rfl
    | some updated =>
      have range := (finSteinerBinaryArrivalStepFromWords_some_iff_valid session.graph session.raw
        session.graphExact height width session.seed session.state word).mp ⟨updated,out⟩
      exact (valid range.2.2).elim

/-- Run the successive input steps, stopping at the first rejected row. -/
def finSteinerBinaryVariableWordTrace {n height : ℕ} :
    FinSteinerBinaryWordSession n height → List (List Bool × List Bool) →
      Option (FinSteinerBinaryWordSession n height) × ℕ
  | session, [] => (some session,2)
  | session, word::rest =>
    let step := finSteinerBinaryVariableWordStep session word
    match step.1 with
    | none => (none,step.2+2)
    | some next =>
      let suffix := finSteinerBinaryVariableWordTrace next rest
      (suffix.1,step.2+suffix.2+4)

/-- Both acceptance and rejection refine the value decoder. On acceptance
only the typed prefix state changes. -/
theorem finSteinerBinaryVariableWordTrace_result {n height : ℕ} (session : FinSteinerBinaryWordSession n height)
    (words : List (List Bool × List Bool)) :
    (finSteinerBinaryVariableWordTrace session words).1 =
      ((decodeBinaryFinArcRowsWithWork 0 words).1.map fun D => {session with
        state := D.foldl (finSteinerBinaryArrivalStepFromSeed session.graph session.raw session.graphExact
          height session.seed) session.state}) := by
  induction words generalizing session with
  | nil => rfl
  | cons word tail ih =>
    simp only [finSteinerBinaryVariableWordTrace,finSteinerBinaryVariableWordStep_result,
      decodeBinaryFinArcRowsWithWork,decodeBinaryNatWithWork_spec]
    by_cases valid : binaryWordValue word.1 < n ∧ binaryWordValue word.2 < n
    · simp only [dite_eq_left valid]
      rw [ih]
      simp only [Option.map_map]
      rfl
    · simp [valid]

private theorem finSteinerBinaryVariableWordStep_work_le {n height : ℕ}
    (session : FinSteinerBinaryWordSession n height) (word : List Bool × List Bool) :
    (finSteinerBinaryVariableWordStep session word).2 ≤
      60*(n+(word.1.length+word.2.length)+1)^2 := by
  let bits := word.1.length+word.2.length
  let width := n+bits
  have bitBound : bits ≤ width := Nat.le_add_left _ _
  have measured := finSteinerBinaryArrivalStepFromWords_work_le session.graph session.raw session.graphExact
    height width session.seed session.state word
  simp only [binaryEndpointWidthCheckBudget,binaryEndpointBits,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,List.length_singleton,Nat.one_mul,Nat.add_zero,
    binaryFinArcDecodingWorkBudget] at measured
  change (finSteinerBinaryArrivalStepFromWords session.graph session.raw session.graphExact
    height width session.seed session.state word).2 + bits+8 ≤ 60*(width+1)^2
  change _ ≤ 2+bits+4*(width+1)+7+(2+(2*(2+width*(2*(width+1)+5))+4*(width+1)+7))+7 at measured
  nlinarith only [measured,bitBound,Nat.zero_le width,Nat.zero_le (width*width)]

/-- The input work on a trace has one quadratic charge per row at a
width bounded by the supplied bits and vertex count. The same bound
covers stopping at an invalid row. -/
theorem finSteinerBinaryVariableWordTrace_work_le {n height : ℕ}
    (session : FinSteinerBinaryWordSession n height) (words : List (List Bool × List Bool)) (size : ℕ)
    (fits : n+binaryEndpointBits words+1 ≤ size) :
    (finSteinerBinaryVariableWordTrace session words).2 ≤ 2+words.length*(64*size^2) := by
  induction words generalizing session with
  | nil => simp [finSteinerBinaryVariableWordTrace]
  | cons word rest ih =>
    rw [binaryEndpointBits_cons] at fits
    have stepWidth : n+(word.1.length+word.2.length)+1 ≤ size := by omega
    have tailWidth : n+binaryEndpointBits rest+1 ≤ size := by omega
    have positive : 1 ≤ size^2 := by
      simpa only [one_pow] using Nat.pow_le_pow_left (show 1 ≤ size by omega) 2
    let step := finSteinerBinaryVariableWordStep session word
    have measured : step.2 ≤ 60*size^2 :=
      (finSteinerBinaryVariableWordStep_work_le session word).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left stepWidth 2))
    simp only [finSteinerBinaryVariableWordTrace,List.length_cons,Nat.add_mul,Nat.one_mul]
    change (match step.1 with
      | none => (none,step.2+2)
      | some next =>
        let suffix := finSteinerBinaryVariableWordTrace next rest
        (suffix.1,step.2+suffix.2+4) : Option (FinSteinerBinaryWordSession n height) × ℕ).2 ≤ _
    cases accepted : step.1 with
    | none =>
      change step.2+2 ≤ _
      omega
    | some next =>
      have suffix := ih next tailWidth
      change step.2+(finSteinerBinaryVariableWordTrace next rest).2+4 ≤ _
      omega

/-- The variable-width entry computes widths from the fixed graph and
from one word pair on each arrival. -/
def finSteinerBinaryServeFromVariableWords {n : ℕ} {m : Type → Type} [Monad m]
    (arcWords demands : List (List Bool × List Bool)) (height : ℕ) (nextBit : m Bool) :
    m (Option (FinSteinerBinaryArrivalState n) × ℕ) := do
  let (initial,charge) ← finSteinerBinaryStartFromVariableWords (n := n) arcWords height nextBit
  match initial with
  | none => pure (none,charge+2)
  | some session =>
    let served := finSteinerBinaryVariableWordTrace session demands
    pure (served.1.map FinSteinerBinaryWordSession.state,charge+served.2+5)

/-- A graph with out-of-range endpoint words consumes no random bits. -/
theorem finSteinerBinaryServeFromVariableWords_rejects_graph {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (bad : (decodeBinaryFinArcRowsWithWork (n := n) 0 arcWords).1 = none) :
    let result := (finSteinerBinaryServeFromVariableWords (n := n) arcWords demands height
      (steinerBitStreamSource stream)).run start
    result.1.1 = none ∧ result.2 = start := by
  let width := n+binaryEndpointBits arcWords
  have rejected : (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).1 = none := by
    cases out : (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).1 with
    | none => rfl
    | some raw =>
      have decoded := (decodeCheckedBinaryFinArcRowsWithWork_of_actual_bits arcWords raw).mp out
      rw [bad] at decoded
      exact nomatch decoded
  unfold finSteinerBinaryServeFromVariableWords finSteinerBinaryStartFromVariableWords
  rw [StateT.run_bind,StateT.run_bind,
    finSteinerBinaryStartFromWords_rejects arcWords height width stream start rejected]
  exact ⟨rfl,rfl⟩

/-- Accepted words give exactly the decoded typed solver's current
graph, history, solver work and stream position. -/
theorem finSteinerBinaryServeFromVariableWords_refines_decoded {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (raw D : List (Fin n × Fin n)) (goodGraph : (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw)
    (goodDemands : (decodeBinaryFinArcRowsWithWork 0 demands).1 = some D) :
    let result := (finSteinerBinaryServeFromVariableWords (n := n) arcWords demands height
      (steinerBitStreamSource stream)).run start
    let typed := (finSteinerBinaryServeFromBinaryArcRowsWithWork raw height (steinerBitStreamSource stream) D).run start
    ∃ state, result.1.1 = some state ∧ state.graph = typed.1.graph ∧ state.history = typed.1.history ∧
      state.work+(prepareSteinerBinaryArcRowsWithWork raw).2+4 = typed.1.work ∧ result.2 = typed.2 := by
  let width := n+binaryEndpointBits arcWords
  let prepared := prepareSteinerBinaryArcRowsWithWork raw
  let same := (prepareSteinerBinaryArcRowsWithWork_spec raw).1
  let initial := (finSteinerBinaryArrivalStartFromBitSource prepared.1 raw same height
    (steinerBitStreamSource stream)).run start
  let session : FinSteinerBinaryWordSession n height := ⟨width,raw,prepared.1,same,initial.1.1,initial.1.2⟩
  let final := D.foldl (finSteinerBinaryArrivalStepFromSeed prepared.1 raw same height initial.1.1) initial.1.2
  have guarded := (decodeCheckedBinaryFinArcRowsWithWork_of_actual_bits arcWords raw).mpr goodGraph
  have trace : (finSteinerBinaryVariableWordTrace session demands).1 = some {session with state := final} := by
    rw [finSteinerBinaryVariableWordTrace_result,goodDemands]
    rfl
  dsimp only
  have outcome : (finSteinerBinaryServeFromVariableWords (n := n) arcWords demands height
      (steinerBitStreamSource stream)).run start =
      ((some final,
        (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).2+prepared.2+5+
          binaryEndpointBits arcWords+8*arcWords.length+7+(finSteinerBinaryVariableWordTrace session demands).2+5),
        initial.2) := by
    unfold finSteinerBinaryServeFromVariableWords finSteinerBinaryStartFromVariableWords
    rw [StateT.run_bind,StateT.run_bind,
      finSteinerBinaryStartFromWords_accepts arcWords height width stream start raw guarded]
    change (((finSteinerBinaryVariableWordTrace session demands).1.map FinSteinerBinaryWordSession.state, _),_) = _
    rw [trace]
    rfl
  have typed : (finSteinerBinaryServeFromBinaryArcRowsWithWork raw height (steinerBitStreamSource stream) D).run start =
      ({final with work := final.work+prepared.2+4},initial.2) := rfl
  rw [outcome,typed]
  exact ⟨final,rfl,rfl,rfl,rfl,rfl⟩

/-- Input size uses the vertex count and only the supplied words and rows. -/
def binaryVariableWordInputSize (n : ℕ) (arcWords demands : List (List Bool × List Bool)) : ℕ :=
  n+binaryEndpointBits arcWords+binaryEndpointBits demands+arcWords.length+demands.length+1

private theorem finSteinerBinaryStartFromWords_input_le {n : ℕ} (arcWords : List (List Bool × List Bool))
    (height width : ℕ) (stream : ℕ → Bool) (start : ℕ) :
    ((finSteinerBinaryStartFromWords (n := n) arcWords height width (steinerBitStreamSource stream)).run start).1.2 ≤
      binaryWordOnlineInputWorkBudget n width arcWords [] := by
  have total := finSteinerBinaryServeFromWords_input_work_le (n := n) arcWords [] height width stream start
  unfold finSteinerBinaryServeFromWords at total
  rw [StateT.run_bind] at total
  generalize (finSteinerBinaryStartFromWords (n := n) arcWords height width
    (steinerBitStreamSource stream)).run start = initial at total ⊢
  rcases initial with ⟨⟨result,work⟩,position⟩
  change work ≤ _
  cases result with
  | none =>
    change work+2 ≤ _ at total
    omega
  | some _ =>
    change work+2+5 ≤ _ at total
    omega

/-- Recorded input work is cubic even on rejection, with no declared
width in the size parameter. -/
theorem finSteinerBinaryServeFromVariableWords_input_work_le {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height : ℕ) (stream : ℕ → Bool) (start : ℕ) :
    ((finSteinerBinaryServeFromVariableWords (n := n) arcWords demands height
      (steinerBitStreamSource stream)).run start).1.2 ≤ 2200*(binaryVariableWordInputSize n arcWords demands)^3 := by
  let width := n+binaryEndpointBits arcWords
  let S := binaryVariableWordInputSize n arcWords demands
  have sizeBounds : n+binaryEndpointBits demands+1 ≤ S ∧
      binaryEndpointBits arcWords+8*arcWords.length+7 ≤ 16*S ∧ demands.length ≤ S := by
    dsimp [S,binaryVariableWordInputSize]
    omega
  have oldSize : binaryWordOnlineInputSize n width arcWords [] ≤ 2*S := by
    simp only [S,width,binaryVariableWordInputSize,binaryWordOnlineInputSize,List.length_nil,binaryEndpointBits,
      List.map_nil,List.sum_nil]
    omega
  have oldCost := (binaryWordOnlineInputWorkBudget_cubic n width arcWords []).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left oldSize 3))
  have init := (finSteinerBinaryStartFromWords_input_le (n := n) arcWords height width stream start).trans oldCost
  have initCost : ((finSteinerBinaryStartFromWords (n := n) arcWords height width
      (steinerBitStreamSource stream)).run start).1.2 ≤ 2048*S^3 := by
    convert init using 1
    ring
  have one : 1 ≤ S := by dsimp [S,binaryVariableWordInputSize]; omega
  have oneCube : 1 ≤ S^3 := by simpa only [one_pow] using Nat.pow_le_pow_left one 3
  have sizeCube : S ≤ S^3 := by nlinarith [Nat.mul_le_mul_left S one,Nat.mul_le_mul_left (S^2) one]
  have traceBound (session : FinSteinerBinaryWordSession n height) :
      (finSteinerBinaryVariableWordTrace session demands).2 ≤ 2+64*S^3 := by
    refine (finSteinerBinaryVariableWordTrace_work_le session demands S sizeBounds.1).trans ?_
    have count := Nat.mul_le_mul_right (64*S^2) sizeBounds.2.2
    nlinarith only [count]
  unfold finSteinerBinaryServeFromVariableWords finSteinerBinaryStartFromVariableWords
  rw [StateT.run_bind,StateT.run_bind]
  generalize out : (finSteinerBinaryStartFromWords (n := n) arcWords height width
    (steinerBitStreamSource stream)).run start = decoded at initCost ⊢
  rcases decoded with ⟨⟨result,work⟩,position⟩
  change work ≤ 2048*S^3 at initCost
  cases result with
  | none =>
    change work+(binaryEndpointBits arcWords)+8*arcWords.length+7+2 ≤ 2200*S^3
    omega
  | some session =>
    change work+(binaryEndpointBits arcWords)+8*arcWords.length+7+
      (finSteinerBinaryVariableWordTrace session demands).2+5 ≤ 2200*S^3
    have trace := traceBound session
    omega

private theorem binaryValueDecodedLength {n : ℕ} {words : List (List Bool × List Bool)}
    {rows : List (Fin n × Fin n)} (accepted : (decodeBinaryFinArcRowsWithWork 0 words).1 = some rows) :
    rows.length = words.length := by
  have values := (decodeBinaryFinArcRowsWithWork_eq_some_iff 0 words rows).mp accepted
  simpa only [List.length_map] using congrArg List.length values

private theorem binaryValueDecodedPrefix {n : ℕ} {words extension : List (List Bool × List Bool)}
    {D E : List (Fin n × Fin n)} (prefixOf : words <+: extension)
    (goodD : (decodeBinaryFinArcRowsWithWork 0 words).1 = some D)
    (goodE : (decodeBinaryFinArcRowsWithWork 0 extension).1 = some E) : D <+: E := by
  let values (row : Fin n × Fin n) := (row.1.val,row.2.val)
  have injective : Function.Injective values := fun _ _ equal =>
    Prod.ext (Fin.ext (congrArg Prod.fst equal)) (Fin.ext (congrArg Prod.snd equal))
  have a := (decodeBinaryFinArcRowsWithWork_eq_some_iff 0 words D).mp goodD
  have b := (decodeBinaryFinArcRowsWithWork_eq_some_iff 0 extension E).mp goodE
  apply (List.prefix_map_iff_of_injective injective).mp
  rw [show D.map values = _ from a,show E.map values = _ from b]
  exact prefixOf.map _

private theorem finSteinerBinaryServeFromVariableWords_graph_of_decoded {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height : ℕ) (stream : ℕ → Bool)
    (raw D : List (Fin n × Fin n))
    (goodGraph : (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw)
    (goodDemands : (decodeBinaryFinArcRowsWithWork 0 demands).1 = some D) :
    finSteinerBinaryWordResultGraph ((finSteinerBinaryServeFromVariableWords (n := n) arcWords demands height
      (steinerBitStreamSource stream)).run 0).1.1 =
      ((finSteinerBinaryServeFromBinaryArcRowsWithWork raw height (steinerBitStreamSource stream) D).run 0).1.graph := by
  obtain ⟨state,success,graph,_,_,_⟩ :=
    finSteinerBinaryServeFromVariableWords_refines_decoded arcWords demands height stream 0 raw D goodGraph goodDemands
  rw [success]
  exact graph

open MeasureTheory
open scoped ENNReal

/-- Theorem 21 for accepted variable-length input words. The zero
allowance in the value projection is immaterial to acceptance. The
actual solver takes its allowances from the graph and current request.
The combined recorded work only depends on the vertex and row counts
and actual supplied bits. The seed and competitive guarantee stay exact. -/
theorem theorem21_online_steiner_sampled_variable_words {ε : ℝ} (epsilon : 0 < ε) :
    ∃ (height : ℕ) (K : ℝ) (C k : ℕ), 0 < height ∧ 0 < K ∧
      (∀ {n : ℕ} (arcWords demands : List (List Bool × List Bool))
        (raw D : List (Fin n × Fin n)) (stream : ℕ → Bool),
        (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw →
        (decodeBinaryFinArcRowsWithWork 0 demands).1 = some D →
        (∀ d ∈ D, Reach raw.toFinset d.1 d.2) →
        let out := (finSteinerBinaryServeFromVariableWords (n := n) arcWords demands height
          (steinerBitStreamSource stream)).run 0
        ∃ state, out.1.1 = some state ∧ out.2 = steinerBitBudget raw.toFinset height ∧
          state.history.reverse = D ∧ state.graph ⊆ raw.toFinset ∧ Preserves raw.toFinset state.graph D ∧
          state.work + out.1.2 ≤ C*(binaryVariableWordInputSize n arcWords demands)^k) ∧
      (∀ {n : ℕ} (arcWords demands extension : List (List Bool × List Bool))
        (raw D E : List (Fin n × Fin n)) (stream : ℕ → Bool),
        (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw →
        (decodeBinaryFinArcRowsWithWork 0 demands).1 = some D →
        (decodeBinaryFinArcRowsWithWork 0 extension).1 = some E →
        demands <+: extension → (∀ d ∈ E, Reach raw.toFinset d.1 d.2) →
        let graph (words : List (List Bool × List Bool)) :=
          finSteinerBinaryWordResultGraph ((finSteinerBinaryServeFromVariableWords (n := n) arcWords words height
            (steinerBitStreamSource stream)).run 0).1.1
        graph demands ⊆ graph extension) ∧
      (∀ {n : ℕ} {Z : Arcs (Fin n)} (arcWords demands : List (List Bool × List Bool))
        (raw D : List (Fin n × Fin n)),
        (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw →
        (decodeBinaryFinArcRowsWithWork 0 demands).1 = some D →
        Z ⊆ raw.toFinset → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∫⁻ stream, ((finSteinerBinaryWordResultGraph ((finSteinerBinaryServeFromVariableWords (n := n)
          arcWords demands height (steinerBitStreamSource stream)).run 0).1.1).card : ℝ≥0∞) ∂fairBitMeasure) ≤
            ENNReal.ofReal (K*(n:ℝ)^(3/5+ε)*Z.card)) := by
  obtain ⟨height,K,C,k,heightPos,constantPos,correct,monotonically,expected⟩ :=
    theorem21_online_steiner_sampled_binary_arc_rows epsilon
  refine ⟨height,K,C+2200,max k 3,heightPos,constantPos,?_,?_,?_⟩
  · intro n arcWords demands raw D stream goodGraph goodDemands feasible
    obtain ⟨state,success,graph,history,work,position⟩ :=
      finSteinerBinaryServeFromVariableWords_refines_decoded arcWords demands height stream 0 raw D goodGraph goodDemands
    obtain ⟨bits,trace,sub,preserves,servingCost⟩ := correct raw stream D feasible
    have inputCost := finSteinerBinaryServeFromVariableWords_input_work_le (n := n) arcWords demands height stream 0
    refine ⟨state,success,position.trans bits,?_,?_,?_,?_⟩
    · rw [history]
      exact trace
    · rw [graph]
      exact sub
    · rw [graph]
      exact preserves
    · have solverCost : state.work ≤ C*(n+raw.length+D.length+1)^k := calc
        _ ≤ state.work+(prepareSteinerBinaryArcRowsWithWork raw).2+4 := by omega
        _ = _ := work
        _ ≤ _ := servingCost
      let size := binaryVariableWordInputSize n arcWords demands
      have positive : 0 < size := by dsimp [size,binaryVariableWordInputSize]; omega
      have leSize : n+raw.length+D.length+1 ≤ size := by
        rw [binaryValueDecodedLength goodGraph,binaryValueDecodedLength goodDemands]
        dsimp [size,binaryVariableWordInputSize]
        omega
      have serve : state.work ≤ C*size^(max k 3) :=
        (solverCost.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left leSize k))).trans
          (Nat.mul_le_mul_left C (Nat.pow_le_pow_right positive (le_max_left k 3)))
      have input := inputCost.trans (Nat.mul_le_mul_left 2200 (Nat.pow_le_pow_right positive (le_max_right k 3)))
      change _ ≤ (C+2200)*size^(max k 3)
      rw [Nat.add_mul]
      exact Nat.add_le_add serve input
  · intro n arcWords demands extension raw D E stream goodGraph goodD goodE prefixOf feasible
    dsimp only
    rw [finSteinerBinaryServeFromVariableWords_graph_of_decoded arcWords demands height stream raw D goodGraph goodD,
      finSteinerBinaryServeFromVariableWords_graph_of_decoded arcWords extension height stream raw E goodGraph goodE]
    exact monotonically raw stream (binaryValueDecodedPrefix prefixOf goodD goodE) feasible
  · intro n Z arcWords demands raw D goodGraph goodDemands sub feasible
    simp_rw [fun stream => finSteinerBinaryServeFromVariableWords_graph_of_decoded arcWords demands height stream
      raw D goodGraph goodDemands]
    exact expected raw D sub feasible

end OnlineReachabilityPreservers
