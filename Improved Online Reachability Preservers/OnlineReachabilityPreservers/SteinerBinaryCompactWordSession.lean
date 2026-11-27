import OnlineReachabilityPreservers.SteinerBinaryCompactArrivals
import OnlineReachabilityPreservers.SteinerBinaryVariableWordInput

/-! A variable-length input session with a bounded replay history. -/

namespace OnlineReachabilityPreservers

set_option maxHeartbeats 1800000

/-- Prepare the fixed arc representation and seed once. The saved arc
rows and request history remain bounded independently of input repetition. -/
structure FinSteinerBinaryCompactWordSession (n height : ℕ) where
  graph : Arcs (Fin n)
  arcs : {rows : List (Fin n × Fin n) // rows.Nodup}
  graphExact : arcs.val.toFinset = graph
  seed : Vector Bool (steinerBitBudget graph height)
  state : FinSteinerBinaryCompactState n

private def compactWordSessionFrom {n height : ℕ} (inner : FinSteinerBinaryWordSession n height) :
    FinSteinerBinaryCompactWordSession n height × ℕ :=
  let prepared := finArcRowsWithWordWork inner.raw
  let exactGraph := (finArcRowsWithWordWork_spec inner.graph inner.raw inner.graphExact).1
  (⟨inner.graph,prepared.1,exactGraph,inner.seed,⟨inner.state.history,inner.state.graph⟩⟩,prepared.2+7)

/-- Check the graph and draw the usual seed before service, then save a
duplicate-free arc list. The recorded charge includes all initialization. -/
def finSteinerBinaryCompactWordStart {n : ℕ} {m : Type → Type} [Monad m]
    (arcWords : List (List Bool × List Bool)) (height : ℕ) (nextBit : m Bool) :
    m (Option (FinSteinerBinaryCompactWordSession n height) × ℕ) := do
  let (result,inputWork) ← finSteinerBinaryStartFromVariableWords (n := n) arcWords height nextBit
  match result with
  | none => pure (none,inputWork+2)
  | some inner =>
    let compact := compactWordSessionFrom inner
    pure (some compact.1,inputWork+inner.state.work+compact.2+5)

/-- Process just the two supplied endpoint words and retain the same seed
and arc representation on acceptance. Invalid values return no new state. -/
def finSteinerBinaryCompactWordStep {n height : ℕ} (session : FinSteinerBinaryCompactWordSession n height)
    (word : List Bool × List Bool) : Option (FinSteinerBinaryCompactWordSession n height) × ℕ :=
  let bits := word.1.length+word.2.length
  let decoded := decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+bits) [word]
  match decoded.1 with
  | some [d] =>
    let step := finSteinerBinaryCompactStep session.graph session.arcs.val session.graphExact height
      (fun i => session.seed[i.val]) session.state d
    (some {session with state := step.1},decoded.2+bits+step.2+12)
  | _ => (none,decoded.2+bits+9)

private theorem decodeOneVariableWord {n : ℕ} (word : List Bool × List Bool) :
    (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+(word.1.length+word.2.length)) [word]).1 =
      if valid : binaryWordValue word.1 < n ∧ binaryWordValue word.2 < n then
        some [(⟨binaryWordValue word.1,valid.1⟩,⟨binaryWordValue word.2,valid.2⟩)] else none := by
  have exactDecode :
      (decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+(word.1.length+word.2.length)) [word]).1 =
        (decodeBinaryFinArcRowsWithWork (n := n) 0 [word]).1 := by
    apply Option.eq_of_eq_some
    intro rows
    simpa only [binaryEndpointBits,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using
      decodeCheckedBinaryFinArcRowsWithWork_of_actual_bits [word] rows
  rw [exactDecode]
  simp only [decodeBinaryFinArcRowsWithWork,decodeBinaryNatWithWork_spec]
  split <;> rfl

/-- Rejected requests give no next state. Each accepted request has the
compact step at the exact decoded values. -/
theorem finSteinerBinaryCompactWordStep_result {n height : ℕ} (session : FinSteinerBinaryCompactWordSession n height)
    (word : List Bool × List Bool) :
    (finSteinerBinaryCompactWordStep session word).1 =
      if valid : binaryWordValue word.1 < n ∧ binaryWordValue word.2 < n then
        let step := finSteinerBinaryCompactStep session.graph session.arcs.val session.graphExact height
          (fun i => session.seed[i.val]) session.state
          (⟨binaryWordValue word.1,valid.1⟩,⟨binaryWordValue word.2,valid.2⟩)
        some {session with state := step.1}
      else none := by
  unfold finSteinerBinaryCompactWordStep
  dsimp only
  rw [decodeOneVariableWord]
  by_cases valid : binaryWordValue word.1 < n ∧ binaryWordValue word.2 < n
  · simp only [dite_eq_left valid]
  · simp only [dite_eq_right valid]

/-- A rejected graph still leaves the seed-stream position untouched. -/
theorem finSteinerBinaryCompactWordStart_rejects {n : ℕ} (arcWords : List (List Bool × List Bool))
    (height : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (bad : (decodeBinaryFinArcRowsWithWork (n := n) 0 arcWords).1 = none) :
    let out := (finSteinerBinaryCompactWordStart (n := n) arcWords height (steinerBitStreamSource stream)).run start
    out.1.1 = none ∧ out.2 = start := by
  let width := n+binaryEndpointBits arcWords
  have rejected : (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).1 = none := by
    cases out : (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).1 with
    | none => rfl
    | some raw =>
      have decoded := (decodeCheckedBinaryFinArcRowsWithWork_of_actual_bits arcWords raw).mp out
      rw [bad] at decoded
      exact nomatch decoded
  unfold finSteinerBinaryCompactWordStart finSteinerBinaryStartFromVariableWords
  rw [StateT.run_bind,StateT.run_bind,finSteinerBinaryStartFromWords_rejects arcWords height width stream start rejected]
  exact ⟨rfl,rfl⟩

/-- Acceptance keeps the graph and exact seed word of the existing
initializer. Its starting history is empty. -/
theorem finSteinerBinaryCompactWordStart_accepts {n : ℕ} (arcWords : List (List Bool × List Bool))
    (height : ℕ) (stream : ℕ → Bool) (start : ℕ) (raw : List (Fin n × Fin n))
    (good : (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw) :
    let out := (finSteinerBinaryCompactWordStart (n := n) arcWords height (steinerBitStreamSource stream)).run start
    ∃ session, out.1.1 = some session ∧ session.graph = raw.toFinset ∧ session.state.history = [] ∧
      session.state.graph = (finSteinerBinaryCompactStart session.graph session.arcs.val session.graphExact height
        (fun i => session.seed[i.val])).1.graph ∧
      (∀ i : Fin (steinerBitBudget session.graph height), session.seed[i.val] = stream (start+i.val)) ∧
      out.2 = start+steinerBitBudget raw.toFinset height := by
  let width := n+binaryEndpointBits arcWords
  let prepared := prepareSteinerBinaryArcRowsWithWork raw
  let same := (prepareSteinerBinaryArcRowsWithWork_spec raw).1
  let initial := (finSteinerBinaryArrivalStartFromBitSource prepared.1 raw same height
    (steinerBitStreamSource stream)).run start
  let inner : FinSteinerBinaryWordSession n height := ⟨width,raw,prepared.1,same,initial.1.1,initial.1.2⟩
  let session := (compactWordSessionFrom inner).1
  have guarded := (decodeCheckedBinaryFinArcRowsWithWork_of_actual_bits arcWords raw).mpr good
  change ∃ session, _ = some session ∧ _
  refine ⟨session,?_,same.symm,?_,?_,?_,?_⟩
  · unfold finSteinerBinaryCompactWordStart finSteinerBinaryStartFromVariableWords
    rw [StateT.run_bind,StateT.run_bind,finSteinerBinaryStartFromWords_accepts arcWords height width stream start raw guarded]
    rfl
  · change initial.1.2.history = []
    simp only [initial,finSteinerBinaryArrivalStartFromBitSource,StateT.run_bind,
      readSteinerSeedWithWork_stream,StateT.run_pure,finSteinerBinaryArrivalStart]
    rfl
  · let bits (i : Fin (steinerBitBudget prepared.1 height)) := initial.1.1[i.val]
    have initialGraph : initial.1.2.graph = (finSteinerBinaryFinalGraphWithWork prepared.1 raw same height bits []).1 := by
      simp only [bits,initial,finSteinerBinaryArrivalStartFromBitSource,StateT.run_bind,
        readSteinerSeedWithWork_stream,StateT.run_pure,finSteinerBinaryArrivalStart]
      rfl
    change initial.1.2.graph =
      (finSteinerBinaryFinalGraphWithWork prepared.1 session.arcs.val session.graphExact height bits []).1
    exact initialGraph.trans (finSteinerBinaryFinalGraphWithWork_eq_of_distinct_trace prepared.1 raw session.arcs.val
      same session.graphExact height bits (fun _ on => by simp at on) (fun _ on => by simp at on) rfl)
  · intro i
    change initial.1.1[i.val] = stream (start+i.val)
    simp only [initial,finSteinerBinaryArrivalStartFromBitSource,StateT.run_bind,
      readSteinerSeedWithWork_stream,StateT.run_pure]
    change (Vector.ofFn (fun j : Fin (steinerBitBudget prepared.1 height) => stream (start+j.val)))[i.val] = _
    simp
  · unfold finSteinerBinaryCompactWordStart finSteinerBinaryStartFromVariableWords
    rw [StateT.run_bind,StateT.run_bind,finSteinerBinaryStartFromWords_accepts arcWords height width stream start raw guarded]
    change initial.2 = _
    have endAtPrepared := congrArg Prod.snd
      (finSteinerBinaryServeFromBitSource_stream prepared.1 raw same height stream start [])
    change initial.2 = start+steinerBitBudget prepared.1 height at endAtPrepared
    rw [endAtPrepared,same]

private theorem oneVariableWord_charge {n : ℕ} (word : List Bool × List Bool) :
    let bits := word.1.length+word.2.length
    let width := n+bits
    (decodeCheckedBinaryFinArcRowsWithWork (n := n) width [word]).2+bits+12 ≤ 60*(width+1)^2 := by
  let bits := word.1.length+word.2.length
  let width := n+bits
  have bitsFit : bits ≤ width := Nat.le_add_left _ _
  have decode := decodeCheckedBinaryFinArcRowsWithWork_work_le (n := n) width [word]
  simp only [binaryEndpointWidthCheckBudget,binaryEndpointBits,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,List.length_singleton,Nat.one_mul,Nat.add_zero,binaryFinArcDecodingWorkBudget] at decode
  change _ ≤ 2+bits+4*(width+1)+7+(2+(2*(2+width*(2*(width+1)+5))+4*(width+1)+7))+3 at decode
  change (decodeCheckedBinaryFinArcRowsWithWork (n := n) width [word]).2+bits+12 ≤ 60*(width+1)^2
  nlinarith only [decode,bitsFit,Nat.zero_le width,Nat.zero_le (width*width)]

/-- At fixed height, a request's recorded cost depends polynomially on
the vertex count and its two words. Rejected values are covered as well.
For a valid value the graph must serve the decoded request. -/
theorem finSteinerBinaryCompactWordStep_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (session : FinSteinerBinaryCompactWordSession n height)
      (word : List Bool × List Bool), session.state.history.Nodup →
      (∀ d ∈ session.state.history, Reach session.graph d.1 d.2) →
      (∀ valid : binaryWordValue word.1 < n ∧ binaryWordValue word.2 < n,
        Reach session.graph ⟨binaryWordValue word.1,valid.1⟩ ⟨binaryWordValue word.2,valid.2⟩) →
      (finSteinerBinaryCompactWordStep session word).2 ≤ C*(n+(word.1.length+word.2.length)+1)^k := by
  obtain ⟨C,k,compactWork⟩ := finSteinerBinaryCompactStep_polynomial height
  refine ⟨C+60,max k 2,?_⟩
  intro n session word distinct prior feasible
  let bits := word.1.length+word.2.length
  let size := n+bits+1
  let decoded := decodeCheckedBinaryFinArcRowsWithWork (n := n) (n+bits) [word]
  have positive : 0 < size := by dsimp [size]; omega
  have decodeWork : decoded.2+bits+12 ≤ 60*size^2 := oneVariableWord_charge word
  have inputBound : decoded.2+bits+12 ≤ 60*size^(max k 2) :=
    decodeWork.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_right _ _)))
  unfold finSteinerBinaryCompactWordStep
  dsimp only
  rw [decodeOneVariableWord]
  by_cases valid : binaryWordValue word.1 < n ∧ binaryWordValue word.2 < n
  · rw [dite_eq_left valid]
    let d : Fin n × Fin n := (⟨binaryWordValue word.1,valid.1⟩,⟨binaryWordValue word.2,valid.2⟩)
    let step := finSteinerBinaryCompactStep session.graph session.arcs.val session.graphExact height
      (fun i => session.seed[i.val]) session.state d
    have core : step.2 ≤ C*(n+1)^k := compactWork session.graph session.arcs.val session.graphExact
      session.arcs.property (fun i => session.seed[i.val]) session.state d distinct prior (feasible valid)
    have shorter : n+1 ≤ size := by dsimp [size]; omega
    have served : step.2 ≤ C*size^(max k 2) :=
      (core.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left shorter _))).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_left _ _)))
    change decoded.2+bits+step.2+12 ≤ (C+60)*size^(max k 2)
    rw [Nat.add_mul]
    omega
  · rw [dite_eq_right valid]
    change decoded.2+bits+9 ≤ (C+60)*size^(max k 2)
    rw [Nat.add_mul]
    omega

/-- At fixed height the graph input and one-time seed work have a
polynomial bound in the supplied graph size, including rejected input. -/
theorem finSteinerBinaryCompactWordStart_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (arcWords : List (List Bool × List Bool)) (stream : ℕ → Bool) (start : ℕ),
      ((finSteinerBinaryCompactWordStart (n := n) arcWords height (steinerBitStreamSource stream)).run start).1.2 ≤
        C*(binaryVariableWordInputSize n arcWords [])^k := by
  obtain ⟨C,k,replay⟩ := finSteinerBinaryServeFromBitSource_polynomial height
  refine ⟨C*2^k+2300,max k 3,?_⟩
  intro n arcWords stream start
  let size := binaryVariableWordInputSize n arcWords []
  let width := n+binaryEndpointBits arcWords
  let base := (finSteinerBinaryStartFromVariableWords (n := n) arcWords height (steinerBitStreamSource stream)).run start
  have positive : 0 < size := by dsimp [size,binaryVariableWordInputSize]; omega
  let scale := size^(max k 3)
  have cube : size^3 ≤ scale := Nat.pow_le_pow_right positive (le_max_right _ _)
  have one : 1 ≤ size^3 := by simpa only [one_pow] using Nat.pow_le_pow_left positive 3
  have charged : base.1.2 ≤ 2200*scale := by
    apply le_trans _ (Nat.mul_le_mul_left _ cube)
    have original := finSteinerBinaryServeFromVariableWords_input_work_le (n := n) arcWords [] height stream start
    unfold finSteinerBinaryServeFromVariableWords at original
    rw [StateT.run_bind] at original
    change ((finSteinerBinaryStartFromVariableWords (n := n) arcWords height (steinerBitStreamSource stream)).run start).1.2
      ≤ 2200*size^3
    generalize result : (finSteinerBinaryStartFromVariableWords (n := n) arcWords height
      (steinerBitStreamSource stream)).run start = out at original ⊢
    rcases out with ⟨⟨answer,charge⟩,position⟩
    change charge ≤ 2200*size^3
    cases answer with
    | none => change charge+2 ≤ 2200*size^3 at original; omega
    | some _ => change charge+2+5 ≤ 2200*size^3 at original; omega
  have additional {inner : FinSteinerBinaryWordSession n height} (success : base.1.1 = some inner) :
      inner.state.work+(compactWordSessionFrom inner).2+5 ≤ (C*2^k+64)*scale := by
    cases accepted : (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).1 with
    | none =>
      have noneOut : base.1.1 = none := by
        unfold base finSteinerBinaryStartFromVariableWords
        rw [StateT.run_bind,finSteinerBinaryStartFromWords_rejects arcWords height width stream start accepted]
        rfl
      rw [noneOut] at success
      exact nomatch success
    | some raw =>
      let prepared := prepareSteinerBinaryArcRowsWithWork raw
      let same := (prepareSteinerBinaryArcRowsWithWork_spec raw).1
      let initial := (finSteinerBinaryArrivalStartFromBitSource prepared.1 raw same height
        (steinerBitStreamSource stream)).run start
      let decoded : FinSteinerBinaryWordSession n height := ⟨width,raw,prepared.1,same,initial.1.1,initial.1.2⟩
      have exactSession : base.1.1 = some decoded := by
        unfold base finSteinerBinaryStartFromVariableWords
        rw [StateT.run_bind,finSteinerBinaryStartFromWords_accepts arcWords height width stream start raw accepted]
        rfl
      have equal := Option.some.inj (success.symm.trans exactSession)
      subst inner
      have words := (decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff width arcWords raw).mp accepted
      have count : raw.length = arcWords.length := by
        simpa only [List.length_map] using congrArg List.length words.2
      have inputRoom : n+raw.length+1 ≤ size := by
        rw [count]
        dsimp [size,binaryVariableWordInputSize]
        omega
      have cardinal : prepared.1.card ≤ raw.length := (prepareSteinerBinaryArcRowsWithWork_spec raw).2.1
      have combined : n+prepared.1.card+raw.length+1 ≤ 2*size := by omega
      have initialized : initial.1.2.work ≤ (C*2^k)*scale := calc
        _ ≤ C*(n+prepared.1.card+raw.length+1)^k :=
          replay prepared.1 raw same stream start [] (fun _ on => by simp at on)
        _ ≤ C*(2*size)^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left combined _)
        _ = (C*2^k)*size^k := by rw [mul_pow]; ring
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_left _ _))
      have paid := (finArcRowsWithWordWork_spec prepared.1 raw same).2
      have rows := Nat.mul_le_mul (Nat.mul_le_mul (show n ≤ size by omega) (show n ≤ size by omega))
        (show 2*raw.length+30 ≤ 32*size by omega)
      have quadratic : n*n*(2*raw.length+30) ≤ 32*size^3 := by
        convert rows using 1
        ring
      have cubeSize : size ≤ size^3 := by
        simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1 ≤ 3)
      have canonical : (finArcRowsWithWordWork raw).2+7+5 ≤ 64*size^3 := by
        unfold finArcRowsWordBudget at paid
        omega
      have extra := canonical.trans (Nat.mul_le_mul_left _ cube)
      change initial.1.2.work+((finArcRowsWithWordWork raw).2+7)+5 ≤ (C*2^k+64)*scale
      rw [Nat.add_mul]
      omega
  unfold finSteinerBinaryCompactWordStart
  rw [StateT.run_bind]
  change ((finSteinerBinaryStartFromVariableWords (n := n) arcWords height (steinerBitStreamSource stream)).run start).1.2
    ≤ 2200*scale at charged
  change ∀ {inner}, ((finSteinerBinaryStartFromVariableWords (n := n) arcWords height
    (steinerBitStreamSource stream)).run start).1.1 = some inner →
    inner.state.work+(compactWordSessionFrom inner).2+5 ≤ (C*2^k+64)*scale at additional
  generalize result : (finSteinerBinaryStartFromVariableWords (n := n) arcWords height
    (steinerBitStreamSource stream)).run start = out at charged additional ⊢
  rcases out with ⟨⟨answer,charge⟩,position⟩
  change charge ≤ 2200*scale at charged
  cases answer with
  | none =>
    change charge+2 ≤ (C*2^k+2300)*scale
    rw [Nat.add_mul]
    have scaleOne := one.trans cube
    omega
  | some inner =>
    change charge+inner.state.work+(compactWordSessionFrom inner).2+5 ≤ (C*2^k+2300)*scale
    have extra := additional (inner := inner) rfl
    rw [Nat.add_mul]
    rw [Nat.add_mul] at extra
    omega

end OnlineReachabilityPreservers
