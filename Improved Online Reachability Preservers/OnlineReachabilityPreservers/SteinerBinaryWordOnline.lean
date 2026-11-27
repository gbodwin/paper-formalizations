import OnlineReachabilityPreservers.SteinerBinaryWordTrace

/-! Connect guarded binary inputs to the sampled solver's full trace. -/

namespace OnlineReachabilityPreservers

/-- On accepted binary input, use the exact decoded trace in the typed fold.
The decoder specification supplies the trace comparison for the proof. -/
theorem finSteinerBinaryWordSessionServe_refines_decoded {n height : ℕ}
    (session : FinSteinerBinaryWordSession n height) (words : List (List Bool × List Bool))
    (demands : List (Fin n × Fin n))
    (accepted : (decodeCheckedBinaryFinArcRowsWithWork session.width words).1 = some demands) :
    (finSteinerBinaryWordSessionServe session words).1 =
      some { session with
        state := demands.foldl (finSteinerBinaryArrivalStepFromSeed session.graph session.raw session.graphExact
          height session.seed) session.state } := by
  induction words generalizing session demands with
  | nil =>
    have ⟨_,values⟩ := (decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff session.width [] demands).mp accepted
    cases demands with
    | nil => rfl
    | cons _ _ => simp at values
  | cons word rest ih =>
    have ⟨widths,values⟩ :=
      (decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff session.width (word::rest) demands).mp accepted
    cases demands with
    | nil => simp at values
    | cons demand tail =>
      have ⟨atWord,atTail⟩ := List.cons.inj values
      have fits := widths word List.mem_cons_self
      let next := finSteinerBinaryArrivalStepFromSeed session.graph session.raw session.graphExact
        height session.seed session.state demand
      have arrival : (finSteinerBinaryArrivalStepFromWords session.graph session.raw session.graphExact
          height session.width session.seed session.state word).1 = some next :=
        (finSteinerBinaryArrivalStepFromWords_eq_some_iff session.graph session.raw session.graphExact
          height session.width session.seed session.state next word).mpr
          ⟨demand,fits.1,fits.2,congrArg Prod.fst atWord,congrArg Prod.snd atWord,rfl⟩
      have step : (finSteinerBinaryWordSessionStep session word).1 = some {session with state := next} := by
        unfold finSteinerBinaryWordSessionStep
        dsimp only
        rw [arrival]
        rfl
      let advanced := {session with state := next}
      have decodedTail : (decodeCheckedBinaryFinArcRowsWithWork advanced.width rest).1 = some tail :=
        (decodeCheckedBinaryFinArcRowsWithWork_eq_some_iff advanced.width rest tail).mpr
          ⟨fun w present => widths w (List.mem_cons_of_mem word present),atTail⟩
      simp only [finSteinerBinaryWordSessionServe,step,List.foldl_cons]
      exact ih advanced tail decodedTail

/-- Validate the graph, draw its seed once and process the demand words
as individual arrivals. The second component counts input work. -/
def finSteinerBinaryServeFromWords {n : ℕ} {m : Type → Type} [Monad m]
    (arcWords demands : List (List Bool × List Bool)) (height width : ℕ) (nextBit : m Bool) :
    m (Option (FinSteinerBinaryArrivalState n) × ℕ) := do
  let (initial, charge) ← finSteinerBinaryStartFromWords (n := n) arcWords height width nextBit
  match initial with
  | none => pure (none,charge+2)
  | some session =>
    let served := finSteinerBinaryWordSessionServe session demands
    pure (served.1.map FinSteinerBinaryWordSession.state,charge+served.2+5)

/-- An invalid binary graph leaves even the seed source untouched. -/
theorem finSteinerBinaryServeFromWords_rejects_graph {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height width : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (bad : (decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).1 = none) :
    (finSteinerBinaryServeFromWords (n := n) arcWords demands height width (steinerBitStreamSource stream)).run start =
      ((none,(decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).2+2+2),start) := by
  unfold finSteinerBinaryServeFromWords
  rw [StateT.run_bind,finSteinerBinaryStartFromWords_rejects arcWords height width stream start bad]
  rfl

/-- Accepted graph and demand words refine the typed solver on their exact
decodes. Input preparation is accounted for separately from arrival work. -/
theorem finSteinerBinaryServeFromWords_refines_decoded {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height width : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (raw D : List (Fin n × Fin n))
    (goodGraph : (decodeCheckedBinaryFinArcRowsWithWork width arcWords).1 = some raw)
    (goodDemands : (decodeCheckedBinaryFinArcRowsWithWork width demands).1 = some D) :
    let result := (finSteinerBinaryServeFromWords (n := n) arcWords demands height width
      (steinerBitStreamSource stream)).run start
    let typed := (finSteinerBinaryServeFromBinaryArcRowsWithWork raw height (steinerBitStreamSource stream) D).run start
    ∃ state, result.1.1 = some state ∧ state.graph = typed.1.graph ∧ state.history = typed.1.history ∧
      state.work+(prepareSteinerBinaryArcRowsWithWork raw).2+4 = typed.1.work ∧ result.2 = typed.2 := by
  let prepared := prepareSteinerBinaryArcRowsWithWork raw
  let same := (prepareSteinerBinaryArcRowsWithWork_spec raw).1
  let initial := (finSteinerBinaryArrivalStartFromBitSource prepared.1 raw same height
    (steinerBitStreamSource stream)).run start
  let session : FinSteinerBinaryWordSession n height := ⟨width,raw,prepared.1,same,initial.1.1,initial.1.2⟩
  let final := D.foldl (finSteinerBinaryArrivalStepFromSeed prepared.1 raw same height initial.1.1) initial.1.2
  have trace : (finSteinerBinaryWordSessionServe session demands).1 = some {session with state := final} :=
    finSteinerBinaryWordSessionServe_refines_decoded session demands D goodDemands
  dsimp only
  have runState : (finSteinerBinaryServeFromWords (n := n) arcWords demands height width
      (steinerBitStreamSource stream)).run start =
      ((some final,(decodeCheckedBinaryFinArcRowsWithWork (n := n) width arcWords).2+prepared.2+5+
          (finSteinerBinaryWordSessionServe session demands).2+5),initial.2) := by
    unfold finSteinerBinaryServeFromWords
    rw [StateT.run_bind,finSteinerBinaryStartFromWords_accepts arcWords height width stream start raw goodGraph]
    change (((finSteinerBinaryWordSessionServe session demands).1.map FinSteinerBinaryWordSession.state, _),_) = _
    rw [trace]
    rfl
  have typedState : (finSteinerBinaryServeFromBinaryArcRowsWithWork raw height (steinerBitStreamSource stream) D).run start =
      ({final with work := final.work+prepared.2+4},initial.2) := rfl
  rw [runState,typedState]
  exact ⟨final,rfl,rfl,rfl,rfl,rfl⟩

end OnlineReachabilityPreservers
