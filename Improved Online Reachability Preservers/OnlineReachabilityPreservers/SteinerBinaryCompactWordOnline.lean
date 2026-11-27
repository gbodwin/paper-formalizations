import OnlineReachabilityPreservers.SteinerBinaryCompactWordSession

/-! Serve an encoded trace using the bounded compact state. -/

namespace OnlineReachabilityPreservers

set_option maxHeartbeats 1600000

/-- Invoke the word step on each request and stop at the first invalid pair. -/
def finSteinerBinaryCompactWordTrace {n height : ℕ} :
    FinSteinerBinaryCompactWordSession n height → List (List Bool × List Bool) →
      Option (FinSteinerBinaryCompactWordSession n height) × ℕ
  | session, [] => (some session,2)
  | session, word::rest =>
    let step := finSteinerBinaryCompactWordStep session word
    match step.1 with
    | none => (none,step.2+2)
    | some next =>
      let tail := finSteinerBinaryCompactWordTrace next rest
      (tail.1,step.2+tail.2+4)

private def compactWordTypedStep {n height : ℕ} (session : FinSteinerBinaryCompactWordSession n height)
    (state : FinSteinerBinaryCompactState n) (d : Fin n × Fin n) : FinSteinerBinaryCompactState n :=
  (finSteinerBinaryCompactStep session.graph session.arcs.val session.graphExact height
    (fun i => session.seed[i.val]) state d).1

/-- Success of the whole word trace means applying the typed compact
steps, in the decoded order, on the same stored graph and seed. -/
theorem finSteinerBinaryCompactWordTrace_result {n height : ℕ} (session : FinSteinerBinaryCompactWordSession n height)
    (words : List (List Bool × List Bool)) :
    (finSteinerBinaryCompactWordTrace session words).1 =
      ((decodeBinaryFinArcRowsWithWork 0 words).1.map fun D => {session with
        state := D.foldl (compactWordTypedStep session) session.state}) := by
  induction words generalizing session with
  | nil => rfl
  | cons word tail ih =>
    simp only [finSteinerBinaryCompactWordTrace,finSteinerBinaryCompactWordStep_result,
      decodeBinaryFinArcRowsWithWork,decodeBinaryNatWithWork_spec]
    by_cases valid : binaryWordValue word.1 < n ∧ binaryWordValue word.2 < n
    · simp only [dite_eq_left valid]
      rw [ih]
      simp only [Option.map_map]
      rfl
    · simp [valid]

/-- Check the fixed graph, draw one seed, and expose only the compact state
and the measured startup and request work. -/
def finSteinerBinaryServeCompactFromVariableWords {n : ℕ} {m : Type → Type} [Monad m]
    (arcWords demands : List (List Bool × List Bool)) (height : ℕ) (nextBit : m Bool) :
    m (Option (FinSteinerBinaryCompactState n) × ℕ) := do
  let (initial,charge) ← finSteinerBinaryCompactWordStart (n := n) arcWords height nextBit
  match initial with
  | none => pure (none,charge+2)
  | some start =>
    let outcome := finSteinerBinaryCompactWordTrace start demands
    pure (outcome.1.map FinSteinerBinaryCompactWordSession.state,charge+outcome.2+5)

/-- The graph projection assigns the empty graph to invalid inputs. -/
def finSteinerBinaryCompactWordResultGraph {n : ℕ} (out : Option (FinSteinerBinaryCompactState n)) : Arcs (Fin n) :=
  (out.map FinSteinerBinaryCompactState.graph).getD ∅

private theorem compactState_eq {n : ℕ} {a b : FinSteinerBinaryCompactState n}
    (history : a.history = b.history) (graph : a.graph = b.graph) : a = b := by
  cases a
  cases b
  simp_all

private theorem completeSteinerStreamGraph_eq {n : ℕ} {G H : Arcs (Fin n)} (same : G = H)
    (height : ℕ) (stream : ℕ → Bool) (start : ℕ) (D : List (Fin n × Fin n)) :
    completeSteinerRunWithBitBudget G height (fun i => stream (start+i.val)) D =
      completeSteinerRunWithBitBudget H height (fun i => stream (start+i.val)) D := by
  subst H
  rfl

/-- On accepted feasible words, compact service reaches the same graph as
the full-history word entry for each stream. It stores first non-self
arrivals in reverse order and ends at the same seed offset. -/
theorem finSteinerBinaryServeCompactFromVariableWords_refines {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (raw D : List (Fin n × Fin n)) (goodGraph : (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw)
    (goodDemands : (decodeBinaryFinArcRowsWithWork 0 demands).1 = some D)
    (feasible : ∀ d ∈ D, Reach raw.toFinset d.1 d.2) :
    let out := (finSteinerBinaryServeCompactFromVariableWords (n := n) arcWords demands height
      (steinerBitStreamSource stream)).run start
    let old := (finSteinerBinaryServeFromVariableWords (n := n) arcWords demands height
      (steinerBitStreamSource stream)).run start
    ∃ state, out.1.1 = some state ∧ state.history.reverse = distinctNonselfTrace D ∧
      state.graph = finSteinerBinaryWordResultGraph old.1.1 ∧
      out.2 = start+steinerBitBudget raw.toFinset height := by
  obtain ⟨session,success,arcEq,empty,initial,seed,position⟩ :=
    finSteinerBinaryCompactWordStart_accepts arcWords height stream start raw goodGraph
  let bits : Fin (steinerBitBudget session.graph height) → Bool := fun i => session.seed[i.val]
  have sameState : session.state =
      (finSteinerBinaryCompactStart session.graph session.arcs.val session.graphExact height bits).1 :=
    compactState_eq empty initial
  have possible (d : Fin n × Fin n) (on : d ∈ D) : Reach session.graph d.1 d.2 := by
    rw [arcEq]
    exact feasible d on
  let state := finSteinerBinaryServeCompact session.graph session.arcs.val session.graphExact height bits D
  have running : (finSteinerBinaryCompactWordTrace session demands).1 = some {session with state} := by
    rw [finSteinerBinaryCompactWordTrace_result,goodDemands]
    change some {session with state := D.foldl (compactWordTypedStep session) session.state} = _
    rw [sameState]
    rfl
  have service := finSteinerBinaryServeCompact_refines session.graph session.arcs.val session.graphExact height bits D possible
  have sameBits : bits = fun i => stream (start+i.val) := funext seed
  have abstract : state.graph = completeSteinerRunWithBitBudget session.graph height (fun i => stream (start+i.val)) D := by
    calc
      _ = (finSteinerBinaryServeWithWork session.graph session.arcs.val session.graphExact height bits D).graph := service.2
      _ = (finSteinerBinaryFinalGraphWithWork session.graph session.arcs.val session.graphExact height bits D).1 :=
        (finSteinerBinaryServeWithWork_spec session.graph session.arcs.val session.graphExact height bits D).2
      _ = finSteinerBinaryFinalGraph session.graph session.arcs.val session.graphExact height bits D :=
        (finSteinerBinaryFinalGraphWithWork_spec session.graph session.arcs.val session.graphExact height bits D possible).1
      _ = _ := by rw [finSteinerBinaryFinalGraph_eq _ _ _ _ _ _ possible,sameBits]
  let prepared := prepareSteinerArcRowsWithWork raw
  let graphExact := (prepareSteinerArcRowsWithWork_spec raw).1
  have reaches (d : Fin n × Fin n) (on : d ∈ D) : Reach prepared.1 d.1 d.2 := graphExact ▸ feasible d on
  obtain ⟨oldState,oldSome,oldGraph,_,_,_⟩ :=
    finSteinerBinaryServeFromVariableWords_refines_decoded arcWords demands height stream start raw D goodGraph goodDemands
  have sameGraph : state.graph = oldState.graph := by
    rw [oldGraph,(finSteinerBinaryServeFromBinaryArcRows_refines raw height stream start D).1,
      finSteinerBinaryServeFromArcRowsWithWork_stream,finSteinerBinaryServeFromBitSource_stream]
    let oldBits : Fin (steinerBitBudget prepared.1 height) → Bool := fun i => stream (start+i.val)
    change state.graph = (finSteinerBinaryServeWithWork prepared.1 raw graphExact height oldBits D).graph
    rw [(finSteinerBinaryServeWithWork_spec prepared.1 raw graphExact height oldBits D).2,
      (finSteinerBinaryFinalGraphWithWork_spec prepared.1 raw graphExact height oldBits D reaches).1,
      finSteinerBinaryFinalGraph_eq prepared.1 raw graphExact height oldBits D reaches]
    exact abstract.trans (completeSteinerStreamGraph_eq (arcEq.trans graphExact) height stream start D)
  dsimp only
  refine ⟨state,?_,service.1,?_,?_⟩
  · unfold finSteinerBinaryServeCompactFromVariableWords
    rw [StateT.run_bind]
    generalize out : (finSteinerBinaryCompactWordStart (n := n) arcWords height (steinerBitStreamSource stream)).run start =
      ready at success ⊢
    rcases ready with ⟨⟨answer,tally⟩,offset⟩
    change answer = some session at success
    subst answer
    change ((finSteinerBinaryCompactWordTrace session demands).1.map FinSteinerBinaryCompactWordSession.state) = some state
    rw [running]
    rfl
  · rw [oldSome]
    exact sameGraph
  · unfold finSteinerBinaryServeCompactFromVariableWords
    rw [StateT.run_bind]
    generalize out : (finSteinerBinaryCompactWordStart (n := n) arcWords height (steinerBitStreamSource stream)).run start =
      ready at position ⊢
    rcases ready with ⟨⟨answer,tally⟩,offset⟩
    cases answer <;> exact position

private theorem finSteinerBinaryCompactVariable_graph_eq {n : ℕ}
    (arcWords demands : List (List Bool × List Bool)) (height : ℕ) (stream : ℕ → Bool)
    (raw D : List (Fin n × Fin n)) (goodGraph : (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw)
    (goodDemands : (decodeBinaryFinArcRowsWithWork 0 demands).1 = some D)
    (feasible : ∀ d ∈ D, Reach raw.toFinset d.1 d.2) :
    finSteinerBinaryCompactWordResultGraph ((finSteinerBinaryServeCompactFromVariableWords (n := n)
      arcWords demands height (steinerBitStreamSource stream)).run 0).1.1 =
    finSteinerBinaryWordResultGraph ((finSteinerBinaryServeFromVariableWords (n := n)
      arcWords demands height (steinerBitStreamSource stream)).run 0).1.1 := by
  obtain ⟨_,present,_,same,_⟩ := finSteinerBinaryServeCompactFromVariableWords_refines
    arcWords demands height stream 0 raw D goodGraph goodDemands feasible
  rw [present]
  exact same

private theorem compactWordTypedStep_preserves_history {n height : ℕ}
    (s : FinSteinerBinaryCompactWordSession n height) (d : Fin n × Fin n)
    (simple : s.state.history.Nodup) (prior : ∀ x ∈ s.state.history, Reach s.graph x.1 x.2)
    (feasible : Reach s.graph d.1 d.2) :
    let next := compactWordTypedStep s s.state d
    next.history.Nodup ∧ ∀ x ∈ next.history, Reach s.graph x.1 x.2 := by
  unfold compactWordTypedStep finSteinerBinaryCompactStep
  have scan := (memScanWithWordWork_spec d s.state.history).1
  by_cases self : d.1 = d.2
  · rw [ite_eq_left self]
    exact ⟨simple,prior⟩
  · rw [ite_eq_right self]
    dsimp only
    by_cases present : d ∈ s.state.history
    · simp only [scan,decide_eq_true_eq,present,ite_true]
      exact ⟨simple,prior⟩
    · simp only [scan,decide_eq_true_eq,present,ite_false]
      change (d::s.state.history).Nodup ∧ ∀ x ∈ d::s.state.history, Reach s.graph x.1 x.2
      refine ⟨List.nodup_cons.mpr ⟨present,simple⟩,?_⟩
      intro x on
      rcases List.mem_cons.mp on with rfl | old
      · exact feasible
      · exact prior x old

private theorem finSteinerBinaryCompactWordTrace_work_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (session : FinSteinerBinaryCompactWordSession n height)
      (words : List (List Bool × List Bool)) (D : List (Fin n × Fin n)) (size : ℕ),
      (decodeBinaryFinArcRowsWithWork 0 words).1 = some D →
      session.state.history.Nodup → (∀ d ∈ session.state.history, Reach session.graph d.1 d.2) →
      (∀ d ∈ D, Reach session.graph d.1 d.2) → n+binaryEndpointBits words+1 ≤ size →
      (finSteinerBinaryCompactWordTrace session words).2 ≤ 2+(C*size^k)*words.length := by
  obtain ⟨C,k,stepWork⟩ := finSteinerBinaryCompactWordStep_polynomial height
  refine ⟨C+4,k,?_⟩
  intro n session words
  induction words generalizing session with
  | nil => simp [finSteinerBinaryCompactWordTrace]
  | cons word rest ih =>
    intro D size accepted simple prior feasible fits
    have valid := (decodeBinaryFinArcRowsWithWork_some_iff_valid (n := n) 0 (word::rest)).mp
      ⟨D,accepted⟩ word List.mem_cons_self
    let d : Fin n × Fin n := (⟨binaryWordValue word.1,valid.1⟩,⟨binaryWordValue word.2,valid.2⟩)
    have decomposed : ∃ E : List (Fin n × Fin n),
        (decodeBinaryFinArcRowsWithWork 0 rest).1 = some E ∧ D = d::E := by
      simp only [decodeBinaryFinArcRowsWithWork,decodeBinaryNatWithWork_spec,dite_eq_left valid] at accepted
      change (decodeBinaryFinArcRowsWithWork 0 rest).1.map (d::·) = some D at accepted
      obtain ⟨E,decoded,equal⟩ := Option.map_eq_some_iff.mp accepted
      exact ⟨E,decoded,equal.symm⟩
    obtain ⟨E,tailAccepted,rfl⟩ := decomposed
    have current := feasible d List.mem_cons_self
    let next := {session with state := compactWordTypedStep session session.state d}
    have result : (finSteinerBinaryCompactWordStep session word).1 = some next := by
      rw [finSteinerBinaryCompactWordStep_result,dite_eq_left valid]
      rfl
    obtain ⟨nextSimple,nextFeasible⟩ := compactWordTypedStep_preserves_history session d simple prior current
    change n+(word.1.length+word.2.length+binaryEndpointBits rest)+1 ≤ size at fits
    have firstSize : n+(word.1.length+word.2.length)+1 ≤ size := by omega
    have tailSize : n+binaryEndpointBits rest+1 ≤ size := by omega
    have currentCost := stepWork session word simple prior (fun _ => current)
    have firstCost : (finSteinerBinaryCompactWordStep session word).2 ≤ C*size^k := currentCost.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left firstSize _))
    have later (x : Fin n × Fin n) (on : x ∈ E) : Reach next.graph x.1 x.2 := feasible x (List.mem_cons_of_mem _ on)
    have tailCost := ih next E size tailAccepted nextSimple nextFeasible later tailSize
    have enough : 1 ≤ size^k := by
      simpa only [one_pow] using Nat.pow_le_pow_left (show 1 ≤ size by omega) k
    unfold finSteinerBinaryCompactWordTrace
    dsimp only
    rw [result]
    simp only [List.length_cons,Nat.mul_succ]
    have headBound : (finSteinerBinaryCompactWordStep session word).2+4 ≤ (C+4)*size^k := by
      rw [Nat.add_mul]
      omega
    omega

/-- The recorded startup and service work over an accepted feasible
compact trace is polynomial in the supplied input dimensions. -/
theorem finSteinerBinaryServeCompactFromVariableWords_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (arcWords demands : List (List Bool × List Bool))
      (raw D : List (Fin n × Fin n)) (stream : ℕ → Bool) (start : ℕ),
      (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw →
      (decodeBinaryFinArcRowsWithWork 0 demands).1 = some D →
      (∀ d ∈ D, Reach raw.toFinset d.1 d.2) →
      ((finSteinerBinaryServeCompactFromVariableWords (n := n) arcWords demands height
        (steinerBitStreamSource stream)).run start).1.2 ≤ C*(binaryVariableWordInputSize n arcWords demands)^k := by
  obtain ⟨A,a,startWork⟩ := finSteinerBinaryCompactWordStart_polynomial height
  obtain ⟨B,b,traceWork⟩ := finSteinerBinaryCompactWordTrace_work_polynomial height
  refine ⟨A+B+7,max a (b+1),?_⟩
  intro n arcWords demands raw D stream start goodGraph goodDemands feasible
  let size := binaryVariableWordInputSize n arcWords demands
  let exponent := max a (b+1)
  have positive : 0 < size := by dsimp [size,binaryVariableWordInputSize]; omega
  have graphSize : binaryVariableWordInputSize n arcWords [] ≤ size := by
    simp only [size,binaryVariableWordInputSize,binaryEndpointBits,List.map_nil,List.sum_nil,List.length_nil]
    omega
  have traceSize : n+binaryEndpointBits demands+1 ≤ size := by dsimp [size,binaryVariableWordInputSize]; omega
  have demandCount : demands.length ≤ size := by dsimp [size,binaryVariableWordInputSize]; omega
  have startupBound := startWork (n := n) arcWords stream start
  have started : ((finSteinerBinaryCompactWordStart (n := n) arcWords height
      (steinerBitStreamSource stream)).run start).1.2 ≤ A*size^exponent :=
    (startupBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left graphSize a))).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_left _ _)))
  obtain ⟨session,present,graph,empty,_,_,_⟩ := finSteinerBinaryCompactWordStart_accepts
    arcWords height stream start raw goodGraph
  have reachable (d : Fin n × Fin n) (on : d ∈ D) : Reach session.graph d.1 d.2 := by
    rw [graph]
    exact feasible d on
  have traced := traceWork session demands D size goodDemands (by simp [empty])
    (fun _ on => by rw [empty] at on; exact (List.not_mem_nil on).elim) reachable traceSize
  have demandWork : (B*size^b)*demands.length ≤ B*size^exponent := calc
    _ ≤ (B*size^b)*size := Nat.mul_le_mul_left _ demandCount
    _ = B*size^(b+1) := by rw [pow_succ,mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_right _ _))
  have one : 1 ≤ size^exponent := by
    simpa only [one_pow] using Nat.pow_le_pow_left (show 1 ≤ size from positive) exponent
  unfold finSteinerBinaryServeCompactFromVariableWords
  rw [StateT.run_bind]
  generalize result : (finSteinerBinaryCompactWordStart (n := n) arcWords height
    (steinerBitStreamSource stream)).run start = ready at present started ⊢
  rcases ready with ⟨⟨answer,charge⟩,offset⟩
  change charge ≤ A*size^exponent at started
  change answer = some session at present
  subst answer
  change charge+(finSteinerBinaryCompactWordTrace session demands).2+5 ≤ (A+B+7)*size^exponent
  rw [Nat.add_mul,Nat.add_mul]
  omega

open MeasureTheory
open scoped ENNReal

/-- Compact variable-word service keeps the reference prefix behavior,
polynomial total recorded work, and Theorem 21's competitive bound
under the fair seed stream. -/
theorem theorem21_online_steiner_sampled_compact_variable_words {ε : ℝ} (epsilon : 0 < ε) :
    ∃ (height : ℕ) (K : ℝ) (C k : ℕ), 0 < height ∧ 0 < K ∧
      (∀ {n : ℕ} (arcWords demands : List (List Bool × List Bool))
        (raw D : List (Fin n × Fin n)) (stream : ℕ → Bool),
        (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw →
        (decodeBinaryFinArcRowsWithWork 0 demands).1 = some D →
        (∀ d ∈ D, Reach raw.toFinset d.1 d.2) →
        let out := (finSteinerBinaryServeCompactFromVariableWords (n := n) arcWords demands height
          (steinerBitStreamSource stream)).run 0
        ∃ state, out.1.1 = some state ∧ out.2 = steinerBitBudget raw.toFinset height ∧
          state.history.reverse = distinctNonselfTrace D ∧ state.history.length ≤ n^2 ∧
          state.graph ⊆ raw.toFinset ∧ Preserves raw.toFinset state.graph D ∧
          out.1.2 ≤ C*(binaryVariableWordInputSize n arcWords demands)^k) ∧
      (∀ {n : ℕ} (arcWords demands extension : List (List Bool × List Bool))
        (raw D E : List (Fin n × Fin n)) (stream : ℕ → Bool),
        (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw →
        (decodeBinaryFinArcRowsWithWork 0 demands).1 = some D →
        (decodeBinaryFinArcRowsWithWork 0 extension).1 = some E →
        demands <+: extension → (∀ d ∈ E, Reach raw.toFinset d.1 d.2) →
        let graph (words : List (List Bool × List Bool)) :=
          finSteinerBinaryCompactWordResultGraph ((finSteinerBinaryServeCompactFromVariableWords (n := n)
            arcWords words height (steinerBitStreamSource stream)).run 0).1.1
        graph demands ⊆ graph extension) ∧
      (∀ {n : ℕ} {Z : Arcs (Fin n)} (arcWords demands : List (List Bool × List Bool))
        (raw D : List (Fin n × Fin n)),
        (decodeBinaryFinArcRowsWithWork 0 arcWords).1 = some raw →
        (decodeBinaryFinArcRowsWithWork 0 demands).1 = some D →
        Z ⊆ raw.toFinset → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∫⁻ stream, ((finSteinerBinaryCompactWordResultGraph ((finSteinerBinaryServeCompactFromVariableWords (n := n)
          arcWords demands height (steinerBitStreamSource stream)).run 0).1.1).card : ℝ≥0∞) ∂fairBitMeasure) ≤
            ENNReal.ofReal (K*(n:ℝ)^(3/5+ε)*Z.card)) := by
  obtain ⟨height,K,_,_,heightPos,constantPos,correct,monotone,expected⟩ := theorem21_online_steiner_sampled_variable_words epsilon
  obtain ⟨C,k,work⟩ := finSteinerBinaryServeCompactFromVariableWords_polynomial height
  refine ⟨height,K,C,k,heightPos,constantPos,?_,?_,?_⟩
  · intro n arcWords demands raw D stream goodGraph goodDemands feasible
    obtain ⟨state,present,history,graph,position⟩ := finSteinerBinaryServeCompactFromVariableWords_refines
      arcWords demands height stream 0 raw D goodGraph goodDemands feasible
    obtain ⟨old,oldPresent,_,_,sub,served,_⟩ := correct arcWords demands raw D stream goodGraph goodDemands feasible
    rw [oldPresent] at graph
    have same : state.graph = old.graph := graph
    have simple : state.history.reverse.Nodup := history.symm ▸ distinctNonselfTrace_nodup D
    have count : state.history.length ≤ n^2 := by
      have sizes := Finset.card_le_univ (state.history.reverse.toFinset)
      rw [List.toFinset_card_of_nodup simple,List.length_reverse] at sizes
      simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using sizes
    exact ⟨state,present,by simpa only [Nat.zero_add] using position,history,count,same.symm ▸ sub,same.symm ▸ served,
      work arcWords demands raw D stream 0 goodGraph goodDemands feasible⟩
  · intro n arcWords demands extension raw D E stream goodGraph goodD goodE pref feasible
    have possible : ∀ d ∈ D, Reach raw.toFinset d.1 d.2 := by
      intro d on
      have before := (decodeBinaryFinArcRowsWithWork_eq_some_iff 0 demands D).mp goodD
      have after := (decodeBinaryFinArcRowsWithWork_eq_some_iff 0 extension E).mp goodE
      let values (p : Fin n × Fin n) := (p.1.val,p.2.val)
      have mapped : D.map values <+: E.map values := by
        rw [show D.map values = _ from before,show E.map values = _ from after]
        exact pref.map _
      have injective : Function.Injective values := fun a b eq =>
        Prod.ext (Fin.ext (congrArg Prod.fst eq)) (Fin.ext (congrArg Prod.snd eq))
      have typedPrefix := (List.prefix_map_iff_of_injective injective).mp mapped
      exact feasible d (typedPrefix.subset on)
    dsimp only
    rw [finSteinerBinaryCompactVariable_graph_eq arcWords demands height stream raw D goodGraph goodD possible,
      finSteinerBinaryCompactVariable_graph_eq arcWords extension height stream raw E goodGraph goodE feasible]
    exact monotone arcWords demands extension raw D E stream goodGraph goodD goodE pref feasible
  · intro n Z arcWords demands raw D goodGraph goodDemands sub feasible
    have reachable (d : Fin n × Fin n) (on : d ∈ D) : Reach raw.toFinset d.1 d.2 := reach_mono sub (feasible d on)
    simp_rw [fun stream => finSteinerBinaryCompactVariable_graph_eq arcWords demands height stream raw D goodGraph goodDemands reachable]
    exact expected arcWords demands raw D goodGraph goodDemands sub feasible

end OnlineReachabilityPreservers
