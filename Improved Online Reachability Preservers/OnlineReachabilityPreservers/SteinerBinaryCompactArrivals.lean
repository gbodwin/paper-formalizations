import OnlineReachabilityPreservers.SteinerBinaryArrivals

/-! Retain just the first non-self occurrence of each demand in the online state. -/

namespace OnlineReachabilityPreservers

/-- A compact session stores the reverse first-occurrence trace and its current graph. -/
structure FinSteinerBinaryCompactState (n : ℕ) where
  history : List (Fin n × Fin n)
  graph : Arcs (Fin n)

/-- Reuse the existing initialization. Report its work separately from the state. -/
def finSteinerBinaryCompactStart {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool) :
    FinSteinerBinaryCompactState n × ℕ :=
  let start := finSteinerBinaryArrivalStart G raw same height bits
  (⟨start.history,start.graph⟩,start.work+3)

/-- Self requests and repeats return the current graph. The first arrival
of any other request invokes the existing bounded prefix replay. -/
def finSteinerBinaryCompactStep {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (state : FinSteinerBinaryCompactState n) (demand : Fin n × Fin n) : FinSteinerBinaryCompactState n × ℕ :=
  if demand.1 = demand.2 then (state,3)
  else
    let checked := memScanWithWordWork demand state.history
    if checked.1 then (state,checked.2+4)
    else
      let next := finSteinerBinaryArrivalStep G raw same height bits ⟨state.history,state.graph,0⟩ demand
      (⟨next.history,next.graph⟩,next.work+checked.2+8)

private theorem distinctNonselfTrace_append_one {n : ℕ} (D : List (Fin n × Fin n)) (d : Fin n × Fin n) :
    distinctNonselfTrace (D ++ [d]) =
      if d.1 = d.2 ∨ d ∈ distinctNonselfTrace D then distinctNonselfTrace D else distinctNonselfTrace D ++ [d] := by
  unfold distinctNonselfTrace
  rw [List.foldl_append]
  rfl

private theorem distinctNonselfTrace_of_distinct {n : ℕ} (D : List (Fin n × Fin n))
    (simple : D.Nodup) (nonself : ∀ d ∈ D, d.1 ≠ d.2) : distinctNonselfTrace D = D := by
  induction D using List.reverseRecOn with
  | nil => rfl
  | append_singleton D d ih =>
    obtain ⟨simpleD,_,apart⟩ := List.nodup_append.mp simple
    have fresh : d ∉ D := fun hd => apart d hd d (by simp) rfl
    have nonselfD (x : Fin n × Fin n) (on : x ∈ D) : x.1 ≠ x.2 :=
      nonself x (List.mem_append_left _ on)
    have nonselfD' := nonself d (List.mem_append_right _ (by simp))
    simp only [distinctNonselfTrace_append_one,ih simpleD nonselfD,nonselfD',fresh,or_self,ite_false]

/-- The final graph depends on the arc set, the seed and the ordered
first occurrences of non-self requests. -/
theorem finSteinerBinaryFinalGraphWithWork_eq_of_distinct_trace {n : ℕ} (G : Arcs (Fin n))
    (raw newRaw : List (Fin n × Fin n)) (same : raw.toFinset = G) (sameNew : newRaw.toFinset = G)
    (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool) {D E : List (Fin n × Fin n)}
    (feasibleD : ∀ d ∈ D, Reach G d.1 d.2) (feasibleE : ∀ d ∈ E, Reach G d.1 d.2)
    (sameTrace : distinctNonselfTrace D = distinctNonselfTrace E) :
    (finSteinerBinaryFinalGraphWithWork G raw same height bits D).1 =
      (finSteinerBinaryFinalGraphWithWork G newRaw sameNew height bits E).1 := by
  rw [(finSteinerBinaryFinalGraphWithWork_spec G raw same height bits D feasibleD).1,
    (finSteinerBinaryFinalGraphWithWork_spec G newRaw sameNew height bits E feasibleE).1,
    finSteinerBinaryFinalGraph_eq G raw same height bits D feasibleD,
    finSteinerBinaryFinalGraph_eq G newRaw sameNew height bits E feasibleE]
  unfold completeSteinerRunWithBitBudget
  split
  · change (if distinctNonselfTrace D = [] then ∅ else G) = (if distinctNonselfTrace E = [] then ∅ else G)
    rw [sameTrace]
  · simp only [completeSteinerDrawRun,completeSteinerRun,sameTrace]

/-- The compact step yields the exact graph for the original feasible
trace, including skipped self requests and repeated requests. -/
theorem finSteinerBinaryCompactStep_refines {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (state : FinSteinerBinaryCompactState n) (D : List (Fin n × Fin n)) (d : Fin n × Fin n)
    (history : state.history.reverse = distinctNonselfTrace D)
    (graph : state.graph = (finSteinerBinaryFinalGraphWithWork G raw same height bits D).1)
    (feasible : ∀ x ∈ D ++ [d], Reach G x.1 x.2) :
    let out := (finSteinerBinaryCompactStep G raw same height bits state d).1
    out.history.reverse = distinctNonselfTrace (D ++ [d]) ∧
      out.graph = (finSteinerBinaryFinalGraphWithWork G raw same height bits (D ++ [d])).1 := by
  have feasibleD (x : Fin n × Fin n) (on : x ∈ D) : Reach G x.1 x.2 := feasible x (List.mem_append_left _ on)
  have skip (skip : d.1 = d.2 ∨ d ∈ distinctNonselfTrace D) :
      state.history.reverse = distinctNonselfTrace (D ++ [d]) ∧
      state.graph = (finSteinerBinaryFinalGraphWithWork G raw same height bits (D ++ [d])).1 := by
    have trace : distinctNonselfTrace (D ++ [d]) = distinctNonselfTrace D := by
      rw [distinctNonselfTrace_append_one,ite_eq_left skip]
    exact ⟨history.trans trace.symm,graph.trans (finSteinerBinaryFinalGraphWithWork_eq_of_distinct_trace
      G raw raw same same height bits feasibleD feasible trace.symm)⟩
  have scan := (memScanWithWordWork_spec d state.history).1
  unfold finSteinerBinaryCompactStep
  by_cases isSelf : d.1 = d.2
  · rw [ite_eq_left isSelf]
    exact skip (Or.inl isSelf)
  · rw [ite_eq_right isSelf]
    dsimp only
    by_cases present : d ∈ state.history
    · simp only [scan,decide_eq_true_eq,present,ite_true]
      have prior : d ∈ distinctNonselfTrace D := history ▸ List.mem_reverse.mpr present
      exact skip (Or.inr prior)
    · simp only [scan,decide_eq_true_eq,present,ite_false]
      let E := state.history.reverse ++ [d]
      have absent : d ∉ distinctNonselfTrace D := fun h => present (List.mem_reverse.mp (history.symm ▸ h))
      have trace : distinctNonselfTrace (D ++ [d]) = E := by
        rw [distinctNonselfTrace_append_one,ite_eq_right (not_or.mpr ⟨isSelf,absent⟩)]
        exact congrArg (· ++ [d]) history.symm
      have simpleE : E.Nodup := trace ▸ distinctNonselfTrace_nodup (D ++ [d])
      have nonselfE (x : Fin n × Fin n) (on : x ∈ E) : x.1 ≠ x.2 :=
        (mem_distinctNonselfTrace.mp (trace.symm ▸ on)).2
      have feasibleE (x : Fin n × Fin n) (on : x ∈ E) : Reach G x.1 x.2 :=
        feasible x (mem_distinctNonselfTrace.mp (trace.symm ▸ on)).1
      let dummy : FinSteinerBinaryArrivalState n := ⟨state.history,state.graph,0⟩
      obtain ⟨nextHistory,nextGraph,_⟩ := finSteinerBinaryArrivalStep_spec G raw same height bits dummy d
      exact ⟨nextHistory.trans trace.symm,nextGraph.trans (finSteinerBinaryFinalGraphWithWork_eq_of_distinct_trace
        G raw raw same same height bits feasibleE feasible ((distinctNonselfTrace_of_distinct E simpleE nonselfE).trans trace.symm))⟩

/-- Replay a compact session over a trace, exposing the same one-request
operation at each arrival. Each step reports its own work. -/
def finSteinerBinaryServeCompact {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) : FinSteinerBinaryCompactState n :=
  D.foldl (fun state demand => (finSteinerBinaryCompactStep G raw same height bits state demand).1)
    (finSteinerBinaryCompactStart G raw same height bits).1

/-- At every feasible prefix the compact history retains exactly the first
non-self arrivals, and the graph is the already verified arrival output. -/
theorem finSteinerBinaryServeCompact_refines {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := finSteinerBinaryServeCompact G raw same height bits D
    out.history.reverse = distinctNonselfTrace D ∧
      out.graph = (finSteinerBinaryServeWithWork G raw same height bits D).graph := by
  rw [(finSteinerBinaryServeWithWork_spec G raw same height bits D).2]
  induction D using List.reverseRecOn with
  | nil => exact ⟨rfl,rfl⟩
  | append_singleton D d ih =>
    obtain ⟨history,graph⟩ := ih fun x on => feasible x (List.mem_append_left _ on)
    simpa only [finSteinerBinaryServeCompact,List.foldl_append,List.foldl_cons,List.foldl_nil] using
      finSteinerBinaryCompactStep_refines G raw same height bits
        (finSteinerBinaryServeCompact G raw same height bits D) D d history graph feasible

private theorem finPairList_length_le_square {n : ℕ} {rows : List (Fin n × Fin n)}
    (simple : rows.Nodup) : rows.length ≤ n^2 := by
  rw [← List.toFinset_card_of_nodup simple]
  simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using Finset.card_le_univ rows.toFinset

/-- A feasible compact prefix stores at most one entry per possible request. -/
theorem finSteinerBinaryServeCompact_history_le {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (finSteinerBinaryServeCompact G raw same height bits D).history.length ≤ n^2 := by
  let state := finSteinerBinaryServeCompact G raw same height bits D
  have history : state.history.reverse = distinctNonselfTrace D :=
    (finSteinerBinaryServeCompact_refines G raw same height bits D feasible).1
  have simple : state.history.reverse.Nodup := history.symm ▸ distinctNonselfTrace_nodup D
  simpa only [List.length_reverse] using finPairList_length_le_square simple

/-- For a duplicate-free input arc list and feasible requests, one compact
arrival has polynomial recorded cost in the vertex count alone. The
cost does not depend on the number of prior arrivals. -/
theorem finSteinerBinaryCompactStep_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G),
      raw.Nodup → ∀ (bits : Fin (steinerBitBudget G height) → Bool)
      (state : FinSteinerBinaryCompactState n) (d : Fin n × Fin n),
      state.history.Nodup → (∀ x ∈ state.history, Reach G x.1 x.2) → Reach G d.1 d.2 →
      (finSteinerBinaryCompactStep G raw same height bits state d).2 ≤ C*(n+1)^k := by
  obtain ⟨C,k,poly⟩ := finSteinerBinaryFinalGraphWithWork_polynomial height
  refine ⟨C*3^k+20,2*k+2,?_⟩
  intro n G raw same arcSimple bits state d historySimple earlier feasible
  have histories := finPairList_length_le_square historySimple
  have arcs := finPairList_length_le_square arcSimple
  have graph : G.card ≤ n^2 := by
    simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using Finset.card_le_univ G
  have scan := memScanWithWordWork_spec d state.history
  have positive : 0 < n+1 := by omega
  have growth : (n+1)^(2*k) ≤ (n+1)^(2*k+2) := Nat.pow_le_pow_right positive (by omega)
  have growthTwo : (n+1)^2 ≤ (n+1)^(2*k+2) := Nat.pow_le_pow_right positive (by omega)
  have overhead : 7*n^2+20 ≤ 20*(n+1)^2 := by nlinarith
  have smallWork : 7*n^2+20 ≤ (C*3^k+20)*(n+1)^(2*k+2) :=
    (overhead.trans (Nat.mul_le_mul_left _ growthTwo)).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
  unfold finSteinerBinaryCompactStep
  by_cases isSelf : d.1 = d.2
  · rw [ite_eq_left isSelf]
    exact (show 3 ≤ 7*n^2+20 by omega).trans smallWork
  · rw [ite_eq_right isSelf]
    dsimp only
    by_cases present : d ∈ state.history
    · simp only [scan.1,decide_eq_true_eq,present,ite_true]
      exact (show (memScanWithWordWork d state.history).2+4 ≤ 7*n^2+20 by
        have charged := scan.2
        omega).trans smallWork
    · simp only [scan.1,decide_eq_true_eq,present,ite_false]
      let E := state.history.reverse ++ [d]
      have simpleE : E.Nodup := by
        refine List.nodup_append.mpr ⟨List.nodup_reverse.mpr historySimple,by simp,?_⟩
        intro x on y last equal
        have yEq := List.mem_singleton.mp last
        exact present (List.mem_reverse.mp ((equal.trans yEq) ▸ on))
      have feasibleE (x : Fin n × Fin n) (on : x ∈ E) : Reach G x.1 x.2 := by
        rcases List.mem_append.mp on with old | new
        · exact earlier x (List.mem_reverse.mp old)
        · exact (List.mem_singleton.mp new).symm ▸ feasible
      have trace := finPairList_length_le_square simpleE
      have inputSize : n+G.card+raw.length+E.length+1 ≤ 3*(n+1)^2 := by
        nlinarith only [graph,arcs,trace,Nat.zero_le n]
      let result := finSteinerBinaryFinalGraphWithWork G raw same height bits E
      have cost : result.2 ≤ C*3^k*(n+1)^(2*k) := calc
        _ ≤ C*(n+G.card+raw.length+E.length+1)^k :=
          (Nat.le_add_right _ _).trans (poly G raw same bits E feasibleE)
        _ ≤ C*(3*(n+1)^2)^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left inputSize k)
        _ = _ := by rw [mul_pow,pow_mul]; ring
      let dummy : FinSteinerBinaryArrivalState n := ⟨state.history,state.graph,0⟩
      have exactWork : (finSteinerBinaryArrivalStep G raw same height bits dummy d).work =
          result.2+(3+5*E.length)+8 := by
        simpa only [dummy,Nat.zero_add,E,result] using (finSteinerBinaryArrivalStep_spec G raw same height bits dummy d).2.2
      change (finSteinerBinaryArrivalStep G raw same height bits dummy d).work+
        (memScanWithWordWork d state.history).2+8 ≤ _
      rw [exactWork]
      have paid : (3+5*E.length)+8+(memScanWithWordWork d state.history).2+8 ≤ 7*n^2+20 := by
        have charged := scan.2
        omega
      calc
        _ ≤ result.2+(7*n^2+20) := by omega
        _ ≤ C*3^k*(n+1)^(2*k)+20*(n+1)^2 := Nat.add_le_add cost overhead
        _ ≤ _ := by rw [Nat.add_mul]; exact Nat.add_le_add (Nat.mul_le_mul_left _ growth) (Nat.mul_le_mul_left _ growthTwo)

/-- A self request or a previously seen request does not replay the solver. -/
theorem finSteinerBinaryCompactStep_skip {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (state : FinSteinerBinaryCompactState n) (d : Fin n × Fin n) (skip : d.1 = d.2 ∨ d ∈ state.history) :
    let out := finSteinerBinaryCompactStep G raw same height bits state d
    out.1 = state ∧ out.2 ≤ 2*state.history.length+5 := by
  unfold finSteinerBinaryCompactStep
  by_cases isSelf : d.1 = d.2
  · rw [ite_eq_left isSelf]
    exact ⟨rfl,by omega⟩
  · have seen := skip.resolve_left isSelf
    have scan := memScanWithWordWork_spec d state.history
    simp only [isSelf,ite_false,scan.1,decide_eq_true_eq,seen,ite_true]
    exact ⟨True.intro,by have charged := scan.2; omega⟩

/-- Theorem 21 with a bounded first-occurrence history and polynomial
recorded work per feasible arrival. The fixed graph has a duplicate-free
arc representation for the work bound. The finite seed law and the
irrevocable graph are the same as in the original replay. -/
theorem theorem21_online_steiner_binary_compact_arrivals {ε : ℝ} (epsilon : 0 < ε) :
    ∃ (height : ℕ) (K : ℝ) (C k : ℕ), 0 < height ∧ 0 < K ∧
      (∀ {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G),
        raw.Nodup → ∀ (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)),
        (∀ d ∈ D, Reach G d.1 d.2) →
        let out := finSteinerBinaryServeCompact G raw same height bits D
        out.graph ⊆ G ∧ Preserves G out.graph D ∧ out.history.length ≤ n^2 ∧
        ∀ d : Fin n × Fin n, Reach G d.1 d.2 →
          (finSteinerBinaryCompactStep G raw same height bits out d).2 ≤ C*(n+1)^k) ∧
      (∀ {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
        (bits : Fin (steinerBitBudget G height) → Bool) {D E : List (Fin n × Fin n)},
        D <+: E → (∀ d ∈ E, Reach G d.1 d.2) →
          (finSteinerBinaryServeCompact G raw same height bits D).graph ⊆
          (finSteinerBinaryServeCompact G raw same height bits E).graph) ∧
      (∀ {n : ℕ} {G Z : Arcs (Fin n)} (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
        (D : List (Fin n × Fin n)), Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∑ bits : Fin (steinerBitBudget G height) → Bool,
          ((finSteinerBinaryServeCompact G raw same height bits D).graph.card : ℝ)) /
          (Fintype.card (Fin (steinerBitBudget G height) → Bool) : ℝ) ≤ K*(n:ℝ)^(3/5+ε)*Z.card) := by
  obtain ⟨height,K,_,_,heightPos,Kpos,correct,earlierGraphs,expected⟩ := theorem21_online_steiner_binary_arrivals epsilon
  obtain ⟨C,k,stepWork⟩ := finSteinerBinaryCompactStep_polynomial height
  refine ⟨height,K,C,k,heightPos,Kpos,?_,?_,?_⟩
  · intro n G raw same arcSimple bits D feasible
    let state := finSteinerBinaryServeCompact G raw same height bits D
    obtain ⟨history,graph⟩ := finSteinerBinaryServeCompact_refines G raw same height bits D feasible
    obtain ⟨sub,preserves,_⟩ := correct G raw same bits D feasible
    refine ⟨graph.symm ▸ sub,graph.symm ▸ preserves,
      finSteinerBinaryServeCompact_history_le G raw same height bits D feasible,?_⟩
    have historySimple : state.history.Nodup := List.nodup_reverse.mp (history.symm ▸ distinctNonselfTrace_nodup D)
    have seenFeasible (d : Fin n × Fin n) (seen : d ∈ state.history) : Reach G d.1 d.2 :=
      feasible d (mem_distinctNonselfTrace.mp (history ▸ List.mem_reverse.mpr seen)).1
    intro d reachable
    exact stepWork G raw same arcSimple bits state d historySimple seenFeasible reachable
  · intro n G raw same bits D E pref feasible
    rw [(finSteinerBinaryServeCompact_refines G raw same height bits D (fun d hd => feasible d (pref.subset hd))).2,
      (finSteinerBinaryServeCompact_refines G raw same height bits E feasible).2]
    exact earlierGraphs G raw same bits pref feasible
  · intro n G Z raw same D sub feasible
    have feasibleG (d : Fin n × Fin n) (on : d ∈ D) : Reach G d.1 d.2 := reach_mono sub (feasible d on)
    simp_rw [fun bits => (finSteinerBinaryServeCompact_refines G raw same height bits D feasibleG).2]
    exact expected raw same D sub feasible

end OnlineReachabilityPreservers
