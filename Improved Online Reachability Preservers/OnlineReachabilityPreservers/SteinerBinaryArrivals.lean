import OnlineReachabilityPreservers.SteinerBinaryReplayAsymptotics

/-! Serve incoming demands using the same sampled bit word throughout. -/

namespace OnlineReachabilityPreservers

/-- The history is stored with the latest demand first. The graph and work
tally summarize the outputs already returned on that history. -/
structure FinSteinerBinaryArrivalState (n : ℕ) where
  history : List (Fin n × Fin n)
  graph : Arcs (Fin n)
  work : ℕ

private def reverseDemandHistoryWithWork {A : Type*} (history : List A) : List A × ℕ :=
  history.foldl (fun acc demand => (demand :: acc.1, acc.2 + 5)) ([], 3)

private theorem reverseDemandHistoryWithWork_spec {A : Type*} (history : List A) :
    reverseDemandHistoryWithWork history = (history.reverse, 3 + 5 * history.length) := by
  have fold (tail : List A) (work : ℕ) :
      history.foldl (fun acc demand => (demand :: acc.1, acc.2 + 5)) (tail, work) =
        (history.reverse ++ tail, work + 5 * history.length) := by
    induction history generalizing tail work with
    | nil => simp
    | cons demand rest ih =>
      rw [List.foldl_cons, ih, List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons, Nat.mul_succ, Nat.add_right_comm work]
      simp only [Nat.add_assoc]
  simpa [reverseDemandHistoryWithWork] using fold [] 3

/-- Prepare the empty prefix before any demand has arrived. -/
def finSteinerBinaryArrivalStart {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool) :
    FinSteinerBinaryArrivalState n :=
  let result := finSteinerBinaryFinalGraphWithWork G raw same height bits []
  ⟨[], result.1, result.2 + 4⟩

/-- On one arrival, run the prefix solver using only the saved history and
the new demand. The fixed graph and the sampled bit word are reused. -/
def finSteinerBinaryArrivalStep {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (state : FinSteinerBinaryArrivalState n) (demand : Fin n × Fin n) : FinSteinerBinaryArrivalState n :=
  let history := demand :: state.history
  let input := reverseDemandHistoryWithWork history
  let result := finSteinerBinaryFinalGraphWithWork G raw same height bits input.1
  ⟨history, result.1, state.work + result.2 + input.2 + 8⟩

theorem finSteinerBinaryArrivalStep_spec {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (state : FinSteinerBinaryArrivalState n) (demand : Fin n × Fin n) :
    let next := finSteinerBinaryArrivalStep G raw same height bits state demand
    let trace := state.history.reverse ++ [demand]
    let result := finSteinerBinaryFinalGraphWithWork G raw same height bits trace
    next.history.reverse = trace ∧ next.graph = result.1 ∧
      next.work = state.work + result.2 + (3 + 5 * trace.length) + 8 := by
  dsimp only [finSteinerBinaryArrivalStep]
  rw [reverseDemandHistoryWithWork_spec (demand :: state.history)]
  simp

/-- Fold the same arrival operation over a trace for its final graph and
total work. Each call receives only the next demand. -/
def finSteinerBinaryServeWithWork {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) : FinSteinerBinaryArrivalState n :=
  D.foldl (finSteinerBinaryArrivalStep G raw same height bits)
    (finSteinerBinaryArrivalStart G raw same height bits)

theorem finSteinerBinaryServeWithWork_append {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) (demand : Fin n × Fin n) :
    finSteinerBinaryServeWithWork G raw same height bits (D ++ [demand]) =
      finSteinerBinaryArrivalStep G raw same height bits
        (finSteinerBinaryServeWithWork G raw same height bits D) demand := by
  simp only [finSteinerBinaryServeWithWork, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem finSteinerBinaryServeWithWork_spec {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) :
    let result := finSteinerBinaryServeWithWork G raw same height bits D
    result.history.reverse = D ∧
      result.graph = (finSteinerBinaryFinalGraphWithWork G raw same height bits D).1 := by
  induction D using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton D demand ih =>
    rw [finSteinerBinaryServeWithWork_append]
    obtain ⟨history, _, _⟩ := finSteinerBinaryArrivalStep_spec G raw same height bits
      (finSteinerBinaryServeWithWork G raw same height bits D) demand
    exact ⟨history.trans (congrArg (· ++ [demand]) ih.1), by
      rw [(finSteinerBinaryArrivalStep_spec G raw same height bits _ demand).2.1, ih.1]⟩

/-- The tally adds each prefix evaluation and the history work for its
arrival. The empty prefix is evaluated once at initialization. -/
theorem finSteinerBinaryServeWithWork_tally {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) :
    (finSteinerBinaryServeWithWork G raw same height bits D).work =
      (D.inits.map fun E => (finSteinerBinaryFinalGraphWithWork G raw same height bits E).2 +
        if E.isEmpty then 4 else 3 + 5 * E.length + 8).sum := by
  induction D using List.reverseRecOn with
  | nil => simp [finSteinerBinaryServeWithWork, finSteinerBinaryArrivalStart]
  | append_singleton D demand ih =>
    rw [finSteinerBinaryServeWithWork_append,
      (finSteinerBinaryArrivalStep_spec G raw same height bits _ demand).2.2,
      (finSteinerBinaryServeWithWork_spec G raw same height bits D).1, ih, List.inits_append]
    simp [Nat.add_assoc]

/-- The online graph serves the entire seen prefix for each supplied word. -/
theorem finSteinerBinaryServeWithWork_correct {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let output := finSteinerBinaryServeWithWork G raw same height bits D
    output.graph ⊆ G ∧ Preserves G output.graph D := by
  dsimp only
  rw [(finSteinerBinaryServeWithWork_spec G raw same height bits D).2,
    (finSteinerBinaryFinalGraphWithWork_spec G raw same height bits D feasible).1]
  exact finSteinerBinaryFinalGraph_correct G raw same height bits D feasible

/-- For a fixed word, later outputs contain every edge previously returned. -/
theorem finSteinerBinaryServeWithWork_prefix {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    {D E : List (Fin n × Fin n)} (prefixOf : D <+: E) (feasible : ∀ d ∈ E, Reach G d.1 d.2) :
    (finSteinerBinaryServeWithWork G raw same height bits D).graph ⊆
      (finSteinerBinaryServeWithWork G raw same height bits E).graph := by
  rw [(finSteinerBinaryServeWithWork_spec G raw same height bits D).2,
    (finSteinerBinaryServeWithWork_spec G raw same height bits E).2,
    (finSteinerBinaryFinalGraphWithWork_spec G raw same height bits D
      (fun d member => feasible d (prefixOf.subset member))).1,
    (finSteinerBinaryFinalGraphWithWork_spec G raw same height bits E feasible).1]
  exact finSteinerBinaryFinalGraph_prefix G raw same height bits prefixOf feasible

private theorem finSteinerBinaryServeWithWork_tally_le {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) (count allowance : ℕ) (length : D.length ≤ count)
    (bounded : ∀ E : List (Fin n × Fin n), E <+: D →
      (finSteinerBinaryFinalGraphWithWork G raw same height bits E).2 ≤ allowance) :
    (finSteinerBinaryServeWithWork G raw same height bits D).work ≤
      (D.length + 1) * (allowance + 5 * count + 11) := by
  let charge (E : List (Fin n × Fin n)) := (finSteinerBinaryFinalGraphWithWork G raw same height bits E).2 +
    if E.isEmpty then 4 else 3 + 5 * E.length + 8
  have each (x : ℕ) (inside : x ∈ D.inits.map charge) : x ≤ allowance + 5 * count + 11 := by
    obtain ⟨E, member, rfl⟩ := List.mem_map.mp inside
    have prior := (List.mem_inits E D).mp member
    have time := bounded E prior
    have short := prior.length_le.trans length
    dsimp only [charge]
    split <;> omega
  rw [finSteinerBinaryServeWithWork_tally]
  simpa only [List.length_map, List.length_inits, nsmul_eq_mul, Nat.cast_id, charge] using
    List.sum_le_length_nsmul (D.inits.map charge) (allowance + 5 * count + 11) each

/-- The whole sequential invocation cost, including the single shared bit
word, is polynomial at each fixed height in the recorded work model. -/
theorem finSteinerBinaryServeWithWork_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
      (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)),
      (∀ d ∈ D, Reach G d.1 d.2) →
      (finSteinerBinaryServeWithWork G raw same height bits D).work + steinerBitBudget G height ≤
        C * (n + G.card + raw.length + D.length + 1)^k := by
  obtain ⟨C, k, onePrefix⟩ := finSteinerBinaryFinalGraphWithWork_polynomial height
  refine ⟨2 * C + 16, k + 2, ?_⟩
  intro n G raw same bits D feasible
  let size := n + G.card + raw.length + D.length + 1
  have positive : 0 < size := by dsimp [size]; omega
  have count : D.length + 1 ≤ size := by dsimp [size]; omega
  have allowances (E : List (Fin n × Fin n)) (prefixOf : E <+: D) :
      (finSteinerBinaryFinalGraphWithWork G raw same height bits E).2 + steinerBitBudget G height ≤ C * size^k := by
    apply (onePrefix G raw same bits E (fun d member => feasible d (prefixOf.subset member))).trans
    apply Nat.mul_le_mul_left _ (Nat.pow_le_pow_left _ _)
    have lengths := prefixOf.length_le
    dsimp [size]
    omega
  have total := finSteinerBinaryServeWithWork_tally_le G raw same height bits D D.length (C * size^k) le_rfl
    (fun E prefixOf => (Nat.le_add_right _ _).trans (allowances E prefixOf))
  have supply := (Nat.le_add_left _ _).trans (allowances D List.prefix_rfl)
  have history : 5 * D.length + 11 ≤ 16 * size := by omega
  have powers (i : ℕ) (degree : i ≤ k + 2) : size^i ≤ size^(k + 2) := Nat.pow_le_pow_right positive degree
  calc
    _ ≤ (D.length + 1) * (C * size^k + 5 * D.length + 11) + C * size^k := Nat.add_le_add total supply
    _ ≤ size * (C * size^k + 16 * size) + C * size^k :=
      Nat.add_le_add_right (Nat.mul_le_mul count (by omega)) _
    _ = C * size^(k + 1) + 16 * size^2 + C * size^k := by rw [pow_succ, pow_two]; ring
    _ ≤ C * size^(k + 2) + 16 * size^(k + 2) + C * size^(k + 2) := Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left _ (powers _ (by omega))) (Nat.mul_le_mul_left _ (powers _ (by omega))))
      (Nat.mul_le_mul_left _ (powers _ (by omega)))
    _ = (2 * C + 16) * size^(k + 2) := by ring

/-- A single fixed height gives irrevocable online output, a polynomial
recorded total cost and bit budget, and Theorem 21's finite-word mean bound. -/
theorem theorem21_online_steiner_binary_arrivals {ε : ℝ} (epsilon : 0 < ε) :
    ∃ (height : ℕ) (K : ℝ) (C k : ℕ), 0 < height ∧ 0 < K ∧
      (∀ {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
        (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)),
        (∀ d ∈ D, Reach G d.1 d.2) →
        let result := finSteinerBinaryServeWithWork G raw same height bits D
        result.graph ⊆ G ∧ Preserves G result.graph D ∧
          result.work + steinerBitBudget G height ≤ C * (n + G.card + raw.length + D.length + 1)^k) ∧
      (∀ {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
        (bits : Fin (steinerBitBudget G height) → Bool) {D E : List (Fin n × Fin n)},
        D <+: E → (∀ d ∈ E, Reach G d.1 d.2) →
          (finSteinerBinaryServeWithWork G raw same height bits D).graph ⊆
            (finSteinerBinaryServeWithWork G raw same height bits E).graph) ∧
      (∀ {n : ℕ} {G Z : Arcs (Fin n)} (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
        (D : List (Fin n × Fin n)), Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∑ bits : Fin (steinerBitBudget G height) → Bool,
          ((finSteinerBinaryServeWithWork G raw same height bits D).graph.card : ℝ)) /
          (Fintype.card (Fin (steinerBitBudget G height) → Bool) : ℝ) ≤ K * (n : ℝ) ^ (3/5 + ε) * Z.card) := by
  obtain ⟨height, hPos, K, kPos, expected⟩ := theorem21_online_steiner_binary_final_work_expected epsilon
  obtain ⟨C, k, cost⟩ := finSteinerBinaryServeWithWork_polynomial height
  refine ⟨height, K, C, k, hPos, kPos, ?_, ?_, ?_⟩
  · intro n G raw same bits D feasible
    obtain ⟨sub, serve⟩ := finSteinerBinaryServeWithWork_correct G raw same height bits D feasible
    exact ⟨sub, serve, cost G raw same bits D feasible⟩
  · intro n G raw same bits D E prefixOf feasible
    exact finSteinerBinaryServeWithWork_prefix G raw same height bits prefixOf feasible
  · intro n G Z raw same D sub reachable
    simp_rw [fun bits => (finSteinerBinaryServeWithWork_spec G raw same height bits D).2]
    exact expected raw same D sub reachable

/-- Compute the exact seed length, draw the word once, and prepare the
empty prefix. Subsequent arrivals reuse the stored array. -/
def finSteinerBinaryArrivalStartFromBitSource {n : ℕ} {m : Type → Type} [Monad m]
    (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height : ℕ)
    (nextBit : m Bool) : m (Vector Bool (steinerBitBudget G height) × FinSteinerBinaryArrivalState n) := do
  let budget := finSteinerBitBudgetWithWork G raw same height
  let sampled ← readSteinerSeedWithWork budget.1 nextBit
  let first := finSteinerBinaryArrivalStart G raw same height (fun i => sampled.1[i.val])
  pure (sampled.1, {first with work := first.work + (budget.2 + sampled.2 + 6)})

/-- A single arrival uses the same word drawn before service. -/
def finSteinerBinaryArrivalStepFromSeed {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (seed : Vector Bool (steinerBitBudget G height))
    (state : FinSteinerBinaryArrivalState n) (demand : Fin n × Fin n) : FinSteinerBinaryArrivalState n :=
  finSteinerBinaryArrivalStep G raw same height (fun i => seed[i.val]) state demand

/-- Run the sampled initialization once and invoke the array-backed
arrival operation for each demand in turn. -/
def finSteinerBinaryServeFromBitSource {n : ℕ} {m : Type → Type} [Monad m]
    (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height : ℕ)
    (nextBit : m Bool) (D : List (Fin n × Fin n)) : m (FinSteinerBinaryArrivalState n) := do
  let (seed, first) ← finSteinerBinaryArrivalStartFromBitSource G raw same height nextBit
  pure (D.foldl (finSteinerBinaryArrivalStepFromSeed G raw same height seed) first)

private theorem finSteinerBinaryArrivalFold_work_offset {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height : ℕ)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (state : FinSteinerBinaryArrivalState n) (extra : ℕ) :
    let step := finSteinerBinaryArrivalStep G raw same height bits
    let out := D.foldl step state
    D.foldl step {state with work := state.work + extra} = {out with work := out.work + extra} := by
  have addWork (s : FinSteinerBinaryArrivalState n) (demand : Fin n × Fin n) :
      let step := finSteinerBinaryArrivalStep G raw same height bits
      let next := step s demand
      step {s with work := s.work + extra} demand = {next with work := next.work + extra} := by
    simp only [finSteinerBinaryArrivalStep]
    congr 1
    omega
  induction D generalizing state with
  | nil => rfl
  | cons first rest ih =>
    dsimp only
    rw [List.foldl_cons, List.foldl_cons, addWork]
    exact ih _

/-- The seeded arrival run consumes the prescribed prefix, keeps the
same graph and history, and charges initialization once. -/
theorem finSteinerBinaryServeFromBitSource_stream {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height : ℕ)
    (stream : ℕ → Bool) (start : ℕ) (D : List (Fin n × Fin n)) :
    let size := steinerBitBudget G height
    let bits := fun i : Fin size => stream (start+i.val)
    let old := finSteinerBinaryServeWithWork G raw same height bits D
    let extra := (finSteinerBitBudgetWithWork G raw same height).2 + 6*size+11
    (finSteinerBinaryServeFromBitSource G raw same height (steinerBitStreamSource stream) D).run start =
      ({old with work := old.work + extra}, start+size) := by
  let size := steinerBitBudget G height
  let bits (i : Fin size) := stream (start+i.val)
  have read (i : Fin size) : (Vector.ofFn bits)[i.val] = bits i := by simp
  have sameStep : finSteinerBinaryArrivalStepFromSeed G raw same height (Vector.ofFn bits) =
      finSteinerBinaryArrivalStep G raw same height bits := by
    unfold finSteinerBinaryArrivalStepFromSeed
    rw [funext read]
  simp only [finSteinerBinaryServeFromBitSource, finSteinerBinaryArrivalStartFromBitSource, StateT.run_bind,
    readSteinerSeedWithWork_stream, StateT.run_pure]
  change (D.foldl (finSteinerBinaryArrivalStepFromSeed G raw same height (Vector.ofFn bits))
    { (finSteinerBinaryArrivalStart G raw same height (fun i => (Vector.ofFn bits)[i.val])) with
      work := (finSteinerBinaryArrivalStart G raw same height (fun i => (Vector.ofFn bits)[i.val])).work +
        ((finSteinerBitBudgetWithWork G raw same height).2 + (6*size+5)+6)}, start+size) = _
  simp only [sameStep, read, finSteinerBinaryServeWithWork]
  rw [finSteinerBinaryArrivalFold_work_offset]
  simp only [Nat.add_assoc]
  rfl

/-- Include computing and drawing the word in the fixed-height work bound. -/
theorem finSteinerBinaryServeFromBitSource_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
      (stream : ℕ → Bool) (start : ℕ) (D : List (Fin n × Fin n)),
      (∀ d ∈ D, Reach G d.1 d.2) →
      ((finSteinerBinaryServeFromBitSource G raw same height (steinerBitStreamSource stream) D).run start).1.work ≤
        C*(n+G.card+raw.length+D.length+1)^k := by
  obtain ⟨C, k, arrival⟩ := finSteinerBinaryServeWithWork_polynomial height
  obtain ⟨S, j, initialization⟩ := finSteinerSeedInitializationWorkBudget_polynomial height
  refine ⟨C+S, max k j, ?_⟩
  intro n G raw same stream start D feasible
  let size := n+G.card+raw.length+D.length+1
  have positive : 0 < size := by dsimp [size]; omega
  let bits (i : Fin (steinerBitBudget G height)) := stream (start+i.val)
  let out := finSteinerBinaryServeWithWork G raw same height bits D
  have arrived : out.work ≤ C*size^k :=
    (Nat.le_add_right _ _).trans (arrival G raw same bits D feasible)
  have budget := finSteinerBitBudgetWithWork_le G raw same height
  have draws := steinerBitBudget_polynomial G height
  simp only [Fintype.card_fin] at draws
  have initialized : (finSteinerBitBudgetWithWork G raw same height).2 + 6*steinerBitBudget G height+11 ≤
      S*size^j := by
    apply le_trans _ (initialization n G.card raw.length D.length)
    unfold finSteinerSeedInitializationWorkBudget
    omega
  have first := arrived.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_right positive (le_max_left k j)))
  have second := initialized.trans (Nat.mul_le_mul_left S (Nat.pow_le_pow_right positive (le_max_right k j)))
  rw [finSteinerBinaryServeFromBitSource_stream]
  change out.work+((finSteinerBitBudgetWithWork G raw same height).2+6*steinerBitBudget G height+11) ≤ _
  exact (Nat.add_le_add first second).trans_eq (Nat.add_mul _ _ _).symm

open MeasureTheory
open scoped ENNReal

/-- Theorem 21 with initialization from a single stream of fair bits.
The run consumes its exact fixed budget before service, works on every
scripted stream, and keeps the competitive expectation under fair bits. -/
theorem theorem21_online_steiner_sampled_arrivals {ε : ℝ} (epsilon : 0 < ε) :
    ∃ (height : ℕ) (K : ℝ) (C k : ℕ), 0 < height ∧ 0 < K ∧
      (∀ {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
        (stream : ℕ → Bool) (D : List (Fin n × Fin n)),
        (∀ d ∈ D, Reach G d.1 d.2) →
        let result := (finSteinerBinaryServeFromBitSource G raw same height (steinerBitStreamSource stream) D).run 0
        result.2 = steinerBitBudget G height ∧ result.1.graph ⊆ G ∧ Preserves G result.1.graph D ∧
          result.1.work ≤ C*(n+G.card+raw.length+D.length+1)^k) ∧
      (∀ {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
        (stream : ℕ → Bool) {D E : List (Fin n × Fin n)},
        D <+: E → (∀ d ∈ E, Reach G d.1 d.2) →
          ((finSteinerBinaryServeFromBitSource G raw same height (steinerBitStreamSource stream) D).run 0).1.graph ⊆
            ((finSteinerBinaryServeFromBitSource G raw same height (steinerBitStreamSource stream) E).run 0).1.graph) ∧
      (∀ {n : ℕ} {G Z : Arcs (Fin n)} (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
        (D : List (Fin n × Fin n)), Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∫⁻ stream, (((finSteinerBinaryServeFromBitSource G raw same height
          (steinerBitStreamSource stream) D).run 0).1.graph.card : ℝ≥0∞) ∂fairBitMeasure) ≤
            ENNReal.ofReal (K * (n : ℝ) ^ (3/5 + ε) * Z.card)) := by
  obtain ⟨height, K, _, _, high, positive, correct, monotone, expected⟩ := theorem21_online_steiner_binary_arrivals epsilon
  obtain ⟨C, k, cost⟩ := finSteinerBinaryServeFromBitSource_polynomial height
  refine ⟨height, K, C, k, high, positive, ?_, ?_, ?_⟩
  · intro n G raw same stream D feasible
    let bits (i : Fin (steinerBitBudget G height)) := stream (0+i.val)
    obtain ⟨subset, serve, _⟩ := correct G raw same bits D feasible
    have bound := cost G raw same stream 0 D feasible
    dsimp only
    rw [finSteinerBinaryServeFromBitSource_stream] at bound ⊢
    exact ⟨Nat.zero_add _, subset, serve, bound⟩
  · intro n G raw same stream D E prior feasible
    let bits (i : Fin (steinerBitBudget G height)) := stream (0+i.val)
    rw [finSteinerBinaryServeFromBitSource_stream, finSteinerBinaryServeFromBitSource_stream]
    exact monotone G raw same bits prior feasible
  · intro n G Z raw same D sub feasible
    let loss (bits : Fin (steinerBitBudget G height) → Bool) :=
      (finSteinerBinaryServeWithWork G raw same height bits D).graph.card
    have agreement (stream : ℕ → Bool) :
        ((finSteinerBinaryServeFromBitSource G raw same height (steinerBitStreamSource stream) D).run 0).1.graph.card =
          loss (fairBitPrefix (steinerBitBudget G height) stream) := by
      rw [finSteinerBinaryServeFromBitSource_stream]
      simp only [loss, Nat.zero_add]
      rfl
    simp_rw [agreement]
    rw [fairBitPrefix_lintegral_eq]
    exact ENNReal.ofReal_le_ofReal (expected raw same D sub feasible)

end OnlineReachabilityPreservers
