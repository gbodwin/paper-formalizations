import OnlineReachabilityPreservers.SteinerBinaryReplayCompetitive

/-! A metered entry point that prepares the arc count and reports the final graph. -/

namespace OnlineReachabilityPreservers

private theorem foldCount_eq {A : Type*} (rows : List A) (start : ℕ) :
    rows.foldl (fun count _ => count+1) start = start+rows.length := by
  induction rows generalizing start with
  | nil => simp
  | cons row rest ih =>
    rw [List.foldl_cons,ih,List.length_cons]
    omega

private def countReplayArcRowsWithWork {A : Type*} (rows : List A) : ℕ × ℕ :=
  let count := rows.foldl (fun count _ => count+1) 0
  (count,4*count+3)

private theorem countReplayArcRowsWithWork_spec {A : Type*} (rows : List A) :
    countReplayArcRowsWithWork rows = (rows.length,4*rows.length+3) := by
  simp only [countReplayArcRowsWithWork,foldCount_eq,Nat.zero_add]

private def countReplayArcSetWithWork {A : Type*} (arcs : Multiset A) : ℕ × ℕ :=
  Quot.lift countReplayArcRowsWithWork (fun first second same => by
    rw [countReplayArcRowsWithWork_spec,countReplayArcRowsWithWork_spec,same.length_eq]) arcs

private theorem countReplayArcSetWithWork_spec {A : Type*} (arcs : Multiset A) :
    countReplayArcSetWithWork arcs = (arcs.card,4*arcs.card+3) := by
  refine Quot.ind (β := fun values : Multiset A => countReplayArcSetWithWork values =
    (values.card,4*values.card+3)) ?_ arcs
  intro rows
  exact countReplayArcRowsWithWork_spec rows

private def finishReplayRecordsFromWithWork {A : Type*} (start : A × ℕ × ℕ) (rows : List (A × ℕ)) : A × ℕ × ℕ :=
  rows.foldl (fun total row => (row.1,total.2.1+row.2,total.2.2+6)) start

private theorem finishReplayRecordsFromWithWork_spec {A : Type*} (start : A × ℕ × ℕ) (rows : List (A × ℕ)) :
    finishReplayRecordsFromWithWork start rows =
      ((rows.map Prod.fst).getLastD start.1,start.2.1+(rows.map Prod.snd).sum,start.2.2+6*rows.length) := by
  induction rows generalizing start with
  | nil => simp [finishReplayRecordsFromWithWork]
  | cons row rest ih =>
    unfold finishReplayRecordsFromWithWork
    rw [List.foldl_cons,← finishReplayRecordsFromWithWork,ih]
    simp only [List.map_cons,List.getLastD_cons,List.sum_cons,List.length_cons,add_assoc,Nat.mul_succ]
    rw [Nat.add_comm 6 (6*rest.length)]

/-- The binary replay with an input arc-list count and a final pass that
reports the last graph together with all recorded work. -/
def finSteinerBinaryFinalGraphWithWork {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) : Arcs (Fin n) × ℕ :=
  let count := countReplayArcSetWithWork G.val
  have exactCount : count.1 = G.card := congrArg Prod.fst (countReplayArcSetWithWork_spec G.val)
  let out := completeFinSteinerReplayWithBinaryPhasesWork G raw same height count.1 exactCount bits D
  let base := out.1.1.1
  let report := finishReplayRecordsFromWithWork (∅,0,3) base.1.1
  (report.1,report.2.1+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1+
    count.2+report.2.2+12)

/-- Add the arc-count preparation and final record scan to the replay allowance. -/
def finSteinerBinaryFinalGraphWorkBudget (n m raw h p : ℕ) : ℕ :=
  finSteinerBinaryPhasesReplaySizeBudget n m raw h p+(4*m+3)+(3+6*(p+1))+12

set_option maxHeartbeats 900000 in
/-- The final result agrees with the executable competitive graph and its
tally includes the added work for obtaining the count and reading the records. -/
theorem finSteinerBinaryFinalGraphWithWork_spec {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) (bits : Fin (steinerBitBudget G height) → Bool)
    (D : List (Fin n × Fin n)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := finSteinerBinaryFinalGraphWithWork G raw same height bits D
    out.1 = finSteinerBinaryFinalGraph G raw same height bits D ∧
      out.2 ≤ finSteinerBinaryFinalGraphWorkBudget n G.card raw.length height D.length := by
  let count := countReplayArcSetWithWork G.val
  have countEq : count.1 = G.card := congrArg Prod.fst (countReplayArcSetWithWork_spec G.val)
  have countWork : count.2 = 4*G.card+3 := congrArg Prod.snd (countReplayArcSetWithWork_spec G.val)
  let out := completeFinSteinerReplayWithBinaryPhasesWork G raw same height G.card rfl bits D
  let base := out.1.1.1
  let records := base.1.1
  have reset (m : ℕ) (exactCount : m = G.card) :
      completeFinSteinerReplayWithBinaryPhasesWork G raw same height m exactCount bits D = out := by
    subst m
    rfl
  unfold finSteinerBinaryFinalGraphWithWork
  dsimp only
  rw [reset _ countEq]
  obtain ⟨graphs,_,budget⟩ := completeFinSteinerReplayWithBinaryPhasesWork_input_sizes G raw same height G.card rfl bits D feasible
  have length : records.length = D.length+1 := by
    have lengths := congrArg List.length graphs
    simpa only [List.length_map,List.length_inits] using lengths
  have report := finishReplayRecordsFromWithWork_spec ((∅ : Arcs (Fin n)),0,3) records
  change (finishReplayRecordsFromWithWork (∅,0,3) records).1 = _ ∧
    (finishReplayRecordsFromWithWork (∅,0,3) records).2.1+base.1.2.1+base.1.2.2.1+base.1.2.2.2+
      base.2+out.1.1.2+out.1.2+out.2.1+count.2+
      (finishReplayRecordsFromWithWork (∅,0,3) records).2.2+12 ≤ _
  rw [report,countWork,length]
  refine ⟨?_,?_⟩
  · change (records.map Prod.fst).getLastD ∅ = (records.getLastD (∅,0)).1
    exact List.getLastD_map (l := records) (a := (∅,0))
  · let spent := (records.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+
      out.1.1.2+out.1.2+out.2.1
    have metered : spent ≤ finSteinerBinaryPhasesReplaySizeBudget n G.card raw.length height D.length := budget
    dsimp only
    rw [Nat.zero_add]
    change spent+(4*G.card+3)+(3+6*(D.length+1))+12 ≤ _
    unfold finSteinerBinaryFinalGraphWorkBudget
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right metered _) _) _

/-- The metered final graph has the same competitive rate for uniform
fixed-length seeds on any fixed feasible trace. -/
theorem theorem21_online_steiner_binary_final_work_expected {ε : ℝ} (epsilon : 0 < ε) :
    ∃ height : ℕ, 0 < height ∧ ∃ K : ℝ, 0 < K ∧
      ∀ {n : ℕ} {G Z : Arcs (Fin n)} (raw : List (Fin n × Fin n)) (same : raw.toFinset = G)
        (D : List (Fin n × Fin n)), Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∑ bits : Fin (steinerBitBudget G height) → Bool,
          (((finSteinerBinaryFinalGraphWithWork G raw same height bits D).1).card : ℝ)) /
          (Fintype.card (Fin (steinerBitBudget G height) → Bool) : ℝ) ≤ K * (n : ℝ) ^ (3/5 + ε) * Z.card := by
  obtain ⟨height,hPos,K,Kpos,expected⟩ := theorem21_online_steiner_binary_replay_expected epsilon
  refine ⟨height,hPos,K,Kpos,?_⟩
  intro n G Z raw same D sub reaches
  have feasible (d : Fin n × Fin n) (inside : d ∈ D) : Reach G d.1 d.2 := reach_mono sub (reaches d inside)
  simp_rw [fun bits => (finSteinerBinaryFinalGraphWithWork_spec G raw same height bits D feasible).1]
  exact expected raw same D sub reaches

/-- Compute the exact seed length from the graph and height before any bits
or demands are supplied. The already checked weighted preparation provides
the forest scale and its recorded work. -/
def finSteinerBitBudgetWithWork {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) : {b : ℕ // b = steinerBitBudget G height} × ℕ :=
  let count := countReplayArcSetWithWork G.val
  have countEq : count.1 = G.card := congrArg Prod.fst (countReplayArcSetWithWork_spec G.val)
  let pre := prepareFinSteinerWeightedForSeedWithWordWork G raw same height
  let scaleWidth := bitLengthWithWork pre.1.1.val
  let width := max 1 scaleWidth.1
  have widthEq : width = (forestScale G height).log2+1 := by
    dsimp only [width, scaleWidth]
    rw [(bitLengthWithWork_spec _).1, max_size_eq_log2_add_one, pre.1.1.property]
  let sizes := prepareSteinerSeedDecoderSizesWithWork G height width n count.1 (by simp) countEq
  (⟨steinerBitBudgetFromDecoderSizes sizes.1, steinerBitBudgetFromDecoderSizes_eq widthEq sizes.1⟩,
    count.2 + pre.1.2.2.1 + pre.1.2.2.2.1 + pre.2 + scaleWidth.2 + sizes.2 + 20)

/-- Recorded work to compute the budget, including the hop table, forest
list, weighted plan, and size arithmetic. -/
def finSteinerBitBudgetWorkBound (n m raw height : ℕ) : ℕ :=
  (4*m+3) + (distanceTableListWorkPolynomial n raw+8*n+9) +
    (heightForestListDistanceWorkPolynomial n height 1+5) + finSteinerWeightPlanWorkPolynomial n height +
    (7*(1+n*((2*n)*((height+1)*n^height))^2)+3) + (30*n+7*m+5*height+57) + 20

theorem finSteinerBitBudgetWithWork_le {n : ℕ} (G : Arcs (Fin n)) (raw : List (Fin n × Fin n))
    (same : raw.toFinset = G) (height : ℕ) :
    (finSteinerBitBudgetWithWork G raw same height).2 ≤ finSteinerBitBudgetWorkBound n G.card raw.length height := by
  let count := countReplayArcSetWithWork G.val
  have countEq : count.1 = G.card := congrArg Prod.fst (countReplayArcSetWithWork_spec G.val)
  have countWork : count.2 = 4*G.card+3 := congrArg Prod.snd (countReplayArcSetWithWork_spec G.val)
  let pre := prepareFinSteinerWeightedForSeedWithWordWork G raw same height
  let scaleWidth := bitLengthWithWork pre.1.1.val
  let width := max 1 scaleWidth.1
  let sizes := prepareSteinerSeedDecoderSizesWithWork G height width n count.1 (by simp) countEq
  have budget : forestScale G height ≤ 1+n*((2*n)*((height+1)*n^height))^2 := by
    have scale := forestNetworkScale_le G height
    rw [Fintype.card_fin] at scale
    have vertices : Fintype.card (HeightForestVertex (Fin n) height) ≤ (2*n)*((height+1)*n^height) := by
      cases isEmpty_or_nonempty (Fin n) with
      | inl empty => simp [HeightForestVertex]
      | inr nonempty => simpa only [Fintype.card_fin, Nat.mul_comm n 2] using heightForestVertex_card_le (Fin n) height
    apply scale.trans (max_le (Nat.le_add_right _ _) ?_)
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left vertices 2)).trans (Nat.le_add_left _ _)
  have scaleWork : scaleWidth.2 ≤ 7*(1+n*((2*n)*((height+1)*n^height))^2)+3 := by
    change (bitLengthWithWork pre.1.1.val).2 ≤ _
    rw [pre.1.1.property]
    exact (bitLengthWork_le _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 7 budget) 3)
  obtain ⟨preEq, planWork⟩ := prepareFinSteinerWeightedForSeedWithWordWork_spec G raw same height
  obtain ⟨_, distanceWork, forestWork⟩ := prepareFinSteinerForSeedWithWordWork_spec G raw same height
  rw [← preEq] at distanceWork forestWork
  have sizesWork : sizes.2 ≤ 30*n+7*G.card+5*height+57 := by
    have h := prepareSteinerSeedDecoderSizesWithWork_le G height width n count.1 (by simp) countEq
    exact h.trans_eq (congrArg (fun m => 30*n+7*m+5*height+57) countEq)
  change count.2 + pre.1.2.2.1 + pre.1.2.2.2.1 + pre.2 + scaleWidth.2 + sizes.2 + 20 ≤ _
  rw [countWork]
  unfold finSteinerBitBudgetWorkBound
  change pre.1.2.2.1 ≤ _ at distanceWork
  change pre.1.2.2.2.1 ≤ _ at forestWork
  change pre.2 ≤ _ at planWork
  omega

/-- Fill a fixed-size array in order, calling the supplied bit action once
for each position. Work charges one draw and one append in each iteration. -/
def readSteinerSeedWithWork {size : ℕ} {m : Type → Type} [Monad m]
    (count : {b : ℕ // b = size}) (nextBit : m Bool) : m (Vector Bool size × ℕ) := do
  let word ← Vector.ofFnM (fun _ : Fin count.val => nextBit)
  pure (word.cast count.property, 6*count.val+5)

/-- A deterministic stream supplies the next bit and advances its cursor. -/
def steinerBitStreamSource (stream : ℕ → Bool) : StateM ℕ Bool :=
  fun position => (stream position, position+1)

private theorem steinerBitStreamSource_draws (stream : ℕ → Bool) (size start : ℕ) :
    (Vector.ofFnM (fun _ : Fin size => steinerBitStreamSource stream)).run start =
      (Vector.ofFn (fun i : Fin size => stream (start+i.val)), start+size) := by
  induction size generalizing start with
  | zero =>
    rw [Vector.ofFnM_zero]
    have emptyWord : (Vector.ofFn fun i : Fin 0 => stream (start+i.val)) = #v[] := by
      ext i inside
      omega
    rw [emptyWord]
    rfl
  | succ size ih =>
    rw [Vector.ofFnM_succ]
    simp only [StateT.run_bind, StateT.run_pure, ih]
    change ((Vector.ofFn (fun i : Fin size => stream (start+i.val))).push (stream (start+size)),
      start+size+1) = _
    rw [Vector.ofFn_succ]
    rfl

/-- The sampler returns the next consecutive bits, consumes exactly the
specified count, and leaves the rest of the source available. -/
theorem readSteinerSeedWithWork_stream {size : ℕ} (count : {b : ℕ // b = size})
    (stream : ℕ → Bool) (start : ℕ) :
    (readSteinerSeedWithWork count (steinerBitStreamSource stream)).run start =
      ((Vector.ofFn (fun i : Fin size => stream (start+i.val)), 6*size+5), start+size) := by
  obtain ⟨n, rfl⟩ := count
  simp only [readSteinerSeedWithWork, StateT.run_bind, steinerBitStreamSource_draws, StateT.run_pure, Vector.cast_rfl]
  rfl

end OnlineReachabilityPreservers
