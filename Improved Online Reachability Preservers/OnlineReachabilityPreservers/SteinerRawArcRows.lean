import OnlineReachabilityPreservers.SteinerBinaryArrivals

/-! Prepare the graph directly from its raw arc list before sampling. -/

namespace OnlineReachabilityPreservers

private def scanArcRowsWithWork {n : ℕ} (needle : Fin n × Fin n) :
    List (Fin n × Fin n) → Bool × ℕ
  | [] => (false, 2)
  | arc::rest =>
    if needle = arc then (true, 5) else
      let tail := scanArcRowsWithWork needle rest
      (tail.1, tail.2+5)

private theorem scanArcRowsWithWork_spec {n : ℕ} (needle : Fin n × Fin n)
    (rows : List (Fin n × Fin n)) :
    let out := scanArcRowsWithWork needle rows
    (out.1 = true ↔ needle ∈ rows) ∧ out.2 ≤ 5*rows.length+2 := by
  induction rows with
  | nil => simp [scanArcRowsWithWork]
  | cons arc rest ih =>
    by_cases equal : needle = arc
    · simp [scanArcRowsWithWork,equal]
      omega
    · rw [scanArcRowsWithWork,ite_eq_right equal]
      refine ⟨?_,?_⟩
      · simpa only [List.mem_cons,equal,false_or] using ih.1
      · have bound := ih.2
        simp only [List.length_cons]
        omega

private def dedupArcRowsWithWork {n : ℕ} :
    List (Fin n × Fin n) → {rows : List (Fin n × Fin n) // rows.Nodup} × ℕ
  | [] => (⟨[],by simp⟩,2)
  | arc::rest =>
    let tail := dedupArcRowsWithWork rest
    let scan := scanArcRowsWithWork arc tail.1.val
    if found : scan.1 = true then
      (tail.1,tail.2+scan.2+6)
    else
      (⟨arc::tail.1.val,List.nodup_cons.mpr
        ⟨fun member => found ((scanArcRowsWithWork_spec arc tail.1.val).1.mpr member),tail.1.property⟩⟩,
        tail.2+scan.2+8)

private theorem dedupArcRowsWithWork_spec {n : ℕ} (rows : List (Fin n × Fin n)) :
    let out := dedupArcRowsWithWork rows
    (∀ arc, arc ∈ out.1.val ↔ arc ∈ rows) ∧
      out.1.val.length ≤ rows.length ∧ out.2 ≤ 20*(rows.length+1)^2 := by
  induction rows with
  | nil => simp [dedupArcRowsWithWork]
  | cons arc rest ih =>
    let tail := dedupArcRowsWithWork rest
    let scan := scanArcRowsWithWork arc tail.1.val
    have members (e : Fin n × Fin n) : e ∈ tail.1.val ↔ e ∈ rest := ih.1 e
    have size : tail.1.val.length ≤ rest.length := ih.2.1
    have tailWork : tail.2 ≤ 20*(rest.length+1)^2 := ih.2.2
    have scanWork : scan.2 ≤ 5*rest.length+2 :=
      (scanArcRowsWithWork_spec arc tail.1.val).2.trans (by omega)
    have work : tail.2+scan.2+8 ≤ 20*((arc::rest).length+1)^2 := by
      have bound : tail.2+scan.2+8 ≤ 20*(rest.length+1)^2+5*rest.length+10 := by omega
      refine bound.trans ?_
      rw [List.length_cons]
      nlinarith
    by_cases found : scan.1 = true
    · have built : dedupArcRowsWithWork (arc::rest) = (tail.1,tail.2+scan.2+6) := by
        rw [dedupArcRowsWithWork]
        exact dite_eq_left found
      simp only [built]
      have kept := (scanArcRowsWithWork_spec arc tail.1.val).1.mp found
      refine ⟨?_,size.trans (Nat.le_succ _),by omega⟩
      intro e
      rw [members e,List.mem_cons]
      exact ⟨Or.inr,fun disj => disj.elim (fun eq => eq ▸ (members arc).mp kept) id⟩
    · let row : {rows : List (Fin n × Fin n) // rows.Nodup} := ⟨arc::tail.1.val,List.nodup_cons.mpr
        ⟨fun member => found ((scanArcRowsWithWork_spec arc tail.1.val).1.mpr member),tail.1.property⟩⟩
      have built : dedupArcRowsWithWork (arc::rest) = (row,tail.2+scan.2+8) := by
        rw [dedupArcRowsWithWork]
        exact dite_eq_right found
      simp only [built]
      refine ⟨?_,Nat.succ_le_succ size,work⟩
      intro e
      change e ∈ arc::tail.1.val ↔ e ∈ arc::rest
      simp only [List.mem_cons,members e]

/-- Build the graph using only the raw arc rows. The tally counts scans,
list construction, and equality tests on finite labels. -/
def prepareSteinerArcRowsWithWork {n : ℕ} (raw : List (Fin n × Fin n)) :
    Arcs (Fin n) × ℕ :=
  let dedup := dedupArcRowsWithWork raw
  (⟨(dedup.1.val : Multiset (Fin n × Fin n)),by simpa using dedup.1.property⟩,dedup.2+3)

theorem prepareSteinerArcRowsWithWork_spec {n : ℕ} (raw : List (Fin n × Fin n)) :
    let out := prepareSteinerArcRowsWithWork raw
    raw.toFinset = out.1 ∧ out.1.card ≤ raw.length ∧ out.2 ≤ 23*(raw.length+1)^2 := by
  let dedup := dedupArcRowsWithWork raw
  obtain ⟨members,size,work⟩ := dedupArcRowsWithWork_spec raw
  have eq : raw.toFinset = (prepareSteinerArcRowsWithWork raw).1 := by
    ext arc
    change arc ∈ raw.toFinset ↔ arc ∈ (dedup.1.val : Multiset (Fin n × Fin n))
    rw [List.mem_toFinset,Multiset.mem_coe]
    exact (members arc).symm
  refine ⟨eq,size,?_⟩
  change dedup.2+3 ≤ 23*(raw.length+1)^2
  have overhead : 3 ≤ 3*(raw.length+1)^2 := by nlinarith
  change dedup.2 ≤ 20*(raw.length+1)^2 at work
  omega

/-- Run the sampled solver from a raw arc list, building its graph once
and adding the ingestion tally to the returned state. -/
def finSteinerBinaryServeFromArcRowsWithWork {n : ℕ} {m : Type → Type} [Monad m]
    (raw : List (Fin n × Fin n)) (height : ℕ) (nextBit : m Bool) (D : List (Fin n × Fin n)) :
    m (FinSteinerBinaryArrivalState n) := do
  let graph := prepareSteinerArcRowsWithWork raw
  let result ← finSteinerBinaryServeFromBitSource graph.1 raw
    (prepareSteinerArcRowsWithWork_spec raw).1 height nextBit D
  pure { result with work := result.work+graph.2+4 }

theorem finSteinerBinaryServeFromArcRowsWithWork_stream {n : ℕ}
    (raw : List (Fin n × Fin n)) (height : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (D : List (Fin n × Fin n)) :
    let graph := prepareSteinerArcRowsWithWork raw
    let expected := (finSteinerBinaryServeFromBitSource graph.1 raw
      (prepareSteinerArcRowsWithWork_spec raw).1 height (steinerBitStreamSource stream) D).run start
    (finSteinerBinaryServeFromArcRowsWithWork raw height (steinerBitStreamSource stream) D).run start =
      ({ expected.1 with work := expected.1.work+graph.2+4 },expected.2) := by
  rfl

theorem finSteinerBinaryServeFromArcRows_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (raw : List (Fin n × Fin n)) (stream : ℕ → Bool) (start : ℕ)
      (D : List (Fin n × Fin n)), (∀ d ∈ D, Reach raw.toFinset d.1 d.2) →
      ((finSteinerBinaryServeFromArcRowsWithWork raw height (steinerBitStreamSource stream) D).run start).1.work ≤
        C*(n+raw.length+D.length+1)^k := by
  obtain ⟨C,k,replay⟩ := finSteinerBinaryServeFromBitSource_polynomial height
  refine ⟨C*2^k+27,max k 2,?_⟩
  intro n raw stream start D feasible
  let graph := prepareSteinerArcRowsWithWork raw
  let size := n+raw.length+D.length+1
  have positive : 0 < size := by dsimp [size]; omega
  obtain ⟨same,cardBound,buildBound⟩ := prepareSteinerArcRowsWithWork_spec raw
  have sizeBound : n+graph.1.card+raw.length+D.length+1 ≤ 2*size := by
    change graph.1.card ≤ raw.length at cardBound
    dsimp [size]
    omega
  have feasibleGraph : ∀ d ∈ D, Reach graph.1 d.1 d.2 := by rw [← same]; exact feasible
  have replayCost := replay graph.1 raw same stream start D feasibleGraph
  have paidReplay : ((finSteinerBinaryServeFromBitSource graph.1 raw same height
      (steinerBitStreamSource stream) D).run start).1.work ≤ (C*2^k)*size^(max k 2) := calc
    _ ≤ C*(n+graph.1.card+raw.length+D.length+1)^k := replayCost
    _ ≤ C*(2*size)^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left sizeBound _)
    _ = (C*2^k)*size^k := by rw [Nat.mul_pow,Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_left _ _))
  have paidBuild : graph.2+4 ≤ 27*size^(max k 2) := by
    have bound : graph.2 ≤ 23*size^2 :=
      buildBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [size]; omega) _))
    have posSq : 1 ≤ size^2 := Nat.one_le_pow _ _ positive
    have allowance : graph.2+4 ≤ 27*size^2 := by omega
    exact allowance.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (le_max_right _ _)))
  rw [finSteinerBinaryServeFromArcRowsWithWork_stream]
  change ((finSteinerBinaryServeFromBitSource graph.1 raw same height
    (steinerBitStreamSource stream) D).run start).1.work + graph.2+4 ≤ _
  rw [Nat.add_assoc, Nat.add_mul]
  exact Nat.add_le_add paidReplay paidBuild

open MeasureTheory
open scoped ENNReal

/-- Theorem 21 from raw arc rows. The recorded work includes building
the graph, and one sampled word serves all online prefixes. -/
theorem theorem21_online_steiner_sampled_arc_rows {ε : ℝ} (epsilon : 0 < ε) :
    ∃ (height : ℕ) (K : ℝ) (C k : ℕ), 0 < height ∧ 0 < K ∧
      (∀ {n : ℕ} (raw : List (Fin n × Fin n)) (stream : ℕ → Bool) (D : List (Fin n × Fin n)),
        (∀ d ∈ D, Reach raw.toFinset d.1 d.2) →
        let result := (finSteinerBinaryServeFromArcRowsWithWork raw height (steinerBitStreamSource stream) D).run 0
        result.2 = steinerBitBudget raw.toFinset height ∧
          result.1.graph ⊆ raw.toFinset ∧ Preserves raw.toFinset result.1.graph D ∧
          result.1.work ≤ C*(n+raw.length+D.length+1)^k) ∧
      (∀ {n : ℕ} (raw : List (Fin n × Fin n)) (stream : ℕ → Bool) {D E : List (Fin n × Fin n)},
        D <+: E → (∀ d ∈ E, Reach raw.toFinset d.1 d.2) →
          ((finSteinerBinaryServeFromArcRowsWithWork raw height (steinerBitStreamSource stream) D).run 0).1.graph ⊆
            ((finSteinerBinaryServeFromArcRowsWithWork raw height (steinerBitStreamSource stream) E).run 0).1.graph) ∧
      (∀ {n : ℕ} {Z : Arcs (Fin n)} (raw : List (Fin n × Fin n)) (D : List (Fin n × Fin n)),
        Z ⊆ raw.toFinset → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∫⁻ stream, (((finSteinerBinaryServeFromArcRowsWithWork raw height
          (steinerBitStreamSource stream) D).run 0).1.graph.card : ℝ≥0∞) ∂fairBitMeasure) ≤
            ENNReal.ofReal (K*(n:ℝ)^(3/5+ε)*Z.card)) := by
  obtain ⟨height,K,_,_,heightPos,constantPos,correct,monotone,expected⟩ :=
    theorem21_online_steiner_sampled_arrivals epsilon
  obtain ⟨C,k,cost⟩ := finSteinerBinaryServeFromArcRows_polynomial height
  refine ⟨height,K,C,k,heightPos,constantPos,?_,?_,?_⟩
  · intro n raw stream D feasible
    let G := (prepareSteinerArcRowsWithWork raw).1
    have same : raw.toFinset = G := (prepareSteinerArcRowsWithWork_spec raw).1
    have feasibleGraph : ∀ d ∈ D, Reach G d.1 d.2 := by rw [← same]; exact feasible
    obtain ⟨bits,sub,preserves,_⟩ := correct G raw same stream D feasibleGraph
    refine ⟨?_,?_,?_,cost raw stream 0 D feasible⟩
    · rw [finSteinerBinaryServeFromArcRowsWithWork_stream]
      exact bits.trans (congrArg (fun graphs => steinerBitBudget graphs height) same.symm)
    · rw [finSteinerBinaryServeFromArcRowsWithWork_stream]
      intro arc member
      exact same.symm ▸ sub member
    · rw [finSteinerBinaryServeFromArcRowsWithWork_stream]
      intro demand member
      exact (preserves demand member).trans (by rw [same])
  · intro n raw stream D E prefixOf feasible
    let G := (prepareSteinerArcRowsWithWork raw).1
    have same : raw.toFinset = G := (prepareSteinerArcRowsWithWork_spec raw).1
    have feasibleGraph : ∀ d ∈ E, Reach G d.1 d.2 := by rw [← same]; exact feasible
    rw [finSteinerBinaryServeFromArcRowsWithWork_stream,finSteinerBinaryServeFromArcRowsWithWork_stream]
    exact monotone G raw same stream prefixOf feasibleGraph
  · intro n Z raw D sub feasible
    let G := (prepareSteinerArcRowsWithWork raw).1
    have same : raw.toFinset = G := (prepareSteinerArcRowsWithWork_spec raw).1
    have subGraph : Z ⊆ G := same ▸ sub
    simpa only [finSteinerBinaryServeFromArcRowsWithWork_stream] using expected raw same D subGraph feasible

end OnlineReachabilityPreservers
