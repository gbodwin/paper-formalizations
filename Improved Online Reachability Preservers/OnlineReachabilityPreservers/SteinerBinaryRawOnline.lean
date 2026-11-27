import OnlineReachabilityPreservers.SteinerRawArcRows

/-! Run the sampled arrival solver after metered binary arc preparation. -/

namespace OnlineReachabilityPreservers

/-- Prepare the raw arc list using cached binary comparisons, then draw
one seed for the arrival solver on the resulting graph. -/
def finSteinerBinaryServeFromBinaryArcRowsWithWork {n : ℕ} {m : Type → Type} [Monad m]
    (raw : List (Fin n × Fin n)) (height : ℕ) (nextBit : m Bool) (D : List (Fin n × Fin n)) :
    m (FinSteinerBinaryArrivalState n) := do
  let graph := prepareSteinerBinaryArcRowsWithWork raw
  let result ← finSteinerBinaryServeFromBitSource graph.1 raw
    (prepareSteinerBinaryArcRowsWithWork_spec raw).1 height nextBit D
  pure { result with work := result.work+graph.2+4 }

private theorem finSteinerBinaryServeFromBinaryArcRowsWithWork_stream {n : ℕ}
    (raw : List (Fin n × Fin n)) (height : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (D : List (Fin n × Fin n)) :
    let graph := prepareSteinerBinaryArcRowsWithWork raw
    let expected := (finSteinerBinaryServeFromBitSource graph.1 raw
      (prepareSteinerBinaryArcRowsWithWork_spec raw).1 height (steinerBitStreamSource stream) D).run start
    (finSteinerBinaryServeFromBinaryArcRowsWithWork raw height (steinerBitStreamSource stream) D).run start =
      ({ expected.1 with work := expected.1.work+graph.2+4 },expected.2) := by
  rfl

private theorem finSteinerBinaryServeFromBitSource_graph_congr {n : ℕ}
    {G H : Arcs (Fin n)} (equal : G = H) (raw : List (Fin n × Fin n))
    (left : raw.toFinset = G) (right : raw.toFinset = H) (height : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (D : List (Fin n × Fin n)) :
    (finSteinerBinaryServeFromBitSource G raw left height (steinerBitStreamSource stream) D).run start =
      (finSteinerBinaryServeFromBitSource H raw right height (steinerBitStreamSource stream) D).run start := by
  subst H
  rfl

/-- Binary preparation keeps the entire sampled computation, including
stream consumption and history. The recorded work exchanges exactly
the two preparation charges. -/
theorem finSteinerBinaryServeFromBinaryArcRows_refines {n : ℕ}
    (raw : List (Fin n × Fin n)) (height : ℕ) (stream : ℕ → Bool) (start : ℕ)
    (D : List (Fin n × Fin n)) :
    let result := (finSteinerBinaryServeFromBinaryArcRowsWithWork raw height
      (steinerBitStreamSource stream) D).run start
    let old := (finSteinerBinaryServeFromArcRowsWithWork raw height (steinerBitStreamSource stream) D).run start
    result.1.graph = old.1.graph ∧ result.1.history = old.1.history ∧ result.2 = old.2 ∧
      result.1.work+(prepareSteinerArcRowsWithWork raw).2 =
        old.1.work+(prepareSteinerBinaryArcRowsWithWork raw).2 := by
  have binaryGraph := (prepareSteinerBinaryArcRowsWithWork_spec raw).1
  have primitiveGraph := (prepareSteinerArcRowsWithWork_spec raw).1
  have equal := finSteinerBinaryServeFromBitSource_graph_congr (binaryGraph.symm.trans primitiveGraph)
    raw binaryGraph primitiveGraph height stream start D
  dsimp only
  rw [finSteinerBinaryServeFromBinaryArcRowsWithWork_stream,finSteinerBinaryServeFromArcRowsWithWork_stream,equal]
  simp only [true_and]
  omega

theorem finSteinerBinaryServeFromBinaryArcRows_polynomial (height : ℕ) :
    ∃ C k : ℕ, ∀ {n : ℕ} (raw : List (Fin n × Fin n)) (stream : ℕ → Bool) (start : ℕ)
      (D : List (Fin n × Fin n)), (∀ d ∈ D, Reach raw.toFinset d.1 d.2) →
      ((finSteinerBinaryServeFromBinaryArcRowsWithWork raw height (steinerBitStreamSource stream) D).run start).1.work ≤
        C*(n+raw.length+D.length+1)^k := by
  obtain ⟨C,k,original⟩ := finSteinerBinaryServeFromArcRows_polynomial height
  refine ⟨C+100,max k 3,?_⟩
  intro n raw stream start D feasible
  let size := n+raw.length+D.length+1
  have positive : 0 < size := by dsimp only [size]; omega
  have preSize : n+raw.length+1 ≤ size := by dsimp only [size]; omega
  have old : ((finSteinerBinaryServeFromArcRowsWithWork raw height
      (steinerBitStreamSource stream) D).run start).1.work ≤ C*size^(max k 3) :=
    (original raw stream start D feasible).trans
      (Nat.mul_le_mul_left C (Nat.pow_le_pow_right positive (le_max_left k 3)))
  have intake : (prepareSteinerBinaryArcRowsWithWork raw).2 ≤ 100*size^(max k 3) := by
    calc
      _ ≤ 100*(n+raw.length+1)^3 := (prepareSteinerBinaryArcRowsWithWork_spec raw).2.2.trans
        (steinerBinaryArcRowsWorkBudget_cubic n raw.length)
      _ ≤ 100*size^3 := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left preSize _)
      _ ≤ _ := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_right positive (le_max_right k 3))
  have sameCost := (finSteinerBinaryServeFromBinaryArcRows_refines raw height stream start D).2.2.2
  have total := Nat.add_le_add old intake
  change _ ≤ (C+100)*size^(max k 3)
  rw [Nat.add_mul]
  omega

open MeasureTheory
open scoped ENNReal

/-- Theorem 21 from raw arc rows with the cached binary preparation.
The same sampled stream supplies the exact graph at every prefix. -/
theorem theorem21_online_steiner_sampled_binary_arc_rows {ε : ℝ} (epsilon : 0 < ε) :
    ∃ (height : ℕ) (K : ℝ) (C k : ℕ), 0 < height ∧ 0 < K ∧
      (∀ {n : ℕ} (raw : List (Fin n × Fin n)) (stream : ℕ → Bool) (D : List (Fin n × Fin n)),
        (∀ d ∈ D, Reach raw.toFinset d.1 d.2) →
        let result := (finSteinerBinaryServeFromBinaryArcRowsWithWork raw height (steinerBitStreamSource stream) D).run 0
        result.2 = steinerBitBudget raw.toFinset height ∧ result.1.history.reverse = D ∧
          result.1.graph ⊆ raw.toFinset ∧ Preserves raw.toFinset result.1.graph D ∧
          result.1.work ≤ C*(n+raw.length+D.length+1)^k) ∧
      (∀ {n : ℕ} (raw : List (Fin n × Fin n)) (stream : ℕ → Bool) {D E : List (Fin n × Fin n)},
        D <+: E → (∀ d ∈ E, Reach raw.toFinset d.1 d.2) →
          ((finSteinerBinaryServeFromBinaryArcRowsWithWork raw height (steinerBitStreamSource stream) D).run 0).1.graph ⊆
            ((finSteinerBinaryServeFromBinaryArcRowsWithWork raw height (steinerBitStreamSource stream) E).run 0).1.graph) ∧
      (∀ {n : ℕ} {Z : Arcs (Fin n)} (raw : List (Fin n × Fin n)) (D : List (Fin n × Fin n)),
        Z ⊆ raw.toFinset → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∫⁻ stream, (((finSteinerBinaryServeFromBinaryArcRowsWithWork raw height
          (steinerBitStreamSource stream) D).run 0).1.graph.card : ℝ≥0∞) ∂fairBitMeasure) ≤
            ENNReal.ofReal (K*(n:ℝ)^(3/5+ε)*Z.card)) := by
  obtain ⟨height,K,_,_,heightPos,constantPos,correct,monotone,expected⟩ :=
    theorem21_online_steiner_sampled_arc_rows epsilon
  obtain ⟨C,k,cost⟩ := finSteinerBinaryServeFromBinaryArcRows_polynomial height
  refine ⟨height,K,C,k,heightPos,constantPos,?_,?_,?_⟩
  · intro n raw stream D feasible
    obtain ⟨same,history,bits,_⟩ := finSteinerBinaryServeFromBinaryArcRows_refines raw height stream 0 D
    obtain ⟨rawBits,sub,preserves,_⟩ := correct raw stream D feasible
    refine ⟨bits.trans rawBits,?_,?_,?_,cost raw stream 0 D feasible⟩
    · rw [history,finSteinerBinaryServeFromArcRowsWithWork_stream,finSteinerBinaryServeFromBitSource_stream]
      exact (finSteinerBinaryServeWithWork_spec _ _ _ _ _ _).1
    · rw [same]
      exact sub
    · rw [same]
      exact preserves
  · intro n raw stream D E prefixOf feasible
    rw [(finSteinerBinaryServeFromBinaryArcRows_refines raw height stream 0 D).1,
      (finSteinerBinaryServeFromBinaryArcRows_refines raw height stream 0 E).1]
    exact monotone raw stream prefixOf feasible
  · intro n Z raw D sub feasible
    simp_rw [fun stream => (finSteinerBinaryServeFromBinaryArcRows_refines raw height stream 0 D).1]
    exact expected raw D sub feasible

end OnlineReachabilityPreservers
