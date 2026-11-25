import OnlineReachabilityPreservers.SteinerEarlyCoordinateRankWork
import OnlineReachabilityPreservers.SteinerFinWeightedReplayWork

/-! Feed one arc index and arithmetic vertex and coordinate indexes to the fixed-budget decoder. -/

namespace OnlineReachabilityPreservers

/-- Build the graph-key lookup table and the arithmetic index functions. -/
def finSteinerReplaySeedIndexesWithWordWork {n : ℕ} (G : Arcs (Fin n)) (height : ℕ)
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) : SteinerReplaySeedIndexes G height × ℕ :=
  let arcs := finSteinerArcIndexWithWordWork G raw same
  (⟨finSteinerVertexIndex n,arcs.1,fun width => finSteinerEarlyCoordinateIndexWithWordWork G height width.val width.property⟩,
    arcs.2+9)

def finSteinerReplayIndexWorkPolynomial (n raw : ℕ) : ℕ :=
  (n*n)*(2*raw+30)+21*raw+39

theorem finSteinerReplaySeedIndexesWithWordWork_spec {n : ℕ} (G : Arcs (Fin n)) (height : ℕ)
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) :
    let out := finSteinerReplaySeedIndexesWithWordWork G height raw same
    out.1 = steinerReplaySeedIndexes G height ∧ out.2 ≤ finSteinerReplayIndexWorkPolynomial n raw.length := by
  obtain ⟨arcs,work⟩ := finSteinerArcIndexWithWordWork_spec G raw same
  have coords : (fun width : {w : ℕ // w = (forestScale G height).log2+1} =>
      finSteinerEarlyCoordinateIndexWithWordWork G height width.val width.property) =
    (fun width => steinerEarlyCoordinateIndexLex G height width.val width.property
      (steinerUniverseArrayIndex (Fin n))) :=
    funext fun width => finSteinerEarlyCoordinateIndexWithWordWork_eq G height width.val width.property
  constructor
  · dsimp only [finSteinerReplaySeedIndexesWithWordWork,steinerReplaySeedIndexes]
    rw [arcs,finSteinerVertexIndex_eq,coords]
  · exact (Nat.add_le_add_right work 9).trans_eq (by unfold finSteinerReplayIndexWorkPolynomial; omega)

/-- Prepare one arc index for the whole replay. Its arithmetic vertex and
early-coordinate ranks give the same seed positions as the ordinary indexes. -/
def completeFinSteinerReplayWithIndexPreparationWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  let prepared := prepareFinSteinerWeightedForSeedWithWordWork G raw same height
  let indexes := finSteinerReplaySeedIndexesWithWordWork G height raw same
  ((completeSteinerReplayWithDecoderWorkUsingIndexes G height n m (by simp) hm prepared.1 indexes.1 bits D,
    prepared.2),indexes.2)

theorem completeFinSteinerReplayWithIndexPreparationWork_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithIndexPreparationWork G raw same height m hm bits D
    out.1 = completeFinSteinerReplayWithWeightedPreparationWork G raw same height m hm bits D ∧
      out.2 ≤ finSteinerReplayIndexWorkPolynomial n raw.length := by
  obtain ⟨indexes,work⟩ := finSteinerReplaySeedIndexesWithWordWork_spec G height raw same
  refine ⟨?_,work⟩
  dsimp only [completeFinSteinerReplayWithIndexPreparationWork,
    completeFinSteinerReplayWithWeightedPreparationWork,completeSteinerReplayWithDecoderWorkFromPreparation]
  rw [indexes]

theorem completeFinSteinerReplayWithIndexPreparationWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithIndexPreparationWork G raw same height m hm bits D
    let base := out.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.2+out.2 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length := by
  obtain ⟨sameRun,construction⟩ := completeFinSteinerReplayWithIndexPreparationWork_spec G raw same height m hm bits D
  obtain ⟨prefixes, measured⟩ := completeFinSteinerReplayWithWeightedPreparationWork_prefixes G raw same height m hm bits D feasible
  dsimp only
  rw [sameRun]
  exact ⟨prefixes,Nat.add_le_add measured construction⟩

end OnlineReachabilityPreservers
