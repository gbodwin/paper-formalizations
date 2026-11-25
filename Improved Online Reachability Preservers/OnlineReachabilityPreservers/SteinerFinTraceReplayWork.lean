import OnlineReachabilityPreservers.SteinerFinIndexedReplayWork
import OnlineReachabilityPreservers.SteinerTraceDispatchWork
import OnlineReachabilityPreservers.SteinerTraceInputsWork

/-! Share phase parameters, sampled hubs, and normalized request prefixes in replay. -/

namespace OnlineReachabilityPreservers

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- One cap for phase preparation and the trace and split work at all
evaluated prefixes. The cost of a sampled draw is a unit lookup with
a fixed allowance for passing its index and result. -/
def steinerTraceReplayWorkPolynomial (n p : ℕ) : ℕ :=
  let hubs := 4*(n+1)*n+1
  let perSplit := 11*p+13
  p*(10*p+31+perSplit)+perSplit+7 +
    (16*n^2+23*n+33) + (hubs*(2*hubs+26)+13) + 10

private def evaluateSteinerTraceWithSplitWork (G : Arcs V)
    (early : List (V × V) → Arcs V × ℕ) (T τ : ℕ) (hubs : Finset V)
    (thin : ThinSample G) (P : List (V × V)) : (Arcs V × ℕ) × ℕ :=
  let split := splitSteinerTraceWithWordWork T P
  (completeSteinerDrawRunWithSearchWorkFromParts G early τ hubs thin split.1.1 split.1.2,split.2+8)

/-- Use one pair of integer cutoffs and one set of sampled hubs for the
entire successful replay. Split and evaluate only a new non-self request. -/
def replaySteinerSeededPrefixesWithTraceWork (G : Arcs V) (n : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (D : List (V × V)) : List (Arcs V × ℕ) × ℕ × ℕ :=
  let params := steinerTraceParametersWithWordWork n
  have countOk : params.1.hubCount = completeSteinerHubCount V := by
    rw [params.1.hubCount_eq,hn]
    rfl
  let hubs := collectSteinerHubsWithWordWork countOk draw
  let evaluate := evaluateSteinerTraceWithSplitWork G early params.1.earlyCutoff params.1.thinThreshold hubs.1 thin
  let out := replayFirstOccurrencesWithWordWork evaluate D
  (out.1,out.2.1+params.2+hubs.2+10,out.2.2)

theorem replaySteinerSeededPrefixesWithTraceWork_spec (G : Arcs V) (n : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) (D : List (V × V)) :
    let out := replaySteinerSeededPrefixesWithTraceWork G n hn early draw thin D
    out.1 = D.inits.map (completeSteinerDrawRunWithSearchWorkFromEarly G early draw thin) ∧
      out.2.1 ≤ steinerTraceReplayWorkPolynomial n D.length ∧
      out.2.2 = (distinctNonselfTrace D).length+1 := by
  let params := steinerTraceParametersWithWordWork n
  have countOk : params.1.hubCount = completeSteinerHubCount V := by
    rw [params.1.hubCount_eq,hn]
    rfl
  let hubs := collectSteinerHubsWithWordWork countOk draw
  let evaluate := evaluateSteinerTraceWithSplitWork G early params.1.earlyCutoff params.1.thinThreshold hubs.1 thin
  let out := replayFirstOccurrencesWithWordWork evaluate D
  obtain ⟨exactHubs,hubWork⟩ := collectSteinerHubsWithWordWork_spec countOk draw
  have each (P : List (V × V)) (short : P.length ≤ D.length) : (evaluate P).2 ≤ 11*D.length+13 := by
    have work := (splitSteinerTraceWithWordWork_spec params.1.earlyCutoff P).2
    change (splitSteinerTraceWithWordWork params.1.earlyCutoff P).2+8 ≤ _
    have size := Nat.mul_le_mul_left 11 short
    omega
  obtain ⟨records,traceWork,number⟩ := replayFirstOccurrencesWithWordWork_spec evaluate D (11*D.length+13) each
  have sameWithTrace (P : List (V × V)) :
      (evaluate (distinctNonselfTrace P)).1 = completeSteinerDrawRunWithSearchWorkFromEarly G early draw thin P := by
    dsimp only [evaluate,evaluateSteinerTraceWithSplitWork]
    rw [(splitSteinerTraceWithWordWork_spec _ _).1, params.1.earlyCutoff_eq,
      params.1.thinThreshold_eq,exactHubs,hn]
    rfl
  refine ⟨records.trans (List.map_congr_left (fun P _ => sameWithTrace P)), ?_,number⟩
  have paramWork := steinerTraceParametersWithWordWork_bound n
  have hcount : params.1.hubCount ≤ 4*(n+1)*n+1 := by
    rw [countOk]
    apply (completeSteinerHubCount_le V).trans
    rw [← hn]
    gcongr
    exact Nat.log2_le_self n
  have hubLimit : hubs.2 ≤ (4*(n+1)*n+1)*(2*(4*(n+1)*n+1)+26)+13 := by
    apply hubWork.trans
    gcongr
  change out.2.1+params.2+hubs.2+10 ≤ _
  change out.2.1 ≤ _ at traceWork
  change params.2 ≤ _ at paramWork
  dsimp only [steinerTraceReplayWorkPolynomial]
  omega

private theorem steinerFallbackReplayWordWork_bound (n p : ℕ) :
    16*p+6 ≤ steinerTraceReplayWorkPolynomial n p := by
  dsimp only [steinerTraceReplayWorkPolynomial]
  have bound : p*16 ≤ p*(10*p+31+(11*p+13)) := Nat.mul_le_mul_left p (by omega)
  omega

/-- Extend the indexed replay with its phase and request-list tally and
the number of seeded prefix evaluations. -/
def completeFinSteinerReplayWithTraceWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  let prepared := prepareFinSteinerWeightedForSeedWithWordWork G raw same height
  let indexes := finSteinerReplaySeedIndexesWithWordWork G height raw same
  let decoded := decodeSteinerSeedFromPreparedScale G height n m (by simp) hm prepared.1.1 indexes.1 bits
  let replay := match decoded.1 with
    | none =>
      let fallback := steinerFallbackPrefixScanWithWordWork G D
      (fallback.1,fallback.2,0)
    | some seed => replaySteinerSeededPrefixesWithTraceWork G n (by simp)
      (prepared.1.2.1 seed.1) seed.2.1 seed.2.2 D
  (((((replay.1,prepared.1.2.2),decoded.2),prepared.2),indexes.2),replay.2)

theorem completeFinSteinerReplayWithTraceWork_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithTraceWork G raw same height m hm bits D
    out.1 = completeFinSteinerReplayWithIndexPreparationWork G raw same height m hm bits D ∧
      out.2.1 ≤ steinerTraceReplayWorkPolynomial n D.length ∧
      out.2.2 ≤ (distinctNonselfTrace D).length+1 := by
  unfold completeFinSteinerReplayWithTraceWork completeFinSteinerReplayWithIndexPreparationWork
    completeSteinerReplayWithDecoderWorkUsingIndexes
  dsimp only
  split
  · rename_i exhausted
    obtain ⟨equivalent,work⟩ := steinerFallbackPrefixScanWithWordWork_spec G D
    simpa only [exhausted,equivalent,work,zero_le,and_true,true_and] using
      steinerFallbackReplayWordWork_bound n D.length
  · rename_i seed decoded
    obtain ⟨equivalent,work,number⟩ := replaySteinerSeededPrefixesWithTraceWork_spec G n (by simp)
      ((prepareFinSteinerWeightedForSeedWithWordWork G raw same height).1.2.1 seed.1) seed.2.1 seed.2.2 D
    simpa only [decoded,equivalent,number,le_refl,and_true,true_and] using work

theorem completeFinSteinerReplayWithTraceWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithTraceWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          steinerTraceReplayWorkPolynomial n D.length := by
  obtain ⟨sameRun,traceWork,_⟩ := completeFinSteinerReplayWithTraceWork_spec G raw same height m hm bits D
  obtain ⟨prefixes,charged⟩ := completeFinSteinerReplayWithIndexPreparationWork_prefixes G raw same height m hm bits D feasible
  dsimp only
  rw [sameRun]
  exact ⟨prefixes,Nat.add_le_add charged traceWork⟩

end OnlineReachabilityPreservers
