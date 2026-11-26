import OnlineReachabilityPreservers.SteinerPhaseUnionWork
import OnlineReachabilityPreservers.SteinerFinIndexedReplayWork
import OnlineReachabilityPreservers.SteinerHubRouteWork
import OnlineReachabilityPreservers.SteinerTraceDispatchWork
import OnlineReachabilityPreservers.SteinerTraceInputsWork

/-! Share phase parameters, sampled hubs, and normalized request prefixes in replay. -/

namespace OnlineReachabilityPreservers

variable {V : Type*} [LinearOrder V] [Fintype V]

private def steinerTraceWorkFromCallbackBound (n p callback : ℕ) : ℕ :=
  let hubs := 4*(n+1)*n+1
  p*(10*p+31+callback)+callback+7 +
    (16*n^2+23*n+33) + (hubs*(2*hubs+26)+13) + 10

/-- One cap for phase preparation and the trace and split work at all
evaluated prefixes. The cost of a sampled draw is a unit lookup with
a fixed allowance for passing its index and result. -/
def steinerTraceReplayWorkPolynomial (n p : ℕ) : ℕ :=
  steinerTraceWorkFromCallbackBound n p (11*p+13)

private def evaluateSteinerTraceWithSplitWork (G : Arcs V)
    (early : List (V × V) → Arcs V × ℕ) (T τ : ℕ) (hubs : Finset V)
    (thin : ThinSample G) (P : List (V × V)) : (Arcs V × ℕ) × ℕ :=
  let split := splitSteinerTraceWithWordWork T P
  (completeSteinerDrawRunWithSearchWorkFromParts G early τ hubs thin split.1.1 split.1.2,split.2+8)

@[inline] private def replaySteinerTraceWithCallback (n : ℕ) (hn : n = Fintype.card V)
    (draw : Fin (completeSteinerHubCount V) → V) (D : List (V × V))
    (evaluate : ℕ → ℕ → Finset V → List (V × V) → (Arcs V × ℕ) × ℕ) : List (Arcs V × ℕ) × ℕ × ℕ :=
  let params := steinerTraceParametersWithWordWork n
  have countOk : params.1.hubCount = completeSteinerHubCount V := by
    rw [params.1.hubCount_eq,hn]
    rfl
  let hubs := collectSteinerHubsWithWordWork countOk draw
  let out := replayFirstOccurrencesWithWordWork
    (evaluate params.1.earlyCutoff params.1.thinThreshold hubs.1) D
  (out.1,out.2.1+params.2+hubs.2+10,out.2.2)

private theorem replaySteinerTraceWithCallback_spec_of_demand_property (n : ℕ) (hn : n = Fintype.card V)
    (draw : Fin (completeSteinerHubCount V) → V) (D : List (V × V))
    (valid : V × V → Prop) (inputValid : ∀ d ∈ D, valid d)
    (evaluate : ℕ → ℕ → Finset V → List (V × V) → (Arcs V × ℕ) × ℕ)
    (target : List (V × V) → Arcs V × ℕ) (C : ℕ)
    (exactValue : ∀ P, (evaluate (steinerEarlyCutoff n) (steinerThinThreshold n) (sampledVertices draw)
      (distinctNonselfTrace P)).1 = target P)
    (each : ∀ T τ hubs P, P.length ≤ D.length → (∀ d ∈ P, valid d) → (evaluate T τ hubs P).2 ≤ C) :
    let out := replaySteinerTraceWithCallback n hn draw D evaluate
    out.1 = D.inits.map target ∧
      out.2.1 ≤ steinerTraceWorkFromCallbackBound n D.length C ∧
      out.2.2 = (distinctNonselfTrace D).length+1 := by
  let params := steinerTraceParametersWithWordWork n
  have countOk : params.1.hubCount = completeSteinerHubCount V := by
    rw [params.1.hubCount_eq,hn]
    rfl
  let hubs := collectSteinerHubsWithWordWork countOk draw
  let run := evaluate params.1.earlyCutoff params.1.thinThreshold hubs.1
  let out := replayFirstOccurrencesWithWordWork run D
  obtain ⟨exactHubs,hubWork⟩ := collectSteinerHubsWithWordWork_spec countOk draw
  obtain ⟨records,traceWork,number⟩ := replayFirstOccurrencesWithWordWork_spec_of_demand_property
    run D C valid (each _ _ _) inputValid
  have sameWithTrace (P : List (V × V)) :
      (run (distinctNonselfTrace P)).1 = target P := by
    dsimp only [run]
    rw [params.1.earlyCutoff_eq,params.1.thinThreshold_eq,exactHubs]
    exact exactValue P
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
  dsimp only [steinerTraceWorkFromCallbackBound]
  omega

private theorem replaySteinerTraceWithCallback_spec (n : ℕ) (hn : n = Fintype.card V)
    (draw : Fin (completeSteinerHubCount V) → V) (D : List (V × V))
    (evaluate : ℕ → ℕ → Finset V → List (V × V) → (Arcs V × ℕ) × ℕ)
    (target : List (V × V) → Arcs V × ℕ) (C : ℕ)
    (exactValue : ∀ P, (evaluate (steinerEarlyCutoff n) (steinerThinThreshold n) (sampledVertices draw)
      (distinctNonselfTrace P)).1 = target P)
    (each : ∀ T τ hubs P, P.length ≤ D.length → (evaluate T τ hubs P).2 ≤ C) :
    let out := replaySteinerTraceWithCallback n hn draw D evaluate
    out.1 = D.inits.map target ∧
      out.2.1 ≤ steinerTraceWorkFromCallbackBound n D.length C ∧
      out.2.2 = (distinctNonselfTrace D).length+1 :=
  replaySteinerTraceWithCallback_spec_of_demand_property n hn draw D (fun _ => True) (by simp)
    evaluate target C exactValue (fun T τ hubs P short _ => each T τ hubs P short)

private theorem replaySteinerTraceWithCallback_records_eq (n : ℕ) (hn : n = Fintype.card V)
    (draw : Fin (completeSteinerHubCount V) → V) (D : List (V × V))
    (first second : ℕ → ℕ → Finset V → List (V × V) → (Arcs V × ℕ) × ℕ)
    (same : ∀ T τ hubs P, (first T τ hubs P).1 = (second T τ hubs P).1) :
    let left := replaySteinerTraceWithCallback n hn draw D first
    let right := replaySteinerTraceWithCallback n hn draw D second
    left.1 = right.1 ∧ left.2.2 = right.2.2 := by
  unfold replaySteinerTraceWithCallback
  exact replayFirstOccurrencesWithWordWork_records_eq _ _ (same _ _ _) D

/-- Use one pair of integer cutoffs and one set of sampled hubs for the
entire successful replay. Split and evaluate each first-occurrence prefix once. -/
def replaySteinerSeededPrefixesWithTraceWork (G : Arcs V) (n : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (D : List (V × V)) : List (Arcs V × ℕ) × ℕ × ℕ :=
  replaySteinerTraceWithCallback n hn draw D (fun T τ hubs => evaluateSteinerTraceWithSplitWork G early T τ hubs thin)

theorem replaySteinerSeededPrefixesWithTraceWork_spec (G : Arcs V) (n : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) (D : List (V × V)) :
    let out := replaySteinerSeededPrefixesWithTraceWork G n hn early draw thin D
    out.1 = D.inits.map (completeSteinerDrawRunWithSearchWorkFromEarly G early draw thin) ∧
      out.2.1 ≤ steinerTraceReplayWorkPolynomial n D.length ∧
      out.2.2 = (distinctNonselfTrace D).length+1 := by
  apply replaySteinerTraceWithCallback_spec
  · intro P
    dsimp only [evaluateSteinerTraceWithSplitWork]
    rw [(splitSteinerTraceWithWordWork_spec _ _).1,hn]
    rfl
  · intro T τ hubs P short
    have work := (splitSteinerTraceWithWordWork_spec T P).2
    change (splitSteinerTraceWithWordWork T P).2+8 ≤ 11*D.length+13
    have size := Nat.mul_le_mul_left 11 short
    omega

private theorem steinerFallbackReplayWordWork_bound (n p : ℕ) :
    16*p+6 ≤ steinerTraceReplayWorkPolynomial n p := by
  dsimp only [steinerTraceReplayWorkPolynomial,steinerTraceWorkFromCallbackBound]
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

private def steinerTraceEarlySeedWorkBound (n p perMetric : ℕ) : ℕ :=
  steinerTraceReplayWorkPolynomial n p+(p+1)*((p+1)*perMetric+5)

/-- Allow one unit per seed read in early rounding, alongside trace work. -/
def steinerTraceEarlySeedReadWorkPolynomial (n height p : ℕ) : ℕ :=
  steinerTraceEarlySeedWorkBound n p (earlyRoundingSeedReadPolynomial n height)

private def evaluateSteinerTraceWithEarlySeedReads
    (early : List (V × V) → Arcs V × ℕ × ℕ) (T τ : ℕ) (hubs : Finset V)
    (late : ℕ → Finset V → List (V × V) → Arcs V × ℕ) (P : List (V × V)) : (Arcs V × ℕ) × ℕ :=
  let split := splitSteinerTraceWithWordWork T P
  let first := early split.1.1
  let rest := late τ hubs split.1.2
  ((first.1 ∪ rest.1,first.2.1+rest.2),split.2+8+first.2.2+5)

private def replaySteinerTraceWithEarlySeedReadsUsing (n : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ × ℕ)
    (draw : Fin (completeSteinerHubCount V) → V) (late : ℕ → Finset V → List (V × V) → Arcs V × ℕ)
    (D : List (V × V)) : List (Arcs V × ℕ) × ℕ × ℕ :=
  replaySteinerTraceWithCallback n hn draw D
    (fun T τ hubs => evaluateSteinerTraceWithEarlySeedReads early T τ hubs late)

private def replaySteinerTraceWithEarlySeedReads (G : Arcs V) (n : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ × ℕ)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (D : List (V × V)) : List (Arcs V × ℕ) × ℕ × ℕ :=
  replaySteinerTraceWithEarlySeedReadsUsing n hn early draw (fun τ hubs => lateSteinerWithSearchWork G τ hubs thin) D

private def steinerPrefixFromEvaluators (n : ℕ) (early : List (V × V) → Arcs V × ℕ)
    (draw : Fin (completeSteinerHubCount V) → V) (late : ℕ → Finset V → List (V × V) → Arcs V × ℕ)
    (P : List (V × V)) : Arcs V × ℕ :=
  let requests := distinctNonselfTrace P
  let first := early (requests.take (steinerEarlyCutoff n))
  let rest := late (steinerThinThreshold n) (sampledVertices draw) (requests.drop (steinerEarlyCutoff n))
  (first.1 ∪ rest.1,first.2+rest.2)

private theorem replaySteinerTraceWithEarlySeedReadsUsing_spec (n : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ × ℕ) (B : ℕ)
    (earlyBound : ∀ P, (early P).2.2 ≤ (P.length+1)*B)
    (draw : Fin (completeSteinerHubCount V) → V) (late : ℕ → Finset V → List (V × V) → Arcs V × ℕ)
    (D : List (V × V)) :
    let out := replaySteinerTraceWithEarlySeedReadsUsing n hn early draw late D
    out.1 = D.inits.map (steinerPrefixFromEvaluators n (fun P => ((early P).1,(early P).2.1)) draw late) ∧
      out.2.1 ≤ steinerTraceEarlySeedWorkBound n D.length B ∧ out.2.2 = (distinctNonselfTrace D).length+1 := by
  let run := fun T τ hubs => evaluateSteinerTraceWithEarlySeedReads early T τ hubs late
  let target := steinerPrefixFromEvaluators n (fun P => ((early P).1,(early P).2.1)) draw late
  let extra := (D.length+1)*B+5
  have exactValue (P : List (V × V)) : (run (steinerEarlyCutoff n) (steinerThinThreshold n)
      (sampledVertices draw) (distinctNonselfTrace P)).1 = target P := by
    dsimp only [run,evaluateSteinerTraceWithEarlySeedReads,target,steinerPrefixFromEvaluators]
    rw [(splitSteinerTraceWithWordWork_spec _ _).1]
  have work (T τ : ℕ) (hubs : Finset V) (P : List (V × V)) (len : P.length ≤ D.length) :
      (run T τ hubs P).2 ≤ 11*D.length+13+extra := by
    let split := splitSteinerTraceWithWordWork T P
    obtain ⟨parts,splitWork⟩ := splitSteinerTraceWithWordWork_spec T P
    have shorter : split.1.1.length ≤ D.length := by
      change (splitSteinerTraceWithWordWork T P).1.1.length ≤ _
      rw [parts]
      exact (List.length_take_le' T P).trans len
    have reads := (earlyBound split.1.1).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right shorter 1))
    have times := Nat.mul_le_mul_left 11 len
    change split.2+8+(early split.1.1).2.2+5 ≤ 11*D.length+13+extra
    change split.2 ≤ _ at splitWork
    dsimp only [extra]
    omega
  obtain ⟨same,bound,number⟩ := replaySteinerTraceWithCallback_spec n hn draw D run target _ exactValue work
  refine ⟨same,bound.trans_eq ?_,number⟩
  unfold steinerTraceEarlySeedWorkBound steinerTraceReplayWorkPolynomial steinerTraceWorkFromCallbackBound
  ring

private theorem replaySteinerTraceWithEarlySeedReads_spec (G : Arcs V) (n height : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ × ℕ) (oldEarly : List (V × V) → Arcs V × ℕ)
    (exactEarly : ∀ P, ((early P).1,(early P).2.1) = oldEarly P)
    (earlyBound : ∀ P, (early P).2.2 ≤ (P.length+1)*earlyRoundingSeedReadPolynomial n height)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) (D : List (V × V)) :
    let out := replaySteinerTraceWithEarlySeedReads G n hn early draw thin D
    let old := replaySteinerSeededPrefixesWithTraceWork G n hn oldEarly draw thin D
    out.1 = old.1 ∧ out.2.1 ≤ steinerTraceEarlySeedReadWorkPolynomial n height D.length ∧ out.2.2 = old.2.2 := by
  obtain ⟨prior,_,priorCount⟩ := replaySteinerSeededPrefixesWithTraceWork_spec G n hn oldEarly draw thin D
  obtain ⟨same,work,count⟩ := replaySteinerTraceWithEarlySeedReadsUsing_spec n hn early _ earlyBound draw
    (fun τ hubs => lateSteinerWithSearchWork G τ hubs thin) D
  rw [funext exactEarly] at same
  have samePrefix : steinerPrefixFromEvaluators n oldEarly draw (fun τ hubs => lateSteinerWithSearchWork G τ hubs thin) =
      completeSteinerDrawRunWithSearchWorkFromEarly G oldEarly draw thin := by
    subst n
    rfl
  rw [samePrefix] at same
  exact ⟨same.trans prior.symm,work,count.trans priorCount.symm⟩

/-- Replay the fixed-budget decoder with early seed reads charged once
per evaluated prefix. The exhaustion branch keeps its measured fallback. -/
def completeFinSteinerReplayWithEarlySeedReads {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  let prepared := prepareFinSteinerWeightedForSeedWithSeedReads G raw same height
  let indexes := finSteinerReplaySeedIndexesWithWordWork G height raw same
  let decoded := decodeSteinerSeedFromPreparedScale G height n m (by simp) hm prepared.1.1 indexes.1 bits
  let replay := match decoded.1 with
    | none =>
      let fallback := steinerFallbackPrefixScanWithWordWork G D
      (fallback.1,fallback.2,0)
    | some seed => replaySteinerTraceWithEarlySeedReads G n (by simp)
      (prepared.1.2.1 seed.1) seed.2.1 seed.2.2 D
  (((((replay.1,prepared.1.2.2),decoded.2),prepared.2),indexes.2),replay.2)

theorem completeFinSteinerReplayWithEarlySeedReads_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithEarlySeedReads G raw same height m hm bits D
    let old := completeFinSteinerReplayWithTraceWork G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.1 ≤ steinerTraceEarlySeedReadWorkPolynomial n height D.length ∧ out.2.2 = old.2.2 := by
  let prepared := prepareFinSteinerWeightedForSeedWithSeedReads G raw same height
  let old := prepareFinSteinerWeightedForSeedWithWordWork G raw same height
  obtain ⟨scale,setup,plan,early⟩ := prepareFinSteinerWeightedForSeedWithSeedReads_spec G raw same height
  unfold completeFinSteinerReplayWithEarlySeedReads completeFinSteinerReplayWithTraceWork
  dsimp only
  rw [scale,setup,plan]
  split
  ·
    have fallback := (steinerFallbackPrefixScanWithWordWork_spec G D).2
    have cap := (steinerFallbackReplayWordWork_bound n D.length).trans
      (Nat.le_add_right _ ((D.length+1)*((D.length+1)*earlyRoundingSeedReadPolynomial n height+5)))
    exact ⟨rfl,fallback.le.trans cap,rfl⟩
  · rename_i seed _decoded
    obtain ⟨records,bound,count⟩ := replaySteinerTraceWithEarlySeedReads_spec G n height (by simp)
      (prepared.1.2.1 seed.1) (old.1.2.1 seed.1)
      (fun P => (early seed.1 P).1) (fun P => (early seed.1 P).2) seed.2.1 seed.2.2 D
    refine ⟨?_,bound,count⟩
    dsimp only [prepared,old] at records
    rw [records]

theorem completeFinSteinerReplayWithEarlySeedReads_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithEarlySeedReads G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          steinerTraceEarlySeedReadWorkPolynomial n height D.length := by
  obtain ⟨equivalence,reads,_⟩ := completeFinSteinerReplayWithEarlySeedReads_spec G raw same height m hm bits D
  obtain ⟨trace,_⟩ := completeFinSteinerReplayWithTraceWork_spec G raw same height m hm bits D
  obtain ⟨prefixes,charged⟩ := completeFinSteinerReplayWithIndexPreparationWork_prefixes G raw same height m hm bits D feasible
  dsimp only
  rw [equivalence,trace]
  exact ⟨prefixes,Nat.add_le_add charged reads⟩

/-- Take one threshold and one arc directly from storage for each position.
Reuse those rows across every late prefix of the successful replay. -/
def completeFinSteinerReplayWithStoredThinThresholds {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  let prepared := prepareFinSteinerWeightedForSeedWithSeedReads G raw same height
  let indexes := finSteinerReplaySeedIndexesWithWordWork G height raw same
  let decoded := decodeSteinerSeedWithIndexedThinFromPreparedScale G height n m (by simp) hm
    prepared.1.1 indexes.1 bits
  let replay := match decoded.1 with
    | none =>
      let fallback := steinerFallbackPrefixScanWithWordWork G D
      (fallback.1,fallback.2,0)
    | some (seed,thin) =>
      let rows := prepareThinThresholdRowsByIndex G m hm indexes.1.arcs thin
      let out := replaySteinerTraceWithEarlySeedReadsUsing n (by simp) (prepared.1.2.1 seed.1) seed.2.1
        (fun τ hubs => lateSteinerWithStoredThinThresholds G τ m hubs rows.1) D
      (out.1,out.2.1+2*rows.2+9,out.2.2)
  (((((replay.1,prepared.1.2.2),decoded.2),prepared.2),indexes.2),replay.2)

theorem completeFinSteinerReplayWithStoredThinThresholds_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithStoredThinThresholds G raw same height m hm bits D
    let old := completeFinSteinerReplayWithEarlySeedReads G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 ∧ out.2.1 ≤ old.2.1+2*m+9 := by
  let prepared := prepareFinSteinerWeightedForSeedWithSeedReads G raw same height
  let indexes := finSteinerReplaySeedIndexesWithWordWork G height raw same
  let decoded := decodeSteinerSeedWithIndexedThinFromPreparedScale G height n m (by simp) hm
    prepared.1.1 indexes.1 bits
  let former := decodeSteinerSeedFromPreparedScale G height n m (by simp) hm prepared.1.1 indexes.1 bits
  obtain ⟨read,thinView⟩ := decodeSteinerSeedWithIndexedThinFromPreparedScale_spec G height n m (by simp) hm
    prepared.1.1 indexes.1 bits
  have seedEq : decoded.1.map Prod.fst = former.1 := congrArg Prod.fst read
  have workEq : decoded.2 = former.2 := congrArg Prod.snd read
  unfold completeFinSteinerReplayWithStoredThinThresholds completeFinSteinerReplayWithEarlySeedReads
  dsimp only
  rw [show (decodeSteinerSeedWithIndexedThinFromPreparedScale G height n m (by simp) hm
    prepared.1.1 indexes.1 bits).2 = former.2 from workEq]
  cases branch : decoded.1 with
  | none =>
    have old : former.1 = none := by simpa only [branch,Option.map_none] using seedEq.symm
    dsimp only [former,prepared,indexes] at old
    rw [old]
    exact ⟨rfl,rfl,(Nat.le_add_right _ _).trans (Nat.le_add_right _ _)⟩
  | some entry =>
    have old : former.1 = some entry.1 := by simpa only [branch,Option.map_some] using seedEq.symm
    have sample : (fun e => entry.2 (indexes.1.arcs e)) = entry.1.2.2 := funext (thinView entry branch)
    have rows := prepareThinThresholdRowsByIndex_eq G m hm indexes.1.arcs entry.2
    have sameLate (τ : ℕ) (hubs : Finset (Fin n)) (E : List (Fin n × Fin n)) :
        lateSteinerWithStoredThinThresholds G τ m hubs
          (prepareThinThresholdRowsByIndex G m hm indexes.1.arcs entry.2).1 E =
          lateSteinerWithSearchWork G τ hubs entry.1.2.2 E := by
      rw [rows,sample]
      exact lateSteinerWithStoredThinThresholds_eq G τ m hm hubs entry.1.2.2 E
    have sameReplay := congrArg (fun late => replaySteinerTraceWithEarlySeedReadsUsing n (by simp)
      (prepared.1.2.1 entry.1.1) entry.1.2.1 late D)
      (funext fun τ => funext fun hubs => funext fun E => sameLate τ hubs E)
    dsimp only [former,prepared,indexes] at old sameReplay
    rw [old]
    dsimp only
    rw [sameReplay]
    exact ⟨rfl,rfl,le_rfl⟩

theorem completeFinSteinerReplayWithStoredThinThresholds_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithStoredThinThresholds G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          steinerTraceEarlySeedReadWorkPolynomial n height D.length + 2*m + 9 := by
  obtain ⟨equivalence,_,rows⟩ := completeFinSteinerReplayWithStoredThinThresholds_spec G raw same height m hm bits D
  obtain ⟨prefixes,charged⟩ := completeFinSteinerReplayWithEarlySeedReads_prefixes G raw same height m hm bits D feasible
  dsimp only
  rw [equivalence]
  refine ⟨prefixes,?_⟩
  omega

private structure SteinerPhaseUnion (W : Type*) [DecidableEq W] where
  combine : Arcs W → Arcs W → Arcs W × ℕ
  graph_eq : ∀ left right, (combine left right).1 = left ∪ right

@[inline] private def unmeteredPhaseUnion (W : Type*) [DecidableEq W] : SteinerPhaseUnion W where
  combine left right := (left ∪ right,0)
  graph_eq _ _ := rfl

@[inline] private def meteredPhaseUnion (W : Type*) [DecidableEq W] : SteinerPhaseUnion W where
  combine := unionFinsetWithWordWork
  graph_eq left right := (unionFinsetWithWordWork_spec left right).1

@[inline] private def evaluateSteinerTraceWithPhaseWork
    (early : List (V × V) → Arcs V × ℕ × ℕ) (T τ : ℕ) (hubs : Finset V)
    (late : ℕ → Finset V → List (V × V) → (Arcs V × ℕ) × ℕ) (P : List (V × V))
    (join : SteinerPhaseUnion V := unmeteredPhaseUnion V) : (Arcs V × ℕ) × ℕ :=
  let split := splitSteinerTraceWithWordWork T P
  let first := early split.1.1
  let rest := late τ hubs split.1.2
  let output := join.combine first.1 rest.1.1
  ((output.1,first.2.1+rest.1.2),split.2+8+first.2.2+rest.2+7+output.2)

@[inline] private def replaySteinerTraceWithPhaseWork (n : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ × ℕ) (draw : Fin (completeSteinerHubCount V) → V)
    (late : ℕ → Finset V → List (V × V) → (Arcs V × ℕ) × ℕ)
    (D : List (V × V)) (join : SteinerPhaseUnion V := unmeteredPhaseUnion V) : List (Arcs V × ℕ) × ℕ × ℕ :=
  replaySteinerTraceWithCallback n hn draw D (fun T τ hubs P => evaluateSteinerTraceWithPhaseWork early T τ hubs late P join)

private theorem replaySteinerTraceWithPhaseWork_records_eq (n : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ × ℕ) (draw : Fin (completeSteinerHubCount V) → V)
    (late : ℕ → Finset V → List (V × V) → (Arcs V × ℕ) × ℕ)
    (priorLate : ℕ → Finset V → List (V × V) → Arcs V × ℕ)
    (record : ∀ τ hubs P, (late τ hubs P).1 = priorLate τ hubs P) (D : List (V × V)) :
    let out := replaySteinerTraceWithPhaseWork n hn early draw late D
    let old := replaySteinerTraceWithEarlySeedReadsUsing n hn early draw priorLate D
    out.1 = old.1 ∧ out.2.2 = old.2.2 := by
  apply replaySteinerTraceWithCallback_records_eq
  intro T τ hubs P
  dsimp only [evaluateSteinerTraceWithPhaseWork,evaluateSteinerTraceWithEarlySeedReads,unmeteredPhaseUnion]
  rw [record]

private theorem replaySteinerTraceWithPhaseWork_bound_using (n : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ × ℕ) (B : ℕ)
    (earlyBound : ∀ P, (early P).2.2 ≤ (P.length+1)*B)
    (draw : Fin (completeSteinerHubCount V) → V)
    (late : ℕ → Finset V → List (V × V) → (Arcs V × ℕ) × ℕ)
    (D : List (V × V)) (valid : V × V → Prop) (inputValid : ∀ d ∈ D, valid d) (L : ℕ)
    (lateBound : ∀ τ hubs P, P.length ≤ D.length → (∀ d ∈ P, valid d) → (late τ hubs P).2 ≤ L)
    (join : SteinerPhaseUnion V) (unionBudget : ℕ)
    (joinBound : ∀ left right, (join.combine left right).2 ≤ unionBudget) :
    (replaySteinerTraceWithPhaseWork n hn early draw late D join).2.1 ≤
      steinerTraceEarlySeedWorkBound n D.length B+(D.length+1)*(L+unionBudget+2) := by
  let run := fun T τ hubs P => evaluateSteinerTraceWithPhaseWork early T τ hubs late P join
  let target := steinerPrefixFromEvaluators n (fun P => ((early P).1,(early P).2.1)) draw
    (fun τ hubs P => (late τ hubs P).1)
  let extra := (D.length+1)*B+5+(L+unionBudget+2)
  have record (P : List (V × V)) : (run (steinerEarlyCutoff n) (steinerThinThreshold n)
      (sampledVertices draw) (distinctNonselfTrace P)).1 = target P := by
    dsimp only [run,evaluateSteinerTraceWithPhaseWork,target,steinerPrefixFromEvaluators]
    rw [(splitSteinerTraceWithWordWork_spec _ _).1,join.graph_eq]
  have work (T τ : ℕ) (hubs : Finset V) (P : List (V × V)) (len : P.length ≤ D.length)
      (selected : ∀ d ∈ P, valid d) : (run T τ hubs P).2 ≤ 11*D.length+13+extra := by
    let split := splitSteinerTraceWithWordWork T P
    obtain ⟨parts,splitWork⟩ := splitSteinerTraceWithWordWork_spec T P
    have shorter : split.1.1.length ≤ D.length := by
      change (splitSteinerTraceWithWordWork T P).1.1.length ≤ _
      rw [parts]
      exact (List.length_take_le' T P).trans len
    have suffix : split.1.2.length ≤ D.length := by
      change (splitSteinerTraceWithWordWork T P).1.2.length ≤ _
      rw [parts]
      exact (List.drop_sublist T P).length_le.trans len
    have suffixValid : ∀ d ∈ split.1.2, valid d := by
      intro d hd
      change d ∈ (splitSteinerTraceWithWordWork T P).1.2 at hd
      rw [parts] at hd
      exact selected d (List.mem_of_mem_drop hd)
    have reads := (earlyBound split.1.1).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right shorter 1))
    have later := lateBound τ hubs split.1.2 suffix suffixValid
    have times := Nat.mul_le_mul_left 11 len
    let union := join.combine (early split.1.1).1 (late τ hubs split.1.2).1.1
    have unionWork : union.2 ≤ unionBudget := joinBound _ _
    change split.2+8+(early split.1.1).2.2+(late τ hubs split.1.2).2+7+union.2 ≤ 11*D.length+13+extra
    change split.2 ≤ _ at splitWork
    dsimp only [extra]
    omega
  obtain ⟨_,bound,_⟩ := replaySteinerTraceWithCallback_spec_of_demand_property n hn draw D valid inputValid
    run target _ record work
  refine bound.trans_eq ?_
  unfold steinerTraceEarlySeedWorkBound steinerTraceReplayWorkPolynomial steinerTraceWorkFromCallbackBound
  dsimp only [extra]
  ring

private theorem replaySteinerTraceWithPhaseWork_bound (n : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ × ℕ) (B : ℕ)
    (earlyBound : ∀ P, (early P).2.2 ≤ (P.length+1)*B)
    (draw : Fin (completeSteinerHubCount V) → V)
    (late : ℕ → Finset V → List (V × V) → (Arcs V × ℕ) × ℕ)
    (D : List (V × V)) (valid : V × V → Prop) (inputValid : ∀ d ∈ D, valid d) (L : ℕ)
    (lateBound : ∀ τ hubs P, P.length ≤ D.length → (∀ d ∈ P, valid d) → (late τ hubs P).2 ≤ L) :
    (replaySteinerTraceWithPhaseWork n hn early draw late D).2.1 ≤
      steinerTraceEarlySeedWorkBound n D.length B+(D.length+1)*(L+2) :=
  replaySteinerTraceWithPhaseWork_bound_using n hn early B earlyBound draw late D valid inputValid L lateBound
    (unmeteredPhaseUnion V) 0 (fun _ _ => le_rfl)

/-- Include the arithmetic ranks and indexed reads used by early rounding. -/
def steinerTraceEarlySeedRankWorkPolynomial (n height p : ℕ) : ℕ :=
  steinerTraceEarlySeedWorkBound n p (earlyRoundingSeedReadPolynomial n height*earlySeedArrayReadWordBudget height)

@[inline] private def replayFromCachedFinSteinerSeed {n : ℕ} {Cache : Type*} (G : Arcs (Fin n))
    (height : ℕ) (D : List (Fin n × Fin n)) (indexes : SteinerReplaySeedIndexes G height)
    (prepared : SteinerSeedPreparationWithSeedWork G height)
    (decoded : {w : ℕ // w = (forestScale G height).log2+1} ×
      Option ((EarlyRoundSample G height × (Fin (completeSteinerHubCount (Fin n)) → Fin n) × ThinSample G) ×
        SteinerSeedArrayViews G height))
    (cache : (G ≃ Fin G.card) → (Fin G.card → Fin G.card) → Cache × ℕ)
    (run : (List (Fin n × Fin n) → Arcs (Fin n) × ℕ × ℕ) →
      (Fin (completeSteinerHubCount (Fin n)) → Fin n) → Cache → List (Arcs (Fin n) × ℕ) × ℕ × ℕ) :
    List (Arcs (Fin n) × ℕ) × ℕ × ℕ :=
  match decoded.2 with
  | none =>
    let fallback := steinerFallbackPrefixScanWithWordWork G D
    (fallback.1,fallback.2,0)
  | some (seed,arrays) =>
    let width := decoded.1
    let samples := finEarlySeedTrialsWithRankWork G height width.val width.property arrays.early
    let rows := cache indexes.arcs arrays.thin
    let out := run (prepared.2.1 samples) seed.2.1 rows.1
    (out.1,out.2.1+rows.2+9,out.2.2)

@[inline] private def completeFinSteinerReplayWithCachedPhases {n : ℕ} {Cache : Type*} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (cache : (G ≃ Fin G.card) → (Fin G.card → Fin G.card) → Cache × ℕ)
    (run : (List (Fin n × Fin n) → Arcs (Fin n) × ℕ × ℕ) →
      (Fin (completeSteinerHubCount (Fin n)) → Fin n) → Cache → List (Arcs (Fin n) × ℕ) × ℕ × ℕ)
    (prepared : SteinerSeedPreparationWithSeedWork G height × ℕ :=
      prepareFinSteinerWeightedForSeedWithSeedWork G raw same height) :=
  let indexes := finSteinerReplaySeedIndexesWithWordWork G height raw same
  let decoded := decodeSteinerSeedWithArrayViewsFromPreparedScale G height n m (by simp) hm
    prepared.1.1 indexes.1 bits
  let replay := replayFromCachedFinSteinerSeed G height D indexes.1 prepared.1 decoded.1 cache run
  (((((replay.1,prepared.1.2.2),decoded.2),prepared.2),indexes.2),replay.2.1+8,replay.2.2)

@[inline] private def completeFinSteinerReplayWithSeedRankWorkUsing {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (cache : (G ≃ Fin G.card) → (Fin G.card → Fin G.card) → Finset ((Fin n × Fin n) × ℕ) × ℕ) :=
  completeFinSteinerReplayWithCachedPhases G raw same height m hm bits D cache fun early draw rows =>
    replaySteinerTraceWithEarlySeedReadsUsing n (by simp) early draw
      (fun τ hubs => lateSteinerWithStoredThinThresholds G τ m hubs rows) D

/-- Decode the arrays once, charge early ranks at the gates and tests that
need their words, and retain the late threshold cache. -/
def completeFinSteinerReplayWithSeedRankWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithSeedRankWorkUsing G raw same height m hm bits D fun arcs sample =>
    let rows := prepareThinThresholdRowsByIndex G m hm arcs sample
    (rows.1,2*rows.2)

set_option maxHeartbeats 800000 in
theorem completeFinSteinerReplayWithSeedRankWork_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithSeedRankWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithStoredThinThresholds G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 ∧
      out.2.1 ≤ steinerTraceEarlySeedRankWorkPolynomial n height D.length+2*m+17 := by
  let prepared := prepareFinSteinerWeightedForSeedWithSeedWork G raw same height
  let previous := prepareFinSteinerWeightedForSeedWithSeedReads G raw same height
  let indexes := finSteinerReplaySeedIndexesWithWordWork G height raw same
  let decoded := decodeSteinerSeedWithArrayViewsFromPreparedScale G height n m (by simp) hm
    prepared.1.1 indexes.1 bits
  let former := decodeSteinerSeedWithIndexedThinFromPreparedScale G height n m (by simp) hm
    previous.1.1 indexes.1 bits
  obtain ⟨newScale,newSetup,newPlan,newEarly⟩ := prepareFinSteinerWeightedForSeedWithSeedWork_spec G raw same height
  obtain ⟨oldScale,oldSetup,oldPlan,oldEarly⟩ := prepareFinSteinerWeightedForSeedWithSeedReads_spec G raw same height
  have scale : prepared.1.1 = previous.1.1 := newScale.trans oldScale.symm
  have setup : prepared.1.2.2 = previous.1.2.2 := newSetup.trans oldSetup.symm
  have plan : prepared.2 = previous.2 := newPlan.trans oldPlan.symm
  obtain ⟨project,earlyView⟩ := decodeSteinerSeedWithArrayViewsFromPreparedScale_spec G height n m
    (by simp) hm prepared.1.1 indexes.1 bits
  have decoder : (decoded.1.2.map (fun p => (p.1,p.2.thin)),decoded.2) = former := by
    change _ = decodeSteinerSeedWithIndexedThinFromPreparedScale G height n m (by simp) hm
      previous.1.1 indexes.1 bits
    rw [← scale]
    exact project
  have seedEq := congrArg Prod.fst decoder
  have workEq := congrArg Prod.snd decoder
  unfold completeFinSteinerReplayWithSeedRankWork completeFinSteinerReplayWithSeedRankWorkUsing
    completeFinSteinerReplayWithCachedPhases replayFromCachedFinSteinerSeed completeFinSteinerReplayWithStoredThinThresholds
  dsimp only
  rw [show (decodeSteinerSeedWithArrayViewsFromPreparedScale G height n m (by simp) hm
    prepared.1.1 indexes.1 bits).2 = former.2 from workEq, setup,plan]
  cases branch : decoded.1.2 with
  | none =>
    have old : former.1 = none := by simpa only [branch,Option.map_none] using seedEq.symm
    dsimp only [former,previous,indexes] at old
    rw [old]
    have fallback := (steinerFallbackPrefixScanWithWordWork_spec G D).2.le.trans
      (steinerFallbackReplayWordWork_bound n D.length)
    refine ⟨rfl,rfl,?_⟩
    change (steinerFallbackPrefixScanWithWordWork G D).2+8 ≤ _
    unfold steinerTraceEarlySeedRankWorkPolynomial steinerTraceEarlySeedWorkBound
    omega
  | some entry =>
    have old : former.1 = some (entry.1,entry.2.thin) := by
      simpa only [branch,Option.map_some] using seedEq.symm
    let width := decoded.1.1
    let samples := finEarlySeedTrialsWithRankWork G height width.val width.property entry.2.early
    obtain ⟨plain,perRead⟩ := finEarlySeedTrialsWithRankWork_spec G height width.val width.property entry.2.early
    have sampleEq : (fun trial => forestRoundingSampleValues (forestScale G height) (samples trial)) = entry.1.1 :=
      plain.trans (earlyView entry branch)
    let first := prepared.1.2.1 samples
    let priorFirst := previous.1.2.1 entry.1.1
    have sameEarly (P : List (Fin n × Fin n)) : ((first P).1,(first P).2.1) = ((priorFirst P).1,(priorFirst P).2.1) ∧
        (first P).2.2 ≤ (P.length+1)*(earlyRoundingSeedReadPolynomial n height*earlySeedArrayReadWordBudget height) := by
      obtain ⟨values,work⟩ := newEarly samples _ perRead P
      rw [sampleEq] at values
      exact ⟨values.trans (oldEarly entry.1.1 P).1.symm,work⟩
    let rows := prepareThinThresholdRowsByIndex G m hm indexes.1.arcs entry.2.thin
    let late := fun τ hubs => lateSteinerWithStoredThinThresholds G τ m hubs rows.1
    obtain ⟨records,bound,count⟩ := replaySteinerTraceWithEarlySeedReadsUsing_spec n (by simp) first _
      (fun P => (sameEarly P).2) entry.1.2.1 late D
    obtain ⟨priorRecords,_,priorCount⟩ := replaySteinerTraceWithEarlySeedReadsUsing_spec n (by simp) priorFirst
      (earlyRoundingSeedReadPolynomial n height) (fun P => (oldEarly entry.1.1 P).2) entry.1.2.1 late D
    have projected : (fun P => ((first P).1,(first P).2.1)) = (fun P => ((priorFirst P).1,(priorFirst P).2.1)) :=
      funext fun P => (sameEarly P).1
    rw [projected] at records
    have agrees := records.trans priorRecords.symm
    have evaluations := count.trans priorCount.symm
    dsimp only [former,previous,indexes] at old
    rw [old]
    dsimp only
    refine ⟨congrArg (fun values : List (Arcs (Fin n) × ℕ) =>
      ((((values,previous.1.2.2),former.2),previous.2),indexes.2)) agrees,
      evaluations,?_⟩
    change (replaySteinerTraceWithEarlySeedReadsUsing n (by simp) first entry.1.2.1 late D).2.1+2*m+9+8 ≤ _
    change _ ≤ steinerTraceEarlySeedRankWorkPolynomial n height D.length at bound
    omega

theorem completeFinSteinerReplayWithSeedRankWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithSeedRankWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          steinerTraceEarlySeedRankWorkPolynomial n height D.length + 2*m + 17 := by
  have sameRun := (completeFinSteinerReplayWithSeedRankWork_spec G raw same height m hm bits D).1
  have rankWork := (completeFinSteinerReplayWithSeedRankWork_spec G raw same height m hm bits D).2.2
  have cached := (completeFinSteinerReplayWithStoredThinThresholds_spec G raw same height m hm bits D).1
  have reads := (completeFinSteinerReplayWithEarlySeedReads_spec G raw same height m hm bits D).1
  have trace := (completeFinSteinerReplayWithTraceWork_spec G raw same height m hm bits D).1
  obtain ⟨prefixes,charged⟩ := completeFinSteinerReplayWithIndexPreparationWork_prefixes G raw same height m hm bits D feasible
  dsimp only
  rw [sameRun,cached,reads,trace]
  refine ⟨prefixes,?_⟩
  omega

/-- Charge construction of the cached thin threshold rows as well as the
early rank, decoder, and replay work. -/
def completeFinSteinerReplayWithThinRowWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithSeedRankWorkUsing G raw same height m hm bits D
    (prepareThinThresholdRowsByIndexWithWordWork G m hm)

theorem completeFinSteinerReplayWithThinRowWork_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithSeedRankWork G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 ∧ out.2.1 ≤ old.2.1+9*m+4 := by
  let prepared := prepareFinSteinerWeightedForSeedWithSeedWork G raw same height
  let indexes := finSteinerReplaySeedIndexesWithWordWork G height raw same
  let decoded := decodeSteinerSeedWithArrayViewsFromPreparedScale G height n m (by simp) hm prepared.1.1 indexes.1 bits
  unfold completeFinSteinerReplayWithThinRowWork completeFinSteinerReplayWithSeedRankWork
    completeFinSteinerReplayWithSeedRankWorkUsing completeFinSteinerReplayWithCachedPhases replayFromCachedFinSteinerSeed
  dsimp only
  cases state : decoded.1.2 with
  | none => exact ⟨rfl,rfl,by dsimp only; omega⟩
  | some entry =>
    rcases entry with ⟨seed,arrays⟩
    dsimp only
    obtain ⟨sameRows,work⟩ := prepareThinThresholdRowsByIndexWithWordWork_spec G m hm indexes.1.arcs arrays.thin
    dsimp only [indexes] at sameRows work
    rw [sameRows,work]
    refine ⟨rfl,rfl,?_⟩
    dsimp only [prepareThinThresholdRowsByIndex]
    omega

theorem completeFinSteinerReplayWithThinRowWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          steinerTraceEarlySeedRankWorkPolynomial n height D.length + 11*m + 21 := by
  obtain ⟨stored,_,rowWork⟩ := completeFinSteinerReplayWithThinRowWork_spec G raw same height m hm bits D
  obtain ⟨prefixes,charged⟩ := completeFinSteinerReplayWithSeedRankWork_prefixes G raw same height m hm bits D feasible
  dsimp only
  rw [stored]
  refine ⟨prefixes,?_⟩
  omega

/-- Bound trace operations and the additional word work in both phases. -/
def steinerTracePhaseWorkPolynomial (n m height p : ℕ) : ℕ :=
  steinerTraceEarlySeedRankWorkPolynomial n height p+(p+1)*(steinerStreamingThinWorkPolynomial n m p+2)

/-- Bound the measured trace with indexed signed flow in each thin separator. -/
def steinerTraceDenseSeparatorWorkPolynomial (n m height p : ℕ) : ℕ :=
  steinerTraceEarlySeedRankWorkPolynomial n height p+(p+1)*(steinerThinSeparatorWorkPolynomial n m p+2)

private abbrev FinLateReplayEvaluator (n : ℕ) :=
  ℕ → Finset (Fin n) → ThinThresholdList (Fin n) → List (Fin n × Fin n) →
    (Arcs (Fin n) × ℕ) × ℕ

private def completeFinSteinerReplayWithLateEvaluator {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (lateEval : FinLateReplayEvaluator n) (join : SteinerPhaseUnion (Fin n) := unmeteredPhaseUnion (Fin n))
    (prepared : SteinerSeedPreparationWithSeedWork G height × ℕ :=
      prepareFinSteinerWeightedForSeedWithSeedWork G raw same height) :=
  completeFinSteinerReplayWithCachedPhases G raw same height m hm bits D
    (prepareThinThresholdListByIndexWithWordWork G m hm) (fun early draw rows =>
      replaySteinerTraceWithPhaseWork n (by simp) early draw (fun τ hubs => lateEval τ hubs rows) D join) prepared

/-- Reuse decoded thresholds and advance the fractional thin loads once per
request inside each evaluated late prefix. -/
def completeFinSteinerReplayWithStreamingThinWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D
    (fun τ hubs rows => lateSteinerWithStreamingThinWork G τ m hubs rows)

/-- Use indexed signed-flow updates in the thin separator at every late prefix. -/
def completeFinSteinerReplayWithThinSeparatorWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D
    (fun τ hubs rows => lateSteinerWithThinSeparatorWork G τ m hubs rows)

private theorem completeFinSteinerReplayWithLateEvaluator_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (lateEval : FinLateReplayEvaluator n) (L : ℕ)
    (lateExact : ∀ τ hubs rows P, (lateEval τ hubs rows P).1 =
      lateSteinerWithStoredThinThresholds G τ m hubs rows.val.toFinset P)
    (lateWork : ∀ (_early : EarlySteinerRule G) τ hubs rows, (∀ r ∈ rows.val, r.1 ∈ G) →
      rows.val.length ≤ m → ∀ P, P.length ≤ D.length → (∀ d ∈ P, Reach G d.1 d.2) →
        (lateEval τ hubs rows P).2 ≤ L) :
    let out := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D lateEval
    let old := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 ∧
      ((∀ d ∈ D, Reach G d.1 d.2) → out.2.1 ≤ (steinerTraceEarlySeedRankWorkPolynomial n height D.length+(D.length+1)*(L+2))+11*m+21) := by
  let prepared := prepareFinSteinerWeightedForSeedWithSeedWork G raw same height
  let indexes := finSteinerReplaySeedIndexesWithWordWork G height raw same
  let decoded := decodeSteinerSeedWithArrayViewsFromPreparedScale G height n m (by simp) hm prepared.1.1 indexes.1 bits
  unfold completeFinSteinerReplayWithLateEvaluator completeFinSteinerReplayWithThinRowWork
    completeFinSteinerReplayWithSeedRankWorkUsing completeFinSteinerReplayWithCachedPhases replayFromCachedFinSteinerSeed
  dsimp only
  cases state : decoded.1.2 with
  | none =>
    refine ⟨rfl,rfl,fun _ => ?_⟩
    have fallback := (steinerFallbackPrefixScanWithWordWork_spec G D).2.le.trans
      (steinerFallbackReplayWordWork_bound n D.length)
    change (steinerFallbackPrefixScanWithWordWork G D).2+8 ≤ _
    unfold steinerTraceEarlySeedRankWorkPolynomial steinerTraceEarlySeedWorkBound
    omega
  | some entry =>
    rcases entry with ⟨seed,arrays⟩
    dsimp only
    let width := decoded.1.1
    let samples := finEarlySeedTrialsWithRankWork G height width.val width.property arrays.early
    let early := prepared.1.2.1 samples
    let rows := prepareThinThresholdListByIndexWithWordWork G m hm indexes.1.arcs arrays.thin
    let oldRows := prepareThinThresholdRowsByIndexWithWordWork G m hm indexes.1.arcs arrays.thin
    obtain ⟨listRows,rowCount,rowEdges,rowWork⟩ := prepareThinThresholdListByIndexWithWordWork_spec
      G m hm indexes.1.arcs arrays.thin
    have sameRows := listRows.trans (prepareThinThresholdRowsByIndexWithWordWork_spec G m hm indexes.1.arcs arrays.thin).1.symm
    let late := fun τ hubs => lateEval τ hubs rows.1
    let priorLate := fun τ hubs => lateSteinerWithStoredThinThresholds G τ m hubs oldRows.1
    have lateRecord (τ : ℕ) (hubs : Finset (Fin n)) (P : List (Fin n × Fin n)) : (late τ hubs P).1 = priorLate τ hubs P := by
      dsimp only [late,priorLate]
      rw [lateExact,show rows.1.val.toFinset = oldRows.1 from sameRows]
    obtain ⟨records,calls⟩ := replaySteinerTraceWithPhaseWork_records_eq n (by simp) early seed.2.1 late priorLate lateRecord D
    refine ⟨congrArg (fun data : List (Arcs (Fin n) × ℕ) =>
      ((((data,prepared.1.2.2),decoded.2),prepared.2),indexes.2)) records,calls,?_⟩
    intro feasible
    let B := earlyRoundingSeedReadPolynomial n height*earlySeedArrayReadWordBudget height
    obtain ⟨_,perRead⟩ := finEarlySeedTrialsWithRankWork_spec G height width.val width.property arrays.early
    have earlyBound (P : List (Fin n × Fin n)) : (early P).2.2 ≤ (P.length+1)*B :=
      ((prepareFinSteinerWeightedForSeedWithSeedWork_spec G raw same height).2.2.2 samples _ perRead P).2
    have lateBound (τ : ℕ) (hubs : Finset (Fin n)) (P : List (Fin n × Fin n))
        (short : P.length ≤ D.length) (reachable : ∀ d ∈ P, Reach G d.1 d.2) : (late τ hubs P).2 ≤ L := by
      exact lateWork (earlyRoundedRule G height seed.1) τ hubs rows.1 rowEdges rowCount.le P short reachable
    have work := replaySteinerTraceWithPhaseWork_bound n (by simp) early B earlyBound seed.2.1 late D
      (fun d => Reach G d.1 d.2) feasible L lateBound
    change (replaySteinerTraceWithPhaseWork n (by simp) early seed.2.1 late D).2.1+rows.2+9+8 ≤ _
    change _ ≤ (steinerTraceEarlySeedRankWorkPolynomial n height D.length+(D.length+1)*(L+2)) at work
    change rows.2 = 11*m+4 at rowWork
    omega

/-- Preserve the prefix records and evaluation count on every input. The
additional trace allowance applies when the demands are reachable. -/
theorem completeFinSteinerReplayWithStreamingThinWork_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithStreamingThinWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 ∧
      ((∀ d ∈ D, Reach G d.1 d.2) → out.2.1 ≤ steinerTracePhaseWorkPolynomial n m height D.length+11*m+21) := by
  apply completeFinSteinerReplayWithLateEvaluator_spec G raw same height m hm bits D
    (fun τ hubs rows => lateSteinerWithStreamingThinWork G τ m hubs rows)
    (steinerStreamingThinWorkPolynomial n m D.length)
  · exact fun τ hubs rows P => lateSteinerWithStreamingThinWork_eq G τ m hm hubs rows P
  · intro early τ hubs rows edges count P short reachable
    have work := lateSteinerWithStreamingThinWork_bound early τ m hm hubs rows edges count P reachable
    refine work.trans ((steinerStreamingThinWorkBound_le n m P.length).trans ?_)
    unfold steinerStreamingThinWorkPolynomial
    gcongr

theorem completeFinSteinerReplayWithThinSeparatorWork_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithThinSeparatorWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 ∧
      ((∀ d ∈ D, Reach G d.1 d.2) → out.2.1 ≤ steinerTraceDenseSeparatorWorkPolynomial n m height D.length+11*m+21) := by
  apply completeFinSteinerReplayWithLateEvaluator_spec G raw same height m hm bits D
    (fun τ hubs rows => lateSteinerWithThinSeparatorWork G τ m hubs rows)
    (steinerThinSeparatorWorkPolynomial n m D.length)
  · exact fun τ hubs rows P => lateSteinerWithThinSeparatorWork_eq G τ m hm hubs rows P
  · intro early τ hubs rows edges count P short reachable
    have work := lateSteinerWithThinSeparatorWork_bound early τ m hm hubs rows edges count P reachable
    refine work.trans ((steinerThinSeparatorWorkBound_le n m P.length).trans ?_)
    unfold steinerThinSeparatorWorkPolynomial steinerStreamingThinWorkPolynomial
    gcongr

private theorem completeFinSteinerReplayWithLateEvaluator_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) (lateEval : FinLateReplayEvaluator n) (work : ℕ)
    (issued : let out := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D lateEval
      out.1 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).1 ∧
      out.2.1 ≤ work) :
    let out := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D lateEval
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          work := by
  obtain ⟨sameRun,budget⟩ := issued
  have rows := (completeFinSteinerReplayWithThinRowWork_spec G raw same height m hm bits D).1
  have ranks := (completeFinSteinerReplayWithSeedRankWork_spec G raw same height m hm bits D).1
  have cached := (completeFinSteinerReplayWithStoredThinThresholds_spec G raw same height m hm bits D).1
  have reads := (completeFinSteinerReplayWithEarlySeedReads_spec G raw same height m hm bits D).1
  have trace := (completeFinSteinerReplayWithTraceWork_spec G raw same height m hm bits D).1
  obtain ⟨prefixes,charged⟩ := completeFinSteinerReplayWithIndexPreparationWork_prefixes G raw same height m hm bits D feasible
  dsimp only
  rw [sameRun,rows,ranks,cached,reads,trace]
  refine ⟨prefixes,?_⟩
  omega

/-- Exact fixed-budget prefix graphs with the additional word work of the
incremental thin evaluator included in the same bound. -/
theorem completeFinSteinerReplayWithStreamingThinWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithStreamingThinWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          steinerTracePhaseWorkPolynomial n m height D.length + 11*m + 21 := by
  obtain ⟨sameRun,_,traceWork⟩ := completeFinSteinerReplayWithStreamingThinWork_spec G raw same height m hm bits D
  simpa only [completeFinSteinerReplayWithStreamingThinWork,Nat.add_assoc] using
    completeFinSteinerReplayWithLateEvaluator_prefixes G raw same height m hm bits D feasible
    (fun τ hubs rows => lateSteinerWithStreamingThinWork G τ m hubs rows)
    (steinerTracePhaseWorkPolynomial n m height D.length + 11*m + 21) ⟨sameRun,traceWork feasible⟩

/-- Exact fixed-budget prefix graphs with the additional signed-flow work. -/
theorem completeFinSteinerReplayWithThinSeparatorWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithThinSeparatorWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          steinerTraceDenseSeparatorWorkPolynomial n m height D.length + 11*m + 21 := by
  obtain ⟨sameRun,_,traceWork⟩ := completeFinSteinerReplayWithThinSeparatorWork_spec G raw same height m hm bits D
  simpa only [completeFinSteinerReplayWithThinSeparatorWork,Nat.add_assoc] using
    completeFinSteinerReplayWithLateEvaluator_prefixes G raw same height m hm bits D feasible
    (fun τ hubs rows => lateSteinerWithThinSeparatorWork G τ m hubs rows)
    (steinerTraceDenseSeparatorWorkPolynomial n m height D.length + 11*m + 21) ⟨sameRun,traceWork feasible⟩

/-- Bound the measured trace with stored capacities and indexed residual scans. -/
def steinerTraceIndexedThinWorkPolynomial (n m height p : ℕ) : ℕ :=
  steinerTraceEarlySeedRankWorkPolynomial n height p+(p+1)*(steinerThinIndexedTablesWorkPolynomial n m p+2)

/-- Use stored capacities and indexed residual scans in the thin separator at each late prefix. -/
def completeFinSteinerReplayWithIndexedThinTablesWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D
    (fun τ hubs rows => lateSteinerWithIndexedThinTablesWork G τ m hubs rows)

theorem completeFinSteinerReplayWithIndexedThinTablesWork_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithIndexedThinTablesWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 ∧
      ((∀ d ∈ D, Reach G d.1 d.2) → out.2.1 ≤ steinerTraceIndexedThinWorkPolynomial n m height D.length+11*m+21) := by
  apply completeFinSteinerReplayWithLateEvaluator_spec G raw same height m hm bits D
    (fun τ hubs rows => lateSteinerWithIndexedThinTablesWork G τ m hubs rows)
    (steinerThinIndexedTablesWorkPolynomial n m D.length)
  · exact fun τ hubs rows P => lateSteinerWithIndexedThinTablesWork_eq G τ m hm hubs rows P
  · intro early τ hubs rows edges count P short reachable
    have work := lateSteinerWithIndexedThinTablesWork_bound early τ m hm hubs rows edges count P reachable
    refine work.trans ((steinerThinIndexedTablesWorkBound_le n m P.length).trans ?_)
    unfold steinerThinIndexedTablesWorkPolynomial steinerStreamingThinWorkPolynomial
    gcongr

/-- Exact fixed-budget prefix graphs including measured thin capacity and residual work. -/
theorem completeFinSteinerReplayWithIndexedThinTablesWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithIndexedThinTablesWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          steinerTraceIndexedThinWorkPolynomial n m height D.length + 11*m + 21 := by
  obtain ⟨sameRun,_,traceWork⟩ := completeFinSteinerReplayWithIndexedThinTablesWork_spec G raw same height m hm bits D
  simpa only [completeFinSteinerReplayWithIndexedThinTablesWork,Nat.add_assoc] using
    completeFinSteinerReplayWithLateEvaluator_prefixes G raw same height m hm bits D feasible
    (fun τ hubs rows => lateSteinerWithIndexedThinTablesWork G τ m hubs rows)
    (steinerTraceIndexedThinWorkPolynomial n m height D.length + 11*m + 21) ⟨sameRun,traceWork feasible⟩

def steinerTraceThinResidualRouteWorkPolynomial (n m height p : ℕ) : ℕ :=
  steinerTraceEarlySeedRankWorkPolynomial n height p+(p+1)*(steinerThinResidualRouteWorkPolynomial n m p+2)

/-- Search the indexed residual arcs as lists in the thin separator at each late prefix. -/
def completeFinSteinerReplayWithThinResidualRouteWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D
    (fun τ hubs rows => lateSteinerWithThinResidualRouteWork G τ m hubs rows)

theorem completeFinSteinerReplayWithThinResidualRouteWork_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithThinResidualRouteWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 ∧
      ((∀ d ∈ D, Reach G d.1 d.2) → out.2.1 ≤ steinerTraceThinResidualRouteWorkPolynomial n m height D.length+11*m+21) := by
  apply completeFinSteinerReplayWithLateEvaluator_spec G raw same height m hm bits D
    (fun τ hubs rows => lateSteinerWithThinResidualRouteWork G τ m hubs rows)
    (steinerThinResidualRouteWorkPolynomial n m D.length)
  · exact fun τ hubs rows P => lateSteinerWithThinResidualRouteWork_eq G τ m hm hubs rows P
  · intro early τ hubs rows edges count P short reachable
    have work := lateSteinerWithThinResidualRouteWork_bound early τ m hm hubs rows edges count P reachable
    refine work.trans ((steinerThinResidualRouteWorkBound_le n m P.length).trans ?_)
    unfold steinerThinResidualRouteWorkPolynomial steinerStreamingThinWorkPolynomial
    gcongr

/-- Exact fixed-budget prefix graphs with the thin residual routes and terminal reachability metered. -/
theorem completeFinSteinerReplayWithThinResidualRouteWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithThinResidualRouteWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          steinerTraceThinResidualRouteWorkPolynomial n m height D.length + 11*m + 21 := by
  obtain ⟨sameRun,_,traceWork⟩ := completeFinSteinerReplayWithThinResidualRouteWork_spec G raw same height m hm bits D
  simpa only [completeFinSteinerReplayWithThinResidualRouteWork,Nat.add_assoc] using
    completeFinSteinerReplayWithLateEvaluator_prefixes G raw same height m hm bits D feasible
    (fun τ hubs rows => lateSteinerWithThinResidualRouteWork G τ m hubs rows)
    (steinerTraceThinResidualRouteWorkPolynomial n m height D.length + 11*m + 21) ⟨sameRun,traceWork feasible⟩

def steinerTraceThinIntervalWorkPolynomial (n m height p : ℕ) : ℕ :=
  steinerTraceEarlySeedRankWorkPolynomial n height p+(p+1)*(steinerThinIntervalWorkPolynomial n m p+2)

private theorem completeFinSteinerReplayWithThinIntervalEvaluator_spec {n : ℕ} (G : Arcs (Fin n))
    (arcs : {r : List (Fin n × Fin n) // r.Nodup}) (arcsEq : arcs.val.toFinset = G)
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let late := fun τ hubs rows => lateSteinerWithThinIntervalWork G arcs τ m hubs rows
    let out := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D late
    let old := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 ∧
      ((∀ d ∈ D, Reach G d.1 d.2) → out.2.1 ≤ steinerTraceThinIntervalWorkPolynomial n m height D.length+11*m+21) := by
  apply completeFinSteinerReplayWithLateEvaluator_spec G raw same height m hm bits D
    (fun τ hubs rows => lateSteinerWithThinIntervalWork G arcs τ m hubs rows)
    (steinerThinIntervalWorkPolynomial n m D.length)
  · exact fun τ hubs rows P => lateSteinerWithThinIntervalWork_eq G arcs arcsEq τ m hm hubs rows P
  · intro early τ hubs rows edges count P short reachable
    have work := lateSteinerWithThinIntervalWork_bound early arcs arcsEq τ m hm hubs rows edges count P reachable
    refine work.trans ((steinerThinIntervalWorkBound_le n m P.length).trans ?_)
    unfold steinerThinIntervalWorkPolynomial steinerThinResidualRouteWorkPolynomial steinerStreamingThinWorkPolynomial
    gcongr

/-- Prepare the original arc list once and share each thin demand interval across its cut searches. -/
def completeFinSteinerReplayWithThinIntervalWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  let rows := finArcRowsWithWordWork raw
  let out := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D
    (fun τ hubs thresholds => lateSteinerWithThinIntervalWork G rows.1 τ m hubs thresholds)
  (out.1,out.2.1+rows.2+3,out.2.2)

theorem completeFinSteinerReplayWithThinIntervalWork_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithThinIntervalWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 ∧
      ((∀ d ∈ D, Reach G d.1 d.2) → out.2.1 ≤ steinerTraceThinIntervalWorkPolynomial n m height D.length+
        11*m+21+finArcRowsWordBudget n raw.length+3) := by
  obtain ⟨arcs,ready⟩ := finArcRowsWithWordWork_spec G raw same
  obtain ⟨sameRecord,count,work⟩ := completeFinSteinerReplayWithThinIntervalEvaluator_spec G
    (finArcRowsWithWordWork raw).1 arcs raw same height m hm bits D
  exact ⟨sameRecord,count,fun feasible => Nat.add_le_add_right (Nat.add_le_add (work feasible) ready) 3⟩

/-- Exact fixed-budget prefix graphs, including the thin interval searches and their cut applications. -/
theorem completeFinSteinerReplayWithThinIntervalWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithThinIntervalWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          steinerTraceThinIntervalWorkPolynomial n m height D.length+11*m+21+finArcRowsWordBudget n raw.length+3 := by
  let arcs := finArcRowsWithWordWork raw
  let late := fun τ hubs rows => lateSteinerWithThinIntervalWork G arcs.1 τ m hubs rows
  let prior := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D late
  let work := steinerTraceThinIntervalWorkPolynomial n m height D.length+11*m+21
  obtain ⟨exactArcs,assembly⟩ := finArcRowsWithWordWork_spec G raw same
  obtain ⟨sameRecord,_,traceWork⟩ := completeFinSteinerReplayWithThinIntervalEvaluator_spec G
    arcs.1 exactArcs raw same height m hm bits D
  obtain ⟨samePrefix,charged⟩ := completeFinSteinerReplayWithLateEvaluator_prefixes G raw same height m hm bits D
    feasible late work ⟨sameRecord,traceWork feasible⟩
  refine ⟨samePrefix,?_⟩
  have ready : arcs.2 ≤ finArcRowsWordBudget n raw.length := assembly
  dsimp only [completeFinSteinerReplayWithThinIntervalWork]
  change _+((prior.2.1+arcs.2)+3) ≤ _
  have bounded := Nat.add_le_add_right (Nat.add_le_add charged ready) 3
  simpa only [work,Nat.add_assoc] using bounded

/-- Fixed-height replay allowance with the late classification, fallback tests
and hub-leg preparation included in each evaluation. -/
def steinerTraceClassificationWorkPolynomial (n m height p : ℕ) : ℕ :=
  steinerTraceEarlySeedRankWorkPolynomial n height p+
    (p+1)*(lateSteinerIntervalPreparationWordBudget n m p+steinerThinIntervalWorkPolynomial n m p+2)

private theorem completeFinSteinerReplayWithClassificationEvaluator_spec {n : ℕ} (G : Arcs (Fin n))
    (arcs : {r : List (Fin n × Fin n) // r.Nodup}) (arcsEq : arcs.val.toFinset = G)
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let late := fun τ hubs rows => lateSteinerWithClassificationWork G arcs τ m hubs rows
    let out := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D late
    let old := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 ∧
      ((∀ d ∈ D, Reach G d.1 d.2) → out.2.1 ≤ steinerTraceClassificationWorkPolynomial n m height D.length+11*m+21) := by
  apply completeFinSteinerReplayWithLateEvaluator_spec G raw same height m hm bits D
    (fun τ hubs rows => lateSteinerWithClassificationWork G arcs τ m hubs rows)
    (lateSteinerIntervalPreparationWordBudget n m D.length+steinerThinIntervalWorkPolynomial n m D.length)
  · intro τ hubs rows P
    exact (lateSteinerWithClassificationWork_eq G arcs arcsEq τ m hm hubs rows P).trans
      (lateSteinerWithThinIntervalWork_eq G arcs arcsEq τ m hm hubs rows P)
  · intro early τ hubs rows edges count P short reachable
    have spent := lateSteinerWithClassificationWork_bound early arcs arcsEq τ m hm hubs rows edges count P reachable
    refine spent.trans (Nat.add_le_add (lateSteinerIntervalPreparationWordBudget_mono n m short) ?_)
    refine (steinerThinIntervalWorkBound_le n m P.length).trans ?_
    unfold steinerThinIntervalWorkPolynomial steinerThinResidualRouteWorkPolynomial steinerStreamingThinWorkPolynomial
    gcongr

/-- Run the same replay with explicit late classification and fallback scans. -/
def completeFinSteinerReplayWithClassificationWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  let rows := finArcRowsWithWordWork raw
  let out := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D
    (fun τ hubs thresholds => lateSteinerWithClassificationWork G rows.1 τ m hubs thresholds)
  (out.1,out.2.1+rows.2+3,out.2.2)

theorem completeFinSteinerReplayWithClassificationWork_spec {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithClassificationWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithThinIntervalWork G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 ∧
      ((∀ d ∈ D, Reach G d.1 d.2) → out.2.1 ≤ steinerTraceClassificationWorkPolynomial n m height D.length+
        11*m+21+finArcRowsWordBudget n raw.length+3) := by
  obtain ⟨arcs,ready⟩ := finArcRowsWithWordWork_spec G raw same
  obtain ⟨current,count,work⟩ := completeFinSteinerReplayWithClassificationEvaluator_spec G
    (finArcRowsWithWordWork raw).1 arcs raw same height m hm bits D
  obtain ⟨previous,priorCount,_⟩ := completeFinSteinerReplayWithThinIntervalWork_spec G raw same height m hm bits D
  exact ⟨current.trans previous.symm,count.trans priorCount.symm,
    fun feasible => Nat.add_le_add_right (Nat.add_le_add (work feasible) ready) 3⟩

/-- Exact fixed-budget prefix graphs with the late classification and thick
fallback driven by metered scans of the original graph arcs. -/
theorem completeFinSteinerReplayWithClassificationWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithClassificationWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          steinerTraceClassificationWorkPolynomial n m height D.length+11*m+21+finArcRowsWordBudget n raw.length+3 := by
  let arcs := finArcRowsWithWordWork raw
  let late := fun τ hubs rows => lateSteinerWithClassificationWork G arcs.1 τ m hubs rows
  let prior := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D late
  let work := steinerTraceClassificationWorkPolynomial n m height D.length+11*m+21
  obtain ⟨exactArcs,assembly⟩ := finArcRowsWithWordWork_spec G raw same
  obtain ⟨sameRecord,_,traceWork⟩ := completeFinSteinerReplayWithClassificationEvaluator_spec G
    arcs.1 exactArcs raw same height m hm bits D
  obtain ⟨samePrefix,charged⟩ := completeFinSteinerReplayWithLateEvaluator_prefixes G raw same height m hm bits D
    feasible late work ⟨sameRecord,traceWork feasible⟩
  refine ⟨samePrefix,?_⟩
  have ready : arcs.2 ≤ finArcRowsWordBudget n raw.length := assembly
  dsimp only [completeFinSteinerReplayWithClassificationWork]
  change _+((prior.2.1+arcs.2)+3) ≤ _
  have bounded := Nat.add_le_add_right (Nat.add_le_add charged ready) 3
  simpa only [work,Nat.add_assoc] using bounded

private def sameGraphAndLessSearch {W : Type*} (new old : Arcs W × ℕ) : Prop :=
  new.1 = old.1 ∧ new.2 ≤ old.2

private theorem replaySteinerTraceWithPhaseWork_related (n : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ × ℕ) (draw : Fin (completeSteinerHubCount V) → V)
    (late : ℕ → Finset V → List (V × V) → (Arcs V × ℕ) × ℕ)
    (priorLate : ℕ → Finset V → List (V × V) → Arcs V × ℕ)
    (valid : V × V → Prop)
    (compare : ∀ τ hubs P, (∀ d ∈ P, valid d) → sameGraphAndLessSearch (late τ hubs P).1 (priorLate τ hubs P))
    (D : List (V × V)) (inputValid : ∀ d ∈ D, valid d) (join : SteinerPhaseUnion V) :
    let out := replaySteinerTraceWithPhaseWork n hn early draw late D join
    let old := replaySteinerTraceWithEarlySeedReadsUsing n hn early draw priorLate D
    List.Forall₂ sameGraphAndLessSearch out.1 old.1 ∧ out.2.2 = old.2.2 := by
  have callback (T τ : ℕ) (hubs : Finset V) (P : List (V × V)) (ok : ∀ d ∈ P, valid d) :
      sameGraphAndLessSearch (evaluateSteinerTraceWithPhaseWork early T τ hubs late P join).1
        (evaluateSteinerTraceWithEarlySeedReads early T τ hubs priorLate P).1 := by
    let split := splitSteinerTraceWithWordWork T P
    have validLate (d : V × V) (hd : d ∈ split.1.2) : valid d := by
      change d ∈ (splitSteinerTraceWithWordWork T P).1.2 at hd
      rw [(splitSteinerTraceWithWordWork_spec T P).1] at hd
      exact ok d (List.mem_of_mem_drop hd)
    obtain ⟨graph,work⟩ := compare τ hubs split.1.2 validLate
    exact ⟨(join.graph_eq _ _).trans (congrArg ((early split.1.1).1 ∪ ·) graph),Nat.add_le_add_left work _⟩
  dsimp only [replaySteinerTraceWithPhaseWork,replaySteinerTraceWithEarlySeedReadsUsing,replaySteinerTraceWithCallback]
  exact replayFirstOccurrencesWithWordWork_rel _ _ sameGraphAndLessSearch valid (callback _ _ _) D inputValid

private theorem completeFinSteinerReplayWithLateEvaluator_related {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) (lateEval : FinLateReplayEvaluator n) (L : ℕ)
    (lateExact : ∀ (_early : EarlySteinerRule G) τ hubs rows, (∀ r ∈ rows.val, r.1 ∈ G) →
      rows.val.length ≤ m → ∀ P, (∀ d ∈ P, Reach G d.1 d.2) →
        sameGraphAndLessSearch (lateEval τ hubs rows P).1 (lateSteinerWithStoredThinThresholds G τ m hubs rows.val.toFinset P))
    (lateWork : ∀ (_early : EarlySteinerRule G) τ hubs rows, (∀ r ∈ rows.val, r.1 ∈ G) →
      rows.val.length ≤ m → ∀ P, P.length ≤ D.length → (∀ d ∈ P, Reach G d.1 d.2) →
        (lateEval τ hubs rows P).2 ≤ L)
    (join : SteinerPhaseUnion (Fin n)) (unionBudget : ℕ)
    (joinBound : ∀ left right, (join.combine left right).2 ≤ unionBudget) :
    let out := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D lateEval join
    let old := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
    List.Forall₂ sameGraphAndLessSearch out.1.1.1.1.1 old.1.1.1.1.1 ∧ out.2.2 = old.2.2 ∧
      out.2.1 ≤ steinerTraceEarlySeedRankWorkPolynomial n height D.length+
        (D.length+1)*(L+unionBudget+2)+11*m+21 := by
  let prepared := prepareFinSteinerWeightedForSeedWithSeedWork G raw same height
  let indexes := finSteinerReplaySeedIndexesWithWordWork G height raw same
  let decoded := decodeSteinerSeedWithArrayViewsFromPreparedScale G height n m (by simp) hm prepared.1.1 indexes.1 bits
  unfold completeFinSteinerReplayWithLateEvaluator completeFinSteinerReplayWithThinRowWork
    completeFinSteinerReplayWithSeedRankWorkUsing completeFinSteinerReplayWithCachedPhases replayFromCachedFinSteinerSeed
  dsimp only
  cases state : decoded.1.2 with
  | none =>
    have identical (records : List (Arcs (Fin n) × ℕ)) : List.Forall₂ sameGraphAndLessSearch records records := by
      induction records with
      | nil => exact .nil
      | cons row rest ih => exact .cons ⟨rfl,le_rfl⟩ ih
    refine ⟨identical _,rfl,?_⟩
    have fallback := (steinerFallbackPrefixScanWithWordWork_spec G D).2.le.trans
      (steinerFallbackReplayWordWork_bound n D.length)
    change (steinerFallbackPrefixScanWithWordWork G D).2+8 ≤ _
    unfold steinerTraceEarlySeedRankWorkPolynomial steinerTraceEarlySeedWorkBound
    omega
  | some entry =>
    rcases entry with ⟨seed,arrays⟩
    dsimp only
    let width := decoded.1.1
    let samples := finEarlySeedTrialsWithRankWork G height width.val width.property arrays.early
    let early := prepared.1.2.1 samples
    let rule := earlyRoundedRule G height seed.1
    let rows := prepareThinThresholdListByIndexWithWordWork G m hm indexes.1.arcs arrays.thin
    let oldRows := prepareThinThresholdRowsByIndexWithWordWork G m hm indexes.1.arcs arrays.thin
    let late := fun τ hubs => lateEval τ hubs rows.1
    let priorLate := fun τ hubs => lateSteinerWithStoredThinThresholds G τ m hubs oldRows.1
    obtain ⟨stored,rowCount,rowEdges,rowWork⟩ := prepareThinThresholdListByIndexWithWordWork_spec G m hm indexes.1.arcs arrays.thin
    have sameRows : rows.1.val.toFinset = oldRows.1 :=
      stored.trans (prepareThinThresholdRowsByIndexWithWordWork_spec G m hm indexes.1.arcs arrays.thin).1.symm
    have compare (τ : ℕ) (hubs : Finset (Fin n)) (P : List (Fin n × Fin n))
        (ok : ∀ d ∈ P, Reach G d.1 d.2) : sameGraphAndLessSearch (late τ hubs P).1 (priorLate τ hubs P) := by
      simpa only [late,priorLate,sameRows] using lateExact rule τ hubs rows.1 rowEdges rowCount.le P ok
    obtain ⟨records,calls⟩ := replaySteinerTraceWithPhaseWork_related n (by simp) early seed.2.1 late priorLate
      (fun d => Reach G d.1 d.2) compare D feasible join
    refine ⟨records,calls,?_⟩
    let B := earlyRoundingSeedReadPolynomial n height*earlySeedArrayReadWordBudget height
    obtain ⟨_,perRead⟩ := finEarlySeedTrialsWithRankWork_spec G height width.val width.property arrays.early
    have earlyBound (P : List (Fin n × Fin n)) : (early P).2.2 ≤ (P.length+1)*B :=
      ((prepareFinSteinerWeightedForSeedWithSeedWork_spec G raw same height).2.2.2 samples _ perRead P).2
    have bound (τ : ℕ) (hubs : Finset (Fin n)) (P : List (Fin n × Fin n))
        (short : P.length ≤ D.length) (reachable : ∀ d ∈ P, Reach G d.1 d.2) : (late τ hubs P).2 ≤ L :=
      lateWork rule τ hubs rows.1 rowEdges rowCount.le P short reachable
    have work := replaySteinerTraceWithPhaseWork_bound_using n (by simp) early B earlyBound seed.2.1 late D
      (fun d => Reach G d.1 d.2) feasible L bound join unionBudget joinBound
    change (replaySteinerTraceWithPhaseWork n (by simp) early seed.2.1 late D join).2.1+rows.2+9+8 ≤ _
    change _ ≤ steinerTraceEarlySeedRankWorkPolynomial n height D.length+(D.length+1)*(L+unionBudget+2) at work
    change rows.2 = 11*m+4 at rowWork
    omega

private theorem sameGraphAndLessSearch_maps {W : Type*} {left right : List (Arcs W × ℕ)}
    (h : List.Forall₂ sameGraphAndLessSearch left right) :
    left.map Prod.fst = right.map Prod.fst ∧ (left.map Prod.snd).sum ≤ (right.map Prod.snd).sum := by
  induction h with
  | nil => simp
  | @cons a b left right current _ ih =>
    obtain ⟨graph,cost⟩ := current
    exact ⟨by simp only [List.map_cons,graph,ih.1],
      by simpa only [List.map_cons,List.sum_cons] using Nat.add_le_add cost ih.2⟩

private theorem replaySteinerTraceWithPhaseWork_changeEarly (n : ℕ) (hn : n = Fintype.card V)
    (early prior : List (V × V) → Arcs V × ℕ × ℕ) (draw : Fin (completeSteinerHubCount V) → V)
    (late : ℕ → Finset V → List (V × V) → (Arcs V × ℕ) × ℕ)
    (D : List (V × V)) (join : SteinerPhaseUnion V) (extra : ℕ)
    (compare : ∀ P, sameGraphAndLessSearch ((early P).1, (early P).2.1) ((prior P).1, (prior P).2.1))
    (perPrefix : ∀ P, P.length ≤ D.length → (early P).2.2 ≤ extra) :
    let out := replaySteinerTraceWithPhaseWork n hn early draw late D join
    let old := replaySteinerTraceWithPhaseWork n hn prior draw late D join
    List.Forall₂ sameGraphAndLessSearch out.1 old.1 ∧ out.2.2 = old.2.2 ∧
      out.2.1 ≤ old.2.1 + (D.length+1)*extra := by
  let params := steinerTraceParametersWithWordWork n
  have correct : params.1.hubCount = completeSteinerHubCount V := by
    rw [params.1.hubCount_eq, hn]
    rfl
  let hubs := collectSteinerHubsWithWordWork correct draw
  let evaluate (metric : List (V × V) → Arcs V × ℕ × ℕ) (P : List (V × V)) :=
    evaluateSteinerTraceWithPhaseWork metric params.1.earlyCutoff params.1.thinThreshold hubs.1 late P join
  let next := evaluate early
  let previous := evaluate prior
  have relate (P : List (V × V)) : sameGraphAndLessSearch (next P).1 (previous P).1 := by
    let split := splitSteinerTraceWithWordWork params.1.earlyCutoff P
    obtain ⟨graph, search⟩ := compare split.1.1
    let final := late params.1.thinThreshold hubs.1 split.1.2
    change (join.combine (early split.1.1).1 final.1.1).1 =
        (join.combine (prior split.1.1).1 final.1.1).1 ∧
      (early split.1.1).2.1+final.1.2 ≤ (prior split.1.1).2.1+final.1.2
    exact ⟨congrArg (fun G => (join.combine G final.1.1).1) graph, Nat.add_le_add_right search _⟩
  have more (P : List (V × V)) (short : P.length ≤ D.length) : (next P).2 ≤ (previous P).2+extra := by
    let split := splitSteinerTraceWithWordWork params.1.earlyCutoff P
    have shorter : split.1.1.length ≤ D.length := by
      change (splitSteinerTraceWithWordWork params.1.earlyCutoff P).1.1.length ≤ D.length
      rw [(splitSteinerTraceWithWordWork_spec _ _).1]
      exact (List.length_take_le' _ _).trans short
    have work := perPrefix split.1.1 shorter
    have graph := (compare split.1.1).1
    let final := late params.1.thinThreshold hubs.1 split.1.2
    change split.2+8+(early split.1.1).2.2+final.2+7+(join.combine (early split.1.1).1 final.1.1).2 ≤
      split.2+8+(prior split.1.1).2.2+final.2+7+(join.combine (prior split.1.1).1 final.1.1).2+extra
    change (early split.1.1).1 = (prior split.1.1).1 at graph
    rw [graph]
    omega
  obtain ⟨records, calls⟩ := replayFirstOccurrencesWithWordWork_rel next previous sameGraphAndLessSearch
    (fun _ => True) (fun P _ => relate P) D (by simp)
  have measured := replayFirstOccurrencesWithWordWork_work_le next previous D extra more
  refine ⟨records, calls, ?_⟩
  change (replayFirstOccurrencesWithWordWork next D).2.1 + params.2 + hubs.2 + 10 ≤
    (replayFirstOccurrencesWithWordWork previous D).2.1 + params.2 + hubs.2 + 10 + (D.length+1)*extra
  omega

@[inline] private def hubRouteLateEvaluator {n : ℕ} (G : Arcs (Fin n))
    (arcs : {r : List (Fin n × Fin n) // r.Nodup}) (m : ℕ) (vertices : List (Fin n)) : FinLateReplayEvaluator n :=
  fun τ sample rows D =>
    let out := lateSteinerWithListHubWork G arcs τ m vertices sample rows D
    ((out.1,0),out.2)

private def steinerTraceHubAndUnionWorkBound (n m height p unionBudget : ℕ) : ℕ :=
  steinerTraceEarlySeedRankWorkPolynomial n height p+
    (p+1)*(lateHubRoutingWordBudget n m p+
      (steinerThinIntervalWorkPolynomial n m p+thinRoundThresholdSearchWorkPolynomial n m p)+unionBudget+2)

def steinerTraceHubRoutingWorkPolynomial (n m height p : ℕ) : ℕ :=
  steinerTraceHubAndUnionWorkBound n m height p 0

/-- Include the outer union along with the measured early and late work. -/
def steinerTracePhaseUnionWorkPolynomial (n m height p : ℕ) : ℕ :=
  steinerTraceHubAndUnionWorkBound n m height p (steinerPhaseUnionWordBudget n)

private theorem completeFinSteinerReplayWithHubRouteEvaluator_spec {n : ℕ} (G : Arcs (Fin n))
    (arcs : {r : List (Fin n × Fin n) // r.Nodup}) (arcsEq : arcs.val.toFinset = G)
    (vertices : List (Fin n)) (simple : vertices.Nodup) (complete : ∀ v : Fin n, v ∈ vertices)
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) (join : SteinerPhaseUnion (Fin n)) (unionBudget : ℕ)
    (joinBound : ∀ left right, (join.combine left right).2 ≤ unionBudget) :
    let out := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D
      (hubRouteLateEvaluator G arcs m vertices) join
    let old := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
    List.Forall₂ sameGraphAndLessSearch out.1.1.1.1.1 old.1.1.1.1.1 ∧ out.2.2 = old.2.2 ∧
      out.2.1 ≤ steinerTraceHubAndUnionWorkBound n m height D.length unionBudget+11*m+21 := by
  apply completeFinSteinerReplayWithLateEvaluator_related G raw same height m hm bits D feasible
    (hubRouteLateEvaluator G arcs m vertices)
    (lateHubRoutingWordBudget n m D.length+
      (steinerThinIntervalWorkPolynomial n m D.length+thinRoundThresholdSearchWorkPolynomial n m D.length))
    (join := join) (unionBudget := unionBudget) (joinBound := joinBound)
  · intro early τ sample rows edges count P ok
    exact ⟨lateSteinerWithListHubWork_graph early arcs arcsEq τ m hm vertices simple complete sample
      rows edges count P ok, Nat.zero_le _⟩
  · intro early τ sample rows edges count P short ok
    have work := (lateSteinerWithListHubWork_spec early arcs arcsEq τ m hm vertices simple complete
      sample rows edges count P ok).2
    have interval : steinerThinIntervalWorkBound n m P.length ≤ steinerThinIntervalWorkPolynomial n m D.length := by
      refine (steinerThinIntervalWorkBound_le n m P.length).trans ?_
      unfold steinerThinIntervalWorkPolynomial steinerThinResidualRouteWorkPolynomial steinerStreamingThinWorkPolynomial
      gcongr
    have legacy : thinRoundThresholdSearchWorkPolynomial n m P.length ≤
        thinRoundThresholdSearchWorkPolynomial n m D.length := by
      unfold thinRoundThresholdSearchWorkPolynomial
      gcongr
    exact work.trans (Nat.add_le_add (lateHubRoutingWordBudget_mono n m short) (Nat.add_le_add interval legacy))

private def completeFinSteinerReplayWithHubRoutingUsing {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) (join : SteinerPhaseUnion (Fin n))
    (prepared : SteinerSeedPreparationWithSeedWork G height × ℕ :=
      prepareFinSteinerWeightedForSeedWithSeedWork G raw same height) :=
  let arcs := finArcRowsWithWordWork raw
  let vertices := finVerticesWithWordWork n
  let out := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D
    (hubRouteLateEvaluator G arcs.1 m vertices.1) join prepared
  (out.1,out.2.1+arcs.2+vertices.2+5,out.2.2)


private theorem completeFinSteinerReplayWithHubRoutingUsing_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) (join : SteinerPhaseUnion (Fin n)) (unionBudget : ℕ)
    (joinBound : ∀ left right, (join.combine left right).2 ≤ unionBudget) :
    let out := completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D join
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTraceHubAndUnionWorkBound n m height D.length unionBudget+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6 := by
  let arcs := finArcRowsWithWordWork raw
  let vertices := finVerticesWithWordWork n
  let current := completeFinSteinerReplayWithLateEvaluator G raw same height m hm bits D
    (hubRouteLateEvaluator G arcs.1 m vertices.1) join
  let old := completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D
  let base := current.1.1.1
  let former := old.1.1.1
  let priorBudget := completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
    finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
    (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21)
  let hubBudget := steinerTraceHubAndUnionWorkBound n m height D.length unionBudget+11*m+21
  obtain ⟨exactArcs,arcWork⟩ := finArcRowsWithWordWork_spec G raw same
  obtain ⟨simple,complete,vertexWork⟩ := finVerticesWithWordWork_spec n
  obtain ⟨records,count,hubWork⟩ := completeFinSteinerReplayWithHubRouteEvaluator_spec G
    arcs.1 exactArcs vertices.1 simple complete raw same height m hm bits D feasible join unionBudget joinBound
  obtain ⟨graphs,search⟩ := sameGraphAndLessSearch_maps records
  obtain ⟨prefixes,prior⟩ := completeFinSteinerReplayWithThinRowWork_prefixes G raw same height m hm bits D feasible
  have graphMatch : base.1.1.map Prod.fst = former.1.1.map Prod.fst := graphs
  have workDecrease : (base.1.1.map Prod.snd).sum ≤ (former.1.1.map Prod.snd).sum := search
  have priorBound : (former.1.1.map Prod.snd).sum+former.1.2.1+former.1.2.2.1+former.1.2.2.2+former.2+
      old.1.1.2+old.1.2 ≤ priorBudget := by
    have reduced := (Nat.le_add_right _ old.2.1).trans prior
    simpa only [priorBudget,Nat.add_assoc] using reduced
  have less : (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+
      current.1.1.2+current.1.2 ≤ priorBudget := by
    change _+former.1.2.1+former.1.2.2.1+former.1.2.2.2+former.2+old.1.1.2+old.1.2 ≤ _
    omega
  refine ⟨graphMatch.trans prefixes,count,?_⟩
  have routing : current.2.1 ≤ hubBudget := hubWork
  have preparation : arcs.2 ≤ finArcRowsWordBudget n raw.length := arcWork
  have vertexAssembly : vertices.2 = 8*n+1 := vertexWork
  change (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+current.1.1.2+current.1.2+
    (current.2.1+arcs.2+vertices.2+5) ≤ priorBudget+hubBudget+finArcRowsWordBudget n raw.length+8*n+6
  omega

/-- Share the original arc and vertex lists across the replay. The late phase
reports its measured routing work alongside the existing early search allowance. -/
def completeFinSteinerReplayWithHubRoutingWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D (unmeteredPhaseUnion (Fin n))

/-- Meter the outer union of the early graph and the list-backed late result. -/
def completeFinSteinerReplayWithPhaseUnionWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D (meteredPhaseUnion (Fin n))

/-- Metering the outer union leaves every graph and search record intact,
and the number of evaluations agrees in both seed branches. -/
theorem completeFinSteinerReplayWithPhaseUnionWork_records {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithPhaseUnionWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithHubRoutingWork G raw same height m hm bits D
    out.1 = old.1 ∧ out.2.2 = old.2.2 := by
  let prepared := prepareFinSteinerWeightedForSeedWithSeedWork G raw same height
  let indexes := finSteinerReplaySeedIndexesWithWordWork G height raw same
  let decoded := decodeSteinerSeedWithArrayViewsFromPreparedScale G height n m (by simp) hm prepared.1.1 indexes.1 bits
  unfold completeFinSteinerReplayWithHubRoutingWork completeFinSteinerReplayWithPhaseUnionWork
    completeFinSteinerReplayWithHubRoutingUsing completeFinSteinerReplayWithLateEvaluator
    completeFinSteinerReplayWithCachedPhases replayFromCachedFinSteinerSeed
  dsimp only
  cases state : decoded.1.2 with
  | none => exact ⟨rfl, rfl⟩
  | some entry =>
    rcases entry with ⟨seed, arrays⟩
    dsimp only
    let width := decoded.1.1
    let samples := finEarlySeedTrialsWithRankWork G height width.val width.property arrays.early
    let early := prepared.1.2.1 samples
    let rows := prepareThinThresholdListByIndexWithWordWork G m hm indexes.1.arcs arrays.thin
    let arcs := finArcRowsWithWordWork raw
    let vertices := finVerticesWithWordWork n
    let late := fun τ hubs => hubRouteLateEvaluator G arcs.1 m vertices.1 τ hubs rows.1
    let first := fun T τ hubs P => evaluateSteinerTraceWithPhaseWork early T τ hubs late P (meteredPhaseUnion (Fin n))
    let second := fun T τ hubs P => evaluateSteinerTraceWithPhaseWork early T τ hubs late P
    obtain ⟨records, calls⟩ := replaySteinerTraceWithCallback_records_eq n (by simp) seed.2.1 D first second
      (by
        intro T τ hubs P
        dsimp only [first, second, evaluateSteinerTraceWithPhaseWork, unmeteredPhaseUnion]
        rw [(meteredPhaseUnion (Fin n)).graph_eq])
    have sameRows : (replaySteinerTraceWithPhaseWork n (by simp) early seed.2.1 late D
        (meteredPhaseUnion (Fin n))).1 = (replaySteinerTraceWithPhaseWork n (by simp) early seed.2.1 late D).1 :=
      records
    have sameCalls : (replaySteinerTraceWithPhaseWork n (by simp) early seed.2.1 late D
        (meteredPhaseUnion (Fin n))).2.2 = (replaySteinerTraceWithPhaseWork n (by simp) early seed.2.1 late D).2.2 :=
      calls
    rw [sameRows, sameCalls]
    exact ⟨rfl, rfl⟩

/-- Exact prefix graphs and evaluation counts on feasible traces, with
the list-backed late routing charged at fixed forest height. -/
theorem completeFinSteinerReplayWithHubRoutingWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithHubRoutingWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTraceHubRoutingWorkPolynomial n m height D.length+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6 := by
  exact completeFinSteinerReplayWithHubRoutingUsing_prefixes G raw same height m hm bits D feasible
    (unmeteredPhaseUnion (Fin n)) 0 (fun _ _ => le_rfl)

/-- Exact prefix graphs and evaluation counts with the outer union charged
once for every evaluated prefix. -/
theorem completeFinSteinerReplayWithPhaseUnionWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithPhaseUnionWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTracePhaseUnionWorkPolynomial n m height D.length+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6 := by
  refine completeFinSteinerReplayWithHubRoutingUsing_prefixes G raw same height m hm bits D feasible
    (meteredPhaseUnion (Fin n)) (steinerPhaseUnionWordBudget n) ?_
  intro left right
  simpa only [meteredPhaseUnion,Fintype.card_fin] using steinerPhaseUnionWordBudget_bound left right

/-- Replay the early phase with the weighted history solver prepared once.
The existing list-backed late phase and the metered outer union are shared. -/
def completeFinSteinerReplayWithEarlyHistoryWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D (meteredPhaseUnion (Fin n))
    (prepareFinSteinerWeightedForSeedWithHistoryWork G raw same height)

private theorem finSteinerEarlyHistoryWordPolynomial_mono (n height seed : ℕ) :
    Monotone (fun p => finSteinerEarlyHistoryWordPolynomial n height p seed) := by
  intro p q shorter
  unfold finSteinerEarlyHistoryWordPolynomial
  dsimp only
  exact Nat.mul_le_mul (Nat.add_le_add_right shorter 1) (Nat.add_le_add_right
    (earlyWeightedHistoryWordBudget_le le_rfl le_rfl le_rfl le_rfl le_rfl shorter) _)

/-- Allow the extra early metric work once per evaluated demand prefix. -/
def steinerTraceEarlyHistoryExtraPolynomial (n height p : ℕ) : ℕ :=
  (p+1)*finSteinerEarlyHistoryWordPolynomial n height p (earlySeedArrayReadWordBudget height)

private theorem completeFinSteinerReplayWithPreparedEarlyWork_compare {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (fresh prior : SteinerSeedPreparationWithSeedWork G height × ℕ) (extraSetup extra : ℕ)
    (scale : fresh.1.1 = prior.1.1) (setup : fresh.1.2.2 = prior.1.2.2)
    (setupWork : fresh.2 ≤ prior.2 + extraSetup)
    (earlySpec : ∀ (samples : ForestTrialArrayWithSeedWork (Fin n) height (forestScale G height)
        (earlyTrialCount (Fin n) height)),
      (∀ i, forestSampleWorkBound (samples i) (earlySeedArrayReadWordBudget height)) → ∀ P,
      let out := fresh.1.2.1 samples P
      let old := prior.1.2.1 samples P
      out.1 = old.1 ∧ out.2.1 ≤ old.2.1 ∧ (P.length ≤ D.length → out.2.2 ≤ extra)) :
    let out := completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D
      (meteredPhaseUnion (Fin n)) fresh
    let old := completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D
      (meteredPhaseUnion (Fin n)) prior
    let base := out.1.1.1
    let prior := old.1.1.1
    base.1.1.map Prod.fst = prior.1.1.map Prod.fst ∧
      (base.1.1.map Prod.snd).sum ≤ (prior.1.1.map Prod.snd).sum ∧ out.2.2 = old.2.2 ∧
      base.1.2 = prior.1.2 ∧ base.2 = prior.2 ∧ out.1.2 = old.1.2 ∧
      out.1.1.2 ≤ old.1.1.2 + extraSetup ∧
      out.2.1 ≤ old.2.1 + (D.length+1)*extra := by
  let indexes := finSteinerReplaySeedIndexesWithWordWork G height raw same
  let decoded := decodeSteinerSeedWithArrayViewsFromPreparedScale G height n m (by simp) hm prior.1.1 indexes.1 bits
  let arcs := finArcRowsWithWordWork raw
  let vertices := finVerticesWithWordWork n
  let join := meteredPhaseUnion (Fin n)
  let sampleBudget := earlySeedArrayReadWordBudget height
  unfold completeFinSteinerReplayWithHubRoutingUsing completeFinSteinerReplayWithLateEvaluator
    completeFinSteinerReplayWithCachedPhases
  dsimp only
  rw [scale, setup]
  unfold replayFromCachedFinSteinerSeed
  cases state : decoded.1.2 with
  | none =>
    refine ⟨rfl, le_rfl, rfl, rfl, rfl, rfl, setupWork, ?_⟩
    exact Nat.le_add_right _ _
  | some entry =>
    rcases entry with ⟨seed, arrays⟩
    dsimp only
    let width := decoded.1.1
    let samples := finEarlySeedTrialsWithRankWork G height width.val width.property arrays.early
    let early := fresh.1.2.1 samples
    let previous := prior.1.2.1 samples
    let rows := prepareThinThresholdListByIndexWithWordWork G m hm indexes.1.arcs arrays.thin
    let late := fun τ hubs => hubRouteLateEvaluator G arcs.1 m vertices.1 τ hubs rows.1
    have reads : ∀ i, forestSampleWorkBound (samples i) sampleBudget :=
      (finEarlySeedTrialsWithRankWork_spec G height width.val width.property arrays.early).2
    have compare (P : List (Fin n × Fin n)) : sameGraphAndLessSearch ((early P).1, (early P).2.1)
        ((previous P).1, (previous P).2.1) :=
      ⟨(earlySpec samples reads P).1, (earlySpec samples reads P).2.1⟩
    have earlyWork (P : List (Fin n × Fin n)) (short : P.length ≤ D.length) : (early P).2.2 ≤ extra :=
      (earlySpec samples reads P).2.2 short
    obtain ⟨rowsRelated, count, work⟩ := replaySteinerTraceWithPhaseWork_changeEarly n (by simp)
      early previous seed.2.1 late D join extra compare earlyWork
    obtain ⟨graphs, search⟩ := sameGraphAndLessSearch_maps rowsRelated
    let next := replaySteinerTraceWithPhaseWork n (by simp) early seed.2.1 late D join
    let old := replaySteinerTraceWithPhaseWork n (by simp) previous seed.2.1 late D join
    change next.1.map Prod.fst = old.1.map Prod.fst ∧
      (next.1.map Prod.snd).sum ≤ (old.1.map Prod.snd).sum ∧ next.2.2 = old.2.2 ∧
      prior.1.2.2 = prior.1.2.2 ∧ decoded.2 = decoded.2 ∧ indexes.2 = indexes.2 ∧
      fresh.2 ≤ prior.2 + extraSetup ∧
      next.2.1+rows.2+9+8+arcs.2+vertices.2+5 ≤
        old.2.1+rows.2+9+8+arcs.2+vertices.2+5+(D.length+1)*extra
    refine ⟨graphs, search, count, rfl, rfl, rfl, setupWork, ?_⟩
    change next.2.1 ≤ old.2.1 + (D.length+1)*extra at work
    omega

/-- Changing the early solver preserves all prefix graphs and the number of
evaluations. The work comparison includes the new preparation and solver. -/
theorem completeFinSteinerReplayWithEarlyHistoryWork_compare {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithEarlyHistoryWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithPhaseUnionWork G raw same height m hm bits D
    let base := out.1.1.1
    let prior := old.1.1.1
    base.1.1.map Prod.fst = prior.1.1.map Prod.fst ∧
      (base.1.1.map Prod.snd).sum ≤ (prior.1.1.map Prod.snd).sum ∧ out.2.2 = old.2.2 ∧
      base.1.2 = prior.1.2 ∧ base.2 = prior.2 ∧ out.1.2 = old.1.2 ∧
      out.1.1.2 ≤ old.1.1.2 + finForestNetworkPairKeysWordPolynomial n height + 3 ∧
      out.2.1 ≤ old.2.1 + steinerTraceEarlyHistoryExtraPolynomial n height D.length := by
  let fresh := prepareFinSteinerWeightedForSeedWithHistoryWork G raw same height
  let prior := prepareFinSteinerWeightedForSeedWithSeedWork G raw same height
  let extra := finSteinerEarlyHistoryWordPolynomial n height D.length (earlySeedArrayReadWordBudget height)
  let extraSetup := finForestNetworkPairKeysWordPolynomial n height + 3
  obtain ⟨scale, setup, _, each⟩ := prepareFinSteinerWeightedForSeedWithHistoryWork_spec G raw same height
  have newSetup : fresh.2 = prior.2 + (finForestNetworkPairKeysWithWordWork n height).2 + 3 :=
    prepareFinSteinerWeightedForSeedWithHistoryWork_setup G raw same height
  have setupWork : fresh.2 ≤ prior.2 + extraSetup := by
    rw [newSetup, ← Nat.add_assoc]
    exact Nat.add_le_add_right (Nat.add_le_add_left (finForestNetworkPairKeysWithWordWork_spec n height).2.2.2 _) _
  have compare := completeFinSteinerReplayWithPreparedEarlyWork_compare G raw same height m hm bits D
    fresh prior extraSetup extra scale setup setupWork (fun samples reads P => by
      obtain ⟨graph, search, work⟩ := each samples (earlySeedArrayReadWordBudget height) reads P
      exact ⟨graph, search, fun short =>
        work.trans (finSteinerEarlyHistoryWordPolynomial_mono n height _ short)⟩)
  simpa only [completeFinSteinerReplayWithEarlyHistoryWork, completeFinSteinerReplayWithPhaseUnionWork,
    steinerTraceEarlyHistoryExtraPolynomial, fresh, prior, extraSetup, extra, Nat.add_assoc] using compare

/-- On feasible traces the new early solver retains the same exact prefix
graphs with a fixed-height bound for its additional measured work. -/
theorem completeFinSteinerReplayWithEarlyHistoryWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithEarlyHistoryWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTracePhaseUnionWorkPolynomial n m height D.length+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6 + finForestNetworkPairKeysWordPolynomial n height + 3 +
          steinerTraceEarlyHistoryExtraPolynomial n height D.length := by
  obtain ⟨graphs, search, counts, setup, decode, index, keyWork, replayWork⟩ :=
    completeFinSteinerReplayWithEarlyHistoryWork_compare G raw same height m hm bits D
  obtain ⟨exactGraphs, exactCounts, oldWork⟩ :=
    completeFinSteinerReplayWithPhaseUnionWork_prefixes G raw same height m hm bits D feasible
  refine ⟨graphs.trans exactGraphs, counts.trans exactCounts, ?_⟩
  rw [setup, decode, index]
  omega

/-- Count the forest charge lookups inside the complete bounded-bit
replay. The early solver, decoder, and late phase are shared. -/
def completeFinSteinerReplayWithRoundingChargeWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D (meteredPhaseUnion (Fin n))
    (prepareFinSteinerWeightedForSeedWithRoundingChargeWork G raw same height)

private theorem finSteinerEarlyRoundingChargeWordPolynomial_mono (n height seed : ℕ) :
    Monotone (fun p => finSteinerEarlyRoundingChargeWordPolynomial n height p seed) := by
  intro p q short
  unfold finSteinerEarlyRoundingChargeWordPolynomial
  dsimp only
  exact Nat.add_le_add (finSteinerEarlyHistoryWordPolynomial_mono n height seed short)
    (Nat.mul_le_mul (Nat.add_le_add_right short 1)
      (earlyRoundingChargeWordBudget_le le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl short))

def steinerTraceRoundingChargeExtraPolynomial (n height p : ℕ) : ℕ :=
  (p+1)*finSteinerEarlyRoundingChargeWordPolynomial n height p (earlySeedArrayReadWordBudget height)

/-- Metered charge reads leave each prefix graph and the number of replay
evaluations intact, including on the exhausted-seed branch. -/
theorem completeFinSteinerReplayWithRoundingChargeWork_compare {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithRoundingChargeWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithEarlyHistoryWork G raw same height m hm bits D
    let base := out.1.1.1
    let prior := old.1.1.1
    base.1.1.map Prod.fst = prior.1.1.map Prod.fst ∧
      (base.1.1.map Prod.snd).sum ≤ (prior.1.1.map Prod.snd).sum ∧ out.2.2 = old.2.2 ∧
      base.1.2 = prior.1.2 ∧ base.2 = prior.2 ∧ out.1.2 = old.1.2 ∧
      out.1.1.2 ≤ old.1.1.2 ∧ out.2.1 ≤ old.2.1 + steinerTraceRoundingChargeExtraPolynomial n height D.length := by
  let fresh := prepareFinSteinerWeightedForSeedWithRoundingChargeWork G raw same height
  let prior := prepareFinSteinerWeightedForSeedWithHistoryWork G raw same height
  let extra := finSteinerEarlyRoundingChargeWordPolynomial n height D.length (earlySeedArrayReadWordBudget height)
  obtain ⟨scale, setup, work, each⟩ := prepareFinSteinerWeightedForSeedWithRoundingChargeWork_spec G raw same height
  have compare := completeFinSteinerReplayWithPreparedEarlyWork_compare G raw same height m hm bits D
    fresh prior 0 extra scale setup (work.le.trans (Nat.le_add_right _ _)) (fun samples reads P => by
      obtain ⟨graph, search, bound⟩ := each samples (earlySeedArrayReadWordBudget height) reads P
      exact ⟨graph, search, fun short =>
        bound.trans (finSteinerEarlyRoundingChargeWordPolynomial_mono n height _ short)⟩)
  simpa only [completeFinSteinerReplayWithRoundingChargeWork, completeFinSteinerReplayWithEarlyHistoryWork,
    steinerTraceRoundingChargeExtraPolynomial, fresh, prior, extra, Nat.add_zero] using compare

/-- On feasible demands the exact prefix replay includes the charge reads
in its fixed-height bound for recorded operations. -/
theorem completeFinSteinerReplayWithRoundingChargeWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithRoundingChargeWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTracePhaseUnionWorkPolynomial n m height D.length+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6+finForestNetworkPairKeysWordPolynomial n height+3 +
          steinerTraceEarlyHistoryExtraPolynomial n height D.length +
          steinerTraceRoundingChargeExtraPolynomial n height D.length := by
  obtain ⟨graphs, search, counts, setup, decode, index, keyWork, replayWork⟩ :=
    completeFinSteinerReplayWithRoundingChargeWork_compare G raw same height m hm bits D
  obtain ⟨exactGraphs, exactCounts, oldWork⟩ :=
    completeFinSteinerReplayWithEarlyHistoryWork_prefixes G raw same height m hm bits D feasible
  refine ⟨graphs.trans exactGraphs, counts.trans exactCounts, ?_⟩
  rw [setup, decode, index]
  omega

/-- Use one construction of the forest vertices and network keys to meter
the current demands' attachments at every evaluated early metric. -/
def completeFinSteinerReplayWithAttachmentWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D (meteredPhaseUnion (Fin n))
    (prepareFinSteinerWeightedForSeedWithAttachmentWork G raw same height)

private theorem finSteinerEarlyAttachmentWordPolynomial_mono (n height seed : ℕ) :
    Monotone (fun p => finSteinerEarlyAttachmentWordPolynomial n height p seed) := by
  intro p q short
  unfold finSteinerEarlyAttachmentWordPolynomial
  dsimp only
  exact Nat.add_le_add (finSteinerEarlyRoundingChargeWordPolynomial_mono n height seed short)
    (Nat.mul_le_mul (Nat.add_le_add_right short 1) (earlyAttachmentWordBudget_le le_rfl le_rfl short))

def steinerTraceAttachmentExtraPolynomial (n height p : ℕ) : ℕ :=
  (p+1)*finSteinerEarlyAttachmentWordPolynomial n height p (earlySeedArrayReadWordBudget height)

/-- The shared vertex rows preserve the replay's exact graphs and number
of prefix evaluations, including on exhausted or infeasible inputs. -/
theorem completeFinSteinerReplayWithAttachmentWork_compare {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithAttachmentWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithEarlyHistoryWork G raw same height m hm bits D
    let base := out.1.1.1
    let prior := old.1.1.1
    base.1.1.map Prod.fst = prior.1.1.map Prod.fst ∧
      (base.1.1.map Prod.snd).sum ≤ (prior.1.1.map Prod.snd).sum ∧ out.2.2 = old.2.2 ∧
      base.1.2 = prior.1.2 ∧ base.2 = prior.2 ∧ out.1.2 = old.1.2 ∧
      out.1.1.2 ≤ old.1.1.2+3 ∧ out.2.1 ≤ old.2.1 + steinerTraceAttachmentExtraPolynomial n height D.length := by
  let fresh := prepareFinSteinerWeightedForSeedWithAttachmentWork G raw same height
  let prior := prepareFinSteinerWeightedForSeedWithHistoryWork G raw same height
  let extra := finSteinerEarlyAttachmentWordPolynomial n height D.length (earlySeedArrayReadWordBudget height)
  obtain ⟨scale, setup, work, each⟩ := prepareFinSteinerWeightedForSeedWithAttachmentWork_spec G raw same height
  have compare := completeFinSteinerReplayWithPreparedEarlyWork_compare G raw same height m hm bits D
    fresh prior 3 extra scale setup work.le (fun samples reads P => by
      obtain ⟨graph, search, bound⟩ := each samples (earlySeedArrayReadWordBudget height) reads P
      exact ⟨graph, search, fun short =>
        bound.trans (finSteinerEarlyAttachmentWordPolynomial_mono n height _ short)⟩)
  exact compare

/-- On feasible traces the complete prefix graphs and evaluation count
agree with the reference replay, with an explicit attachment work bound. -/
theorem completeFinSteinerReplayWithAttachmentWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithAttachmentWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTracePhaseUnionWorkPolynomial n m height D.length+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6+finForestNetworkPairKeysWordPolynomial n height+3 +
          steinerTraceEarlyHistoryExtraPolynomial n height D.length + 3 +
          steinerTraceAttachmentExtraPolynomial n height D.length := by
  obtain ⟨graphs, search, counts, setup, decode, index, keyWork, replayWork⟩ :=
    completeFinSteinerReplayWithAttachmentWork_compare G raw same height m hm bits D
  obtain ⟨exactGraphs, exactCounts, oldWork⟩ :=
    completeFinSteinerReplayWithEarlyHistoryWork_prefixes G raw same height m hm bits D feasible
  refine ⟨graphs.trans exactGraphs, counts.trans exactCounts, ?_⟩
  rw [setup, decode, index]
  omega

/-- Count the terminal-label and table reads inside the weighted solver
and forest rounding at every evaluated early metric. -/
def completeFinSteinerReplayWithMetricLabelWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D (meteredPhaseUnion (Fin n))
    (prepareFinSteinerWeightedForSeedWithMetricLabelWork G raw same height)

def steinerTraceMetricLabelExtraPolynomial (n height p : ℕ) : ℕ :=
  (p+1)*finSteinerEarlyMetricLabelWordPolynomial n height p (earlySeedArrayReadWordBudget height)

/-- Metering the metric queries preserves exact prefix graphs and the
number of evaluations for every trace. -/
theorem completeFinSteinerReplayWithMetricLabelWork_compare {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithMetricLabelWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithEarlyHistoryWork G raw same height m hm bits D
    let base := out.1.1.1
    let prior := old.1.1.1
    base.1.1.map Prod.fst = prior.1.1.map Prod.fst ∧
      (base.1.1.map Prod.snd).sum ≤ (prior.1.1.map Prod.snd).sum ∧ out.2.2 = old.2.2 ∧
      base.1.2 = prior.1.2 ∧ base.2 = prior.2 ∧ out.1.2 = old.1.2 ∧
      out.1.1.2 ≤ old.1.1.2+3 ∧ out.2.1 ≤ old.2.1 + steinerTraceMetricLabelExtraPolynomial n height D.length := by
  let fresh := prepareFinSteinerWeightedForSeedWithMetricLabelWork G raw same height
  let prior := prepareFinSteinerWeightedForSeedWithHistoryWork G raw same height
  let extra := finSteinerEarlyMetricLabelWordPolynomial n height D.length (earlySeedArrayReadWordBudget height)
  obtain ⟨scale, setup, work, each⟩ := prepareFinSteinerWeightedForSeedWithMetricLabelWork_spec G raw same height
  have compare := completeFinSteinerReplayWithPreparedEarlyWork_compare G raw same height m hm bits D
    fresh prior 3 extra scale setup work.le (fun samples reads P => by
      obtain ⟨graph, search, bound⟩ := each samples (earlySeedArrayReadWordBudget height) reads P
      exact ⟨graph, search, fun short =>
        bound.trans (finSteinerEarlyMetricLabelWordPolynomial_mono n height _ short)⟩)
  exact compare

/-- On feasible traces the complete prefix graphs and evaluation count
agree with the reference replay, with label and table reads in the bound. -/
theorem completeFinSteinerReplayWithMetricLabelWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithMetricLabelWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTracePhaseUnionWorkPolynomial n m height D.length+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6+finForestNetworkPairKeysWordPolynomial n height+3 +
          steinerTraceEarlyHistoryExtraPolynomial n height D.length + 3 +
          steinerTraceMetricLabelExtraPolynomial n height D.length := by
  obtain ⟨graphs, search, counts, setup, decode, index, keyWork, replayWork⟩ :=
    completeFinSteinerReplayWithMetricLabelWork_compare G raw same height m hm bits D
  obtain ⟨exactGraphs, exactCounts, oldWork⟩ :=
    completeFinSteinerReplayWithEarlyHistoryWork_prefixes G raw same height m hm bits D feasible
  refine ⟨graphs.trans exactGraphs, counts.trans exactCounts, ?_⟩
  rw [setup, decode, index]
  omega

/-- Count original route expansions when checking each early prefix and
when returning the final rounded forest. -/
def completeFinSteinerReplayWithMetricExpansionWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D (meteredPhaseUnion (Fin n))
    (prepareFinSteinerWeightedForSeedWithMetricExpansionWork G raw same height)

def steinerTraceMetricExpansionExtraPolynomial (n m height p : ℕ) : ℕ :=
  (p+1)*finSteinerEarlyMetricExpansionWordPolynomial n m height p (earlySeedArrayReadWordBudget height)

/-- Metering original-route expansion preserves exact prefix graphs and the
number of evaluations for every trace. -/
theorem completeFinSteinerReplayWithMetricExpansionWork_compare {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithMetricExpansionWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithEarlyHistoryWork G raw same height m hm bits D
    let base := out.1.1.1
    let prior := old.1.1.1
    base.1.1.map Prod.fst = prior.1.1.map Prod.fst ∧
      (base.1.1.map Prod.snd).sum ≤ (prior.1.1.map Prod.snd).sum ∧ out.2.2 = old.2.2 ∧
      base.1.2 = prior.1.2 ∧ base.2 = prior.2 ∧ out.1.2 = old.1.2 ∧
      out.1.1.2 ≤ old.1.1.2+3 ∧ out.2.1 ≤ old.2.1 + steinerTraceMetricExpansionExtraPolynomial n raw.length height D.length := by
  let fresh := prepareFinSteinerWeightedForSeedWithMetricExpansionWork G raw same height
  let prior := prepareFinSteinerWeightedForSeedWithHistoryWork G raw same height
  let extra := finSteinerEarlyMetricExpansionWordPolynomial n raw.length height D.length (earlySeedArrayReadWordBudget height)
  obtain ⟨scale, setup, work, each⟩ := prepareFinSteinerWeightedForSeedWithMetricExpansionWork_spec G raw same height
  have compare := completeFinSteinerReplayWithPreparedEarlyWork_compare G raw same height m hm bits D
    fresh prior 3 extra scale setup work.le (fun samples reads P => by
      obtain ⟨graph, search, bound⟩ := each samples (earlySeedArrayReadWordBudget height) reads P
      exact ⟨graph, search, fun short =>
        bound.trans (finSteinerEarlyMetricExpansionWordPolynomial_mono n raw.length height _ short)⟩)
  exact compare

/-- On feasible traces the complete prefix graphs and evaluation count
agree with the reference replay, with expansion work included in the bound. -/
theorem completeFinSteinerReplayWithMetricExpansionWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithMetricExpansionWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTracePhaseUnionWorkPolynomial n m height D.length+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6+finForestNetworkPairKeysWordPolynomial n height+3 +
          steinerTraceEarlyHistoryExtraPolynomial n height D.length + 3 +
          steinerTraceMetricExpansionExtraPolynomial n raw.length height D.length := by
  obtain ⟨graphs, search, counts, setup, decode, index, keyWork, replayWork⟩ :=
    completeFinSteinerReplayWithMetricExpansionWork_compare G raw same height m hm bits D
  obtain ⟨exactGraphs, exactCounts, oldWork⟩ :=
    completeFinSteinerReplayWithEarlyHistoryWork_prefixes G raw same height m hm bits D feasible
  refine ⟨graphs.trans exactGraphs, counts.trans exactCounts, ?_⟩
  rw [setup, decode, index]
  omega

/-- Count the reverse search and source test on each expanded early
prefix, together with the measured expansion work. -/
def completeFinSteinerReplayWithMetricValidationWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D (meteredPhaseUnion (Fin n))
    (prepareFinSteinerWeightedForSeedWithMetricValidationWork G raw same height)

def steinerTraceMetricValidationExtraPolynomial (n m height p : ℕ) : ℕ :=
  (p+1)*finSteinerEarlyMetricValidationWordPolynomial n m height p (earlySeedArrayReadWordBudget height)

/-- Metering early validation preserves exact prefix graphs and the number
of evaluations for every trace. -/
theorem completeFinSteinerReplayWithMetricValidationWork_compare {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithMetricValidationWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithEarlyHistoryWork G raw same height m hm bits D
    let base := out.1.1.1
    let prior := old.1.1.1
    base.1.1.map Prod.fst = prior.1.1.map Prod.fst ∧
      (base.1.1.map Prod.snd).sum ≤ (prior.1.1.map Prod.snd).sum ∧ out.2.2 = old.2.2 ∧
      base.1.2 = prior.1.2 ∧ base.2 = prior.2 ∧ out.1.2 = old.1.2 ∧
      out.1.1.2 ≤ old.1.1.2+3 ∧ out.2.1 ≤ old.2.1 + steinerTraceMetricValidationExtraPolynomial n raw.length height D.length := by
  let fresh := prepareFinSteinerWeightedForSeedWithMetricValidationWork G raw same height
  let prior := prepareFinSteinerWeightedForSeedWithHistoryWork G raw same height
  let extra := finSteinerEarlyMetricValidationWordPolynomial n raw.length height D.length (earlySeedArrayReadWordBudget height)
  obtain ⟨scale, setup, work, each⟩ := prepareFinSteinerWeightedForSeedWithMetricValidationWork_spec G raw same height
  have compare := completeFinSteinerReplayWithPreparedEarlyWork_compare G raw same height m hm bits D
    fresh prior 3 extra scale setup work.le (fun samples reads P => by
      obtain ⟨graph, search, bound⟩ := each samples (earlySeedArrayReadWordBudget height) reads P
      exact ⟨graph, search, fun short =>
        bound.trans (finSteinerEarlyMetricValidationWordPolynomial_mono n raw.length height _ short)⟩)
  exact compare

/-- On feasible traces the complete prefix graphs and evaluation count
agree with the reference replay, with early validation in the bound. -/
theorem completeFinSteinerReplayWithMetricValidationWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithMetricValidationWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTracePhaseUnionWorkPolynomial n m height D.length+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6+finForestNetworkPairKeysWordPolynomial n height+3 +
          steinerTraceEarlyHistoryExtraPolynomial n height D.length + 3 +
          steinerTraceMetricValidationExtraPolynomial n raw.length height D.length := by
  obtain ⟨graphs, search, counts, setup, decode, index, keyWork, replayWork⟩ :=
    completeFinSteinerReplayWithMetricValidationWork_compare G raw same height m hm bits D
  obtain ⟨exactGraphs, exactCounts, oldWork⟩ :=
    completeFinSteinerReplayWithEarlyHistoryWork_prefixes G raw same height m hm bits D feasible
  refine ⟨graphs.trans exactGraphs, counts.trans exactCounts, ?_⟩
  rw [setup, decode, index]
  omega

/-- Meter construction of each early prefix and the assembly of its final
bought-link union in the complete replay. -/
def completeFinSteinerReplayWithMetricPrefixAssemblyWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D (meteredPhaseUnion (Fin n))
    (prepareFinSteinerWeightedForSeedWithMetricPrefixAssemblyWork G raw same height)

def steinerTraceMetricPrefixAssemblyExtraPolynomial (n m height p : ℕ) : ℕ :=
  (p+1)*finSteinerEarlyMetricPrefixAssemblyWordPolynomial n m height p (earlySeedArrayReadWordBudget height)

/-- Metering early prefix assembly preserves exact prefix graphs and the number
of evaluations for every trace. -/
theorem completeFinSteinerReplayWithMetricPrefixAssemblyWork_compare {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithMetricPrefixAssemblyWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithEarlyHistoryWork G raw same height m hm bits D
    let base := out.1.1.1
    let prior := old.1.1.1
    base.1.1.map Prod.fst = prior.1.1.map Prod.fst ∧
      (base.1.1.map Prod.snd).sum ≤ (prior.1.1.map Prod.snd).sum ∧ out.2.2 = old.2.2 ∧
      base.1.2 = prior.1.2 ∧ base.2 = prior.2 ∧ out.1.2 = old.1.2 ∧
      out.1.1.2 ≤ old.1.1.2+3 ∧ out.2.1 ≤ old.2.1 + steinerTraceMetricPrefixAssemblyExtraPolynomial n raw.length height D.length := by
  let fresh := prepareFinSteinerWeightedForSeedWithMetricPrefixAssemblyWork G raw same height
  let prior := prepareFinSteinerWeightedForSeedWithHistoryWork G raw same height
  let extra := finSteinerEarlyMetricPrefixAssemblyWordPolynomial n raw.length height D.length (earlySeedArrayReadWordBudget height)
  obtain ⟨scale, setup, work, each⟩ := prepareFinSteinerWeightedForSeedWithMetricPrefixAssemblyWork_spec G raw same height
  have compare := completeFinSteinerReplayWithPreparedEarlyWork_compare G raw same height m hm bits D
    fresh prior 3 extra scale setup work.le (fun samples reads P => by
      obtain ⟨graph, search, bound⟩ := each samples (earlySeedArrayReadWordBudget height) reads P
      exact ⟨graph, search, fun short =>
        bound.trans (finSteinerEarlyMetricPrefixAssemblyWordPolynomial_mono n raw.length height _ short)⟩)
  exact compare

/-- On feasible traces the complete prefix graphs and evaluation count
agree with the reference replay, with early prefix assembly in the bound. -/
theorem completeFinSteinerReplayWithMetricPrefixAssemblyWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithMetricPrefixAssemblyWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTracePhaseUnionWorkPolynomial n m height D.length+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6+finForestNetworkPairKeysWordPolynomial n height+3 +
          steinerTraceEarlyHistoryExtraPolynomial n height D.length + 3 +
          steinerTraceMetricPrefixAssemblyExtraPolynomial n raw.length height D.length := by
  obtain ⟨graphs, search, counts, setup, decode, index, keyWork, replayWork⟩ :=
    completeFinSteinerReplayWithMetricPrefixAssemblyWork_compare G raw same height m hm bits D
  obtain ⟨exactGraphs, exactCounts, oldWork⟩ :=
    completeFinSteinerReplayWithEarlyHistoryWork_prefixes G raw same height m hm bits D feasible
  refine ⟨graphs.trans exactGraphs, counts.trans exactCounts, ?_⟩
  rw [setup, decode, index]
  omega

/-- Use measured forest tier arithmetic and ancestor scans in each early
metric of the complete replay. -/
def completeFinSteinerReplayWithMetricArithmeticWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D (meteredPhaseUnion (Fin n))
    (prepareFinSteinerWeightedForSeedWithMetricArithmeticWork G raw same height)

def steinerTraceMetricArithmeticExtraPolynomial (n m height p : ℕ) : ℕ :=
  (p+1)*finSteinerEarlyMetricArithmeticWordPolynomial n m height p (earlySeedArrayReadWordBudget height)

/-- Metering the forest tier arithmetic preserves exact prefix graphs and the number
of evaluations for every trace. -/
theorem completeFinSteinerReplayWithMetricArithmeticWork_compare {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithMetricArithmeticWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithEarlyHistoryWork G raw same height m hm bits D
    let base := out.1.1.1
    let prior := old.1.1.1
    base.1.1.map Prod.fst = prior.1.1.map Prod.fst ∧
      (base.1.1.map Prod.snd).sum ≤ (prior.1.1.map Prod.snd).sum ∧ out.2.2 = old.2.2 ∧
      base.1.2 = prior.1.2 ∧ base.2 = prior.2 ∧ out.1.2 = old.1.2 ∧
      out.1.1.2 ≤ old.1.1.2+3 ∧ out.2.1 ≤ old.2.1 + steinerTraceMetricArithmeticExtraPolynomial n raw.length height D.length := by
  let fresh := prepareFinSteinerWeightedForSeedWithMetricArithmeticWork G raw same height
  let prior := prepareFinSteinerWeightedForSeedWithHistoryWork G raw same height
  let extra := finSteinerEarlyMetricArithmeticWordPolynomial n raw.length height D.length (earlySeedArrayReadWordBudget height)
  obtain ⟨scale, setup, work, each⟩ := prepareFinSteinerWeightedForSeedWithMetricArithmeticWork_spec G raw same height
  have compare := completeFinSteinerReplayWithPreparedEarlyWork_compare G raw same height m hm bits D
    fresh prior 3 extra scale setup work.le (fun samples reads P => by
      obtain ⟨graph, search, bound⟩ := each samples (earlySeedArrayReadWordBudget height) reads P
      exact ⟨graph, search, fun short =>
        bound.trans (finSteinerEarlyMetricArithmeticWordPolynomial_mono n raw.length height _ short)⟩)
  exact compare

/-- On feasible traces the complete prefix graphs and evaluation count
agree with the reference replay, with the forest tier work in the bound. -/
theorem completeFinSteinerReplayWithMetricArithmeticWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithMetricArithmeticWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTracePhaseUnionWorkPolynomial n m height D.length+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6+finForestNetworkPairKeysWordPolynomial n height+3 +
          steinerTraceEarlyHistoryExtraPolynomial n height D.length + 3 +
          steinerTraceMetricArithmeticExtraPolynomial n raw.length height D.length := by
  obtain ⟨graphs, search, counts, setup, decode, index, keyWork, replayWork⟩ :=
    completeFinSteinerReplayWithMetricArithmeticWork_compare G raw same height m hm bits D
  obtain ⟨exactGraphs, exactCounts, oldWork⟩ :=
    completeFinSteinerReplayWithEarlyHistoryWork_prefixes G raw same height m hm bits D feasible
  refine ⟨graphs.trans exactGraphs, counts.trans exactCounts, ?_⟩
  rw [setup, decode, index]
  omega

/-- Use measured forest link, trial, and tier rows in each early
metric of the complete replay. -/
def completeFinSteinerReplayWithMetricTrialRowsWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D (meteredPhaseUnion (Fin n))
    (prepareFinSteinerWeightedForSeedWithMetricTrialRowsWork G raw same height)

def steinerTraceMetricTrialRowsExtraPolynomial (n m height p : ℕ) : ℕ :=
  (p+1)*finSteinerEarlyMetricTrialRowsWordPolynomial n m height p (earlySeedArrayReadWordBudget height)

/-- Metering the forest link selection preserves exact prefix graphs and the number
of evaluations for every trace. -/
theorem completeFinSteinerReplayWithMetricTrialRowsWork_compare {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithMetricTrialRowsWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithEarlyHistoryWork G raw same height m hm bits D
    let base := out.1.1.1
    let prior := old.1.1.1
    base.1.1.map Prod.fst = prior.1.1.map Prod.fst ∧
      (base.1.1.map Prod.snd).sum ≤ (prior.1.1.map Prod.snd).sum ∧ out.2.2 = old.2.2 ∧
      base.1.2 = prior.1.2 ∧ base.2 = prior.2 ∧ out.1.2 = old.1.2 ∧
      out.1.1.2 ≤ old.1.1.2+3 ∧ out.2.1 ≤ old.2.1 + steinerTraceMetricTrialRowsExtraPolynomial n raw.length height D.length := by
  let fresh := prepareFinSteinerWeightedForSeedWithMetricTrialRowsWork G raw same height
  let prior := prepareFinSteinerWeightedForSeedWithHistoryWork G raw same height
  let extra := finSteinerEarlyMetricTrialRowsWordPolynomial n raw.length height D.length (earlySeedArrayReadWordBudget height)
  obtain ⟨scale, setup, work, each⟩ := prepareFinSteinerWeightedForSeedWithMetricTrialRowsWork_spec G raw same height
  have compare := completeFinSteinerReplayWithPreparedEarlyWork_compare G raw same height m hm bits D
    fresh prior 3 extra scale setup work.le (fun samples reads P => by
      obtain ⟨graph, search, bound⟩ := each samples (earlySeedArrayReadWordBudget height) reads P
      exact ⟨graph, search, fun short =>
        bound.trans (finSteinerEarlyMetricTrialRowsWordPolynomial_mono n raw.length height _ short)⟩)
  exact compare

/-- On feasible traces the complete prefix graphs and evaluation count
agree with the reference replay, with the measured link-selection work in the bound. -/
theorem completeFinSteinerReplayWithMetricTrialRowsWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithMetricTrialRowsWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTracePhaseUnionWorkPolynomial n m height D.length+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6+finForestNetworkPairKeysWordPolynomial n height+3 +
          steinerTraceEarlyHistoryExtraPolynomial n height D.length + 3 +
          steinerTraceMetricTrialRowsExtraPolynomial n raw.length height D.length := by
  obtain ⟨graphs, search, counts, setup, decode, index, keyWork, replayWork⟩ :=
    completeFinSteinerReplayWithMetricTrialRowsWork_compare G raw same height m hm bits D
  obtain ⟨exactGraphs, exactCounts, oldWork⟩ :=
    completeFinSteinerReplayWithEarlyHistoryWork_prefixes G raw same height m hm bits D feasible
  refine ⟨graphs.trans exactGraphs, counts.trans exactCounts, ?_⟩
  rw [setup, decode, index]
  omega

/-- Use measured weighted residual searches in each early
metric of the complete replay. -/
def completeFinSteinerReplayWithMetricResidualRowsWork {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  completeFinSteinerReplayWithHubRoutingUsing G raw same height m hm bits D (meteredPhaseUnion (Fin n))
    (prepareFinSteinerWeightedForSeedWithMetricResidualRowsWork G raw same height)

def steinerTraceMetricResidualRowsExtraPolynomial (n m height p : ℕ) : ℕ :=
  (p+1)*finSteinerEarlyMetricResidualRowsWordPolynomial n m height p (earlySeedArrayReadWordBudget height)

/-- Metering the weighted residual search preserves exact prefix graphs and the number
of evaluations for every trace. -/
theorem completeFinSteinerReplayWithMetricResidualRowsWork_compare {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithMetricResidualRowsWork G raw same height m hm bits D
    let old := completeFinSteinerReplayWithEarlyHistoryWork G raw same height m hm bits D
    let base := out.1.1.1
    let prior := old.1.1.1
    base.1.1.map Prod.fst = prior.1.1.map Prod.fst ∧
      (base.1.1.map Prod.snd).sum ≤ (prior.1.1.map Prod.snd).sum ∧ out.2.2 = old.2.2 ∧
      base.1.2 = prior.1.2 ∧ base.2 = prior.2 ∧ out.1.2 = old.1.2 ∧
      out.1.1.2 ≤ old.1.1.2+finSteinerForestDepthWordPolynomial n height ∧ out.2.1 ≤ old.2.1 + steinerTraceMetricResidualRowsExtraPolynomial n raw.length height D.length := by
  let fresh := prepareFinSteinerWeightedForSeedWithMetricResidualRowsWork G raw same height
  let prior := prepareFinSteinerWeightedForSeedWithHistoryWork G raw same height
  let extra := finSteinerEarlyMetricResidualRowsWordPolynomial n raw.length height D.length (earlySeedArrayReadWordBudget height)
  obtain ⟨scale, setup, work, each⟩ := prepareFinSteinerWeightedForSeedWithMetricResidualRowsWork_spec G raw same height
  have compare := completeFinSteinerReplayWithPreparedEarlyWork_compare G raw same height m hm bits D
    fresh prior (finSteinerForestDepthWordPolynomial n height) extra scale setup work (fun samples reads P => by
      obtain ⟨graph, search, bound⟩ := each samples (earlySeedArrayReadWordBudget height) reads P
      exact ⟨graph, search, fun short =>
        bound.trans (finSteinerEarlyMetricResidualRowsWordPolynomial_mono n raw.length height _ short)⟩)
  exact compare

/-- On feasible traces the complete prefix graphs and evaluation count
agree with the reference replay, with the measured weighted residual work in the bound. -/
theorem completeFinSteinerReplayWithMetricResidualRowsWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (raw : List (Fin n × Fin n)) (same : raw.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithMetricResidualRowsWork G raw same height m hm bits D
    let base := out.1.1.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      out.2.2 = (completeFinSteinerReplayWithThinRowWork G raw same height m hm bits D).2.2 ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.1.1.2+out.1.2+out.2.1 ≤
        completeFinSteinerPreparationWorkPolynomial n m raw.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height + finSteinerReplayIndexWorkPolynomial n raw.length +
          (steinerTraceEarlySeedRankWorkPolynomial n height D.length+11*m+21) +
          (steinerTracePhaseUnionWorkPolynomial n m height D.length+11*m+21) +
          finArcRowsWordBudget n raw.length+8*n+6+finForestNetworkPairKeysWordPolynomial n height+3 +
          steinerTraceEarlyHistoryExtraPolynomial n height D.length + finSteinerForestDepthWordPolynomial n height +
          steinerTraceMetricResidualRowsExtraPolynomial n raw.length height D.length := by
  obtain ⟨graphs, search, counts, setup, decode, index, keyWork, replayWork⟩ :=
    completeFinSteinerReplayWithMetricResidualRowsWork_compare G raw same height m hm bits D
  obtain ⟨exactGraphs, exactCounts, oldWork⟩ :=
    completeFinSteinerReplayWithEarlyHistoryWork_prefixes G raw same height m hm bits D feasible
  refine ⟨graphs.trans exactGraphs, counts.trans exactCounts, ?_⟩
  rw [setup, decode, index]
  omega

end OnlineReachabilityPreservers
