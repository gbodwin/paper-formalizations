import OnlineReachabilityPreservers.SteinerFinIndexedReplayWork
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
      out.2.2 = (distinctNonselfTrace D).length+1 := by
  let params := steinerTraceParametersWithWordWork n
  have countOk : params.1.hubCount = completeSteinerHubCount V := by
    rw [params.1.hubCount_eq,hn]
    rfl
  let hubs := collectSteinerHubsWithWordWork countOk draw
  let run := evaluate params.1.earlyCutoff params.1.thinThreshold hubs.1
  let out := replayFirstOccurrencesWithWordWork run D
  obtain ⟨exactHubs,hubWork⟩ := collectSteinerHubsWithWordWork_spec countOk draw
  obtain ⟨records,traceWork,number⟩ := replayFirstOccurrencesWithWordWork_spec run D C (each _ _ _)
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

/-- Allow one unit per seed read in early rounding, alongside trace work. -/
def steinerTraceEarlySeedReadWorkPolynomial (n height p : ℕ) : ℕ :=
  steinerTraceReplayWorkPolynomial n p+(p+1)*((p+1)*earlyRoundingSeedReadPolynomial n height+5)

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

private theorem replaySteinerTraceWithEarlySeedReads_spec (G : Arcs V) (n height : ℕ) (hn : n = Fintype.card V)
    (early : List (V × V) → Arcs V × ℕ × ℕ) (oldEarly : List (V × V) → Arcs V × ℕ)
    (exactEarly : ∀ P, ((early P).1,(early P).2.1) = oldEarly P)
    (earlyBound : ∀ P, (early P).2.2 ≤ (P.length+1)*earlyRoundingSeedReadPolynomial n height)
    (draw : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) (D : List (V × V)) :
    let out := replaySteinerTraceWithEarlySeedReads G n hn early draw thin D
    let old := replaySteinerSeededPrefixesWithTraceWork G n hn oldEarly draw thin D
    out.1 = old.1 ∧ out.2.1 ≤ steinerTraceEarlySeedReadWorkPolynomial n height D.length ∧ out.2.2 = old.2.2 := by
  let run := fun T τ hubs => evaluateSteinerTraceWithEarlySeedReads early T τ hubs
    (fun threshold sampled => lateSteinerWithSearchWork G threshold sampled thin)
  let target := completeSteinerDrawRunWithSearchWorkFromEarly G oldEarly draw thin
  let extra := (D.length+1)*earlyRoundingSeedReadPolynomial n height+5
  have exactValue (P : List (V × V)) : (run (steinerEarlyCutoff n) (steinerThinThreshold n)
      (sampledVertices draw) (distinctNonselfTrace P)).1 = target P := by
    have graph (Q : List (V × V)) : (early Q).1 = (oldEarly Q).1 := congrArg Prod.fst (exactEarly Q)
    have charge (Q : List (V × V)) : (early Q).2.1 = (oldEarly Q).2 := congrArg Prod.snd (exactEarly Q)
    dsimp only [run,evaluateSteinerTraceWithEarlySeedReads,target]
    rw [(splitSteinerTraceWithWordWork_spec _ _).1]
    simp only [completeSteinerDrawRunWithSearchWorkFromParts, completeSteinerDrawRunWithSearchWorkFromEarly,
      graph,charge,hn]
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
  obtain ⟨oldSame,_,oldNumber⟩ := replaySteinerSeededPrefixesWithTraceWork_spec G n hn oldEarly draw thin D
  refine ⟨same.trans oldSame.symm,bound.trans_eq ?_,number.trans oldNumber.symm⟩
  unfold steinerTraceEarlySeedReadWorkPolynomial steinerTraceReplayWorkPolynomial steinerTraceWorkFromCallbackBound
  ring

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

end OnlineReachabilityPreservers
