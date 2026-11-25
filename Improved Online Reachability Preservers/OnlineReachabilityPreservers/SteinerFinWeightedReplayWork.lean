import OnlineReachabilityPreservers.SteinerWeightedPlanWork
import OnlineReachabilityPreservers.SteinerForestPairKeysWork

/-! Carry the one-pass weighted plan into the fixed-budget prefix evaluator. -/

namespace OnlineReachabilityPreservers

local instance {n height : ℕ} : DecidableEq (HeightForestVertex (Fin n) height) :=
  (inferInstance : LinearOrder (HeightForestVertex (Fin n) height)).toDecidableEq

private theorem finiteHopValue_le {n : ℕ} (G : Arcs (Fin n)) (d : Fin n × Fin n) :
    hops G d.1 d.2 ≤ n+1 := by
  change (least? ((Finset.range (Fintype.card (Fin n)+1)).filter
    (fun k => d.1 ∈ reachIn G d.2 k))).getD (Fintype.card (Fin n)+1) ≤ n+1
  cases chosen : least? ((Finset.range (Fintype.card (Fin n)+1)).filter
    (fun k => d.1 ∈ reachIn G d.2 k)) with
  | none => simp
  | some k =>
    have bound := Finset.mem_range.mp (Finset.mem_filter.mp (least?_mem chosen)).1
    simp only [Fintype.card_fin] at bound
    exact bound.le

private theorem finHeightForestVertex_card_le (n height : ℕ) :
    Fintype.card (HeightForestVertex (Fin n) height) ≤ 2*n*(n+1)^height := by
  simp only [HeightForestVertex,Fintype.card_lex,Fintype.card_prod,Fintype.card_bool,
    ← heightLexBlockCount_card, Fintype.card_fin]
  rw [← Nat.mul_assoc, Nat.mul_comm n 2]
  exact Nat.mul_le_mul_left _ (heightLexBlockCount_le_pow n height)

private theorem pairedForestList_length_le {n height : ℕ} (G : Arcs (Fin n))
    (edges : List (HeightForestVertex (Fin n) height × HeightForestVertex (Fin n) height))
    (unique : edges.Nodup) (exactForest : edges.toFinset = heightForest G height) :
    edges.length ≤ (2*n*(n+1)^height)^2 := by
  have verts := finHeightForestVertex_card_le n height
  have edgesBound : (heightForest G height).card ≤ Fintype.card (HeightForestVertex (Fin n) height)^2 := by
    simpa only [Fintype.card_prod,pow_two] using Finset.card_le_univ (heightForest G height)
  rw [← List.toFinset_card_of_nodup unique,exactForest]
  exact edgesBound.trans (Nat.pow_le_pow_left verts 2)

/-- At fixed height, the plan pass and its scale and fuel arithmetic cost
polynomially many unit operations in the vertex count. -/
def finSteinerWeightPlanWorkPolynomial (n height : ℕ) : ℕ :=
  let E := (2*n*(n+1)^height)^2
  E*(10*height+8*n^2+56)+7*(1+E*(n+1))+26

private theorem finWeightsFromTemplateInputs_spec {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ) :
    let inputs := finSteinerTemplateInputsWithWordWork arcs height
    let certified := finSteinerTemplateInputsWithWordWork_spec G arcs same height
    let read := readDistanceRow inputs.1.1
    let W := prepareForestWeightsFromListWithWordWork inputs.2.1 certified.2.2.1 read
    W.1 = prepareForestWeights (arcsFromDistinctList inputs.2.1 certified.2.2.1) (forestWeightWithDistanceWork read) ∧
    W.2 ≤ finSteinerWeightPlanWorkPolynomial n height := by
  let inputs := finSteinerTemplateInputsWithWordWork arcs height
  let certified := finSteinerTemplateInputsWithWordWork_spec G arcs same height
  let read := readDistanceRow inputs.1.1
  have lookup (d : Fin n × Fin n) : (read d).1 ≤ n+1 ∧ (read d).2 ≤ n^2 := by
    change (readDistanceRow inputs.1.1 d).1 ≤ n+1 ∧ (readDistanceRow inputs.1.1 d).2 ≤ n^2
    rw [certified.1]
    obtain ⟨value,work⟩ := distanceTableReadWithSearchWork_spec G d
    simp only [Fintype.card_fin] at work
    exact ⟨value.symm ▸ finiteHopValue_le G d,work⟩
  obtain ⟨equal,work⟩ := prepareForestWeightsFromListWithWordWork_spec inputs.2.1 certified.2.2.1
    read (n^2) (n+1) (fun d => (lookup d).2) (fun d => (lookup d).1)
  have arcsBound := pairedForestList_length_le G inputs.2.1 certified.2.2.1 certified.2.1
  refine ⟨equal,work.trans ?_⟩
  dsimp only [finSteinerWeightPlanWorkPolynomial]
  gcongr

private def prepareFinSteinerWeightedWithPlan {n : ℕ} {Result : Type*} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ)
    (assemble : (table : List ((Fin n × Fin n) × ℕ) × ℕ) →
      table.1 = (distanceTableWithSearchWork G).1 →
      (template : Arcs (HeightForestVertex (Fin n) height) × ℕ) → template.1 = heightForest G height →
      (plan : ForestWeightPlan (Fin n) height) →
      plan = prepareForestWeights template.1 (forestWeightWithDistanceWork (readDistanceRow table.1)) → Result) :
    Result × ℕ :=
  let inputs := finSteinerTemplateInputsWithWordWork arcs height
  let correct := finSteinerTemplateInputsWithWordWork_spec G arcs same height
  let read := readDistanceRow inputs.1.1
  let links := arcsFromDistinctList inputs.2.1 correct.2.2.1
  let exactForest := (arcsFromDistinctList_eq inputs.2.1 correct.2.2.1).trans correct.2.1
  let plan := prepareForestWeightsFromListWithWordWork inputs.2.1 correct.2.2.1 read
  let planEq := (finWeightsFromTemplateInputs_spec G arcs same height).1
  (assemble inputs.1 correct.1 (links,inputs.2.2+5) exactForest plan.1 planEq,plan.2)

/-- Prepare the exact weighted evaluator from the shared hop and forest
lists. Return the weight-plan construction work as one additional tally. -/
def prepareFinSteinerWeightedForSeedWithWordWork {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ) : SteinerSeedPreparation G height × ℕ :=
  prepareFinSteinerWeightedWithPlan G arcs same height (prepareEarlyDistanceTableForSeedFromWeights G height)

/-- Reuse the same weighted plan and count seed reads in early rounding. -/
def prepareFinSteinerWeightedForSeedWithSeedReads {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ) :
    SteinerSeedPreparationWithSeedReads G height × ℕ :=
  prepareFinSteinerWeightedWithPlan G arcs same height (prepareEarlyDistanceTableForSeedFromWeightsWithSeedReads G height)

theorem prepareFinSteinerWeightedForSeedWithSeedReads_spec {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ) :
    let out := prepareFinSteinerWeightedForSeedWithSeedReads G arcs same height
    let old := prepareFinSteinerWeightedForSeedWithWordWork G arcs same height
    out.1.1 = old.1.1 ∧ out.1.2.2 = old.1.2.2 ∧ out.2 = old.2 ∧
      ∀ (sample : EarlyRoundSample G height) (D : List (Fin n × Fin n)),
        let result := out.1.2.1 sample D
        (result.1,result.2.1) = old.1.2.1 sample D ∧
          result.2.2 ≤ (D.length+1)*earlyRoundingSeedReadPolynomial n height := by
  let inputs := finSteinerTemplateInputsWithWordWork arcs height
  let correct := finSteinerTemplateInputsWithWordWork_spec G arcs same height
  let links := arcsFromDistinctList inputs.2.1 correct.2.2.1
  let exactForest := (arcsFromDistinctList_eq inputs.2.1 correct.2.2.1).trans correct.2.1
  let plan := prepareForestWeightsFromListWithWordWork inputs.2.1 correct.2.2.1 (readDistanceRow inputs.1.1)
  let planEq := (finWeightsFromTemplateInputs_spec G arcs same height).1
  obtain ⟨scale,initial,rounding⟩ := prepareEarlyDistanceTableForSeedFromWeightsWithSeedReads_spec
    G height inputs.1 correct.1 (links,inputs.2.2+5) exactForest plan.1 planEq
  refine ⟨scale,initial,rfl,fun sample D => ?_⟩
  obtain ⟨preserves,work⟩ := rounding sample D
  have cap : earlyRoundingSeedReadBound G height ≤ earlyRoundingSeedReadPolynomial n height := by
    simpa only [Fintype.card_fin] using earlyRoundingSeedReadBound_le G height
  exact ⟨preserves,work.trans (Nat.mul_le_mul_left _ cap)⟩

/-- Prepare the same weighted plan for an early seed reader with its own work tally. -/
def prepareFinSteinerWeightedForSeedWithSeedWork {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ) :
    SteinerSeedPreparationWithSeedWork G height × ℕ :=
  prepareFinSteinerWeightedWithPlan G arcs same height (prepareEarlyDistanceTableForSeedFromWeightsWithSeedWork G height)

theorem prepareFinSteinerWeightedForSeedWithSeedWork_spec {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ) :
    let out := prepareFinSteinerWeightedForSeedWithSeedWork G arcs same height
    let old := prepareFinSteinerWeightedForSeedWithWordWork G arcs same height
    out.1.1 = old.1.1 ∧ out.1.2.2 = old.1.2.2 ∧ out.2 = old.2 ∧
      ∀ (samples : ForestTrialArrayWithSeedWork (Fin n) height (forestScale G height) (earlyTrialCount (Fin n) height))
        (B : ℕ), (∀ i, forestSampleWorkBound (samples i) B) → ∀ (D : List (Fin n × Fin n)),
        let result := out.1.2.1 samples D
        let plain := fun i => forestRoundingSampleValues (forestScale G height) (samples i)
        (result.1,result.2.1) = old.1.2.1 plain D ∧
          result.2.2 ≤ (D.length+1)*(earlyRoundingSeedReadPolynomial n height*B) := by
  let inputs := finSteinerTemplateInputsWithWordWork arcs height
  let correct := finSteinerTemplateInputsWithWordWork_spec G arcs same height
  let links := arcsFromDistinctList inputs.2.1 correct.2.2.1
  let exactForest := (arcsFromDistinctList_eq inputs.2.1 correct.2.2.1).trans correct.2.1
  let plan := prepareForestWeightsFromListWithWordWork inputs.2.1 correct.2.2.1 (readDistanceRow inputs.1.1)
  let planEq := (finWeightsFromTemplateInputs_spec G arcs same height).1
  obtain ⟨scale,initial,rounding⟩ := prepareEarlyDistanceTableForSeedFromWeightsWithSeedWork_spec
    G height inputs.1 correct.1 (links,inputs.2.2+5) exactForest plan.1 planEq
  refine ⟨scale,initial,rfl,fun samples B reads D => ?_⟩
  obtain ⟨preserves,work⟩ := rounding samples B reads D
  have cap : earlyRoundingSeedReadBound G height ≤ earlyRoundingSeedReadPolynomial n height := by
    simpa only [Fintype.card_fin] using earlyRoundingSeedReadBound_le G height
  exact ⟨preserves,work.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right B cap))⟩

theorem prepareFinSteinerWeightedForSeedWithWordWork_spec {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ) :
    let out := prepareFinSteinerWeightedForSeedWithWordWork G arcs same height
    out.1 = prepareFinSteinerForSeedWithWordWork G arcs same height ∧
      out.2 ≤ finSteinerWeightPlanWorkPolynomial n height := by
  let inputs := finSteinerTemplateInputsWithWordWork arcs height
  let correct := finSteinerTemplateInputsWithWordWork_spec G arcs same height
  let links := arcsFromDistinctList inputs.2.1 correct.2.2.1
  let exactForest := (arcsFromDistinctList_eq inputs.2.1 correct.2.2.1).trans correct.2.1
  let plan := prepareForestWeightsFromListWithWordWork inputs.2.1 correct.2.2.1 (readDistanceRow inputs.1.1)
  obtain ⟨planEq,work⟩ := finWeightsFromTemplateInputs_spec G arcs same height
  exact ⟨prepareEarlyDistanceTableForSeedFromWeights_eq G height inputs.1 correct.1 (links,inputs.2.2+5)
    exactForest plan.1 planEq,work⟩

/-- Replay with the one-pass weight preparation and the same seed decoder. -/
def completeFinSteinerReplayWithWeightedPreparationWork {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :=
  let prepared := prepareFinSteinerWeightedForSeedWithWordWork G arcs same height
  (completeSteinerReplayWithDecoderWorkFromPreparation G height n m (by simp) hm prepared.1 bits D,prepared.2)

theorem completeFinSteinerReplayWithWeightedPreparationWork_spec {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n)) :
    let out := completeFinSteinerReplayWithWeightedPreparationWork G arcs same height m hm bits D
    out.1 = completeFinSteinerReplayWithPreparationWork G arcs same height m hm bits D ∧
      out.2 ≤ finSteinerWeightPlanWorkPolynomial n height := by
  obtain ⟨prep,work⟩ := prepareFinSteinerWeightedForSeedWithWordWork_spec G arcs same height
  exact ⟨congrArg (fun plan => completeSteinerReplayWithDecoderWorkFromPreparation G height n m
    (by simp) hm plan bits D) prep,work⟩

/-- The replaced plan keeps every prefix graph and the reported preexisting
work. A single polynomial also bounds the extra one-time weight plan work. -/
theorem completeFinSteinerReplayWithWeightedPreparationWork_prefixes {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height m : ℕ) (hm : m = G.card)
    (bits : Fin (steinerBitBudget G height) → Bool) (D : List (Fin n × Fin n))
    (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    let out := completeFinSteinerReplayWithWeightedPreparationWork G arcs same height m hm bits D
    let base := out.1
    base.1.1.map Prod.fst = D.inits.map (completeSteinerRunWithBitBudget G height bits) ∧
      (base.1.1.map Prod.snd).sum+base.1.2.1+base.1.2.2.1+base.1.2.2.2+base.2+out.2 ≤
        completeFinSteinerPreparationWorkPolynomial n m arcs.length height D.length +
          finSteinerWeightPlanWorkPolynomial n height := by
  obtain ⟨replay,work⟩ := completeFinSteinerReplayWithWeightedPreparationWork_spec G arcs same height m hm bits D
  obtain ⟨prefixes,previous⟩ := completeFinSteinerReplayWithPreparationWork_prefixes G arcs same height m hm bits D feasible
  dsimp only
  rw [replay]
  exact ⟨prefixes,Nat.add_le_add previous work⟩

/-- Prepare ordered-pair keys once alongside the weighted plan, then use the
metered weighted history solver at each early metric prefix. -/
def prepareFinSteinerWeightedForSeedWithHistoryWork {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ) :
    SteinerSeedPreparationWithSeedWork G height × ℕ :=
  let keys := finForestNetworkPairKeysWithWordWork n height
  let prepared := prepareFinSteinerWeightedWithPlan G arcs same height
    (prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork G height
      ⟨keys.1, (finForestNetworkPairKeysWithWordWork_spec n height).1⟩)
  (prepared.1, prepared.2 + keys.2 + 3)

theorem prepareFinSteinerWeightedForSeedWithHistoryWork_setup {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ) :
    (prepareFinSteinerWeightedForSeedWithHistoryWork G arcs same height).2 =
      (prepareFinSteinerWeightedForSeedWithSeedWork G arcs same height).2 +
        (finForestNetworkPairKeysWithWordWork n height).2 + 3 := by
  dsimp only [prepareFinSteinerWeightedForSeedWithHistoryWork, prepareFinSteinerWeightedForSeedWithSeedWork,
    prepareFinSteinerWeightedWithPlan]

/-- A fixed-height bound for evaluating all the needed early metrics of
one demand prefix, including their weighted solver and seed reads. -/
def finSteinerEarlyHistoryWordPolynomial (n height p seed : ℕ) : ℕ :=
  let forest := 2*n*(n+1)^height
  let scale := 1+n*forest^2
  let fuel := (scale+1)*scale+1
  (p+1) * (earlyWeightedHistoryWordBudget (3*forest) (forest^2) scale fuel (n^2) p +
    earlyRoundingSeedReadPolynomial n height * seed)

set_option maxHeartbeats 800000 in
theorem prepareFinSteinerWeightedForSeedWithHistoryWork_spec {n : ℕ} (G : Arcs (Fin n))
    (arcs : List (Fin n × Fin n)) (same : arcs.toFinset = G) (height : ℕ) :
    let out := prepareFinSteinerWeightedForSeedWithHistoryWork G arcs same height
    let old := prepareFinSteinerWeightedForSeedWithSeedWork G arcs same height
    out.1.1 = old.1.1 ∧ out.1.2.2 = old.1.2.2 ∧
      out.2 ≤ finSteinerWeightPlanWorkPolynomial n height + finForestNetworkPairKeysWordPolynomial n height + 3 ∧
      ∀ samples B, (∀ i, forestSampleWorkBound (samples i) B) → ∀ D,
        let result := out.1.2.1 samples D
        let prior := old.1.2.1 samples D
        result.1 = prior.1 ∧ result.2.1 ≤ prior.2.1 ∧
          result.2.2 ≤ finSteinerEarlyHistoryWordPolynomial n height D.length B := by
  let inputs := finSteinerTemplateInputsWithWordWork arcs height
  let correct := finSteinerTemplateInputsWithWordWork_spec G arcs same height
  let links := arcsFromDistinctList inputs.2.1 correct.2.2.1
  let exactForest := (arcsFromDistinctList_eq inputs.2.1 correct.2.2.1).trans correct.2.1
  let read := readDistanceRow inputs.1.1
  let plan := prepareForestWeightsFromListWithWordWork inputs.2.1 correct.2.2.1 read
  obtain ⟨planEq, planWork⟩ := finWeightsFromTemplateInputs_spec G arcs same height
  let keys := finForestNetworkPairKeysWithWordWork n height
  obtain ⟨distinct, complete, _, keyWork⟩ := finForestNetworkPairKeysWithWordWork_spec n height
  obtain ⟨scaleEq, setup, evaluate⟩ := prepareEarlyDistanceTableForSeedFromWeightsWithHistoryWork_spec
    G height ⟨keys.1, distinct⟩ complete inputs.1 correct.1 (links, inputs.2.2+5) exactForest plan.1 planEq
  have setupWork := Nat.add_le_add_right (Nat.add_le_add planWork keyWork) 3
  refine ⟨scaleEq, setup, setupWork, fun samples B cap D => ?_⟩
  obtain ⟨graph, ordinary, work⟩ := evaluate samples B cap D
  refine ⟨graph, ordinary, work.trans ?_⟩
  let forest := 2*n*(n+1)^height
  let S := 1+n*forest^2
  have forestBound : Fintype.card (HeightForestVertex (Fin n) height) ≤ forest :=
    finHeightForestVertex_card_le n height
  have network : Fintype.card (ForestNetworkVertex (Fin n) height) ≤ 3*forest := by
    simpa [ForestNetworkVertex] using Nat.mul_le_mul_left 3 forestBound
  have scale : plan.1.2.1.1 = forestScale G height :=
    (prepareFinSteinerWeightedForSeedWithSeedWork G arcs same height).1.1.property
  have scaleBound : plan.1.2.1.1 ≤ S := by
    rw [scale]
    apply (forestNetworkScale_le G height).trans
    rw [Fintype.card_fin]
    refine max_le (Nat.le_add_right _ _) ?_
    exact (Nat.mul_le_mul_left n (Nat.pow_le_pow_left forestBound 2)).trans (Nat.le_add_left _ _)
  let total := ∑ e ∈ links, (forestWeightWithDistanceWork read e).1
  have planShape := planEq.trans (prepareForestWeights_exact links (forestWeightWithDistanceWork read))
  have paidBound : plan.1.1.1.card ≤ forest^2 := by
    rw [planShape, Finset.card_map]
    apply (Finset.card_filter_le _ _).trans
    have all := Finset.card_le_univ links
    rw [Fintype.card_prod, ← pow_two] at all
    exact all.trans (Nat.pow_le_pow_left forestBound 2)
  have scaleShape : plan.1.2.1.1 = max 1 total := congrArg (fun x : ForestWeightPlan (Fin n) height => x.2.1.1) planShape
  have fuelShape : plan.1.2.1.2 = ((max 1 total).log2+1)*total+1 :=
    congrArg (fun x : ForestWeightPlan (Fin n) height => x.2.1.2) planShape
  have totalBound := (le_max_right 1 total).trans (scaleShape ▸ scaleBound)
  have logBound := (Nat.log2_le_self (max 1 total)).trans (scaleShape ▸ scaleBound)
  have fuelBound : plan.1.2.1.2 ≤ (S+1)*S+1 := by
    rw [fuelShape]
    gcongr
  have rounding : earlyRoundingSeedReadBound G height ≤ earlyRoundingSeedReadPolynomial n height := by
    simpa only [Fintype.card_fin] using earlyRoundingSeedReadBound_le G height
  unfold finSteinerEarlyHistoryWordPolynomial
  dsimp only
  rw [Fintype.card_fin]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add
    (earlyWeightedHistoryWordBudget_le network paidBound scaleBound fuelBound le_rfl le_rfl)
    (Nat.mul_le_mul_right B rounding))

end OnlineReachabilityPreservers
