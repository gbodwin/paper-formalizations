import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure
import OnlineReachabilityPreservers.SteinerBitLaw
import OnlineReachabilityPreservers.SteinerBitOrders

/-! Product fair-bit probability, termination, and the expected bit and edge counts. -/

namespace OnlineReachabilityPreservers

universe u

open MeasureTheory
open scoped ENNReal

private noncomputable def fairCoin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

private instance : IsProbabilityMeasure fairCoin := by unfold fairCoin; infer_instance

/-- The countable product probability for a stream of independent fair bits. -/
noncomputable def fairBitMeasure : Measure (ℕ → Bool) := Measure.infinitePi fun _ => fairCoin

instance : IsProbabilityMeasure fairBitMeasure := by unfold fairBitMeasure; infer_instance

def fairBitPrefix (n : ℕ) (stream : ℕ → Bool) : Fin n → Bool := fun i => stream i.val

theorem fairBitPrefix_measurable (n : ℕ) : Measurable (fairBitPrefix n) := by
  exact Measurable.of_eval fun i : Fin n => measurable_pi_apply i.val

private theorem fairCoin_singleton (bit : Bool) : fairCoin {bit} = (2:ℝ≥0∞)⁻¹ := by
  simp [fairCoin]

theorem fairBitPrefix_singleton (n : ℕ) (bits : Fin n → Bool) :
    fairBitMeasure (fairBitPrefix n ⁻¹' {bits}) = ((2:ℝ≥0∞)⁻¹)^n := by
  let box := fun i : ℕ => if inside : i < n then ({bits ⟨i,inside⟩} : Set Bool) else Set.univ
  have form : fairBitPrefix n ⁻¹' {bits} = Set.pi (↑(Finset.range n) : Set ℕ) box := by
    ext stream
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Finset.mem_coe]
    constructor
    · intro eq i inside
      have bound := Finset.mem_range.mp inside
      simp only [box, dite_eq_left bound, Set.mem_singleton_iff]
      exact congrFun eq ⟨i,bound⟩
    · intro all
      funext i
      simpa only [box, dite_eq_left i.isLt, Set.mem_singleton_iff, fairBitPrefix] using
        all i.val (Finset.mem_range.mpr i.isLt)
  rw [form, fairBitMeasure, Measure.infinitePi_pi]
  · calc
      _ = ∏ _ ∈ Finset.range n, (2:ℝ≥0∞)⁻¹ := by
        apply Finset.prod_congr rfl
        intro i inside
        simp only [box, dite_eq_left (Finset.mem_range.mp inside), fairCoin_singleton]
      _ = _ := by simp
  · intro i inside
    simp only [box, dite_eq_left (Finset.mem_range.mp inside)]
    exact MeasurableSet.singleton _

/-- The fair-stream probability of a finite prefix event agrees with the
uniform finite probability used by the decoder's first-success events. -/
theorem fairBitPrefix_probability {n : ℕ} (event : Finset (Fin n → Bool)) :
    fairBitMeasure (fairBitPrefix n ⁻¹' ↑event) = ENNReal.ofReal (finiteProbability event) := by
  have measurable : Measurable (fairBitPrefix n) := fairBitPrefix_measurable n
  have singles : (↑event : Set (Fin n → Bool)) = ⋃ word ∈ event, ({word} : Set (Fin n → Bool)) := by
    ext x
    simp
  have disjoint : Set.PairwiseDisjoint (↑event) (fun word => ({word} : Set (Fin n → Bool))) := by
    intro a _ b _ unequal
    exact Set.disjoint_singleton.mpr unequal
  rw [← Measure.map_apply measurable event.finite_toSet.measurableSet, singles,
    measure_biUnion_finset disjoint (fun _ _ => MeasurableSet.singleton _)]
  simp_rw [Measure.map_apply measurable (MeasurableSet.singleton _), fairBitPrefix_singleton]
  have card : (Fintype.card (Fin n → Bool) : ℝ) = (2:ℝ)^n := by simp
  have half : ENNReal.ofReal (1/2:ℝ) = (2:ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  simp only [finiteProbability, card, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, ← inv_pow]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
  norm_num [half]

/-- A score that uses only a fixed prefix has the ordinary uniform finite mean. -/
theorem fairBitPrefix_lintegral_eq (n : ℕ) (loss : (Fin n → Bool) → ℕ) :
    (∫⁻ stream, (loss (fairBitPrefix n stream) : ℝ≥0∞) ∂fairBitMeasure) =
      ENNReal.ofReal ((∑ bits, (loss bits : ℝ)) / (Fintype.card (Fin n → Bool) : ℝ)) := by
  classical
  let event := fun bits : Fin n → Bool => fairBitPrefix n ⁻¹' ({bits} : Set (Fin n → Bool))
  have meas (bits : Fin n → Bool) : MeasurableSet (event bits) :=
    (MeasurableSet.singleton _).preimage (fairBitPrefix_measurable n)
  have score (stream : ℕ → Bool) : (loss (fairBitPrefix n stream) : ℝ≥0∞) =
      ∑ bits, (event bits).indicator (fun _ => (loss bits : ℝ≥0∞)) stream := by
    rw [Finset.sum_eq_single (fairBitPrefix n stream)]
    · rw [Set.indicator_of_mem (show stream ∈ event (fairBitPrefix n stream) from rfl)]
    · intro bits _ different
      have outside : stream ∉ event bits := fun same => different (Set.mem_singleton_iff.mp same).symm
      rw [Set.indicator_of_notMem outside]
    · simp
  simp_rw [score]
  rw [lintegral_finsetSum _ (fun bits _ => measurable_const.indicator (meas bits))]
  simp only [Finset.sum_div]
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  apply Finset.sum_congr rfl
  intro bits _
  rw [lintegral_indicator_const (meas bits)]
  have prob : fairBitMeasure (event bits) = ENNReal.ofReal (finiteProbability ({bits} : Finset _)) := by
    simpa only [event, Finset.coe_singleton] using fairBitPrefix_probability {bits}
  rw [prob]
  simp only [finiteProbability, Finset.card_singleton, Nat.cast_one]
  rw [← ENNReal.ofReal_natCast (loss bits), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  simp only [div_eq_mul_inv, one_mul]

private theorem fairBitPrefix_ofFn_prefix {a b : ℕ} (short : a ≤ b) (stream : ℕ → Bool) :
    List.ofFn (fairBitPrefix a stream) <+: List.ofFn (fairBitPrefix b stream) := by
  rw [List.prefix_iff_eq_take, List.length_ofFn]
  apply List.ext_getElem
  · simp [Nat.min_eq_left short]
  · intro i left right
    simp only [List.getElem_ofFn, List.getElem_take, fairBitPrefix]

variable {V : Type*} [LinearOrder V] [Fintype V]

private abbrev DecoderSeed (G : Arcs V) (height : ℕ) :=
  EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G

private abbrev DecoderCounts (G : Arcs V) := (Fin (completeSteinerHubCount V) → ℕ) × (Fin G.card → ℕ)

private noncomputable def decoderOutcomeEvent (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (result : DecoderSeed G height × DecoderCounts G) : Set (ℕ → Bool) :=
  fairBitPrefix (completeSteinerBitSeedWidth G height arcs result.2.1 (result.2.2 ∘ arcs)) ⁻¹'
    ↑(completeSteinerRawSeedEvent G height coordinates vertices arcs result.1.1 result.1.2.1 result.1.2.2
      result.2.1 (result.2.2 ∘ arcs) [])

private theorem decoderOutcomeEvent_measurable (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (result : DecoderSeed G height × DecoderCounts G) :
    MeasurableSet (decoderOutcomeEvent G height coordinates vertices arcs result) := by
  unfold decoderOutcomeEvent
  exact (Finset.finite_toSet _).measurableSet.preimage (fairBitPrefix_measurable _)

private theorem decoderOutcomeEvents_disjoint (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) :
    Pairwise (fun a b => Disjoint (decoderOutcomeEvent G height coordinates vertices arcs a)
      (decoderOutcomeEvent G height coordinates vertices arcs b)) := by
  classical
  intro a b unequal
  rw [Set.disjoint_left]
  intro stream ha hb
  simp only [decoderOutcomeEvent, Set.mem_preimage, Finset.mem_coe, completeSteinerRawSeedEvent,
    Finset.mem_filter, Finset.mem_univ, true_and, List.append_nil] at ha hb
  let width := fun (s : DecoderSeed G height × DecoderCounts G) =>
    completeSteinerBitSeedWidth G height arcs s.2.1 (s.2.2 ∘ arcs)
  have same : List.ofFn (fairBitPrefix (width a) stream) = List.ofFn (fairBitPrefix (width b) stream) := by
    rcases le_total (width a) (width b) with ab | ba
    · exact decodeCompleteSteinerSeed_prefixFree G height coordinates vertices arcs ha hb
        (fairBitPrefix_ofFn_prefix ab stream)
    · exact (decodeCompleteSteinerSeed_prefixFree G height coordinates vertices arcs hb ha
        (fairBitPrefix_ofFn_prefix ba stream)).symm
  have run : some ((a.1.1,a.1.2.1,a.1.2.2),(a.2.1,a.2.2 ∘ arcs),([] : List Bool)) =
      some ((b.1.1,b.1.2.1,b.1.2.2),(b.2.1,b.2.2 ∘ arcs),[]) := by
    change decodeCompleteSteinerSeed G height coordinates vertices arcs
      (List.ofFn (fairBitPrefix (width a) stream)) = _ at ha
    rw [same, hb] at ha
    exact ha.symm
  have output := Option.some.inj run
  have seedEq := congrArg Prod.fst output
  have hubEq := congrArg (fun r => r.2.1.1) output
  have arcEq := congrArg (fun r => r.2.1.2) output
  apply unequal
  apply Prod.ext
  · exact seedEq
  · apply Prod.ext
    · exact hubEq
    · funext i
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun arcEq (arcs.symm i)

private theorem decoderSeed_weightSum (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (seed : DecoderSeed G height) :
    (∑' counts : DecoderCounts G, fairBitMeasure (decoderOutcomeEvent G height coordinates vertices arcs (seed,counts))) =
      ENNReal.ofReal (finiteProbability ({seed} : Finset (DecoderSeed G height))) := by
  classical
  let weight (counts : DecoderCounts G) := finiteProbability (completeSteinerRawSeedEvent G height
    coordinates vertices arcs seed.1 seed.2.1 seed.2.2 counts.1 (counts.2 ∘ arcs) [])
  have term (counts : DecoderCounts G) :
      fairBitMeasure (decoderOutcomeEvent G height coordinates vertices arcs (seed,counts)) = ENNReal.ofReal (weight counts) :=
    fairBitPrefix_probability _
  have law : HasSum weight (finiteProbability ({seed} : Finset (DecoderSeed G height))) :=
    completeSteinerRawSeed_hasSum G height coordinates vertices arcs seed.1 seed.2.1 seed.2.2 []
  simp_rw [term]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => show 0 ≤ weight k from finiteProbability_nonneg _) law.summable,
    law.tsum_eq]

/-- Streams whose accepted finite prefix decodes to the specified seed. -/
noncomputable def fairBitDecoderSeedEvent (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) :
    Set (ℕ → Bool) :=
  ⋃ counts, decoderOutcomeEvent G height coordinates vertices arcs ((early,hubs,thin),counts)

theorem fairBitDecoderSeedEvent_probability (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G) :
    fairBitMeasure (fairBitDecoderSeedEvent G height coordinates vertices arcs early hubs thin) =
      ENNReal.ofReal (finiteProbability ({(early,hubs,thin)} : Finset (DecoderSeed G height))) := by
  unfold fairBitDecoderSeedEvent
  rw [measure_iUnion]
  · exact decoderSeed_weightSum G height coordinates vertices arcs (early,hubs,thin)
  · intro a b unequal
    exact decoderOutcomeEvents_disjoint G height coordinates vertices arcs (fun same => unequal (congrArg Prod.snd same))
  · exact fun counts => decoderOutcomeEvent_measurable G height coordinates vertices arcs ((early,hubs,thin),counts)

private theorem decoderTotal_measure (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) :
    fairBitMeasure (⋃ result, decoderOutcomeEvent G height coordinates vertices arcs result) = 1 := by
  classical
  rw [measure_iUnion (decoderOutcomeEvents_disjoint G height coordinates vertices arcs)
    (decoderOutcomeEvent_measurable G height coordinates vertices arcs), ENNReal.tsum_prod', tsum_fintype]
  simp_rw [decoderSeed_weightSum G height coordinates vertices arcs]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => finiteProbability_nonneg _)]
  have weights (seed : DecoderSeed G height) :=
    (completeSteinerRawSeed_hasSum G height coordinates vertices arcs seed.1 seed.2.1 seed.2.2 []).tsum_eq
  have total := completeSteinerRawSeed_totalMass G height coordinates vertices arcs []
  simp_rw [weights] at total
  rw [total, ENNReal.ofReal_one]

private theorem decoderOutcome_ae (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) :
    ∀ᵐ stream ∂fairBitMeasure, ∃ r, stream ∈ decoderOutcomeEvent G height coordinates vertices arcs r := by
  classical
  let success := ⋃ result, decoderOutcomeEvent G height coordinates vertices arcs result
  have full : fairBitMeasure success = 1 := decoderTotal_measure G height coordinates vertices arcs
  have measurable : MeasurableSet success := MeasurableSet.iUnion (decoderOutcomeEvent_measurable G height coordinates vertices arcs)
  have eventually : ∀ᵐ stream ∂fairBitMeasure, stream ∈ success := by
    rw [ae_iff]
    change fairBitMeasure successᶜ = 0
    rw [measure_compl measurable (by rw [full]; simp), full, measure_univ, tsub_self]
  filter_upwards [eventually] with stream member
  exact Set.mem_iUnion.mp member

/-- An infinite stream of independent fair bits almost surely has a finite
prefix on which the complete decoder succeeds. -/
theorem decodeCompleteSteinerSeed_ae_finishes (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) :
    ∀ᵐ stream ∂fairBitMeasure, ∃ n, (decodeCompleteSteinerSeed G height coordinates vertices arcs
      (List.ofFn (fairBitPrefix n stream))).isSome := by
  classical
  filter_upwards [decoderOutcome_ae G height coordinates vertices arcs] with stream member
  obtain ⟨r, yes⟩ := member
  simp only [decoderOutcomeEvent, Set.mem_preimage, Finset.mem_coe, completeSteinerRawSeedEvent,
    Finset.mem_filter, Finset.mem_univ, true_and, List.append_nil] at yes
  exact ⟨_, by rw [yes]; rfl⟩

private def decoderOutcomeWidth (G : Arcs V) (height : ℕ) (arcs : G ≃ Fin G.card)
    (result : DecoderSeed G height × DecoderCounts G) : ℕ :=
  completeSteinerBitSeedWidth G height arcs result.2.1 (result.2.2 ∘ arcs)

/-- The number of bits consumed, given by the unique successful prefix on
the full-measure set where decoding finishes. -/
noncomputable def fairBitDecoderBitLength (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (stream : ℕ → Bool) : ℝ≥0∞ :=
  ∑' result, (decoderOutcomeEvent G height coordinates vertices arcs result).indicator
    (fun _ => (decoderOutcomeWidth G height arcs result : ℝ≥0∞)) stream

private theorem fairBitDecoderBitLength_of_outcome (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (stream : ℕ → Bool)
    (result : DecoderSeed G height × DecoderCounts G)
    (accepted : stream ∈ decoderOutcomeEvent G height coordinates vertices arcs result) :
    fairBitDecoderBitLength G height coordinates vertices arcs stream = decoderOutcomeWidth G height arcs result := by
  classical
  unfold fairBitDecoderBitLength
  rw [tsum_eq_single result]
  · rw [Set.indicator_of_mem accepted]
  · intro r unequal
    have outside : stream ∉ decoderOutcomeEvent G height coordinates vertices arcs r :=
      fun inside => Set.disjoint_left.mp
        (decoderOutcomeEvents_disjoint G height coordinates vertices arcs unequal) inside accepted
    rw [Set.indicator_of_notMem outside]

theorem fairBitDecoderBitLength_ae_matches (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) :
    ∀ᵐ stream ∂fairBitMeasure, ∃ n : ℕ,
      fairBitDecoderBitLength G height coordinates vertices arcs stream = n ∧
        ∃ seed counts, decodeCompleteSteinerSeed G height coordinates vertices arcs
          (List.ofFn (fairBitPrefix n stream)) = some (seed,counts,[]) := by
  classical
  filter_upwards [decoderOutcome_ae G height coordinates vertices arcs] with stream member
  obtain ⟨r, yes⟩ := member
  refine ⟨decoderOutcomeWidth G height arcs r,
    fairBitDecoderBitLength_of_outcome G height coordinates vertices arcs stream r yes, ?_⟩
  simp only [decoderOutcomeEvent, Set.mem_preimage, Finset.mem_coe, completeSteinerRawSeedEvent,
    Finset.mem_filter, Finset.mem_univ, true_and, List.append_nil] at yes
  exact ⟨r.1,(r.2.1,r.2.2 ∘ arcs),yes⟩

theorem fairBitDecoderBitLength_integral (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) :
    (∫⁻ stream, fairBitDecoderBitLength G height coordinates vertices arcs stream ∂fairBitMeasure) =
      ENNReal.ofReal (completeSteinerExpectedSeedBits G height) := by
  classical
  let event := decoderOutcomeEvent G height coordinates vertices arcs
  let width := decoderOutcomeWidth G height arcs
  let cost (result : DecoderSeed G height × DecoderCounts G) := (width result : ℝ) *
    finiteProbability (completeSteinerRawSeedEvent G height coordinates vertices arcs result.1.1
      result.1.2.1 result.1.2.2 result.2.1 (result.2.2 ∘ arcs) [])
  have pointwise (r : DecoderSeed G height × DecoderCounts G) :
      (∫⁻ stream, (event r).indicator (fun _ => (width r : ℝ≥0∞)) stream ∂fairBitMeasure) = ENNReal.ofReal (cost r) := by
    rw [lintegral_indicator_const (decoderOutcomeEvent_measurable G height coordinates vertices arcs r)]
    unfold decoderOutcomeEvent cost
    rw [fairBitPrefix_probability, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have meas (r : DecoderSeed G height × DecoderCounts G) : AEMeasurable
      ((event r).indicator (fun _ => (width r : ℝ≥0∞))) fairBitMeasure :=
    (measurable_const.indicator (decoderOutcomeEvent_measurable G height coordinates vertices arcs r)).aemeasurable
  have costsNonneg (r : DecoderSeed G height × DecoderCounts G) : 0 ≤ cost r :=
    mul_nonneg (Nat.cast_nonneg _) (finiteProbability_nonneg _)
  have summed (seed : DecoderSeed G height) : Summable (fun counts : DecoderCounts G => cost (seed,counts)) :=
    (completeSteinerRawBitMoment_hasSum G height coordinates vertices arcs seed.1 seed.2.1 seed.2.2 []).summable
  change (∫⁻ stream, ∑' r, (event r).indicator (fun _ => (width r : ℝ≥0∞)) stream ∂fairBitMeasure) = _
  rw [lintegral_tsum meas, ENNReal.tsum_prod', tsum_fintype]
  simp_rw [pointwise, ← ENNReal.ofReal_tsum_of_nonneg (fun k => costsNonneg (_,k)) (summed _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun seed _ => tsum_nonneg fun k => costsNonneg (seed,k))]
  change ENNReal.ofReal (completeSteinerRawBitMean G height coordinates vertices arcs) = _
  rw [completeSteinerRawBitMean_eq]

theorem fairBitDecoderBitLength_polynomial (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) :
    (∫⁻ stream, fairBitDecoderBitLength G height coordinates vertices arcs stream ∂fairBitMeasure) ≤
      (completeSteinerSeedPolynomial (Fintype.card V) G.card height : ℝ≥0∞) := by
  rw [fairBitDecoderBitLength_integral, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (completeSteinerExpectedSeedBits_polynomial G height)

/-- Edge count for the seed selected by the successful prefix. -/
noncomputable def fairBitDecoderEdgeCount (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (D : List (V × V))
    (stream : ℕ → Bool) : ℝ≥0∞ :=
    ∑ seed : DecoderSeed G height,
      (fairBitDecoderSeedEvent G height coordinates vertices arcs seed.1 seed.2.1 seed.2.2).indicator
        (fun _ => ((completeSteinerDrawRun G height seed.1 seed.2.1 seed.2.2 D).card : ℝ≥0∞)) stream

/-- The expected retained edge count under the measure on complete fair-bit
streams agrees with the original finite-seed mean on the same trace. -/
theorem fairBitDecoderEdgeIntegral_eq (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (D : List (V × V)) :
    (∫⁻ stream, fairBitDecoderEdgeCount G height coordinates vertices arcs D stream ∂fairBitMeasure) =
      ENNReal.ofReal (completeSteinerMean G height D) := by
  classical
  let event (seed : DecoderSeed G height) :=
    fairBitDecoderSeedEvent G height coordinates vertices arcs seed.1 seed.2.1 seed.2.2
  let cost (seed : DecoderSeed G height) := (completeSteinerDrawRun G height seed.1 seed.2.1 seed.2.2 D).card
  have meas (seed : DecoderSeed G height) : MeasurableSet (event seed) :=
    MeasurableSet.iUnion fun counts => decoderOutcomeEvent_measurable G height coordinates vertices arcs (seed,counts)
  change (∫⁻ stream, ∑ seed, (event seed).indicator (fun _ => (cost seed : ℝ≥0∞)) stream ∂fairBitMeasure) = _
  rw [lintegral_finsetSum _ (fun seed _ => measurable_const.indicator (meas seed))]
  rw [← completeSteinerRawMean_eq G height coordinates vertices arcs D]
  unfold completeSteinerRawMean
  have weight (seed : DecoderSeed G height) :=
    (completeSteinerRawSeed_hasSum G height coordinates vertices arcs seed.1 seed.2.1 seed.2.2 []).tsum_eq
  simp_rw [weight]
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (finiteProbability_nonneg _))]
  apply Finset.sum_congr rfl
  intro seed _
  rw [lintegral_indicator_const (meas seed)]
  unfold event
  rw [fairBitDecoderSeedEvent_probability, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

/-- Theorem 21 under the product fair-bit measure with graph-based index orders. -/
theorem theorem21_online_steiner_fair_expected {ε : ℝ} (epsilon : 0 < ε) :
    ∃ height : ℕ, 0 < height ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (W : Type u) [LinearOrder W] [Fintype W] {G Z : Arcs W}
        (D : List (W × W)), Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
        (∫⁻ stream, fairBitDecoderEdgeCount G height (steinerEarlyCoordinateIndex G height)
          (steinerVertexIndex W) (steinerArcIndex G) D stream ∂fairBitMeasure) ≤
          ENNReal.ofReal (K * (Fintype.card W : ℝ) ^ (3/5 + ε) * Z.card) := by
  obtain ⟨height, heightPos, K, Kpos, rate⟩ := theorem21_online_steiner_expected.{u} epsilon
  refine ⟨height, heightPos, K, Kpos, ?_⟩
  intro W _ _ G Z D sub reaches
  rw [fairBitDecoderEdgeIntegral_eq]
  exact ENNReal.ofReal_le_ofReal (rate W D sub reaches)

theorem fairBitDecoderBitLength_measurable (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) :
    Measurable (fairBitDecoderBitLength G height coordinates vertices arcs) := by
  unfold fairBitDecoderBitLength
  exact Measurable.tsum fun result => measurable_const.indicator
    (decoderOutcomeEvent_measurable G height coordinates vertices arcs result)

/-- A fixed budget of fair bits fails only on the tail of the consumed-length distribution. -/
theorem fairBitDecoder_failure_le (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (budget : ℕ) :
    fairBitMeasure {stream | decodeCompleteSteinerSeed G height coordinates vertices arcs
      (List.ofFn (fairBitPrefix budget stream)) = none} ≤
        (completeSteinerSeedPolynomial (Fintype.card V) G.card height : ℝ≥0∞) / (budget+1 : ℕ) := by
  classical
  let length := fairBitDecoderBitLength G height coordinates vertices arcs
  have outside : {stream | decodeCompleteSteinerSeed G height coordinates vertices arcs
      (List.ofFn (fairBitPrefix budget stream)) = none} ≤ᵐ[fairBitMeasure]
        {stream | ((budget+1 : ℕ) : ℝ≥0∞) ≤ length stream} := by
    filter_upwards [fairBitDecoderBitLength_ae_matches G height coordinates vertices arcs] with stream measured
    obtain ⟨n, len, ⟨early,hubs,thin⟩, ⟨hubRejects,thinRejects⟩, parsed⟩ := measured
    intro failed
    have greater : budget < n := by
      by_contra! within
      obtain ⟨tail, joined⟩ := fairBitPrefix_ofFn_prefix within stream
      have still := decodeCompleteSteinerSeed_append G height coordinates vertices arcs tail parsed
      rw [joined] at still
      change decodeCompleteSteinerSeed G height coordinates vertices arcs
        (List.ofFn (fairBitPrefix budget stream)) = none at failed
      rw [failed] at still
      contradiction
    change ((budget+1 : ℕ) : ℝ≥0∞) ≤ length stream
    rw [show length stream = (n : ℝ≥0∞) from len]
    exact_mod_cast (Nat.succ_le_of_lt greater)
  exact (measure_mono_ae outside).trans <|
    (meas_ge_le_lintegral_div (fairBitDecoderBitLength_measurable G height coordinates vertices arcs).aemeasurable
      (by positivity) (by simp)).trans <|
    ENNReal.div_le_div_right (fairBitDecoderBitLength_polynomial G height coordinates vertices arcs) _

private theorem fairBitOutcome_cost (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (D : List (V × V)) (stream : ℕ → Bool)
    (result : DecoderSeed G height × DecoderCounts G)
    (accepted : stream ∈ decoderOutcomeEvent G height coordinates vertices arcs result) :
    fairBitDecoderEdgeCount G height coordinates vertices arcs D stream = (completeSteinerDrawRun G height result.1.1 result.1.2.1 result.1.2.2 D).card := by
  classical
  unfold fairBitDecoderEdgeCount
  rw [Finset.sum_eq_single result.1]
  · have member : stream ∈ fairBitDecoderSeedEvent G height coordinates vertices arcs result.1.1 result.1.2.1 result.1.2.2 :=
      Set.mem_iUnion.mpr ⟨result.2,accepted⟩
    rw [Set.indicator_of_mem member]
  · intro seed _ unequal
    apply Set.indicator_of_notMem
    intro member
    obtain ⟨counts, inside⟩ := Set.mem_iUnion.mp member
    have separate : (seed,counts) ≠ result := fun eq => unequal (congrArg Prod.fst eq)
    exact Set.disjoint_left.mp (decoderOutcomeEvents_disjoint G height coordinates vertices arcs separate) inside accepted
  · simp

/-- Any successful reading of a prefix gives the same cost as the stream outcome. -/
theorem fairBitDecoderEdgeCount_ae_decode_prefix (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (D : List (V × V)) :
    ∀ᵐ stream ∂fairBitMeasure, ∀ n seed counts rest,
      decodeCompleteSteinerSeed G height coordinates vertices arcs (List.ofFn (fairBitPrefix n stream)) =
        some (seed, counts, rest) →
      fairBitDecoderEdgeCount G height coordinates vertices arcs D stream =
        (completeSteinerDrawRun G height seed.1 seed.2.1 seed.2.2 D).card := by
  filter_upwards [decoderOutcome_ae G height coordinates vertices arcs] with stream accepted
  obtain ⟨result, member⟩ := accepted
  intro n seed counts rest read
  rw [fairBitOutcome_cost G height coordinates vertices arcs D stream result member]
  simp only [decoderOutcomeEvent, Set.mem_preimage, Finset.mem_coe, completeSteinerRawSeedEvent,
    Finset.mem_filter, Finset.mem_univ, true_and, List.append_nil] at member
  let width := decoderOutcomeWidth G height arcs result
  change decodeCompleteSteinerSeed G height coordinates vertices arcs
    (List.ofFn (fairBitPrefix width stream)) = _ at member
  have same : seed = result.1 := by
    rcases le_total width n with short | long
    · obtain ⟨tail, joined⟩ := fairBitPrefix_ofFn_prefix short stream
      have upgraded := decodeCompleteSteinerSeed_append G height coordinates vertices arcs tail member
      rw [joined, read] at upgraded
      exact congrArg Prod.fst (Option.some.inj upgraded)
    · obtain ⟨tail, joined⟩ := fairBitPrefix_ofFn_prefix long stream
      obtain ⟨early, hubs, thin⟩ := seed
      obtain ⟨hubRejects, thinRejects⟩ := counts
      have upgraded := decodeCompleteSteinerSeed_append G height coordinates vertices arcs tail read
      rw [joined, member] at upgraded
      exact (congrArg Prod.fst (Option.some.inj upgraded)).symm
  rw [same]

end OnlineReachabilityPreservers
