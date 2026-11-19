import Mathlib.Analysis.Normed.Ring.InfiniteSum
import OnlineReachabilityPreservers.SteinerBitReplay

/-! Normalize the complete decoder’s raw first-success events and recover the fixed-trace expected cost. -/

namespace OnlineReachabilityPreservers

universe u

private theorem hasSum_nonnegativeProduct {I J : Type*} {f : I → ℝ} {g : J → ℝ} {a b : ℝ}
    (hf : HasSum f a) (hg : HasSum g b) (nonnegF : ∀ i, 0 ≤ f i) (nonnegG : ∀ j, 0 ≤ g j) :
    HasSum (fun z : I × J => f z.1 * g z.2) (a*b) :=
  hf.mul hg (hf.summable.mul_of_nonneg hg.summable nonnegF nonnegG)

private theorem hasSum_coordinateProduct (n : ℕ) (f : Fin n → ℕ → ℝ) (value : Fin n → ℝ)
    (laws : ∀ i, HasSum (f i) (value i)) (nonneg : ∀ i k, 0 ≤ f i k) :
    HasSum (fun k : Fin n → ℕ => ∏ i, f i (k i)) (∏ i, value i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let split := Fin.consEquiv (fun _ : Fin (n+1) => ℕ)
    have tailLaw := ih (fun i => f i.succ) (fun i => value i.succ) (fun i => laws i.succ) (fun i => nonneg i.succ)
    have pairLaw := hasSum_nonnegativeProduct (laws 0) tailLaw (nonneg 0)
      (fun k => Finset.prod_nonneg fun i _ => nonneg i.succ (k i))
    rw [Fin.prod_univ_succ value]
    apply split.hasSum_iff.mp
    simpa [split, Fin.prod_univ_succ, Function.comp_def] using pairLaw

private theorem flatBitRetry_hasSum {N : ℕ} (positive : 0 < N) (target : Fin N) :
    HasSum (fun k => finiteProbability (flatBitRetryLastEvent k target [])) (1/(N:ℝ)) := by
  have summable : Summable (fun k => finiteProbability (flatBitRetryLastEvent k target [])) := by
    simp_rw [flatBitRetryLastEvent_probability positive, fairBitRetryLastEvent_eq positive,
      rejectionAtBitAttempt_probability positive]
    obtain ⟨nonnegative, half, _, _⟩ := uniformRejectionSeries positive
    exact (summable_geometric_of_lt_one nonnegative (by linarith only [half])).mul_right _
  exact summable.hasSum_iff.mpr (flatBitRetry_uniform positive target [])

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Sum the probabilities of the actual complete decoder's raw first-success
events over all joint rejection counts. The count of each thin draw can be
indexed by its position in the supplied arc enumeration. -/
theorem completeSteinerRawSeed_hasSum (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (rest : List Bool) :
    HasSum (fun counts : (Fin (completeSteinerHubCount V) → ℕ) × (Fin G.card → ℕ) =>
      finiteProbability (completeSteinerRawSeedEvent G height coordinates vertices arcs early hubs thin
        counts.1 (counts.2 ∘ arcs) rest))
      (finiteProbability ({(early,hubs,thin)} : Finset (EarlyRoundSample G height × _ × ThinSample G))) := by
  classical
  let fixed := finiteProbability ({earlySeedBitWords G height early ∘ coordinates.symm} : Finset _)
  let hubMass := fun i k => finiteProbability (flatBitRetryLastEvent k (vertices (hubs i)) [])
  let thinMass := fun i k => finiteProbability (flatBitRetryLastEvent k (thin (arcs.symm i)) [])
  have hubLaw (i : Fin (completeSteinerHubCount V)) : HasSum (hubMass i) (1/(Fintype.card V:ℝ)) :=
    flatBitRetry_hasSum (Fintype.card_pos_iff.mpr ⟨hubs i⟩) (vertices (hubs i))
  have thinLaw (i : Fin G.card) : HasSum (thinMass i) (1/(G.card:ℝ)) :=
    flatBitRetry_hasSum (Finset.card_pos.mpr ⟨(arcs.symm i).val,(arcs.symm i).property⟩) (thin (arcs.symm i))
  have hubProd := hasSum_coordinateProduct _ hubMass _ hubLaw
    (fun _ _ => finiteProbability_nonneg _)
  have thinProd := hasSum_coordinateProduct _ thinMass _ thinLaw
    (fun _ _ => finiteProbability_nonneg _)
  have joint := (hasSum_nonnegativeProduct hubProd thinProd
    (fun _ => Finset.prod_nonneg fun _ _ => finiteProbability_nonneg _)
    (fun _ => Finset.prod_nonneg fun _ _ => finiteProbability_nonneg _)).mul_left fixed
  have total := completeSteinerBitSeed_uniform G height coordinates vertices arcs early hubs thin
  dsimp only at total
  change fixed * ((∏ i, ∑' k, hubMass i k) * ∏ i, ∑' k, thinMass i k) = _ at total
  simp_rw [fun i => (hubLaw i).tsum_eq, fun i => (thinLaw i).tsum_eq] at total
  rw [← total]
  convert joint using 1
  funext counts
  rw [completeSteinerRawSeedEvent_probability]
  have terms := completeSteinerBitSeedEvent_probability G height coordinates vertices arcs early hubs thin
    counts.1 (counts.2 ∘ arcs) rest
  dsimp only at terms
  have arcWeight : (∏ i : Fin G.card, thinMass i (counts.2 (arcs (arcs.symm i)))) =
      ∏ i : Fin G.card, thinMass i (counts.2 i) := by
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (thinMass i) (congrArg counts.2 (arcs.apply_symm_apply i))
  exact terms.trans (congrArg (fun weight => fixed*((∏ i, hubMass i (counts.1 i))*weight)) arcWeight)

/-- All successful first prefixes carry total weight one over the seed and
joint rejection-count outcomes. -/
theorem completeSteinerRawSeed_totalMass (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (rest : List Bool) :
    (∑ seed : EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G,
      ∑' counts : (Fin (completeSteinerHubCount V) → ℕ) × (Fin G.card → ℕ),
        finiteProbability (completeSteinerRawSeedEvent G height coordinates vertices arcs
          seed.1 seed.2.1 seed.2.2 counts.1 (counts.2 ∘ arcs) rest)) = 1 := by
  classical
  let Seed := EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G
  have weight (seed : Seed) :=
    (completeSteinerRawSeed_hasSum G height coordinates vertices arcs seed.1 seed.2.1 seed.2.2 rest).tsum_eq
  simp_rw [weight]
  let zero : Fin (forestSeedSize (forestScale G height)) := ⟨0, by positivity⟩
  have early : Nonempty (EarlyRoundSample G height) := ⟨fun _ _ _ => ⟨zero, fun _ _ => zero⟩⟩
  have hub : Nonempty (Fin (completeSteinerHubCount V) → V) := by
    cases isEmpty_or_nonempty V with
    | inl empty => exact completeSteinerHubDraw_empty V
    | inr inhabited => exact ⟨fun _ => Classical.choice inhabited⟩
  have thin : Nonempty (ThinSample G) :=
    ⟨fun e => ⟨0, Finset.card_pos.mpr ⟨e.val,e.property⟩⟩⟩
  have nonempty : Nonempty Seed := ⟨Classical.choice early, Classical.choice hub, Classical.choice thin⟩
  have cardPos : (0 : ℝ) < Fintype.card Seed := Nat.cast_pos.mpr Fintype.card_pos
  simp only [finiteProbability, Finset.card_singleton, Nat.cast_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one_div]
  exact div_self cardPos.ne'

/-- Expected edge count when using the complete decoder's raw first prefixes. -/
noncomputable def completeSteinerRawMean (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (D : List (V × V)) : ℝ := by
  classical
  exact ∑ seed : EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G,
    ((completeSteinerDrawRun G height seed.1 seed.2.1 seed.2.2 D).card : ℝ) *
      (∑' counts : (Fin (completeSteinerHubCount V) → ℕ) × (Fin G.card → ℕ),
        finiteProbability (completeSteinerRawSeedEvent G height coordinates vertices arcs
          seed.1 seed.2.1 seed.2.2 counts.1 (counts.2 ∘ arcs) []))

theorem completeSteinerRawMean_eq (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (D : List (V × V)) :
    completeSteinerRawMean G height coordinates vertices arcs D = completeSteinerMean G height D := by
  classical
  unfold completeSteinerRawMean
  let Seed := EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G
  have weight (seed : Seed) :=
    (completeSteinerRawSeed_hasSum G height coordinates vertices arcs seed.1 seed.2.1 seed.2.2 []).tsum_eq
  simp_rw [weight]
  simp only [finiteProbability, Finset.card_singleton, Nat.cast_one, mul_one_div,
    completeSteinerMean, Fintype.expect_eq_sum_div_card, thinMean, Fintype.sum_prod_type,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_mul, Nat.cast_pow,
    Finset.sum_div, div_div, mul_comm, mul_assoc]

/-- The fixed-trace competitive bound with the seed law induced by actual
consecutive fair-bit prefixes and the supplied finite index orders. -/
theorem theorem21_online_steiner_raw_expected {ε : ℝ} (epsilon : 0 < ε) :
    ∃ height : ℕ, 0 < height ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type u) [LinearOrder V] [Fintype V] {G Z : Arcs V}
        (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
        (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) (D : List (V × V)),
        Z ⊆ G → (∀ d ∈ D, Reach Z d.1 d.2) →
        completeSteinerRawMean G height coordinates vertices arcs D ≤ K * (Fintype.card V : ℝ) ^ (3/5 + ε) * Z.card := by
  obtain ⟨height, heightPos, K, Kpos, rate⟩ := theorem21_online_steiner_expected.{u} epsilon
  refine ⟨height, heightPos, K, Kpos, ?_⟩
  intro V _ _ G Z coordinates vertices arcs D sub reaches
  rw [completeSteinerRawMean_eq]
  exact rate V D sub reaches

private theorem hasSum_weightedProduct {I J : Type*} {f c : I → ℝ} {g d : J → ℝ}
    {a b x y : ℝ} (hf : HasSum f a) (hg : HasSum g b)
    (hfc : HasSum (fun i => c i*f i) (a*x)) (hgd : HasSum (fun j => d j*g j) (b*y))
    (nonnegF : ∀ i, 0 ≤ f i) (nonnegG : ∀ j, 0 ≤ g j) (nonnegC : ∀ i, 0 ≤ c i) (nonnegD : ∀ j, 0 ≤ d j) :
    HasSum (fun p : I × J => (c p.1+d p.2)*(f p.1*g p.2)) ((a*b)*(x+y)) := by
  have left := hfc.mul hg (hfc.summable.mul_of_nonneg hg.summable
    (fun i => mul_nonneg (nonnegC i) (nonnegF i)) nonnegG)
  have right := hf.mul hgd (hf.summable.mul_of_nonneg hgd.summable nonnegF
    (fun j => mul_nonneg (nonnegD j) (nonnegG j)))
  convert left.add right using 1
  · funext p
    ring
  · ring

private theorem flatBitRetry_formula {N : ℕ} (positive : 0 < N) (k : ℕ) (target : Fin N) :
    let total : ℝ := (2^uniformProposalWidth N : ℕ)
    finiteProbability (flatBitRetryLastEvent k target []) = ((total-N)/total)^k*(1/total) := by
  rw [flatBitRetryLastEvent_probability positive, fairBitRetryLastEvent_eq positive]
  exact rejectionAtBitAttempt_probability positive k target

private theorem flatBitRetry_countMoment {N : ℕ} (positive : 0 < N) (target : Fin N) :
    HasSum (fun k : ℕ => (uniformProposalWidth N : ℝ)*(k+1)*
      finiteProbability (flatBitRetryLastEvent k target [])) ((1/(N:ℝ))*expectedRejectionBits N) := by
  let total : ℝ := (2^uniformProposalWidth N : ℕ)
  let miss : ℝ := (total-N)/total
  have bounds := uniformRejectionSeries positive
  have norm : ‖miss‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg bounds.1]
    exact lt_of_le_of_lt bounds.2.1 (by norm_num)
  have geo : Summable (fun k : ℕ => ((k:ℝ)+1)*miss^k) := by
    simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
      summable_choose_mul_geometric_of_norm_lt_one 1 norm
  have summable : Summable (fun k : ℕ => (uniformProposalWidth N : ℝ)*(k+1)*
      finiteProbability (flatBitRetryLastEvent k target [])) := by
    refine ((geo.mul_left (uniformProposalWidth N : ℝ)).mul_right (1/total)).congr ?_
    intro k
    rw [flatBitRetry_formula positive]
    ring
  apply summable.hasSum_iff.mpr
  have combined := flatBitRetry_expectedBits_eq positive []
  have same (k : ℕ) : (∑ t : Fin N, finiteProbability (flatBitRetryLastEvent k t [])) =
      (N:ℝ)*finiteProbability (flatBitRetryLastEvent k target []) := by
    simp only [flatBitRetry_formula positive, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← combined]
  simp_rw [same, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have nonzero : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr positive.ne'
  field_simp

private theorem hasSum_coordinateWeight (n : ℕ) (weight cost : Fin n → ℕ → ℝ)
    (mass moment : Fin n → ℝ) (laws : ∀ i, HasSum (weight i) (mass i))
    (moments : ∀ i, HasSum (fun k => cost i k * weight i k) (mass i * moment i))
    (nonnegWeight : ∀ i k, 0 ≤ weight i k) (nonnegCost : ∀ i k, 0 ≤ cost i k) :
    HasSum (fun count : Fin n → ℕ => (∑ i, cost i (count i)) * ∏ i, weight i (count i))
      ((∏ i, mass i)*(∑ i, moment i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    let split := Fin.consEquiv (fun _ : Fin (n+1) => ℕ)
    let tailWeight := fun count : Fin n → ℕ => ∏ i, weight i.succ (count i)
    let tailCost := fun count : Fin n → ℕ => ∑ i, cost i.succ (count i)
    have tailLaw : HasSum tailWeight (∏ i : Fin n, mass i.succ) := hasSum_coordinateProduct n
      (fun i => weight i.succ) (fun i => mass i.succ) (fun i => laws i.succ) (fun i => nonnegWeight i.succ)
    have tailMoment : HasSum (fun count => tailCost count * tailWeight count)
        ((∏ i : Fin n, mass i.succ) * ∑ i : Fin n, moment i.succ) := ih
      (fun i => weight i.succ) (fun i => cost i.succ) (fun i => mass i.succ) (fun i => moment i.succ)
      (fun i => laws i.succ) (fun i => moments i.succ) (fun i => nonnegWeight i.succ) (fun i => nonnegCost i.succ)
    have pair := hasSum_weightedProduct (laws 0) tailLaw (moments 0) tailMoment (nonnegWeight 0)
      (fun count => Finset.prod_nonneg (fun i _ => nonnegWeight i.succ (count i))) (nonnegCost 0)
      (fun count => Finset.sum_nonneg (fun i _ => nonnegCost i.succ (count i)))
    rw [Fin.prod_univ_succ mass, Fin.sum_univ_succ moment]
    apply split.hasSum_iff.mp
    simpa [split, tailCost, tailWeight, Fin.sum_univ_succ, Fin.prod_univ_succ, Function.comp_def] using pair

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- The actual bit length summed against all joint first-success profiles
has the uniform seed weight times the seed-independent expected bit budget. -/
theorem completeSteinerRawBitMoment_hasSum (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card)
    (early : EarlyRoundSample G height) (hubs : Fin (completeSteinerHubCount V) → V) (thin : ThinSample G)
    (rest : List Bool) :
    HasSum (fun counts : (Fin (completeSteinerHubCount V) → ℕ) × (Fin G.card → ℕ) =>
      (completeSteinerBitSeedWidth G height arcs counts.1 (counts.2 ∘ arcs) : ℝ) *
      finiteProbability (completeSteinerRawSeedEvent G height coordinates vertices arcs early hubs thin
        counts.1 (counts.2 ∘ arcs) rest))
      (finiteProbability ({(early,hubs,thin)} : Finset (EarlyRoundSample G height × _ × ThinSample G)) *
        completeSteinerExpectedSeedBits G height) := by
  classical
  let H := Fin (completeSteinerHubCount V)
  let A := Fin G.card
  let fixed := finiteProbability ({earlySeedBitWords G height early ∘ coordinates.symm} : Finset _)
  let earlySize : ℝ := earlySeedBits G height
  let hubWeight := fun i : H => fun k => finiteProbability (flatBitRetryLastEvent k (vertices (hubs i)) [])
  let thinWeight := fun i : A => fun k => finiteProbability (flatBitRetryLastEvent k (thin (arcs.symm i)) [])
  let hubCost := fun k : ℕ => (uniformProposalWidth (Fintype.card V) : ℝ)*((k:ℝ)+1)
  let thinCost := fun k : ℕ => (uniformProposalWidth G.card : ℝ)*((k:ℝ)+1)
  let hubMass := 1/(Fintype.card V:ℝ)
  let thinMass := 1/(G.card:ℝ)
  let hubMoment := expectedRejectionBits (Fintype.card V)
  let thinMoment := expectedRejectionBits G.card
  let allHubMass := ∏ _ : H, hubMass
  let allThinMass := ∏ _ : A, thinMass
  let allHubMoment := ∑ _ : H, hubMoment
  let allThinMoment := ∑ _ : A, thinMoment
  let allHubWeight := fun k : H → ℕ => ∏ i, hubWeight i (k i)
  let allThinWeight := fun k : A → ℕ => ∏ i, thinWeight i (k i)
  let allHubCost := fun k : H → ℕ => ∑ i, hubCost (k i)
  let allThinCost := fun k : A → ℕ => ∑ i, thinCost (k i)
  have hPos (i : H) : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨hubs i⟩
  have tPos (i : A) : 0 < G.card := Finset.card_pos.mpr ⟨(arcs.symm i).val,(arcs.symm i).property⟩
  have hLaw (i : H) : HasSum (hubWeight i) hubMass := flatBitRetry_hasSum (hPos i) _
  have tLaw (i : A) : HasSum (thinWeight i) thinMass := flatBitRetry_hasSum (tPos i) _
  have hMoment (i : H) : HasSum (fun k => hubCost k * hubWeight i k) (hubMass * hubMoment) :=
    flatBitRetry_countMoment (hPos i) _
  have tMoment (i : A) : HasSum (fun k => thinCost k * thinWeight i k) (thinMass * thinMoment) :=
    flatBitRetry_countMoment (tPos i) _
  have hCostNonneg (k : ℕ) : 0 ≤ hubCost k := by dsimp [hubCost]; positivity
  have tCostNonneg (k : ℕ) : 0 ≤ thinCost k := by dsimp [thinCost]; positivity
  have hh : HasSum allHubWeight allHubMass := hasSum_coordinateProduct _ hubWeight _ hLaw
    (fun _ _ => finiteProbability_nonneg _)
  have tt : HasSum allThinWeight allThinMass := hasSum_coordinateProduct _ thinWeight _ tLaw
    (fun _ _ => finiteProbability_nonneg _)
  have hhWeighted : HasSum (fun k => allHubCost k * allHubWeight k) (allHubMass * allHubMoment) :=
    hasSum_coordinateWeight _ hubWeight (fun _ => hubCost) _ _ hLaw hMoment
      (fun _ _ => finiteProbability_nonneg _) (fun _ => hCostNonneg)
  have ttWeighted : HasSum (fun k => allThinCost k * allThinWeight k) (allThinMass * allThinMoment) :=
    hasSum_coordinateWeight _ thinWeight (fun _ => thinCost) _ _ tLaw tMoment
      (fun _ _ => finiteProbability_nonneg _) (fun _ => tCostNonneg)
  have hhNonneg (k : H → ℕ) : 0 ≤ allHubWeight k := Finset.prod_nonneg fun _ _ => finiteProbability_nonneg _
  have ttNonneg (k : A → ℕ) : 0 ≤ allThinWeight k := Finset.prod_nonneg fun _ _ => finiteProbability_nonneg _
  have variablePart := hasSum_weightedProduct hh tt hhWeighted ttWeighted hhNonneg ttNonneg
    (fun k => Finset.sum_nonneg fun i _ => hCostNonneg (k i))
    (fun k => Finset.sum_nonneg fun i _ => tCostNonneg (k i))
  have constantPart := (hasSum_nonnegativeProduct hh tt hhNonneg ttNonneg).mul_left earlySize
  have combined : HasSum (fun counts : (H → ℕ) × (A → ℕ) =>
      (earlySize + allHubCost counts.1 + allThinCost counts.2) *
        (fixed * (allHubWeight counts.1 * allThinWeight counts.2)))
      ((fixed * (allHubMass * allThinMass)) * (earlySize + allHubMoment + allThinMoment)) := by
    convert (constantPart.add variablePart).mul_left fixed using 1
    · funext count
      ring
    · ring
  have uniform := completeSteinerBitSeed_uniform G height coordinates vertices arcs early hubs thin
  dsimp only at uniform
  change fixed * ((∏ i, ∑' k, hubWeight i k) * ∏ i, ∑' k, thinWeight i k) = _ at uniform
  simp_rw [fun i => (hLaw i).tsum_eq, fun i => (tLaw i).tsum_eq] at uniform
  have budget : earlySize + allHubMoment + allThinMoment = completeSteinerExpectedSeedBits G height := by
    simp only [earlySize, allHubMoment, allThinMoment, hubMoment, thinMoment, H, A, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, completeSteinerExpectedSeedBits]
  rw [← uniform, ← budget]
  convert combined using 1
  funext counts
  have reindex (i : A) : arcs (arcs.symm i) = i := arcs.apply_symm_apply i
  have size : (completeSteinerBitSeedWidth G height arcs counts.1 (counts.2 ∘ arcs) : ℝ) =
      earlySize + allHubCost counts.1 + allThinCost counts.2 := by
    have earlyNat : (∑ _ : Fin (Fintype.card (EarlySeedCoordinate G height)), ((forestScale G height).log2+1)) =
        earlySeedBits G height := by simp [earlySeedBits]
    rw [completeSteinerBitSeedWidth, earlyNat]
    simp only [earlySize, allHubCost, allThinCost, hubCost, thinCost, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sum, Nat.cast_one, Function.comp_apply, reindex, mul_comm, add_assoc]
    rfl
  rw [size, completeSteinerRawSeedEvent_probability]
  have terms := completeSteinerBitSeedEvent_probability G height coordinates vertices arcs early hubs thin
    counts.1 (counts.2 ∘ arcs) rest
  dsimp only at terms
  have arcWeight : (∏ i : A, thinWeight i (counts.2 (arcs (arcs.symm i)))) = allThinWeight counts.2 := by
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (thinWeight i) (congrArg counts.2 (reindex i))
  rw [terms]
  congr 2
  exact congrArg (fun mass => allHubWeight counts.1 * mass) arcWeight

/-- The expectation of the number of bits consumed by the complete decoder,
weighted by its actual successful raw prefixes. -/
noncomputable def completeSteinerRawBitMean (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) : ℝ := by
  classical
  exact ∑ seed : EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G,
    ∑' counts : (Fin (completeSteinerHubCount V) → ℕ) × (Fin G.card → ℕ),
      (completeSteinerBitSeedWidth G height arcs counts.1 (counts.2 ∘ arcs) : ℝ) *
      finiteProbability (completeSteinerRawSeedEvent G height coordinates vertices arcs
        seed.1 seed.2.1 seed.2.2 counts.1 (counts.2 ∘ arcs) [])

theorem completeSteinerRawBitMean_eq (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) :
    completeSteinerRawBitMean G height coordinates vertices arcs = completeSteinerExpectedSeedBits G height := by
  classical
  unfold completeSteinerRawBitMean
  let Seed := EarlyRoundSample G height × (Fin (completeSteinerHubCount V) → V) × ThinSample G
  have moment (seed : Seed) :=
    (completeSteinerRawBitMoment_hasSum G height coordinates vertices arcs seed.1 seed.2.1 seed.2.2 []).tsum_eq
  have weight (seed : Seed) :=
    (completeSteinerRawSeed_hasSum G height coordinates vertices arcs seed.1 seed.2.1 seed.2.2 []).tsum_eq
  have total := completeSteinerRawSeed_totalMass G height coordinates vertices arcs []
  simp_rw [weight] at total
  simp_rw [moment, ← Finset.sum_mul, total, one_mul]

theorem completeSteinerRawBitMean_polynomial (G : Arcs V) (height : ℕ)
    (coordinates : EarlySeedCoordinate G height ≃ Fin (Fintype.card (EarlySeedCoordinate G height)))
    (vertices : V ≃ Fin (Fintype.card V)) (arcs : G ≃ Fin G.card) :
    completeSteinerRawBitMean G height coordinates vertices arcs ≤
      completeSteinerSeedPolynomial (Fintype.card V) G.card height := by
  rw [completeSteinerRawBitMean_eq]
  exact completeSteinerExpectedSeedBits_polynomial G height

end OnlineReachabilityPreservers
