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

end OnlineReachabilityPreservers
