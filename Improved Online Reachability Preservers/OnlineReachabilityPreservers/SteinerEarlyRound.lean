import Mathlib.Algebra.Order.BigOperators.Expect
import OnlineReachabilityPreservers.SteinerAssembly
import OnlineReachabilityPreservers.SteinerForestRounding

/-! Amplification and irrevocable purchases for the early Steiner routine. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped BigOperators

variable {V : Type*} {height : ℕ} [LinearOrder V] [Fintype V]

local instance earlyForestNetworkDecidableEq : DecidableEq (ForestNetworkVertex V height) :=
  (inferInstance : LinearOrder (ForestNetworkVertex V height)).toDecidableEq

def forestScale (G : Arcs V) (height : ℕ) : ℕ :=
  weightedCoverScale (forestNetworkPriced G (heightForest G height)) (forestNetworkWeight G)

theorem forestScale_pos (G : Arcs V) (height : ℕ) : 0 < forestScale G height :=
  Nat.zero_lt_one.trans_le (le_max_left _ _)

abbrev ForestTrialArray (V : Type*) (height scale trials : ℕ) :=
  Fin trials → ForestRoundingSample V height scale

def roundedForestTrials (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ)
    (scale trials : ℕ) (samples : ForestTrialArray V height scale trials) : Arcs (HeightForestVertex V height) :=
  univ.biUnion fun i => roundedForestLinks G charges scale (samples i)

theorem roundedForestTrials_sub (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ)
    (scale trials : ℕ) (samples : ForestTrialArray V height scale trials) :
    roundedForestTrials G charges scale trials samples ⊆ heightForest G height := by
  intro e he
  obtain ⟨i, _, chosen⟩ := mem_biUnion.mp he
  exact roundedForestLinks_sub G charges scale (samples i) chosen

omit [LinearOrder V] [Fintype V] in
private theorem heightForestServes_mono {A B : Arcs (HeightForestVertex V height)}
    (inside : A ⊆ B) {d : V × V} (r : heightForestServes A d) : heightForestServes B d := by
  obtain ⟨a, b, start, finish, path⟩ := r
  exact ⟨a, b, start, finish, reach_mono inside path⟩

noncomputable def forestTrialsFailure (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ)
    (scale trials : ℕ) (d : V × V) : Finset (ForestTrialArray V height scale trials) := by
  classical
  exact univ.filter fun samples => ¬ heightForestServes (roundedForestTrials G charges scale trials samples) d

theorem forestTrialsFailure_bound (G : Arcs V)
    (charges : ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ)
    (scale trials : ℕ) (d : V × V) (scalePos : 0 < scale)
    (covered : weightedNetworkCovered (forestNetworkPriced G (heightForest G height))
      (forestNetworkDemand G height d) (forestNetworkWeight G) charges scale) :
    finiteProbability (forestTrialsFailure G charges scale trials d) ≤
      Real.exp (-(trials : ℝ) / (4 * (height + 1 : ℝ) ^ 2)) := by
  classical
  let miss := forestTrialFailure G charges scale d
  have sub : forestTrialsFailure G charges scale trials d ⊆ constrainedSamples (fun _ : Fin trials => miss) := by
    intro sample member
    have missAll : ¬ heightForestServes (roundedForestTrials G charges scale trials sample) d := by
      simpa [forestTrialsFailure] using member
    simp only [constrainedSamples, mem_filter, mem_univ, true_and, miss, forestTrialFailure]
    intro i succeeds
    have incl : roundedForestLinks G charges scale (sample i) ⊆ roundedForestTrials G charges scale trials sample :=
      fun _ he => mem_biUnion.mpr ⟨i, mem_univ _, he⟩
    exact missAll (heightForestServes_mono incl succeeds)
  refine (finiteProbability_mono sub).trans ?_
  rw [finiteProbability_constrainedSamples, prod_const, card_univ, Fintype.card_fin]
  have base := forestTrialFailure_bound G charges scale d scalePos covered
  calc
    _ ≤ (Real.exp (-(1 / (4 * (height + 1 : ℝ) ^ 2)))) ^ trials :=
      pow_le_pow_left₀ (finiteProbability_nonneg miss) base _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

def earlyTrialCount (V : Type*) [Fintype V] (height : ℕ) : ℕ :=
  16 * (height + 1) ^ 2 * ((Fintype.card V).log2 + 1)

abbrev EarlyRoundSample (G : Arcs V) (height : ℕ) :=
  ForestTrialArray V height (forestScale G height) (earlyTrialCount V height)

def earlyMetricAt (G : Arcs V) (height : ℕ) (D : List (V × V))
    (sample : EarlyRoundSample G height) : Arcs (HeightForestVertex V height) :=
  roundedForestTrials G (forestFractionalRun G height D).1 (forestScale G height) (earlyTrialCount V height) sample

/-- The algorithm retains every earlier metric purchase. An empty
arrival sequence has an empty purchase set. -/
def earlyMetricPurchases (G : Arcs V) (height : ℕ) (D : List (V × V))
    (sample : EarlyRoundSample G height) : Arcs (HeightForestVertex V height) :=
  D.inits.toFinset.biUnion fun P => if P = [] then ∅ else earlyMetricAt G height P sample

private theorem earlyMetricPurchases_mono (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height)
    {D E : List (V × V)} (prefixOf : D <+: E) :
    earlyMetricPurchases G height D sample ⊆ earlyMetricPurchases G height E sample := by
  intro e member
  obtain ⟨P, prefixP, present⟩ := mem_biUnion.mp member
  have hP : P <+: D := (List.mem_inits _ _).mp (List.mem_toFinset.mp prefixP)
  refine mem_biUnion.mpr ⟨P, List.mem_toFinset.mpr ((List.mem_inits _ _).mpr (hP.trans prefixOf)), present⟩

/-- Permanently fall back to the input graph if any current round is
missed by the rounded links. -/
def earlyRoundMiss (G : Arcs V) (height : ℕ) (P : List (V × V))
    (sample : EarlyRoundSample G height) : Prop :=
  match P.getLast? with
  | none => False
  | some d => d.1 ∉ reaches (expandHeightForest G (earlyMetricAt G height P sample)) d.2

instance (G : Arcs V) (height : ℕ) (P : List (V × V))
    (sample : EarlyRoundSample G height) : Decidable (earlyRoundMiss G height P sample) := by
  unfold earlyRoundMiss
  split <;> infer_instance

def earlyRoundFallback (G : Arcs V) (height : ℕ) (D : List (V × V))
    (sample : EarlyRoundSample G height) : Prop :=
  ∃ P ∈ D.inits.toFinset, earlyRoundMiss G height P sample

instance (G : Arcs V) (height : ℕ) (D : List (V × V))
    (sample : EarlyRoundSample G height) : Decidable (earlyRoundFallback G height D sample) := by
  unfold earlyRoundFallback
  infer_instance

private theorem earlyRoundFallback_mono (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height)
    {D E : List (V × V)} (prefixOf : D <+: E) :
    earlyRoundFallback G height D sample → earlyRoundFallback G height E sample := by
  rintro ⟨P, prefixP, fail⟩
  have hP : P <+: D := (List.mem_inits _ _).mp (List.mem_toFinset.mp prefixP)
  exact ⟨P, List.mem_toFinset.mpr ((List.mem_inits _ _).mpr (hP.trans prefixOf)), fail⟩

/-- The early routine runs entirely on demand prefixes and the fixed
random thresholds. -/
def earlyRoundedGraph (G : Arcs V) (height : ℕ) (D : List (V × V))
    (sample : EarlyRoundSample G height) : Arcs V :=
  if earlyRoundFallback G height D sample then G else
    expandHeightForest G (earlyMetricPurchases G height D sample)

theorem earlyRoundedGraph_empty (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height) :
    earlyRoundedGraph G height [] sample = ∅ := by
  simp [earlyRoundedGraph, earlyRoundFallback, earlyRoundMiss, earlyMetricPurchases, expandHeightForest,
    expandLabelledLinks]

theorem earlyRoundedGraph_sub (G : Arcs V) (height : ℕ) (D : List (V × V))
    (sample : EarlyRoundSample G height) : earlyRoundedGraph G height D sample ⊆ G := by
  unfold earlyRoundedGraph
  split
  · exact Subset.rfl
  · exact expandHeightForest_sub _ _

theorem earlyRoundedGraph_mono (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height)
    {D E : List (V × V)} (prefixOf : D <+: E) :
    earlyRoundedGraph G height D sample ⊆ earlyRoundedGraph G height E sample := by
  by_cases fail : earlyRoundFallback G height E sample
  · simpa [earlyRoundedGraph, fail] using earlyRoundedGraph_sub G height D sample
  have before : ¬ earlyRoundFallback G height D sample :=
    fun h => fail (earlyRoundFallback_mono G height sample prefixOf h)
  simpa only [earlyRoundedGraph, fail, before, ↓reduceIte] using
    expandHeightForest_mono G (earlyMetricPurchases_mono G height sample prefixOf)

theorem earlyRoundedGraph_preserves (G : Arcs V) (height : ℕ) (D : List (V × V))
    (sample : EarlyRoundSample G height) : Preserves G (earlyRoundedGraph G height D sample) D := by
  intro d hd
  refine ⟨reach_mono (earlyRoundedGraph_sub G height D sample), ?_⟩
  intro input
  by_cases fail : earlyRoundFallback G height D sample
  · simpa [earlyRoundedGraph, fail] using input
  obtain ⟨before, rest, rfl⟩ := List.mem_iff_append.mp hd
  let P := before ++ [d]
  have pPrefix : P <+: before ++ d :: rest := ⟨rest, by simp [P]⟩
  have pMem : P ∈ (before ++ d :: rest).inits.toFinset :=
    List.mem_toFinset.mpr ((List.mem_inits _ _).mpr pPrefix)
  have pLast : P.getLast? = some d := by simp [P]
  have served : d.1 ∈ reaches (expandHeightForest G (earlyMetricAt G height P sample)) d.2 := by
    by_contra absent
    exact fail ⟨P, pMem, by simpa [earlyRoundMiss, pLast] using absent⟩
  have sub : earlyMetricAt G height P sample ⊆ earlyMetricPurchases G height (before ++ d :: rest) sample := by
    intro e chosen
    apply mem_biUnion.mpr
    exact ⟨P, pMem, by simpa [P] using chosen⟩
  simp only [earlyRoundedGraph, fail, ↓reduceIte]
  exact reach_mono (expandHeightForest_mono G sub) (mem_reaches.mp served)

/-- One fixed sample determines a feasible monotone early online rule. -/
def earlyRoundedRule (G : Arcs V) (height : ℕ) (sample : EarlyRoundSample G height) : EarlySteinerRule G :=
  ⟨fun D => earlyRoundedGraph G height D sample, earlyRoundedGraph_empty G height sample,
    fun D => earlyRoundedGraph_sub G height D sample, earlyRoundedGraph_mono G height sample,
    fun D _ => earlyRoundedGraph_preserves G height D sample⟩

noncomputable def earlyFallbackSamples (G : Arcs V) (height : ℕ) (D : List (V × V)) :
    Finset (EarlyRoundSample G height) := by
  classical
  exact univ.filter (earlyRoundFallback G height D)

private noncomputable def earlyRoundMissSamples (G : Arcs V) (height : ℕ) (P : List (V × V)) :
    Finset (EarlyRoundSample G height) := by
  classical
  exact univ.filter (earlyRoundMiss G height P)

/-- A fallback's probability is bounded by the sum of the amplified
miss probabilities at the fixed input prefixes. -/
theorem earlyFallback_probability (G : Arcs V) {height : ℕ} (heightPos : 0 < height)
    (D : List (V × V)) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    finiteProbability (earlyFallbackSamples G height D) ≤
      (D.length + 1 : ℝ) * Real.exp (-(earlyTrialCount V height : ℝ) / (4 * (height + 1 : ℝ) ^ 2)) := by
  classical
  let ε := Real.exp (-(earlyTrialCount V height : ℝ) / (4 * (height + 1 : ℝ) ^ 2))
  let miss := earlyRoundMissSamples G height
  have failureSet : earlyFallbackSamples G height D = D.inits.toFinset.biUnion miss := by
    ext sample
    simp [earlyFallbackSamples, earlyRoundFallback, miss, earlyRoundMissSamples]
  rw [failureSet]
  refine (finiteProbability_biUnion_le _ _).trans ?_
  have prefixBound (P : List (V × V)) (hp : P ∈ D.inits.toFinset) :
      finiteProbability (miss P) ≤ ε := by
    cases last : P.getLast? with
    | none =>
      have no : miss P = ∅ := by ext sample; simp [miss, earlyRoundMissSamples, earlyRoundMiss, last]
      simp [no, finiteProbability, ε, (Real.exp_pos _).le]
    | some d =>
      have pref := (List.mem_inits _ _).mp (List.mem_toFinset.mp hp)
      have present : d ∈ P := by
        have notEmpty : P ≠ [] := by rintro rfl; simp at last
        rw [List.getLast?_eq_some_getLast notEmpty] at last
        rw [← Option.some.inj last]
        exact List.getLast_mem notEmpty
      have req : ∀ r ∈ P, Reach G r.1 r.2 := fun r hr => feasible r (pref.subset hr)
      have count : 0 < P.toFinset.card := card_pos.mpr ⟨d, List.mem_toFinset.mpr present⟩
      have covering := (forestFractionalRun_bound G G Subset.rfl P req count heightPos).1 d present
      let bad := forestTrialsFailure G (forestFractionalRun G height P).1 (forestScale G height)
        (earlyTrialCount V height) d
      have included : miss P ⊆ bad := by
        intro sample hp
        have absent : d.1 ∉ reaches (expandHeightForest G (earlyMetricAt G height P sample)) d.2 := by
          simpa [miss, earlyRoundMissSamples, earlyRoundMiss, last] using hp
        have failed : ¬ heightForestServes (earlyMetricAt G height P sample) d := by
          intro path
          exact absent (mem_reaches.mpr (expandHeightForest_serves (roundedForestTrials_sub _ _ _ _ _) path))
        simpa [bad, forestTrialsFailure, earlyMetricAt] using failed
      exact (finiteProbability_mono included).trans
        (forestTrialsFailure_bound _ _ _ _ _ (forestScale_pos G height) covering)
  calc
    _ ≤ ∑ _ ∈ D.inits.toFinset, ε := sum_le_sum prefixBound
    _ = (D.inits.toFinset.card : ℝ) * ε := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      exact_mod_cast (List.toFinset_card_le (l := D.inits)).trans_eq (List.length_inits D)) (Real.exp_pos _).le

private theorem earlyTrialCount_failure_le (V : Type*) [Fintype V] [Nonempty V] (height : ℕ) :
    Real.exp (-(earlyTrialCount V height : ℝ) / (4 * (height + 1 : ℝ) ^ 2)) ≤
      1 / (Fintype.card V : ℝ) ^ 4 := by
  let n := Fintype.card V
  have positive : 0 < (n : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hpos : 0 < (height + 1 : ℝ) := by positivity
  have size : (earlyTrialCount V height : ℝ) / (4 * (height + 1 : ℝ) ^ 2) =
      4 * ((n.log2 : ℝ) + 1) := by
    simp only [earlyTrialCount, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add, Nat.cast_one, n]
    field_simp [hpos.ne']
    ring
  calc
    _ = Real.exp (-(4 * ((n.log2 : ℝ) + 1))) := by rw [neg_div, size]
    _ ≤ Real.exp (-(4 * Real.log (n : ℝ))) := by
      rw [Real.exp_le_exp]
      linarith only [log_le_log2_succ (Nat.cast_pos.mp positive)]
    _ = _ := by
      have logPow : Real.log ((n : ℝ) ^ 4) = 4 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num
      rw [← logPow, Real.exp_neg, Real.exp_log (by positivity), inv_eq_one_div]

/-- The expected cost of buying the input graph on a rare fallback is at
most two edges on distinct fixed demand traces. -/
theorem earlyFallback_expectedCost_le [Nonempty V] (G : Arcs V) {height : ℕ} (heightPos : 0 < height)
    (D : List (V × V)) (distinct : D.Nodup) (feasible : ∀ d ∈ D, Reach G d.1 d.2) :
    (G.card : ℝ) * finiteProbability (earlyFallbackSamples G height D) ≤ 2 := by
  let n := Fintype.card V
  have nOne : (1 : ℝ) ≤ n := by exact_mod_cast (Fintype.card_pos (α := V))
  have arcs : (G.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    have := Finset.card_le_univ G
    rw [Fintype.card_prod, ← pow_two] at this
    exact_mod_cast this
  have demands : (D.length : ℝ) ≤ (n : ℝ) ^ 2 := by
    have bound := Finset.card_le_univ D.toFinset
    rw [List.toFinset_card_of_nodup distinct, Fintype.card_prod, ← pow_two] at bound
    exact_mod_cast bound
  have positive : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
  have prob := earlyFallback_probability G heightPos D feasible
  have small := (mul_le_mul_of_nonneg_left (earlyTrialCount_failure_le V height)
    (show 0 ≤ (D.length + 1 : ℝ) by positivity))
  calc
    _ ≤ (G.card : ℝ) * ((D.length + 1 : ℝ) * (1 / (n : ℝ) ^ 4)) :=
      mul_le_mul_of_nonneg_left (prob.trans small) (by positivity)
    _ ≤ (n : ℝ) ^ 2 * (((n : ℝ) ^ 2 + 1) * (1 / (n : ℝ) ^ 4)) := by
      exact mul_le_mul arcs (mul_le_mul_of_nonneg_right (add_le_add demands le_rfl) (by positivity))
        (by positivity) (by positivity)
    _ ≤ 2 := by
      rw [mul_one_div, ← mul_div_assoc]
      refine (div_le_iff₀ positive).mpr ?_
      have squares : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ nOne
      nlinarith only [mul_le_mul_of_nonneg_left squares (show (0 : ℝ) ≤ (n : ℝ) ^ 2 by positivity)]

end OnlineReachabilityPreservers
