import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import OnlineReachabilityPreservers.DagReduction
import OnlineReachabilityPreservers.SteinerCounting

/-! The hub sampling and online hit-routing steps in Section 5. -/

namespace OnlineReachabilityPreservers

open Finset

section Sampling

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Vertices reachable from the source that can also reach the target. -/
def reachInterval (G : Arcs V) (d : V × V) : Finset V :=
  reaches (reverseArcs G) d.1 ∩ reaches G d.2

theorem mem_reachInterval {G : Arcs V} {d : V × V} {v : V} :
    v ∈ reachInterval G d ↔ Reach G d.1 v ∧ Reach G v d.2 := by
  simp [reachInterval, reach_reverseArcs]

/-- All possible demands whose reachability interval exceeds the thin threshold. -/
def thickPairs (G : Arcs V) (τ : ℕ) : Arcs V :=
  univ.filter fun d => τ < (reachInterval G d).card

def sampledVertices {k : ℕ} (sample : Fin k → V) : Finset V := univ.image sample

omit [Fintype V] in
theorem sampledVertices_card {k : ℕ} (sample : Fin k → V) :
    (sampledVertices sample).card ≤ k := card_image_le.trans_eq (by simp)

def missedSamples (S : Finset V) (k : ℕ) : Finset (Fin k → V) :=
  univ.filter fun sample => ∀ i, sample i ∉ S

theorem mem_missedSamples {k : ℕ} {S : Finset V} {sample : Fin k → V} :
    sample ∈ missedSamples S k ↔ ¬ (sampledVertices sample ∩ S).Nonempty := by
  simp only [missedSamples,mem_filter,mem_univ,true_and]
  constructor
  · intro all H
    obtain ⟨v,hv⟩ := H
    obtain ⟨hv,hs⟩ := mem_inter.mp hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact all i hs
  · intro h i hi
    exact h ⟨sample i,mem_inter.mpr ⟨mem_image_of_mem _ (mem_univ i),hi⟩⟩

/-- Exact failure count for a fixed hit set under independent uniform draws. -/
theorem missedSamples_card (S : Finset V) (k : ℕ) :
    (missedSamples S k).card = (Fintype.card V-S.card)^k := by
  classical
  let e : {sample // sample ∈ missedSamples S k} ≃ (Fin k → {v // v ∉ S}) :=
    { toFun := fun sample i => ⟨sample.1 i, (mem_filter.mp sample.2).2 i⟩
      invFun := fun f => ⟨fun i => (f i).1, mem_filter.mpr ⟨mem_univ _,fun i => (f i).2⟩⟩
      left_inv := fun sample => Subtype.ext rfl
      right_inv := fun f => funext (fun i => Subtype.ext rfl) }
  rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
  have complement : Fintype.card {v // v ∉ S} = Fintype.card V-S.card := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [complement]

/-- Bad samples miss at least one of the thick pairs of the input graph. -/
def thickFailures (G : Arcs V) (τ k : ℕ) : Finset (Fin k → V) :=
  (thickPairs G τ).biUnion fun d => missedSamples (reachInterval G d) k

theorem not_mem_thickFailures {G : Arcs V} {τ k : ℕ} {sample : Fin k → V}
    (good : sample ∉ thickFailures G τ k) :
    ∀ d ∈ thickPairs G τ, (sampledVertices sample ∩ reachInterval G d).Nonempty := by
  intro d hd
  by_contra h
  exact good (mem_biUnion.mpr ⟨d,hd,mem_missedSamples.mpr h⟩)

/-- Union bound over all possible pairs, including those that never arrive. -/
theorem thickFailures_card (G : Arcs V) (τ k : ℕ) :
    (thickFailures G τ k).card ≤ (Fintype.card V)^2 * (Fintype.card V-(τ+1))^k := by
  calc
    _ ≤ ∑ d ∈ thickPairs G τ, (missedSamples (reachInterval G d) k).card := card_biUnion_le
    _ ≤ ∑ _d ∈ thickPairs G τ, (Fintype.card V-(τ+1))^k := by
      apply sum_le_sum
      intro d hd
      rw [missedSamples_card]
      exact Nat.pow_le_pow_left (Nat.sub_le_sub_left (Nat.succ_le_of_lt (mem_filter.mp hd).2) _) _
    _ = (thickPairs G τ).card * (Fintype.card V-(τ+1))^k := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by
      simpa [Fintype.card_prod,pow_two] using card_le_univ (thickPairs G τ))

/-- Failure probability under independent uniform draws from a nonempty vertex type. -/
theorem thickFailures_probability (G : Arcs V) {τ k : ℕ}
    (hn : 0 < Fintype.card V) (hτ : τ < Fintype.card V) :
    ((thickFailures G τ k).card:ℝ) / (Fintype.card V:ℝ)^k ≤
      (Fintype.card V:ℝ)^2 * Real.exp (-(k:ℝ)*((τ:ℝ)+1)/(Fintype.card V:ℝ)) := by
  let n := Fintype.card V
  have n0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have le_n : τ+1 ≤ n := Nat.succ_le_of_lt hτ
  have bound := thickFailures_card G τ k
  have cast_bound : ((thickFailures G τ k).card:ℝ) ≤ (n:ℝ)^2*((n:ℝ)-((τ:ℝ)+1))^k := by
    exact_mod_cast (show (thickFailures G τ k).card ≤ n^2*(n-(τ+1))^k from bound)
  have weak : ((n:ℝ)-((τ:ℝ)+1))/(n:ℝ) ≤ Real.exp (-((τ:ℝ)+1)/(n:ℝ)) := by
    rw [sub_div,div_self n0.ne', neg_div]
    simpa only [sub_eq_add_neg, add_comm] using
      (Real.add_one_le_exp (-(((τ:ℝ)+1)/(n:ℝ))))
  have nonneg : 0 ≤ ((n:ℝ)-((τ:ℝ)+1))/(n:ℝ) :=
    div_nonneg (sub_nonneg.mpr (by exact_mod_cast le_n)) n0.le
  calc
    _ ≤ ((n:ℝ)^2*((n:ℝ)-((τ:ℝ)+1))^k)/(n:ℝ)^k :=
      div_le_div_of_nonneg_right cast_bound (by positivity)
    _ = (n:ℝ)^2 * (((n:ℝ)-((τ:ℝ)+1))/(n:ℝ))^k := by rw [div_pow, mul_div_assoc]
    _ ≤ (n:ℝ)^2 * (Real.exp (-((τ:ℝ)+1)/(n:ℝ)))^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nonneg weak _) (by positivity)
    _ = _ := by rw [← Real.exp_nat_mul]; congr 2; ring

/-- Number of independent uniform draws for an inverse-power failure bound. -/
noncomputable def thickSampleCount (n τ : ℕ) (power : ℝ) : ℕ :=
  ⌈(2+power)*Real.log (n:ℝ)*(n:ℝ)/((τ:ℝ)+1)⌉₊

theorem thickSampleCount_probability (G : Arcs V) {τ : ℕ} {power : ℝ}
    (hn : 0 < Fintype.card V) (hτ : τ < Fintype.card V) :
    ((thickFailures G τ (thickSampleCount (Fintype.card V) τ power)).card:ℝ) /
      (Fintype.card V:ℝ)^(thickSampleCount (Fintype.card V) τ power) ≤
        (Fintype.card V:ℝ)^(-power) := by
  let n : ℝ := Fintype.card V
  let k := thickSampleCount (Fintype.card V) τ power
  let u : ℝ := (τ:ℝ)+1
  have hn0 : 0 < n := Nat.cast_pos.mpr hn
  have hu : 0 < u := by dsimp [u]; positivity
  have comp : (2+power)*Real.log n ≤ (k:ℝ)*u/n := by
    have h : ((2+power)*Real.log n*n)/u ≤ k := Nat.le_ceil _
    have rel := (div_le_iff₀ hu).mp h
    exact (le_div_iff₀ hn0).mpr rel
  have tail : -(k:ℝ)*u/n ≤ -((2+power)*Real.log n) := by simpa only [neg_mul, neg_div] using neg_le_neg comp
  calc
    _ ≤ n^2*Real.exp (-(k:ℝ)*u/n) := thickFailures_probability G hn hτ
    _ ≤ n^2*Real.exp (-((2+power)*Real.log n)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr tail) (sq_nonneg _)
    _ = n^(-power) := by
      rw [← Real.rpow_two n, show -((2+power)*Real.log n) = Real.log n*(-(2+power)) by ring,
        ← Real.rpow_def_of_pos hn0, ← Real.rpow_add hn0,
        show (2:ℝ)+(-(2+power)) = -power by ring]

theorem thickSampleCount_le {n τ : ℕ} {power : ℝ}
    (hn : 0 < n) (hp : 0 ≤ power) :
    (thickSampleCount n τ power:ℝ) ≤ (2+power)*Real.log (n:ℝ)*(n:ℝ)/((τ:ℝ)+1)+1 := by
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.log_nonneg n1
  exact (Nat.ceil_lt_add_one (by positivity :
    0 ≤ (2+power)*Real.log (n:ℝ)*(n:ℝ)/((τ:ℝ)+1))).le

/-- The integer sample budget at the thickness used in Theorem 21. -/
theorem thickSampleCount_balanced {n τ : ℕ} {power : ℝ}
    (hn : 0 < n) (hp : 0 ≤ power) (threshold : (n:ℝ)^(3/5:ℝ) ≤ (τ:ℝ)+1) :
    (thickSampleCount n τ power:ℝ) ≤ ((2+power)*Real.log (n:ℝ)+1)*(n:ℝ)^(2/5:ℝ) := by
  have n0 : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have log0 := Real.log_nonneg n1
  have div_le : (n:ℝ)/((τ:ℝ)+1) ≤ (n:ℝ)^(2/5:ℝ) := by
    calc
      _ ≤ (n:ℝ)/(n:ℝ)^(3/5:ℝ) := div_le_div_of_nonneg_left n0.le
        (Real.rpow_pos_of_pos n0 _) threshold
      _ = (n:ℝ)^(1:ℝ)/(n:ℝ)^(3/5:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub n0, show (1:ℝ)-3/5=2/5 by norm_num]
  calc
    _ ≤ (2+power)*Real.log (n:ℝ)*(n:ℝ)/((τ:ℝ)+1)+1 := thickSampleCount_le hn hp
    _ = ((2+power)*Real.log (n:ℝ))*((n:ℝ)/((τ:ℝ)+1))+1 := by ring
    _ ≤ ((2+power)*Real.log (n:ℝ))*(n:ℝ)^(2/5:ℝ)+(n:ℝ)^(2/5:ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left div_le (by positivity))
        (Real.one_le_rpow n1 (by norm_num))
    _ = _ := by ring

theorem log_le_log2_succ {n : ℕ} (positive : 0 < n) :
    Real.log (n : ℝ) ≤ (n.log2 : ℝ) + 1 := by
  have pow : (n : ℝ) ≤ (2 : ℝ) ^ (n.log2 + 1) := by exact_mod_cast (Nat.lt_log2_self (n := n)).le
  have base : Real.log 2 ≤ 1 := by
    have le := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at le
    exact le
  calc
    _ ≤ Real.log ((2 : ℝ) ^ (n.log2 + 1)) := Real.log_le_log (Nat.cast_pos.mpr positive) pow
    _ = ((n.log2 : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow, Nat.cast_add, Nat.cast_one]
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left base (by positivity)

/-- A computable number of hub draws for failure probability at most
n to the power minus two. -/
def steinerHubDraws (n τ : ℕ) : ℕ :=
  if n = 0 then 0 else (4 * (n.log2 + 1) * n) / (τ + 1) + 1

private theorem steinerHubDraws_adequate {n τ : ℕ} (hn : 0 < n) :
    4 * Real.log (n : ℝ) * (n : ℝ) / ((τ : ℝ) + 1) ≤ steinerHubDraws n τ := by
  let a := 4 * (n.log2 + 1) * n
  let b := τ + 1
  have step : a < (a / b + 1) * b :=
    (Nat.div_lt_iff_lt_mul (by dsimp [b]; positivity)).mp (Nat.lt_succ_self _)
  have comparison : 4 * Real.log (n : ℝ) * (n : ℝ) ≤ (a : ℝ) := by
    push_cast [a]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (log_le_log2_succ hn) (by positivity))
      (by positivity)
  apply (div_le_iff₀ (by positivity)).mpr
  simp only [steinerHubDraws, hn.ne', ↓reduceIte]
  exact comparison.trans (by exact_mod_cast step.le)

theorem steinerHubDraws_probability (G : Arcs V)
    (τ : ℕ) (hn : 0 < Fintype.card V) :
    ((thickFailures G τ (steinerHubDraws (Fintype.card V) τ)).card : ℝ) /
      (Fintype.card V : ℝ) ^ (steinerHubDraws (Fintype.card V) τ) ≤
        (Fintype.card V : ℝ) ^ (-(2 : ℝ)) := by
  by_cases thin : τ < Fintype.card V
  · let n : ℝ := Fintype.card V
    let k := steinerHubDraws (Fintype.card V) τ
    let u : ℝ := (τ : ℝ) + 1
    have n0 : 0 < n := Nat.cast_pos.mpr hn
    have u0 : 0 < u := by dsimp [u]; positivity
    have comp : 4 * Real.log n ≤ (k : ℝ) * u / n :=
      (le_div_iff₀ n0).mpr ((div_le_iff₀ u0).mp (steinerHubDraws_adequate hn))
    calc
      _ ≤ n^2 * Real.exp (-(k : ℝ) * u / n) := thickFailures_probability G hn thin
      _ ≤ n^2 * Real.exp (-(4 * Real.log n)) := by
        have le := neg_le_neg comp
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (by simpa only [neg_mul, neg_div] using le)) (sq_nonneg _)
      _ = _ := by
        change n ^ 2 * Real.exp (-(4 * Real.log n)) = n ^ (-(2 : ℝ))
        rw [← Real.rpow_two n, show -(4 * Real.log n) = Real.log n * (-4) by ring,
          ← Real.rpow_def_of_pos n0, ← Real.rpow_add n0]
        norm_num
  · have empty : thickPairs G τ = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro d present
      exact (Nat.not_lt_of_ge ((card_le_univ _).trans (Nat.le_of_not_lt thin))) (mem_filter.mp present).2
    simp only [thickFailures, empty, biUnion_empty, card_empty, Nat.cast_zero, zero_div]
    positivity

theorem steinerHubDraws_balanced {n τ : ℕ} (hn : 0 < n)
    (threshold : (n : ℝ) ^ (3/5 : ℝ) ≤ (τ : ℝ) + 1) :
    (steinerHubDraws n τ : ℝ) ≤ (4 * ((n.log2 : ℝ) + 1) + 1) * (n : ℝ) ^ (2/5 : ℝ) := by
  let a := 4 * (n.log2 + 1) * n
  let b := τ + 1
  have n0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have n1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have b0 : (0 : ℝ) < b := by dsimp [b]; positivity
  have num : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := by
    apply (le_div_iff₀ b0).mpr
    exact_mod_cast Nat.div_mul_le_self a b
  have div : (n : ℝ) / ((τ : ℝ) + 1) ≤ (n : ℝ) ^ (2/5 : ℝ) := by
    calc
      _ ≤ (n : ℝ) / (n : ℝ) ^ (3/5 : ℝ) :=
        div_le_div_of_nonneg_left n0.le (Real.rpow_pos_of_pos n0 _) threshold
      _ = (n : ℝ) ^ (1 : ℝ) / (n : ℝ) ^ (3/5 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub n0]; norm_num
  have pow : 1 ≤ (n : ℝ) ^ (2/5 : ℝ) := Real.one_le_rpow n1 (by norm_num)
  simp only [steinerHubDraws, hn.ne', ↓reduceIte]
  change ((a / b + 1 : ℕ) : ℝ) ≤ _
  rw [Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ (a : ℝ) / b + 1 := add_le_add num le_rfl
    _ = (4 * ((n.log2 : ℝ) + 1)) * ((n : ℝ) / ((τ : ℝ) + 1)) + 1 := by push_cast [a,b]; ring
    _ ≤ (4 * ((n.log2 : ℝ) + 1)) * (n : ℝ) ^ (2/5 : ℝ) + (n : ℝ) ^ (2/5 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left div (by positivity)) pow
    _ = _ := by ring

end Sampling

section Routing

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- Select the first sampled vertex that can connect the two terminals. -/
def hitHub (G : Arcs V) (S : Finset V) (d : V × V) : Option V :=
  least? (S ∩ reachInterval G d)

theorem hitHub_some {G : Arcs V} {S : Finset V} {d : V × V} {hub : V}
    (h : hitHub G S d = some hub) : hub ∈ S ∧ Reach G d.1 hub ∧ Reach G hub d.2 := by
  obtain ⟨hS,hR⟩ := mem_inter.mp (least?_mem h)
  exact ⟨hS,mem_reachInterval.mp hR⟩

theorem hitHub_from_thick {G : Arcs V} {τ k : ℕ} {sample : Fin k → V}
    (good : sample ∉ thickFailures G τ k) {d : V × V} (hd : d ∈ thickPairs G τ) :
    ∃ hub, hitHub G (sampledVertices sample) d = some hub :=
  least?_some (not_mem_thickFailures good d hd)

/-- Split each hit into a source-to-hub demand and a hub-to-target demand. -/
def hitRequests (G : Arcs V) (S : Finset V) (D : List (V × V)) :
    List ((V × V) × (V × V)) :=
  D.filterMap fun d => (hitHub G S d).map fun h => ((d.1,h),(h,d.2))

def hubPreserver (G : Arcs V) (S : Finset V) (D : List (V × V)) : Arcs V :=
  sinkPreserver G ((hitRequests G S D).map Prod.fst) ∪
    sourcePreserver G ((hitRequests G S D).map Prod.snd)

theorem hubPreserver_prefix (G : Arcs V) (S : Finset V) {D E : List (V × V)} (h : D <+: E) :
    hubPreserver G S D ⊆ hubPreserver G S E := by
  obtain ⟨E,rfl⟩ := h
  have hreq : hitRequests G S D <+: hitRequests G S (D++E) := by
    simp [hitRequests,List.filterMap_append]
  exact union_subset_union (sinkPreserver_prefix G (hreq.map _)) (sourcePreserver_prefix G (hreq.map _))

/-- Both legs of every hit are reachable in the current hub preserver. -/
theorem hubPreserver_serves (G : Arcs V) (S : Finset V) (D : List (V × V))
    {d : V × V} (hd : d ∈ D) {hub : V} (h : hitHub G S d = some hub) :
    Reach (hubPreserver G S D) d.1 hub ∧ Reach (hubPreserver G S D) hub d.2 := by
  obtain ⟨_, r₁,r₂⟩ := hitHub_some h
  let P := hitRequests G S D
  have hm : ((d.1,hub),(hub,d.2)) ∈ P := by
    apply List.mem_filterMap.mpr
    exact ⟨d,hd,by simp [h]⟩
  have h₁ := (sinkPreserver_spec G (P.map Prod.fst)).2.1 _ (List.mem_map_of_mem hm)
  have h₂ := (theorem2_sources G (P.map Prod.snd) univ (fun _ _ => mem_univ _)).2.1
    _ (List.mem_map_of_mem hm)
  exact ⟨reach_mono subset_union_left (h₁.mpr r₁),reach_mono subset_union_right (h₂.mpr r₂)⟩

/-- The hub preserver's edge cost depends on the number of hits. -/
theorem hubPreserver_bound (G : Arcs V) (S : Finset V) (D : List (V × V)) :
    hubPreserver G S D ⊆ G ∧
      ((hubPreserver G S D).card:ℝ) ≤
        6*(Fintype.card V:ℝ)+2*Real.sqrt (2*(Fintype.card V:ℝ)*(hitRequests G S D).length*S.card) := by
  let P := hitRequests G S D
  have hit (d : (V × V) × (V × V)) (hd : d ∈ P) : d.1.2 ∈ S ∧ d.2.1 ∈ S := by
    obtain ⟨a,_,ha⟩ := List.mem_filterMap.mp hd
    cases eq : hitHub G S a with
    | none => simp [eq] at ha
    | some hub =>
      simp only [eq,Option.map_some,Option.some.injEq] at ha
      subst d
      exact ⟨(hitHub_some eq).1,(hitHub_some eq).1⟩
  have one := theorem2_sinks G (P.map Prod.fst) S (by
    intro d hd
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hd
    exact (hit a ha).1)
  have two := theorem2_sources G (P.map Prod.snd) S (by
    intro d hd
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hd
    exact (hit a ha).2)
  refine ⟨union_subset one.1 two.1,?_⟩
  have cnt := card_union_le (sinkPreserver G (P.map Prod.fst)) (sourcePreserver G (P.map Prod.snd))
  have cnt' : ((hubPreserver G S D).card:ℝ) ≤
      ((sinkPreserver G (P.map Prod.fst)).card:ℝ)+((sourcePreserver G (P.map Prod.snd)).card:ℝ) := by
    exact_mod_cast cnt
  have c₁ := one.2.2
  have c₂ := two.2.2
  rw [List.length_map] at c₁ c₂
  linarith only [cnt',c₁,c₂]

end Routing

/-- The contribution of the hub phase obtained from both terminal-counting
inequalities. The geometric mean of the two printed regimes is realized by
using the hit count first and the total count second. -/
theorem hub_competitive_contribution {n σ hits opt T : ℝ}
    (hn : 0 ≤ n) (hσ : 0 ≤ σ) (hopt : 0 ≤ opt) (hT : 0 < T)
    (total : T ≤ opt^2) (charged : hits ≤ 2*σ*opt) :
    6*n+2*Real.sqrt (2*n*hits*σ) ≤
      (6*n/(Real.sqrt T)+4*Real.sqrt n*σ/(Real.sqrt (Real.sqrt T)))*opt := by
  have T0 := Real.sqrt_pos.2 hT
  have T1 := Real.sqrt_pos.2 T0
  have root : Real.sqrt T ≤ opt := by
    apply (sq_le_sq₀ T0.le hopt).mp
    rwa [Real.sq_sqrt hT.le]
  have second := Real.sqrt_le_sqrt root
  have hl : n ≤ (n/Real.sqrt T)*opt := by
    calc
      n = (n/Real.sqrt T)*Real.sqrt T := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left root (div_nonneg hn T0.le)
  have hs : Real.sqrt opt ≤ opt/Real.sqrt (Real.sqrt T) := by
    apply (le_div_iff₀ T1).mpr
    calc
      _ ≤ Real.sqrt opt*Real.sqrt opt :=
        mul_le_mul_of_nonneg_left second (Real.sqrt_nonneg _)
      _ = opt := Real.mul_self_sqrt hopt
  have hh : Real.sqrt (2*n*hits*σ) ≤ 2*Real.sqrt n*σ*Real.sqrt opt := by
    have h : 2*n*hits*σ ≤ 4*n*σ^2*opt := by
      calc
        _ ≤ 2*n*(2*σ*opt)*σ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left charged (by positivity)) hσ
        _ = _ := by ring
    apply (Real.sqrt_le_sqrt h).trans
    rw [show 4*n*σ^2*opt = 4*(n*(σ^2*opt)) by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), Real.sqrt_mul hn,
      Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ]
    norm_num
    ring_nf
    exact le_rfl
  have hm := mul_le_mul_of_nonneg_left hs (show 4*Real.sqrt n*σ ≥ 0 by positivity)
  have h₂ : 2*Real.sqrt (2*n*hits*σ) ≤ (4*Real.sqrt n*σ/Real.sqrt (Real.sqrt T))*opt := by
    calc
      _ ≤ (4*Real.sqrt n*σ)*Real.sqrt opt := by linarith only [hh]
      _ ≤ (4*Real.sqrt n*σ)*(opt/Real.sqrt (Real.sqrt T)) := hm
      _ = _ := by ring
  calc
    _ ≤ 6*((n/Real.sqrt T)*opt)+(4*Real.sqrt n*σ/Real.sqrt (Real.sqrt T))*opt := by
      linarith only [hl,h₂]
    _ = _ := by ring


/-- At the thresholds of Theorem 21, the hub contribution is at most a
logarithmic factor times n to the power 3/5. -/
theorem hub_balanced_contribution {n σ T C : ℝ} (hn : 1 ≤ n) (hσ : 0 ≤ σ)
    (ht : n^(6/5:ℝ) ≤ T) (sample : σ ≤ C*n^(2/5:ℝ)) :
    6*n/(Real.sqrt T)+4*Real.sqrt n*σ/(Real.sqrt (Real.sqrt T)) ≤ (6+4*C)*n^(3/5:ℝ) := by
  have n0 := zero_lt_one.trans_le hn
  have rs : n^(3/5:ℝ) ≤ Real.sqrt T := by
    have h := Real.sqrt_le_sqrt ht
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul n0.le,
      show (6/5:ℝ)*(1/2)=3/5 by norm_num] at h
    exact h
  have rss : n^(3/10:ℝ) ≤ Real.sqrt (Real.sqrt T) := by
    have h := Real.sqrt_le_sqrt rs
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul n0.le,
      show (3/5:ℝ)*(1/2)=3/10 by norm_num] at h
    exact h
  have lin : 6*n/(Real.sqrt T) ≤ 6*n^(3/5:ℝ) := by
    calc
      _ ≤ (6*n)/n^(3/5:ℝ) := div_le_div_of_nonneg_left (by positivity)
        (Real.rpow_pos_of_pos n0 _) rs
      _ = 6*n^(2/5:ℝ) := by
        rw [mul_div_assoc]
        have eq : n/n^(3/5:ℝ) = n^(2/5:ℝ) := by
          calc
            _ = n^(1:ℝ)/n^(3/5:ℝ) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_sub n0, show (1:ℝ)-3/5=2/5 by norm_num]
        rw [eq]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn (by norm_num)) (by norm_num)
  have main : 4*Real.sqrt n*σ/(Real.sqrt (Real.sqrt T)) ≤ 4*C*n^(3/5:ℝ) := by
    calc
      _ ≤ (4*Real.sqrt n*σ)/n^(3/10:ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos n0 _) rss
      _ ≤ (4*Real.sqrt n*(C*n^(2/5:ℝ)))/n^(3/10:ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left sample (by positivity)) (by positivity)
      _ = _ := by
        rw [Real.sqrt_eq_rpow, show (4*n^(1/2:ℝ)*(C*n^(2/5:ℝ))) =
          4*C*(n^(1/2:ℝ)*n^(2/5:ℝ)) by ring, mul_div_assoc,
          ← Real.rpow_add n0, ← Real.rpow_sub n0,
          show (1/2:ℝ)+2/5-3/10=3/5 by norm_num]
  calc
    _ ≤ 6*n^(3/5:ℝ)+4*C*n^(3/5:ℝ) := add_le_add lin main
    _ = _ := by ring

private theorem hitRequests_length_of_hits {V : Type*} [LinearOrder V] [Fintype V]
    (G : Arcs V) (S : Finset V) (D : List (V × V))
    (hit : ∀ d ∈ D, ∃ v, hitHub G S d = some v) :
    (hitRequests G S D).length = D.length := by
  induction D with
  | nil => rfl
  | cons d D ih =>
    obtain ⟨v,hv⟩ := hit d List.mem_cons_self
    have hD := ih (fun e he => hit e (List.mem_cons_of_mem _ he))
    have step : hitRequests G S (d :: D) = ((d.1,v),(v,d.2)) :: hitRequests G S D := by
      simp [hitRequests,hv]
    rw [step, List.length_cons, hD, List.length_cons]

/-- Charge the hit phase along its actual prefixes, with any larger monotone
preserver allowed to include the early and thin phases. -/
theorem hubPreserver_charge {V : Type*} [LinearOrder V] [Fintype V]
    (G : Arcs V) (S : Finset V) (D : List (V × V)) (H : ℕ → Arcs V) (mono : Monotone H)
    (hit : ∀ d ∈ D, ∃ v, hitHub G S d = some v)
    (nontrivial : ∀ i : Fin D.length, ¬ Reach (H i) (D.get i).1 (D.get i).2)
    (contains : ∀ i, hubPreserver G S (D.take i) ⊆ H i)
    (Z : Arcs V) (solution : ∀ i : Fin D.length, Reach Z (D.get i).1 (D.get i).2) :
    D.length ≤ 2*S.card*Z.card := by
  choose hub chosen using (fun i : Fin D.length => hit (D.get i) (D.get_mem i))
  apply lemma22_hub_count D S Z H mono hub (fun i => (hitHub_some (chosen i)).1)
    nontrivial _ solution
  intro i
  have hmem : D.get i ∈ D.take (i.1+1) := by
    apply List.mem_take_iff_getElem.mpr
    refine ⟨i.1, ?_, rfl⟩
    exact lt_min (Nat.lt_succ_self _) i.isLt
  obtain ⟨h₁,h₂⟩ := hubPreserver_serves G S _ hmem (chosen i)
  exact ⟨reach_mono (contains _) h₁,reach_mono (contains _) h₂⟩

/-- The checked hit-phase contribution at the parameters of Theorem 21.
The remaining phases are outside this estimate. -/
theorem hubPreserver_balanced_bound_of_size {V : Type*} [LinearOrder V] [Fintype V]
    (G : Arcs V) (S : Finset V) (D : List (V × V)) (H : ℕ → Arcs V) (mono : Monotone H)
    {T : ℕ} {C : ℝ} (hn : 0 < Fintype.card V)
    (hT : (Fintype.card V:ℝ)^(6/5:ℝ) ≤ T)
    (size : (S.card:ℝ) ≤ C * (Fintype.card V:ℝ)^(2/5:ℝ))
    (hit : ∀ d ∈ D, ∃ v, hitHub G S d = some v)
    (nontrivial : ∀ i : Fin D.length, ¬ Reach (H i) (D.get i).1 (D.get i).2)
    (contains : ∀ i, hubPreserver G S (D.take i) ⊆ H i)
    (Z : Arcs V) (solution : ∀ i : Fin D.length, Reach Z (D.get i).1 (D.get i).2)
    (total : T ≤ Z.card^2) :
    ((hubPreserver G S D).card:ℝ) ≤
      (6+4*C)*(Fintype.card V:ℝ)^(3/5:ℝ)*Z.card := by
  let n := Fintype.card V
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ Fintype.card V from hn)
  have charge := hubPreserver_charge G S D H mono hit nontrivial contains Z solution
  have T0 : (0:ℝ) < T := (Real.rpow_pos_of_pos (zero_lt_one.trans_le n1) _).trans_le hT
  have bound := (hubPreserver_bound G S D).2
  rw [hitRequests_length_of_hits G S D hit] at bound
  have contribution := hub_competitive_contribution (n := (n:ℝ)) (σ := (S.card:ℝ))
    (hits := (D.length:ℝ)) (opt := (Z.card:ℝ)) (T := (T:ℝ)) (by positivity) (by positivity)
    (by positivity) T0 (by exact_mod_cast total) (by exact_mod_cast charge)
  have balance := hub_balanced_contribution n1 (show 0 ≤ (S.card:ℝ) by positivity) hT size
  exact bound.trans (contribution.trans (mul_le_mul_of_nonneg_right balance (by positivity)))

theorem hubPreserver_balanced_bound {V : Type*} [LinearOrder V] [Fintype V]
    (G : Arcs V) (D : List (V × V)) (H : ℕ → Arcs V) (mono : Monotone H)
    {τ T : ℕ} {power : ℝ} (hp : 0 ≤ power) (hn : 0 < Fintype.card V)
    (hτ : (Fintype.card V:ℝ)^(3/5:ℝ) ≤ (τ:ℝ)+1)
    (hT : (Fintype.card V:ℝ)^(6/5:ℝ) ≤ T)
    (sample : Fin (thickSampleCount (Fintype.card V) τ power) → V)
    (hit : ∀ d ∈ D, ∃ v, hitHub G (sampledVertices sample) d = some v)
    (nontrivial : ∀ i : Fin D.length, ¬ Reach (H i) (D.get i).1 (D.get i).2)
    (contains : ∀ i, hubPreserver G (sampledVertices sample) (D.take i) ⊆ H i)
    (Z : Arcs V) (solution : ∀ i : Fin D.length, Reach Z (D.get i).1 (D.get i).2)
    (total : T ≤ Z.card^2) :
    ((hubPreserver G (sampledVertices sample) D).card:ℝ) ≤
      (6+4*((2+power)*Real.log (Fintype.card V:ℝ)+1))*(Fintype.card V:ℝ)^(3/5:ℝ)*Z.card :=
  hubPreserver_balanced_bound_of_size G (sampledVertices sample) D H mono hn hT
    ((Nat.cast_le.mpr (sampledVertices_card sample)).trans (thickSampleCount_balanced hn hp hτ))
    hit nontrivial contains Z solution total

end OnlineReachabilityPreservers
