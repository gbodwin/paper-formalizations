import OnlineReachabilityPreservers.SteinerHeightForest
import OnlineReachabilityPreservers.SteinerWeightedNetwork

/-! Apply the weighted capacity procedure to the joined metric forest. -/

namespace OnlineReachabilityPreservers

open Finset

abbrev ForestNetworkVertex (V : Type*) (height : ℕ) := Fin 3 ×ₗ HeightForestVertex V height

variable {V : Type*} {height : ℕ}

def forestNetworkCopy : HeightForestVertex V height ↪ ForestNetworkVertex V height :=
  ⟨fun v => toLex (0, v), fun _ _ eq => congrArg (fun a => (ofLex a).2) eq⟩

def forestNetworkSource (s : V) : ForestNetworkVertex V height :=
  toLex (1, heightCopy s false heightRoot)

def forestNetworkSink (t : V) : ForestNetworkVertex V height :=
  toLex (2, heightCopy t true heightRoot)

theorem forestNetworkSource_ne_sink (s t : V) :
    (forestNetworkSource s : ForestNetworkVertex V height) ≠ forestNetworkSink t := by
  intro equal
  have labels := congrArg (fun a => (ofLex a).1.val) equal
  change 1 = 2 at labels
  contradiction

variable [LinearOrder V] [Fintype V]

local instance : DecidableEq (ForestNetworkVertex V height) :=
  (inferInstance : LinearOrder (ForestNetworkVertex V height)).toDecidableEq

def forestNetworkWeight (G : Arcs V) (e : ForestNetworkVertex V height × ForestNetworkVertex V height) : ℕ :=
  heightForestWeight G ((ofLex e.1).2, (ofLex e.2).2)

def forestNetworkPriced (G : Arcs V) (links : Arcs (HeightForestVertex V height)) :
    Arcs (ForestNetworkVertex V height) :=
  (links.filter (fun e => 0 < heightForestWeight G e)).map (forestNetworkCopy.prodMap forestNetworkCopy)

def forestNetworkZero (G : Arcs V) (height : ℕ) : Arcs (ForestNetworkVertex V height) :=
  ((heightForest G height).filter (fun e => heightForestWeight G e = 0)).map
    (forestNetworkCopy.prodMap forestNetworkCopy)

def forestNetworkEntries (s : V) : Arcs (ForestNetworkVertex V height) :=
  ((univ : Finset (HeightForestVertex V height)).filter (sourceLeaf s)).image fun a =>
    (forestNetworkSource s, forestNetworkCopy a)

def forestNetworkExits (t : V) : Arcs (ForestNetworkVertex V height) :=
  ((univ : Finset (HeightForestVertex V height)).filter (sinkLeaf t)).image fun a =>
    (forestNetworkCopy a, forestNetworkSink t)

/-- The two current leaf groups and the always-free zero-cost metric links. -/
def forestNetworkDemand (G : Arcs V) (height : ℕ) (d : V × V) : WeightedNetworkDemand (ForestNetworkVertex V height) :=
  ⟨forestNetworkZero G height ∪ forestNetworkEntries d.1 ∪ forestNetworkExits d.2,
    forestNetworkSource d.1, forestNetworkSink d.2⟩

theorem forestNetworkPriced_mono (G : Arcs V) :
    Monotone (forestNetworkPriced (height := height) G) := by
  intro A B sub
  apply map_subset_map.mpr
  exact filter_subset_filter _ sub

theorem forestNetworkPriced_positive (G : Arcs V) (links : Arcs (HeightForestVertex V height)) :
    ∀ e ∈ forestNetworkPriced G links, 0 < forestNetworkWeight G e := by
  intro e he
  obtain ⟨arc, present, rfl⟩ := mem_map.mp he
  exact (mem_filter.mp present).2

/-- All paid links have polynomially bounded weights in the fixed template. -/
theorem forestNetworkScale_le (G : Arcs V) (height : ℕ) :
    weightedCoverScale (forestNetworkPriced G (heightForest G height)) (forestNetworkWeight G) ≤
      max 1 (Fintype.card V * Fintype.card (HeightForestVertex V height) ^ 2) := by
  let edges := forestNetworkPriced G (heightForest G height)
  have cardBound : edges.card ≤ Fintype.card (HeightForestVertex V height) ^ 2 := by
    dsimp only [edges]
    rw [forestNetworkPriced, card_map]
    simpa only [Fintype.card_prod, pow_two] using
      (Finset.card_le_univ (((heightForest G height).filter (fun e => 0 < heightForestWeight G e))))
  have weightBound : ∀ e ∈ edges, forestNetworkWeight G e ≤ Fintype.card V := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := mem_map.mp he
    exact (hops_spec (heightForest_edge_spec (mem_filter.mp ha).1).2).1
  unfold weightedCoverScale
  refine max_le_max le_rfl ?_
  calc
    _ ≤ ∑ _ ∈ edges, Fintype.card V := sum_le_sum weightBound
    _ = Fintype.card V * edges.card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ cardBound

theorem forestNetworkPriced_cost_le (G : Arcs V) (links : Arcs (HeightForestVertex V height)) :
    (∑ e ∈ forestNetworkPriced G links, (forestNetworkWeight G e : ℝ)) ≤
      ∑ e ∈ links, (heightForestWeight G e : ℝ) := by
  rw [forestNetworkPriced, Finset.sum_map]
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  intro e _ _
  exact Nat.cast_nonneg _

theorem forestNetworkDemand_feasible {G : Arcs V} {links : Arcs (HeightForestVertex V height)} {d : V × V}
    (sub : links ⊆ heightForest G height) (serves : heightForestServes links d) :
    let q := forestNetworkDemand G height d
    Reach (forestNetworkPriced G links ∪ q.free) q.source q.sink := by
  let q := forestNetworkDemand G height d
  let A := forestNetworkPriced G links ∪ q.free
  obtain ⟨s, t, start, finish, path⟩ := serves
  have lift {u v : HeightForestVertex V height} (r : Reach links u v) :
      Reach A (forestNetworkCopy u) (forestNetworkCopy v) := by
    induction r with
    | refl => exact .refl
    | @tail u v prior edge ih =>
      apply ih.tail
      by_cases pay : 0 < heightForestWeight G (u, v)
      · exact mem_union_left _ (mem_map_of_mem _ (mem_filter.mpr ⟨edge, pay⟩))
      · have hz : heightForestWeight G (u, v) = 0 := by omega
        have free : (forestNetworkCopy u, forestNetworkCopy v) ∈ forestNetworkZero G height :=
          mem_map_of_mem _ (mem_filter.mpr ⟨sub edge, hz⟩)
        exact mem_union_right _ (mem_union_left _ (mem_union_left _ free))
  have entry : (q.source, forestNetworkCopy s) ∈ forestNetworkEntries d.1 :=
    mem_image.mpr ⟨s, mem_filter.mpr ⟨mem_univ _, start⟩, rfl⟩
  have departing : (forestNetworkCopy t, q.sink) ∈ forestNetworkExits d.2 :=
    mem_image.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, finish⟩, rfl⟩
  have enter : Edge A q.source (forestNetworkCopy s) :=
    mem_union_right _ (mem_union_left _ (mem_union_right _ entry))
  have exit : Edge A (forestNetworkCopy t) q.sink :=
    mem_union_right _ (mem_union_right _ departing)
  exact ((lift path).head enter).tail exit

def forestFractionalRun (G : Arcs V) (height : ℕ) (demands : List (V × V)) :
    (ForestNetworkVertex V height × ForestNetworkVertex V height → ℕ) ×
      List (Arcs (ForestNetworkVertex V height)) :=
  weightedNetworkRun (forestNetworkPriced G (heightForest G height)) (forestNetworkWeight G)
    (demands.map (forestNetworkDemand G height)) (fun _ => 0)

private theorem rationalCapacityCost_to_real {A : Type*} (edges chosen : Arcs A)
    (weight units : A × A → ℕ) (scale : ℕ)
    (estimate :
      (∑ e ∈ edges, (weight e : ℚ) * ((units e : ℚ) / scale)) ≤
        2 + ((scale.log2 + 1 : ℕ) : ℚ) * (∑ e ∈ chosen, (weight e : ℚ))) :
    (∑ e ∈ edges, (weight e : ℝ) * ((units e : ℝ) / scale)) ≤
      2 + ((scale.log2 + 1 : ℕ) : ℝ) * (∑ e ∈ chosen, (weight e : ℝ)) := by
  have cast : (((∑ e ∈ edges, (weight e : ℚ) * ((units e : ℚ) / scale)) : ℚ) : ℝ) ≤
      (((2 + ((scale.log2 + 1 : ℕ) : ℚ) * (∑ e ∈ chosen, (weight e : ℚ))) : ℚ) : ℝ) :=
    Rat.cast_le.mpr estimate
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_add, Rat.cast_ofNat] using cast

/-- The online fractional run on the fixed auxiliary forest. The comparator
is any feasible original solution. -/
theorem forestFractionalRun_bound (G Z : Arcs V) (sub : Z ⊆ G) (demands : List (V × V))
    (valid : ∀ d ∈ demands, Reach Z d.1 d.2) (pPos : 0 < demands.toFinset.card)
    {height : ℕ} (heightPos : 0 < height) :
    let edges := forestNetworkPriced G (heightForest G height)
    let weight := forestNetworkWeight (height := height) G
    let scale := weightedCoverScale edges weight
    let out := forestFractionalRun G height demands
    (∀ d ∈ demands, weightedNetworkCovered edges (forestNetworkDemand G height d) weight out.1 scale) ∧
      (∑ e ∈ edges, (weight e : ℝ) * ((roundedWeightedCapacity (weight e) (out.1 e) : ℝ) / scale)) ≤
        2 + ((scale.log2 + 1 : ℕ) : ℝ) *
          (12 * (height : ℝ) * (demands.toFinset.card : ℝ) ^ (1 / (height : ℝ)) *
            ((Nat.sqrt demands.toFinset.card : ℝ) + 1) * (Z.card : ℝ)) := by
  let P := demands.toFinset
  let edges := forestNetworkPriced G (heightForest G height)
  let weight := forestNetworkWeight (height := height) G
  let scale := weightedCoverScale edges weight
  let out := forestFractionalRun G height demands
  have comparator := heightForest_comparison G Z sub P pPos
    (fun d hd => valid d (List.mem_toFinset.mp hd)) heightPos
  obtain ⟨links, allowed, served, cost⟩ := comparator
  let chosen := forestNetworkPriced G links
  have subChosen : chosen ⊆ edges := forestNetworkPriced_mono G allowed
  have reach : ∀ q ∈ demands.map (forestNetworkDemand G height), Reach (chosen ∪ q.free) q.source q.sink := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
    exact forestNetworkDemand_feasible allowed (served d (List.mem_toFinset.mpr hd))
  have certificate := weightedNetworkRun_bound (V := ForestNetworkVertex V height) edges chosen weight
    (demands.map (forestNetworkDemand G height))
    (forestNetworkPriced_positive G (heightForest G height)) subChosen reach
  have fractional := certificate.2.2
  refine ⟨fun d hd => certificate.1 _ (List.mem_map_of_mem hd), ?_⟩
  have realBound :
      (∑ e ∈ edges, (weight e : ℝ) * ((roundedWeightedCapacity (weight e) (out.1 e) : ℝ) / scale)) ≤
        2 + ((scale.log2 + 1 : ℕ) : ℝ) * (∑ e ∈ chosen, (weight e : ℝ)) := by
    exact rationalCapacityCost_to_real edges chosen weight
      (fun e => roundedWeightedCapacity (weight e) (out.1 e)) scale fractional
  have comp := (forestNetworkPriced_cost_le G links).trans cost
  refine realBound.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_left comp (by positivity)

end OnlineReachabilityPreservers
