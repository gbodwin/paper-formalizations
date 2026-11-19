import DirectedFlowCutGap.BinaryFractionalWalkOracle
import DirectedFlowCutGap.EdgeModel

/-!
# Computing the original rational edge threshold demands

The finite list uses the actual binary shortest-path routine on the original
edge weights. Unreachable pairs satisfy the threshold. Zero-length paths
and all finite distances use the same exact binary comparison with one.
-/

namespace DirectedFlowCutGap.RationalEdgeThresholds

open scoped NNReal NNRat ENNReal
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open BinaryFractionalWalkOracle
open BinaryRational (Fraction)
open FractionalCoverRawCore (rational)

abbrev Weights (n : ℕ) := Vector (Vector Fraction n) n

def cost {n : ℕ} (w : Weights n) : Cost n := fun (s, t) => (w[s.val][t.val], 2)

noncomputable def weights {n : ℕ} (w : Weights n) : Fin n × Fin n → ℝ≥0 := fun e =>
  ((decodeCost (cost w) e).value : ℝ≥0)

def far {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (p : Fin n × Fin n) : Bool :=
  match (shortest (ResidualSearch.Enumeration.fin n) adjacency (cost w) p.1 p.2).1 with
  | none => true
  | some q => (BinaryRational.le BinaryRational.one q.cost).1

private theorem costs_equal {n : ℕ} {G : Digraph (Fin n)} {s t : Fin n} (w : Weights n)
    (p : SimplePath G s t) :
    ((FractionalCoverWalkOracle.pathCost (fun e => rational (decodeCost (cost w) e)) p : ℚ) : ℝ) =
      (p.edgeWeight (weights w) : ℝ) := by
  simp only [FractionalCoverWalkOracle.pathCost, SimplePath.edgeWeight, NNReal.coe_sum, Rat.cast_sum,
    weights, rational]
  rfl

private theorem compare_one (c : Fraction) :
    (BinaryRational.le BinaryRational.one c).1 = true ↔ 1 ≤ rational (BinaryRational.decode c) := by
  rw [BinaryRational.le_decode, RawNonnegativeRational.Code.le_eq_true]
  rw [show BinaryRational.decode BinaryRational.one = RawNonnegativeRational.Code.one from rfl,
    RawNonnegativeRational.Code.value_one]
  change (1 : ℚ≥0) ≤ (BinaryRational.decode c).value ↔ (1 : ℚ) ≤ ((BinaryRational.decode c).value : ℚ)
  norm_cast

theorem far_iff {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (p : Fin n × Fin n) :
    far adjacency w p = true ↔ p ∈ edgeThresholdDemands (graph adjacency) (weights w) := by
  let E := ResidualSearch.Enumeration.fin n
  let G := graph adjacency
  let c := fun e => rational (decodeCost (cost w) e)
  let _ : DecidableRel G.Adj := by
    dsimp only [G]
    infer_instance
  have hc (e : Fin n × Fin n) : 0 ≤ c e := NNRat.coe_nonneg _
  have hr := congrArg Prod.fst (FractionalCoverRawOracle.shortest_refines E G (decodeCost (cost w)) p.1 p.2)
  change ((FractionalCoverRawOracle.shortest E G (decodeCost (cost w)) p.1 p.2).1.map
    FractionalCoverRawOracle.decode) = _ at hr
  rw [← shortest_decode] at hr
  change far adjacency w p = true ↔ 1 ≤ edgeDistance G (weights w) p.1 p.2
  rw [← ENNReal.coe_one, coe_le_edgeDistance_iff]
  unfold far
  cases h : (shortest E adjacency (cost w) p.1 p.2).1 with
  | none =>
    rw [h] at hr
    have hn := (FractionalCoverPathOracle.shortest_none_iff E G c hc p.1 p.2).mp hr.symm
    exact ⟨fun _ q => False.elim (hn ⟨q⟩), fun _ => rfl⟩
  | some r =>
    rw [h] at hr
    simp only [compare_one]
    change 1 ≤ rational (BinaryRational.decode r.cost) ↔ ∀ q : SimplePath G p.1 p.2,
      1 ≤ q.edgeWeight (weights w)
    constructor
    · intro hsmall path
      obtain ⟨q, hq, hle⟩ := FractionalCoverPathOracle.shortest_minimum E G c hc p.1 p.2 path
      rw [hq] at hr
      have he := Option.some.inj hr
      subst q
      have hcmp : (1 : ℚ) ≤ FractionalCoverWalkOracle.pathCost c path := hsmall.trans hle
      have hcmpR : (1 : ℝ) ≤ (FractionalCoverWalkOracle.pathCost c path : ℝ) := by exact_mod_cast hcmp
      rw [costs_equal w path] at hcmpR
      exact_mod_cast hcmpR
    · intro hall
      obtain ⟨path, _, heq⟩ := FractionalCoverPathOracle.shortest_valid E G c p.1 p.2 hr.symm
      change rational (BinaryRational.decode r.cost) = FractionalCoverWalkOracle.pathCost c path at heq
      rw [heq]
      have h : (1 : ℝ) ≤ (path.edgeWeight (weights w) : ℝ) := by exact_mod_cast hall path
      rw [← costs_equal w path] at h
      exact_mod_cast h

def demands {n : ℕ} (adjacency : Adjacency n) (w : Weights n) : List (Fin n × Fin n) :=
  ((List.finRange n).flatMap fun s => (List.finRange n).map (fun t => (s, t))).filter
    (far adjacency w)

theorem demands_iff {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (p : Fin n × Fin n) :
    p ∈ demands adjacency w ↔ p ∈ edgeThresholdDemands (graph adjacency) (weights w) := by
  rw [demands, List.mem_filter, far_iff]
  exact and_iff_right (List.mem_flatMap.mpr ⟨p.1, List.mem_finRange _, List.mem_map.mpr
    ⟨p.2, List.mem_finRange _, rfl⟩⟩)

end DirectedFlowCutGap.RationalEdgeThresholds
