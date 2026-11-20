import DirectedFlowCutGap.RationalEdgeThresholds
import DirectedFlowCutGap.SparsestEdgeBridge

/-! Recover the exact finite rational distance from the binary shortest-path
witness. An absent path stays distinct from a finite distance of zero. -/
namespace DirectedFlowCutGap.RationalSparsestEdgeDistances

open scoped NNRat NNReal ENNReal
open IntegralNetworkFlow IntegralNetworkFlow.Tabulated
open BinaryFractionalWalkOracle RationalEdgeThresholds
open FractionalCoverRawCore (rational)

def distance {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (p : Fin n × Fin n) : Option ℚ≥0 :=
  (shortest (ResidualSearch.Enumeration.fin n) adjacency (cost w) p.1 p.2).1.map
    (fun q => (BinaryRational.decode q.cost).value)

private theorem path_cost {n : ℕ} {G : Digraph (Fin n)} {s t : Fin n} (w : Weights n)
    (p : SimplePath G s t) :
    ((FractionalCoverWalkOracle.pathCost (fun e => rational (decodeCost (cost w) e)) p : ℚ) : ℝ) =
      (p.edgeWeight (weights w) : ℝ) := by
  simp only [FractionalCoverWalkOracle.pathCost, SimplePath.edgeWeight, NNReal.coe_sum, Rat.cast_sum,
    weights, rational]
  rfl

noncomputable def observe : Option ℚ≥0 → ℝ≥0∞
  | none => ⊤
  | some d => (d : ℝ≥0)

theorem distance_exact {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (p : Fin n × Fin n) :
    observe (distance adjacency w p) = edgeDistance (graph adjacency) (weights w) p.1 p.2 := by
  let E := ResidualSearch.Enumeration.fin n
  let G := graph adjacency
  let c := fun e => rational (decodeCost (cost w) e)
  let _ : DecidableRel G.Adj := by dsimp only [G]; infer_instance
  have hc (e : Fin n × Fin n) : 0≤c e := NNRat.coe_nonneg _
  have ref := congrArg Prod.fst (FractionalCoverRawOracle.shortest_refines E G (decodeCost (cost w)) p.1 p.2)
  change ((FractionalCoverRawOracle.shortest E G (decodeCost (cost w)) p.1 p.2).1.map
    FractionalCoverRawOracle.decode) = _ at ref
  rw [← shortest_decode] at ref
  change observe ((shortest E adjacency (cost w) p.1 p.2).1.map _) = edgeDistance G (weights w) p.1 p.2
  cases h : (shortest E adjacency (cost w) p.1 p.2).1 with
  | none =>
    rw [h] at ref
    exact ((edgeDistance_eq_top_iff G (weights w) p.1 p.2).mpr
      ((FractionalCoverPathOracle.shortest_none_iff E G c hc p.1 p.2).mp ref.symm)).symm
  | some q =>
    rw [h] at ref
    let d := (BinaryRational.decode q.cost).value
    change ((d : ℝ≥0) : ℝ≥0∞)=edgeDistance G (weights w) p.1 p.2
    obtain ⟨found,_,same⟩ := FractionalCoverPathOracle.shortest_valid E G c p.1 p.2 ref.symm
    have represented : (d : ℝ≥0)=found.edgeWeight (weights w) := by
      change (d : ℚ)=FractionalCoverWalkOracle.pathCost c found at same
      have cast := congrArg (fun a : ℚ => (a : ℝ)) same
      rw [path_cost w found] at cast
      exact NNReal.eq cast
    apply le_antisymm
    · apply (coe_le_edgeDistance_iff G (weights w) p.1 p.2 _).mpr
      intro path
      obtain ⟨min,observed,dominates⟩ := FractionalCoverPathOracle.shortest_minimum E G c hc p.1 p.2 path
      have agree := Option.some.inj (ref.trans observed)
      have prior : (d : ℚ)≤FractionalCoverWalkOracle.pathCost c path := by
        rw [← agree] at dominates
        exact dominates
      have asReal : (d : ℝ)≤(FractionalCoverWalkOracle.pathCost c path : ℝ) := by exact_mod_cast prior
      rw [path_cost w path] at asReal
      exact NNReal.coe_le_coe.mp asReal
    · rw [represented]
      exact edgeDistance_le_weight (weights w) found

theorem none_iff {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (p : Fin n × Fin n) :
    distance adjacency w p=none ↔ edgeDistance (graph adjacency) (weights w) p.1 p.2=⊤ := by
  rw [← distance_exact]
  cases distance adjacency w p <;> simp [observe]

theorem finite_value {n : ℕ} (adjacency : Adjacency n) (w : Weights n) (p : Fin n × Fin n)
    {d : ℚ≥0} (returned : distance adjacency w p=some d) :
    (d : ℝ≥0)=SparsestEdgeBridge.demandDistance (graph adjacency) (weights w) p := by
  have exactDistance := distance_exact adjacency w p
  rw [returned] at exactDistance
  unfold SparsestEdgeBridge.demandDistance
  rw [← exactDistance]
  rfl

end DirectedFlowCutGap.RationalSparsestEdgeDistances
