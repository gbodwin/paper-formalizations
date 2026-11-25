import DirectedFlowCutGap.RationalPositiveArcEdgeFamily
import DirectedFlowCutGap.WeakDecompositionThresholdSlack

/-! Check whether light-arc removal preserves the original threshold
demands. When it does, use the vertex-count horizon at the original budget.
The general positive-arc family covers the other inputs. -/
namespace DirectedFlowCutGap.RationalTrimmedEdgeFamily

open scoped BigOperators NNRat NNReal ENNReal
open BinaryFractionalWalkOracle (Adjacency graph)
open BinaryRational (decode zero)
open RationalEdgeThresholds (Weights weights demands demands_iff)
open RationalEdgeDecomposition (Good originalWeight originalWeight_eq originalTotal)
open RationalOriginalEdgeFamily (light lightMass floor chooseScale horizon)
open RationalDerivedEdgeFamily (factor)
open RationalExactEdgeOracle (Edge)
open ExactFlowCutGap (thresholdSlackCutoff trimmedForSlack outgoingLightLoss efg)

variable {n : ℕ}

def cutoff (n : ℕ) : ℚ≥0 := (2*(n : ℚ≥0))⁻¹

theorem cutoff_value (n : ℕ) : (cutoff n : ℝ≥0) = thresholdSlackCutoff n := by
  simp only [cutoff,thresholdSlackCutoff,NNRat.cast_inv,NNRat.cast_mul,NNRat.cast_ofNat,NNRat.cast_natCast]

def trimmed (A : Adjacency n) (w : Weights n) : Weights n :=
  Vector.ofFn fun u => Vector.ofFn fun v =>
    if originalWeight A w (u,v) ≤ cutoff n then zero else (w.get u).get v

theorem trimmed_value (A : Adjacency n) (w : Weights n) (e : Edge n) :
    weights (trimmed A w) e = trimmedForSlack (graph A) (weights w) e := by
  rcases e with ⟨u,v⟩
  have compare : originalWeight A w (u,v) ≤ cutoff n ↔
      actualEdgeWeight (graph A) (weights w) (u,v) ≤ thresholdSlackCutoff n := by
    rw [← originalWeight_eq,← cutoff_value,NNRat.cast_le]
  simp only [weights,RationalEdgeThresholds.cost,BinaryFractionalWalkOracle.decodeCost,trimmed,
    Vector.getElem_ofFn,Fin.eta,trimmedForSlack]
  by_cases h : originalWeight A w (u,v) ≤ cutoff n
  · rw [ite_eq_left h,ite_eq_left (compare.mp h)]
    simp [BinaryRational.zero,decode,BinaryArithmetic.value]
  · rw [ite_eq_right h,ite_eq_right (fun allowed => h (compare.mpr allowed))]
    have arc : (graph A).Adj u v := by
      by_contra noArc
      apply h
      rw [← NNRat.cast_le (K := ℝ≥0),originalWeight_eq,actualEdgeWeight_of_not_adj _ _ noArc]
      exact zero_le
    rw [actualEdgeWeight_of_adj _ _ arc]
    rfl

theorem trimmed_weight_le (A : Adjacency n) (w : Weights n) (e : Edge n) :
    originalWeight A (trimmed A w) e ≤ originalWeight A w e := by
  rw [← NNRat.cast_le (K := ℝ≥0),originalWeight_eq,originalWeight_eq]
  by_cases arc : (graph A).Adj e.1 e.2
  · rw [actualEdgeWeight_of_adj _ _ arc,actualEdgeWeight_of_adj _ _ arc,trimmed_value]
    exact ExactFlowCutGap.trimmedForSlack_le ..
  · simp only [actualEdgeWeight_of_not_adj _ _ arc,le_refl]

private theorem trimmed_floor (A : Adjacency n) (w : Weights n) (e : Edge n)
    (positive : 0 < originalWeight A (trimmed A w) e) :
    cutoff n < originalWeight A (trimmed A w) e := by
  replace positive : 0 < actualEdgeWeight (graph A) (weights (trimmed A w)) e := by
    rw [← originalWeight_eq]
    exact_mod_cast positive
  rw [← NNRat.cast_lt (K := ℝ≥0),originalWeight_eq,cutoff_value]
  by_cases arc : (graph A).Adj e.1 e.2
  · rw [actualEdgeWeight_of_adj _ _ arc,trimmed_value,trimmedForSlack] at positive ⊢
    by_cases small : actualEdgeWeight (graph A) (weights w) e ≤ thresholdSlackCutoff n
    · rw [ite_eq_left small] at positive
      exact (lt_irrefl _ positive).elim
    · rwa [ite_eq_right small,lt_iff_not_ge]
  · rw [actualEdgeWeight_of_not_adj _ _ arc] at positive
    exact (lt_irrefl _ positive).elim

theorem cutoff_lt_of_trimmed_positive (A : Adjacency n) (w : Weights n) (e : Edge n)
    (positive : 0 < originalWeight A (trimmed A w) e) : cutoff n < originalWeight A (trimmed A w) e :=
  trimmed_floor A w e positive

def keepsDemands (A : Adjacency n) (w : Weights n) : Bool :=
  decide (demands A w ⊆ demands A (trimmed A w))

theorem keepsDemands_value (A : Adjacency n) (w : Weights n) :
    keepsDemands A w = true ↔
      edgeThresholdDemands (graph A) (weights w) ⊆
        edgeThresholdDemands (graph A) (weights (trimmed A w)) := by
  simp only [keepsDemands,decide_eq_true_eq]
  constructor
  · intro h e demand
    exact (demands_iff A _ e).mp (h ((demands_iff A w e).mpr demand))
  · intro h e demand
    exact (demands_iff A _ e).mpr (h ((demands_iff A w e).mp demand))

theorem keepsDemands_of_slack (A : Adjacency n) (w : Weights n)
    (slack : ∀ e ∈ edgeThresholdDemands (graph A) (weights w),
      ((1+outgoingLightLoss (graph A) (weights w) (thresholdSlackCutoff n) : ℝ≥0) : ℝ≥0∞) ≤
        edgeDistance (graph A) (weights w) e.1 e.2) :
    keepsDemands A w = true := by
  rw [keepsDemands_value,funext (trimmed_value A w)]
  exact ExactFlowCutGap.trim_preserves_slack_demands (graph A) (weights w) slack

private theorem trimmed_factor_le (hn : 0 < n) (A : Adjacency n) (w : Weights n) :
    RationalInstanceEdgeFactor.least A (trimmed A w) ≤ efg n (totalEdgeWeight (graph A) (weights w)) := by
  apply RationalInstanceEdgeFactor.least_le_of_factor
  apply ExactFlowCutGap.efg_round_atMost hn
  apply Finset.sum_le_sum
  intro e _
  rw [trimmed_value]
  exact ExactFlowCutGap.trimmedForSlack_le ..

private theorem trimmed_scale (hn : 0 < n) (A : Adjacency n) (w : Weights n)
    (positive : 0 < factor A (trimmed A w)) :
    chooseScale A (trimmed A w) (factor A (trimmed A w)) = n := by
  let q := trimmed A w
  let α := factor A q
  have alpha : (1 : ℚ≥0) ≤ α := by
    change (1 : ℚ≥0) ≤ (RationalInstanceEdgeFactor.least A q : ℚ≥0)
    exact_mod_cast Nat.succ_le_of_lt (Nat.cast_pos.mp (show 0 < (RationalInstanceEdgeFactor.least A q : ℚ≥0) from positive))
  have floor_le : floor n α ≤ cutoff n := by
    unfold floor cutoff
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    have prod := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left alpha (by norm_num : (0 : ℚ≥0) ≤ 4))
      (Nat.cast_nonneg n)
    calc
      (2 : ℚ≥0)*n ≤ 4*n := mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg n)
      _ ≤ 4*α*n := by simpa only [mul_one] using prod
  have mass_zero : lightMass A q α n = 0 := by
    unfold lightMass
    rw [Finset.sum_eq_zero, mul_zero]
    intro e h
    have light := (Finset.mem_filter.mp h).2
    by_contra nonzero
    exact (not_lt_of_ge floor_le) (light.trans' (trimmed_floor A w e (pos_iff_ne_zero.mpr nonzero)))
  change (if lightMass A q α n ≤ 1/4 then n else _) = n
  rw [mass_zero,ite_eq_left (by positivity : (0 : ℚ≥0) ≤ 1/4)]

def family (A : Adjacency n) (w : Weights n) : RationalWeakFamily.History (Edge n) :=
  if keepsDemands A w then RationalDerivedEdgeFamily.family A (trimmed A w)
  else RationalPositiveArcEdgeFamily.family A w

theorem family_nonempty (A : Adjacency n) (w : Weights n) : 0 < (family A w).cuts.length := by
  unfold family
  split
  · exact (RationalDerivedEdgeFamily.family_spec A (trimmed A w)).1
  · exact RationalPositiveArcEdgeFamily.family_nonempty A w

set_option maxHeartbeats 900000 in
theorem family_spec (hn : 0 < n) (A : Adjacency n) (w : Weights n) :
    let L := (family A w).cuts
    (∀ X ∈ L, Good A w X) ∧
      ∀ e, (L.countP (fun X => decide (e ∈ X)) : ℝ)/(L.length : ℝ) ≤
        8*(originalWeight A w e : ℝ)*(efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
  unfold family
  split
  · rename_i eligible
    have spec := RationalOriginalEdgeFamily.adaptive_spec_all hn A (trimmed A w) _
      (RationalDerivedEdgeFamily.factor_valid A (trimmed A w))
    refine ⟨?_,fun e => (spec.2 e).trans ?_⟩
    · intro X member
      obtain ⟨arcs,cut⟩ := spec.1 X member
      have keep := (keepsDemands_value A w).mp eligible
      exact ⟨arcs,fun s t demand => cut s t
        ((demands_iff A _ (s,t)).mpr (keep ((demands_iff A w (s,t)).mp demand)))⟩
    · have fee : ((factor A (trimmed A w) : ℚ≥0) : ℝ) ≤ (efg n (totalEdgeWeight (graph A) (weights w)) : ℝ) := by
        simpa only [factor,NNRat.cast_natCast] using (Nat.cast_le.mpr (trimmed_factor_le hn A w) :
          (RationalInstanceEdgeFactor.least A (trimmed A w) : ℝ) ≤ (efg n (totalEdgeWeight (graph A) (weights w)) : ℝ))
      gcongr
      exact_mod_cast trimmed_weight_le A w e
  · exact RationalPositiveArcEdgeFamily.family_spec A w

set_option maxHeartbeats 900000 in
theorem length_le_vertex_horizon (hn : 0 < n) (A : Adjacency n) (w : Weights n)
    (eligible : keepsDemands A w = true) :
    let α := efg n (totalEdgeWeight (graph A) (weights w))
    (family A w).cuts.length ≤ horizon A w (α : ℚ≥0) n := by
  let q := trimmed A w
  let a := factor A q
  rw [family,ite_eq_left eligible,RationalDerivedEdgeFamily.family]
  by_cases h : a = 0
  · rw [RationalOriginalEdgeFamily.adaptive,ite_eq_left h]
    exact RationalWeakFamily.edgeRounds_pos ..
  · have positive : 0 < a := pos_iff_ne_zero.mpr h
    rw [RationalOriginalEdgeFamily.adaptive,ite_eq_right h,RationalOriginalEdgeFamily.build_length,trimmed_scale hn A w positive]
    have fee : a ≤ (efg n (totalEdgeWeight (graph A) (weights w)) : ℚ≥0) :=
      Nat.cast_le.mpr (trimmed_factor_le hn A w)
    have budget : originalTotal A q ≤ originalTotal A w :=
      Finset.sum_le_sum fun e _ => trimmed_weight_le A w e
    unfold horizon RationalWeakFamily.edgeRounds RationalWeakFamily.edgeMagnitude
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.size_le_size
    apply Nat.ceil_mono
    gcongr

end DirectedFlowCutGap.RationalTrimmedEdgeFamily
