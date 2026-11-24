import DirectedFlowCutGap.ConcurrentEdgeBudgetGrid
import DirectedFlowCutGap.NormalizedOptimalMode

/-! Select both a normalized covering and a rounding mode with rational
comparisons of the sixth powers of their sparsity scales. -/
namespace DirectedFlowCutGap.ConcurrentEdgeBudgetSelection

open scoped BigOperators NNReal NNRat
open BinaryFractionalWalkOracle (Adjacency graph)
open RationalEdgeThresholds (Weights weights)
open RationalEdgeDecomposition (originalTotal originalWeight originalWeight_eq)
open ConcurrentEdgeOracle (Edge)
open NormalizedOptimalMode (harmonic_eq sizeScale massScale)
open SparsestEdgeBridge (demandDistance)

variable {m n : ℕ}

def rawCost (A : Adjacency n) (c w : Weights n) : ℚ≥0 :=
  ∑ e : Edge n, originalWeight A c e * originalWeight A w e

theorem rawCost_eq (A : Adjacency n) (c w : Weights n) :
    (rawCost A c w : ℝ≥0) = weightedEdgeCost (graph A) (weights c) (weights w) := by
  simp only [rawCost, NNRat.cast_sum, NNRat.cast_mul, originalWeight_eq,
    weightedEdgeCost, graphEdges, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases arc : (graph A).Adj e.1 e.2
  · rw [actualEdgeWeight_of_adj _ _ arc, actualEdgeWeight_of_adj _ _ arc, ite_eq_left arc]
  · rw [actualEdgeWeight_of_not_adj _ _ arc, ite_eq_right arc, zero_mul]

theorem rawMass_eq (A : Adjacency n) (w : Weights n) :
    (originalTotal A w : ℝ≥0) = totalEdgeWeight (graph A) (weights w) := by
  simp only [originalTotal, NNRat.cast_sum, originalWeight_eq]
  exact_mod_cast WeakDecomposition.sum_actualEdgeWeight (graph A) (weights w)

noncomputable def scale (n m : ℕ) (amount mass : ℝ≥0) (mode : ChargedVertexModes.Mode) : ℝ :=
  (amount : ℝ)/(m : ℝ) * match mode with
  | .size => sizeScale n m
  | .mass => massScale m mass

def score (n m : ℕ) (amount mass : ℚ≥0) (mode : ChargedVertexModes.Mode) : ℚ≥0 :=
  (amount/(m : ℚ≥0))^6 * match mode with
  | .size => (n : ℚ≥0)^2*(NormalizedOptimalMode.harmonic m)^6
  | .mass => (NormalizedOptimalMode.harmonic m)^9*mass^3

theorem score_eq (n m : ℕ) (amount mass : ℚ≥0) (mode : ChargedVertexModes.Mode) :
    ((score n m amount mass mode : ℝ≥0) : ℝ) =
      (scale n m (amount : ℝ≥0) (mass : ℝ≥0) mode)^6 := by
  have size : ((n : ℝ)^(1/3 : ℝ))^6 = (n : ℝ)^2 := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num [Real.rpow_natCast]
  have h : (((FiniteHarmonicThreshold.harmonicWeight m : ℝ))^(3/2 : ℝ))^6 =
      (FiniteHarmonicThreshold.harmonicWeight m : ℝ)^9 := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num [Real.rpow_natCast]
  have w : ((((mass : ℝ≥0) : ℝ))^(1/2 : ℝ))^6 = ((mass : ℝ≥0) : ℝ)^3 := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num [Real.rpow_natCast]
  cases mode with
  | mass =>
    simp only [score, scale, massScale, NNRat.cast_mul, NNRat.cast_pow, harmonic_eq, NNRat.cast_div,
      NNRat.cast_natCast, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow,
      mul_pow, h, w]
  | size =>
    simp only [score, scale, sizeScale, NNRat.cast_mul, NNRat.cast_pow, harmonic_eq, NNRat.cast_div,
      NNRat.cast_natCast, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, mul_pow, size]

theorem scale_nonnegative (n m : ℕ) (amount mass : ℝ≥0) (mode : ChargedVertexModes.Mode) :
    0 ≤ scale n m amount mass mode := by
  cases mode <;> unfold scale sizeScale massScale <;> positivity

theorem score_le_iff (n m : ℕ) (a b x y : ℚ≥0) (u v : ChargedVertexModes.Mode) :
    score n m a x u ≤ score n m b y v ↔ scale n m (a : ℝ≥0) (x : ℝ≥0) u ≤
      scale n m (b : ℝ≥0) (y : ℝ≥0) v := by
  rw [← NNRat.cast_le (K := ℝ≥0), ← NNReal.coe_le_coe, score_eq, score_eq]
  exact pow_le_pow_iff_left₀ (scale_nonnegative ..) (scale_nonnegative ..) (by decide : 6 ≠ 0)

structure Plan (n : ℕ) where
  lengths : Weights n
  mode : ChargedVertexModes.Mode
  receipt : ℚ≥0

def plan (A : Adjacency n) (c w : Weights n) (m : ℕ) : Plan n :=
  let price := rawCost A c w
  let mass := originalTotal A w
  let s := score n m price mass .size
  let t := score n m price mass .mass
  if t ≤ s then ⟨w,.mass,t⟩ else ⟨w,.size,s⟩

def choose (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m) :
    Option (Plan n) :=
  ((ConcurrentEdgeBudgetGrid.candidates hn A c P).map (fun w => plan A c w m)).argmin Plan.receipt

theorem plan_lengths (A : Adjacency n) (c w : Weights n) (m : ℕ) :
    (plan A c w m).lengths = w := by
  unfold plan
  dsimp only
  split <;> rfl

theorem plan_receipt (A : Adjacency n) (c w : Weights n) (m : ℕ) :
    (plan A c w m).receipt = score n m (rawCost A c w) (originalTotal A w) (plan A c w m).mode := by
  unfold plan
  dsimp only
  split <;> rfl

theorem locally_best (A : Adjacency n) (c w : Weights n) (m : ℕ)
    (mode : ChargedVertexModes.Mode) :
    (plan A c w m).receipt ≤ score n m (rawCost A c w) (originalTotal A w) mode := by
  unfold plan
  dsimp only
  split
  · cases mode
    · exact le_rfl
    · assumption
  · cases mode
    · exact (le_of_not_ge ‹_›)
    · exact le_rfl

theorem chosen_member (hn : 0 < n) (A : Adjacency n) (c : Weights n)
    (P : Vector (Edge n) m) {z : Plan n} (found : choose hn A c P = some z) :
    ∃ w ∈ ConcurrentEdgeBudgetGrid.candidates hn A c P, plan A c w m = z := by
  have selected : z ∈ ((ConcurrentEdgeBudgetGrid.candidates hn A c P).map
      (fun w => plan A c w m)).argmin Plan.receipt := by
    change z ∈ choose hn A c P
    simp only [found, Option.mem_some_iff]
  exact List.mem_map.mp (List.argmin_mem selected)

theorem chosen_le (hn : 0 < n) (A : Adjacency n) (c : Weights n)
    (P : Vector (Edge n) m) {z : Plan n} (found : choose hn A c P = some z)
    (w : Weights n) (member : w ∈ ConcurrentEdgeBudgetGrid.candidates hn A c P)
    (mode : ChargedVertexModes.Mode) :
    scale n m (weightedEdgeCost (graph A) (weights c) (weights z.lengths))
      (totalEdgeWeight (graph A) (weights z.lengths)) z.mode ≤
        scale n m (weightedEdgeCost (graph A) (weights c) (weights w))
          (totalEdgeWeight (graph A) (weights w)) mode := by
  obtain ⟨q,_,rfl⟩ := chosen_member hn A c P found
  rw [plan_lengths, ← rawCost_eq, ← rawMass_eq, ← rawCost_eq, ← rawMass_eq]
  apply (score_le_iff n m ..).mp
  rw [← plan_receipt]
  let plans := (ConcurrentEdgeBudgetGrid.candidates hn A c P).map (fun w => plan A c w m)
  have candidate : plan A c w m ∈ plans := List.mem_map.mpr ⟨w,member,rfl⟩
  have selected : plan A c q m ∈ plans.argmin Plan.receipt := by
    change plan A c q m ∈ choose hn A c P
    simp only [found, Option.mem_some_iff]
  exact (List.le_of_mem_argmin candidate selected).trans (locally_best A c w m mode)

private theorem scale_bound (n m : ℕ) (a b M N : ℝ≥0)
    (cost : a ≤ 12*b) (mass : M ≤ 12*N) (mode : ChargedVertexModes.Mode) :
    scale n m a M mode ≤ 48 * scale n m b N mode := by
  have C : (a : ℝ) ≤ 12*(b : ℝ) := by exact_mod_cast cost
  have W : (M : ℝ) ≤ 12*(N : ℝ) := by exact_mod_cast mass
  have p : (a : ℝ)/(m : ℝ) ≤ 12*((b : ℝ)/(m : ℝ)) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right C (by positivity)
  cases mode with
  | size =>
    have h : 0 ≤ scale n m b N .size := scale_nonnegative ..
    calc
      _ ≤ (12*((b : ℝ)/(m : ℝ)))*sizeScale n m :=
        mul_le_mul_of_nonneg_right p (by unfold sizeScale; positivity)
      _ = 12*scale n m b N .size := by
        simp only [scale, mul_assoc]
      _ ≤ 48*scale n m b N .size := by nlinarith
  | mass =>
    have Wn : (0 : ℝ) ≤ N := NNReal.coe_nonneg _
    have square : (M : ℝ)^(1/2 : ℝ) ≤ 4*(N : ℝ)^(1/2 : ℝ) := by
      have k : (12 : ℝ)^(1/2 : ℝ) ≤ 4 := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
        norm_num
      calc
        _ ≤ (12*(N : ℝ))^(1/2 : ℝ) := Real.rpow_le_rpow (NNReal.coe_nonneg _) W (by norm_num)
        _ = (12 : ℝ)^(1/2 : ℝ)*(N : ℝ)^(1/2 : ℝ) := Real.mul_rpow (by norm_num) Wn
        _ ≤ _ := mul_le_mul_of_nonneg_right k (by positivity)
    unfold scale massScale
    dsimp only
    calc
      _ ≤ (12*((b : ℝ)/(m : ℝ))) *
          ((FiniteHarmonicThreshold.harmonicWeight m : ℝ)^(3/2 : ℝ)*(4*(N : ℝ)^(1/2 : ℝ))) := by
        exact mul_le_mul p (mul_le_mul_of_nonneg_left square (by positivity)) (by positivity) (by positivity)
      _ = _ := by ring

theorem chosen_comparison (hn : 0 < n) (A : Adjacency n) (c : Weights n)
    (P : Vector (Edge n) m) {z : Plan n} (found : choose hn A c P = some z)
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (positivePaths : ∀ j : Fin m,
      Nonempty (SimplePath (graph (ConcurrentEdgeZeroPrices.positiveGraph A c)) (P.get j).1 (P.get j).2))
    (w : Edge n → ℝ≥0) (normalized : (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) w (P.get j))
    (mode : ChargedVertexModes.Mode) :
    scale n m (weightedEdgeCost (graph A) (weights c) (weights z.lengths))
      (totalEdgeWeight (graph A) (weights z.lengths)) z.mode ≤
        48*scale n m (weightedEdgeCost (graph A) (weights c) w) (totalEdgeWeight (graph A) w) mode := by
  obtain ⟨near, member, _, priced, mass⟩ := ConcurrentEdgeBudgetGrid.nearby_candidate hn A c P d different
    reach positivePaths w normalized
  exact (chosen_le hn A c P found near member mode).trans (scale_bound n m _ _ _ _ priced mass mode)

theorem has_choice (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2))
    (positivePaths : ∀ j : Fin m,
      Nonempty (SimplePath (graph (ConcurrentEdgeZeroPrices.positiveGraph A c)) (P.get j).1 (P.get j).2))
    (w : Edge n → ℝ≥0) (normal : (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) w (P.get j)) :
    ∃ z, choose hn A c P = some z := by
  obtain ⟨q, member, _⟩ := ConcurrentEdgeBudgetGrid.nearby_candidate hn A c P d different
    reach positivePaths w normal
  cases found : choose hn A c P with
  | some z => exact ⟨z,rfl⟩
  | none =>
    have check : plan A c q m ∈ ((ConcurrentEdgeBudgetGrid.candidates hn A c P).map
        (fun w => plan A c w m)) := List.mem_map.mpr ⟨q,member,rfl⟩
    rw [choose] at found
    rw [List.argmin_eq_none.mp found] at check
    exact (List.not_mem_nil check).elim

theorem chosen_normalized (hn : 0 < n) (A : Adjacency n) (c : Weights n) (P : Vector (Edge n) m)
    {z : Plan n} (found : choose hn A c P = some z)
    (d : Fin m) (different : (P.get d).1 ≠ (P.get d).2)
    (reach : ∀ j : Fin m, Nonempty (SimplePath (graph A) (P.get j).1 (P.get j).2)) :
    (m : ℝ≥0) ≤ ∑ j : Fin m, demandDistance (graph A) (weights z.lengths) (P.get j) := by
  obtain ⟨w,member,rfl⟩ := chosen_member hn A c P found
  rw [plan_lengths]
  obtain ⟨⟨B,U⟩,budgets,rfl⟩ := List.mem_map.mp member
  obtain ⟨b,_,mass⟩ := List.mem_flatMap.mp budgets
  obtain ⟨u,inside,same⟩ := List.mem_map.mp mass
  have equal : u = U := congrArg Prod.snd same
  subst u
  have posU := ConcurrentEdgeBudgetGrid.positive (lo := 1) zero_lt_one inside
  have realU : (0 : ℝ≥0) < U := by exact_mod_cast posU
  have positive (e : Edge n) (_ : e ∈ graphEdges (graph A)) :
      0 < weights (ConcurrentEdgeMassBudget.reprice c B U) e := by
    rw [ConcurrentEdgeMassBudget.reprice_eq]
    exact add_pos_of_nonneg_of_pos zero_le (div_pos zero_lt_one realU)
  exact ConcurrentEdgeCover.solve_normalized hn A _ P positive reach d different

end DirectedFlowCutGap.ConcurrentEdgeBudgetSelection
