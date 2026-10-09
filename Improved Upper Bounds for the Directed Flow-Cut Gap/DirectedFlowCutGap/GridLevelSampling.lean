import DirectedFlowCutGap.FiniteCutLaw
import Mathlib.Probability.Distributions.Uniform

/-!
# Exact finite sampling of grid-weight level cuts

For nonnegative vertex weights on the grid `ℕ / L`, the actual
endpoint-excluding path distance is either infinite or on the same grid.
Consequently, the actual closed-interval level cut is constant on each open
cell `(j/L,(j+1)/L)`. The finitely many cell boundaries have zero Lebesgue
probability, and the cells have equal probability `1/L` and total probability
one. Thus drawing a uniform `j : Fin L` and using `(j+1/2)/L` gives exactly the
existing `FiniteCutLaw.cutPMF`, including all correlations between vertices.

This is an exact finite distribution theorem. It makes no claim about the
running time of operations on abstract real inputs.
-/

namespace DirectedFlowCutGap.GridLevelSampling

noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal ENNReal Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All actual vertex weights, including source and target weights, are
nonnegative integer multiples of the common grid spacing. -/
def OnGrid (L : ℕ) (w : V → ℝ≥0) : Prop :=
  ∀ v, ∃ n : ℕ, w v = (n : ℝ≥0) / L

omit [Fintype V] [DecidableEq V] in
/-- Convert the nonnegative integer witness convention used by the candidate
optimizer to natural grid coordinates. -/
theorem onGrid_of_nonneg_int {L : ℕ} {w : V → ℝ≥0}
    (hw : ∀ v, ∃ k : ℤ, 0 ≤ k ∧ (w v : ℝ) = (k : ℝ) / L) : OnGrid L w := by
  intro v
  obtain ⟨k, hk, hwk⟩ := hw v
  refine ⟨k.toNat, ?_⟩
  apply NNReal.coe_injective
  have hcast : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
  simpa only [NNReal.coe_div, NNReal.coe_natCast, hcast] using hwk

omit [Fintype V] [DecidableEq V] in
/-- A candidate with weight one on the existing cut and integer-grid weights
outside it has actual grid weights at every vertex. -/
theorem onGrid_of_unit_inside {L : ℕ} (hL : 0 < L) {w : V → ℝ≥0}
    (X : Finset V) (hin : ∀ v ∈ X, w v = 1)
    (hout : ∀ v ∉ X, ∃ k : ℤ, 0 ≤ k ∧ (w v : ℝ) = (k : ℝ) / L) :
    OnGrid L w := by
  apply onGrid_of_nonneg_int
  intro v
  by_cases hv : v ∈ X
  · refine ⟨(L : ℤ), by exact_mod_cast hL.le, ?_⟩
    simp [hin v hv, ne_of_gt hL]
  · exact hout v hv

omit [Fintype V] in
/-- Sums over internal vertices preserve the grid. The path definition excludes
both endpoints, so no change of metric convention is involved. -/
theorem pathWeight_onGrid {G : Digraph V} {w : V → ℝ≥0} {L : ℕ}
    (hw : OnGrid L w) {s t : V} (p : SimplePath G s t) :
    ∃ n : ℕ, p.weight w = (n : ℝ≥0) / L := by
  choose k hk using hw
  refine ⟨∑ v ∈ p.internalVertices, k v, ?_⟩
  simp only [SimplePath.weight, hk, Nat.cast_sum, Finset.sum_div]

/-- Every finite actual distance is a grid point, by minimum-path attainment. -/
theorem vertexDistance_onGrid {G : Digraph V} {w : V → ℝ≥0} {L : ℕ}
    (hw : OnGrid L w) {s t : V} (h : vertexDistance G w s t ≠ ⊤) :
    ∃ n : ℕ, vertexDistance G w s t = (((n : ℝ≥0) / L : ℝ≥0) : ℝ≥0∞) := by
  have hp : Nonempty (SimplePath G s t) := by
    by_contra hn
    exact h ((vertexDistance_eq_top_iff G w s t).mpr hn)
  obtain ⟨p, hp⟩ := vertexDistance_attained w hp
  obtain ⟨n, hn⟩ := pathWeight_onGrid hw p
  exact ⟨n, hp.trans (congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞)) hn)⟩

/-- Infinity is retained explicitly for unreachable pairs. -/
theorem vertexDistance_eq_top_or_onGrid {G : Digraph V} {w : V → ℝ≥0} {L : ℕ}
    (hw : OnGrid L w) (s t : V) :
    vertexDistance G w s t = ⊤ ∨
      ∃ n : ℕ, vertexDistance G w s t = (((n : ℝ≥0) / L : ℝ≥0) : ℝ≥0∞) := by
  by_cases h : vertexDistance G w s t = ⊤
  · exact Or.inl h
  · exact Or.inr (vertexDistance_onGrid hw h)

/-- The open cell avoids every grid boundary, including 0 and 1. -/
def cell (L : ℕ) (j : Fin L) : Set ℝ :=
  Ioo ((j : ℕ) / (L : ℝ)) (((j : ℕ) + 1 : ℝ) / L)

theorem measurableSet_cell (L : ℕ) (j : Fin L) : MeasurableSet (cell L j) :=
  measurableSet_Ioo

/-- A canonical interior sample for every cell. -/
def midpoint (L : ℕ) (j : Fin L) : ℝ :=
  ((j : ℕ) + (1 / 2 : ℝ)) / L

theorem midpoint_mem_cell {L : ℕ} (hL : 0 < L) (j : Fin L) :
    midpoint L j ∈ cell L j := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  constructor <;> apply (div_lt_div_iff_of_pos_right hLR).mpr <;>
    linarith

theorem cell_subset_unit {L : ℕ} (hL : 0 < L) (j : Fin L) :
    cell L j ⊆ Icc (0 : ℝ) 1 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  intro d hd
  refine ⟨(div_nonneg (Nat.cast_nonneg _) hLR.le).trans hd.1.le, hd.2.le.trans ?_⟩
  apply (div_le_one hLR).mpr
  exact_mod_cast Nat.succ_le_of_lt j.isLt

theorem nat_div_le_iff_of_mem_cell {L n : ℕ} (hL : 0 < L) (j : Fin L)
    {d : ℝ} (hd : d ∈ cell L j) :
    (n : ℝ) / L ≤ d ↔ n ≤ (j : ℕ) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  constructor
  · intro hn
    by_contra hnj
    have hjn : ((j : ℕ) + 1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge hnj)
    have hh := div_le_div_of_nonneg_right hjn hLR.le
    exact (not_lt_of_ge hn) (hd.2.trans_le hh)
  · intro hn
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hn) hLR.le).trans hd.1.le

theorem le_nat_div_iff_of_mem_cell {L n : ℕ} (hL : 0 < L) (j : Fin L)
    {d : ℝ} (hd : d ∈ cell L j) :
    d ≤ (n : ℝ) / L ↔ (j : ℕ) < n := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  constructor
  · intro hn
    by_contra hnj
    have hnj' : (n : ℝ) ≤ (j : ℕ) := by exact_mod_cast le_of_not_gt hnj
    have hh := div_le_div_of_nonneg_right hnj' hLR.le
    exact (not_lt_of_ge (hn.trans hh)) hd.1
  · intro hn
    have hjn : ((j : ℕ) + 1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hn
    exact hd.2.le.trans (div_le_div_of_nonneg_right hjn hLR.le)

/-- On an open cell the complete cut is determined by integer comparisons. -/
theorem mem_levelCut_iff_grid {G : Digraph V} {w : V → ℝ≥0} {L : ℕ}
    (hL : 0 < L) (s v : V) (j : Fin L) {d : ℝ} (hd : d ∈ cell L j)
    (n k : ℕ)
    (hn : vertexDistance G w s v = (((n : ℝ≥0) / L : ℝ≥0) : ℝ≥0∞))
    (hk : w v = (k : ℝ≥0) / L) :
    v ∈ levelCut G w s d.toNNReal ↔ n ≤ (j : ℕ) ∧ (j : ℕ) < n + k := by
  have hd0 := (cell_subset_unit hL j hd).1
  rw [mem_levelCut, hn, hk, ← ENNReal.coe_add]
  simp only [ENNReal.coe_le_coe]
  have heq : (n : ℝ≥0) / L + (k : ℝ≥0) / L = ((n + k : ℕ) : ℝ≥0) / L := by
    rw [Nat.cast_add, add_div]
  rw [heq]
  have hleft : ((n : ℝ≥0) / L ≤ d.toNNReal) ↔ (n : ℝ) / L ≤ d := by
    rw [← NNReal.coe_le_coe]
    simp [Real.coe_toNNReal d hd0]
  have hright : (d.toNNReal ≤ ((n + k : ℕ) : ℝ≥0) / L) ↔ d ≤ ((n + k : ℕ) : ℝ) / L := by
    rw [← NNReal.coe_le_coe]
    simp [Real.coe_toNNReal d hd0]
  rw [hleft, hright, nat_div_le_iff_of_mem_cell hL j hd,
    le_nat_div_iff_of_mem_cell hL j hd]

/-- Actual closed-interval cuts agree at every two interior points of a cell.
Unreachable vertices are absent at both levels. -/
theorem levelCut_eq_of_mem_cell {G : Digraph V} {w : V → ℝ≥0} {L : ℕ}
    (hL : 0 < L) (hw : OnGrid L w) (s : V) (j : Fin L)
    {d e : ℝ} (hd : d ∈ cell L j) (he : e ∈ cell L j) :
    levelCut G w s d.toNNReal = levelCut G w s e.toNNReal := by
  ext v
  by_cases ht : vertexDistance G w s v = ⊤
  · simp [not_mem_levelCut_of_distance_top ht]
  · obtain ⟨n, hn⟩ := vertexDistance_onGrid hw ht
    obtain ⟨k, hk⟩ := hw v
    rw [mem_levelCut_iff_grid hL s v j hd n k hn hk,
      mem_levelCut_iff_grid hL s v j he n k hn hk]

/-- The closed grid-boundary set includes both endpoints. -/
def boundaries (L : ℕ) : Set ℝ :=
  Set.range (fun j : Fin (L + 1) => (j : ℕ) / (L : ℝ))

/-- All exceptional boundary atoms have total probability zero. -/
theorem uniformLevel_boundaries (L : ℕ) : uniformLevel (boundaries L) = 0 := by
  change (volume.restrict (Icc (0 : ℝ) 1)) (boundaries L) = 0
  exact (Set.finite_range _).measure_zero _

theorem uniformLevel_cell {L : ℕ} (hL : 0 < L) (j : Fin L) :
    uniformLevel (cell L j) = (L : ℝ≥0∞)⁻¹ := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  rw [uniformLevel, Measure.restrict_apply (measurableSet_cell L j),
    Set.inter_eq_left.mpr (cell_subset_unit hL j), cell, Real.volume_Ioo]
  have he : (((j : ℕ) + 1 : ℝ) / L) - (j : ℕ) / (L : ℝ) = 1 / L := by ring
  rw [he, ENNReal.ofReal_div_of_pos hLR]
  simp

theorem pairwise_disjoint_cells {L : ℕ} (hL : 0 < L) :
    Pairwise (fun i j : Fin L => Disjoint (cell L i) (cell L j)) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  intro i j hij
  apply Set.disjoint_left.mpr
  intro d hi hj
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hij' | hji'
  · have hh : ((i : ℕ) + 1 : ℝ) ≤ (j : ℕ) := by
      exact_mod_cast Nat.succ_le_of_lt hij'
    have hh' := div_le_div_of_nonneg_right hh hLR.le
    exact (not_lt_of_ge hh') (hi.2.trans' hj.1)
  · have hh : ((j : ℕ) + 1 : ℝ) ≤ (i : ℕ) := by
      exact_mod_cast Nat.succ_le_of_lt hji'
    have hh' := div_le_div_of_nonneg_right hh hLR.le
    exact (not_lt_of_ge hh') (hj.2.trans' hi.1)

/-- The open cells have total probability one, so no endpoint mass is lost. -/
theorem uniformLevel_cells {L : ℕ} (hL : 0 < L) :
    uniformLevel (⋃ j : Fin L, cell L j) = 1 := by
  rw [measure_iUnion (pairwise_disjoint_cells hL) (fun j => measurableSet_cell L j)]
  simp only [uniformLevel_cell hL, tsum_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast hL.ne') (ENNReal.natCast_ne_top L)

/-- A general equal-cell quadrature identity for any function constant on the
open cells. No assumption about its values at cell boundaries is needed. -/
theorem uniformLevel_fiber_eq_sum {α : Type*} {L : ℕ} (hL : 0 < L)
    (f : ℝ → α) (hf : ∀ j : Fin L, ∀ d ∈ cell L j, f d = f (midpoint L j)) (a : α) :
    uniformLevel {d | f d = a} =
      ∑ j : Fin L, if f (midpoint L j) = a then (L : ℝ≥0∞)⁻¹ else 0 := by
  let A : Fin L → Set ℝ := fun j => if f (midpoint L j) = a then cell L j else ∅
  have hA (j : Fin L) : A j ⊆ cell L j := by
    dsimp [A]
    split_ifs <;> simp
  have hAe : {d | f d = a} =ᵐ[uniformLevel] ⋃ j : Fin L, A j := by
    have hall : ∀ᵐ d ∂uniformLevel, d ∈ ⋃ j : Fin L, cell L j :=
      (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion (fun j => measurableSet_cell L j))).mpr
        (uniformLevel_cells hL)
    filter_upwards [hall] with d hd
    apply propext
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hd
    constructor
    · intro hfa
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      have he : f (midpoint L j) = a := (hf j d hj).symm.trans hfa
      simpa [A, he] using hj
    · intro hdA
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hdA
      have hkcell := hA k hk
      have he : f (midpoint L k) = a := by
        by_contra hn
        simp [A, hn] at hk
      exact (hf k d hkcell).trans he
  rw [measure_congr hAe,
    measure_iUnion (fun i j hij => (pairwise_disjoint_cells hL hij).mono (hA i) (hA j))
      (fun j => by
        dsimp [A]
        split_ifs
        · exact measurableSet_cell L j
        · exact MeasurableSet.empty), tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [A]
  split_ifs <;> simp [uniformLevel_cell hL]

/-- Uniform finite index sampling followed by the actual midpoint level cut. -/
def gridCutPMF (G : Digraph V) (w : V → ℝ≥0) (s : V) (L : ℕ) (hL : 0 < L) :
    PMF (FiniteCutLaw.Outcome V) := by
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  exact (PMF.uniformOfFintype (Fin L)).map
    (fun j => FiniteCutLaw.draw G w s (midpoint L j))

/-- Exact joint law, not just a marginal or expected-cost approximation. -/
theorem gridCutPMF_eq_cutPMF (G : Digraph V) (w : V → ℝ≥0) (s : V)
    (L : ℕ) (hL : 0 < L) (hw : OnGrid L w) :
    gridCutPMF G w s L hL = FiniteCutLaw.cutPMF G w s := by
  apply PMF.ext
  intro Y
  rw [FiniteCutLaw.cutPMF_apply,
    uniformLevel_fiber_eq_sum hL (FiniteCutLaw.draw G w s) ?_ Y]
  · simp [gridCutPMF, PMF.map_apply, tsum_fintype, eq_comm]
  · intro j d hd
    apply FiniteCutLaw.Outcome.ext
    exact levelCut_eq_of_mem_cell hL hw s j hd (midpoint_mem_cell hL j)

/-- Every positive-probability continuous outcome is realized by one of the
finitely many canonical midpoint levels, and conversely. -/
theorem cutPMF_support_iff_midpoint (G : Digraph V) (w : V → ℝ≥0) (s : V)
    (L : ℕ) (hL : 0 < L) (hw : OnGrid L w) (Y : FiniteCutLaw.Outcome V) :
    Y ∈ (FiniteCutLaw.cutPMF G w s).support ↔
      ∃ j : Fin L, FiniteCutLaw.draw G w s (midpoint L j) = Y := by
  rw [← gridCutPMF_eq_cutPMF G w s L hL hw]
  simp [gridCutPMF]

/-- Measure form of the exact finite-law equality. -/
theorem gridCutPMF_toMeasure (G : Digraph V) (w : V → ℝ≥0) (s : V)
    (L : ℕ) (hL : 0 < L) (hw : OnGrid L w) :
    (gridCutPMF G w s L hL).toMeasure =
      uniformLevel.map (FiniteCutLaw.draw G w s) := by
  rw [gridCutPMF_eq_cutPMF G w s L hL hw, FiniteCutLaw.cutPMF_toMeasure]

end
end DirectedFlowCutGap.GridLevelSampling
