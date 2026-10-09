import LightSpanners.Weight
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-! Numerical subdivision estimates for Lemma 3.5. The graph construction and
cycle correspondence remain separate obligations. -/
namespace LightSpanners

/-- Number of pieces used for a heavy tree edge. -/
noncomputable def subdivisionPieces (w : ℝ) : ℕ := ⌈w⌉₊

theorem subdivisionPieces_pos {w : ℝ} (hw : 1 < w) :
    0 < subdivisionPieces w := by
  exact Nat.ceil_pos.mpr (by linarith)

/-- Every piece of a subdivided heavy edge has weight in (1/2, 1]. -/
theorem subdivision_piece_bounds {w : ℝ} (hw : 1 < w) :
    1 / 2 < w / (subdivisionPieces w : ℝ) ∧
      w / (subdivisionPieces w : ℝ) ≤ 1 := by
  have hp : (0 : ℝ) < subdivisionPieces w := by
    exact_mod_cast subdivisionPieces_pos hw
  have hlo : w ≤ (subdivisionPieces w : ℝ) := Nat.le_ceil w
  have hhi : (subdivisionPieces w : ℝ) < w + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  constructor
  · apply (lt_div_iff₀ hp).mpr
    linarith
  · apply (div_le_iff₀ hp).mpr
    simpa using hlo

/-- Replacing the edge by its equal-weight pieces preserves its total weight. -/
theorem subdivision_weight_preserved {w : ℝ} (hw : 1 < w) :
    (subdivisionPieces w : ℝ) * (w / (subdivisionPieces w : ℝ)) = w := by
  have hp : (subdivisionPieces w : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (subdivisionPieces_pos hw)
  field_simp

/-- A heavy edge introduces strictly fewer than w new vertices. -/
theorem subdivision_new_vertices_lt {w : ℝ} (hw : 1 < w) :
    ((subdivisionPieces w - 1 : ℕ) : ℝ) < w := by
  have hp : 1 ≤ subdivisionPieces w := subdivisionPieces_pos hw
  rw [Nat.cast_sub hp]
  have hhi : (subdivisionPieces w : ℝ) < w + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  norm_num at *
  linarith

/-- Summing over heavy edges bounds the number of inserted vertices by the
original tree weight, even when the other tree edges are arbitrarily light. -/
theorem subdivision_vertex_budget {E : Type*} (edges : Finset E) (w : E → ℝ)
    (hw : ∀ e ∈ edges, 0 ≤ w e) :
    ((∑ e ∈ edges.filter (fun e => 1 < w e), (subdivisionPieces (w e) - 1)) : ℕ)
      ≤ ∑ e ∈ edges, w e := by
  classical
  have hpiece : ∀ e ∈ edges, (if 1 < w e then
      ((subdivisionPieces (w e) - 1 : ℕ) : ℝ) else 0) ≤ w e := by
    intro e he
    split_ifs with h
    · exact (subdivision_new_vertices_lt h).le
    · exact hw e he
  push_cast
  rw [Finset.sum_filter]
  exact Finset.sum_le_sum hpiece

/-- For a tree normalized to total weight n-1, subdivision inserts at most
n-1 vertices, hence the resulting vertex count is at most 2n-1. -/
theorem subdivision_normalized_vertex_count {E : Type*} (edges : Finset E)
    (w : E → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hw : ∀ e ∈ edges, 0 ≤ w e)
    (hweight : ∑ e ∈ edges, w e = (n : ℝ) - 1) :
    n + ∑ e ∈ edges.filter (fun e => 1 < w e),
      (subdivisionPieces (w e) - 1) ≤ 2 * n - 1 := by
  classical
  have h := subdivision_vertex_budget edges w hw
  rw [hweight] at h
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [← hcast] at h
  have hnat : (∑ e ∈ edges.filter (fun e => 1 < w e),
      (subdivisionPieces (w e) - 1)) ≤ n - 1 := by exact_mod_cast h
  omega

end LightSpanners
