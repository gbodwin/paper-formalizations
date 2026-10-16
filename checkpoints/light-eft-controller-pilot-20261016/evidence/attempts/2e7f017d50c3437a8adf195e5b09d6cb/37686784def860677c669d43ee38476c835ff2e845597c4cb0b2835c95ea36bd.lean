import LightSpanners.MinimumTree
import LightSpanners.Girth

namespace LightSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

theorem totalWeight_mono_weights (G : SimpleGraph V) {w w' : Sym2 V → ℝ}
    (h : ∀ e ∈ G.edgeSet, w e ≤ w' e) : totalWeight G w ≤ totalWeight G w' := by
  apply sum_le_sum
  intro e he
  exact h e (by simpa using he)

theorem totalWeight_scale (G : SimpleGraph V) (w : Sym2 V → ℝ) (c : ℝ) :
    totalWeight G (fun e => c * w e) = c * totalWeight G w := by
  simp only [totalWeight, mul_sum]

theorem totalWeight_eq_card_mul (G : SimpleGraph V) (w : Sym2 V → ℝ) (c : ℝ)
    (h : ∀ e ∈ G.edgeSet, w e = c) : totalWeight G w = G.edgeFinset.card * c := by
  unfold totalWeight
  calc
    _ = ∑ _e ∈ G.edgeFinset, c := sum_congr rfl (fun e he => h e (by simpa using he))
    _ = _ := by simp

theorem card_mul_le_totalWeight (G : SimpleGraph V) (w : Sym2 V → ℝ) (c : ℝ)
    (h : ∀ e ∈ G.edgeSet, c ≤ w e) : G.edgeFinset.card * c ≤ totalWeight G w := by
  calc
    _ = totalWeight G (fun _ => c) := (totalWeight_eq_card_mul G _ c (by simp)).symm
    _ ≤ _ := totalWeight_mono_weights G h

theorem totalWeight_round_up_le_double (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (h : ∀ e ∈ G.edgeSet, (1 : ℝ) / 2 ≤ w e) :
    totalWeight G (fun e => max 1 (w e)) ≤ 2 * totalWeight G w := by
  rw [← totalWeight_scale]
  apply totalWeight_mono_weights
  intro e he
  have hh := h e he
  exact max_le (by linarith) (by linarith)

theorem IsMinimumSpanningTree.weight_eq {G S T : SimpleGraph V} {w : Sym2 V → ℝ}
    (hS : IsMinimumSpanningTree G S w) (hT : IsMinimumSpanningTree G T w) :
    totalWeight S w = totalWeight T w :=
  le_antisymm (hS.2.2 T hT.1 hT.2.1) (hT.2.2 S hS.1 hS.2.1)

noncomputable def lightness (G T : SimpleGraph V) (w : Sym2 V → ℝ) : ℝ :=
  totalWeight G w / totalWeight T w

theorem lightness_mst_independent {G S T : SimpleGraph V} {w : Sym2 V → ℝ}
    (hS : IsMinimumSpanningTree G S w) (hT : IsMinimumSpanningTree G T w) :
    lightness G S w = lightness G T w := by
  simp only [lightness, hS.weight_eq hT]

theorem lightness_scale (G T : SimpleGraph V) (w : Sym2 V → ℝ) {c : ℝ} (hc : 0 < c) :
    lightness G T (fun e => c * w e) = lightness G T w := by
  simp only [lightness, totalWeight_scale]
  exact mul_div_mul_left _ _ hc.ne'

theorem IsMinimumSpanningTree.scale {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (h : IsMinimumSpanningTree G T w) {c : ℝ} (hc : 0 < c) :
    IsMinimumSpanningTree G T (fun e => c * w e) := by
  refine ⟨h.1, h.2.1, fun S hSG hS => ?_⟩
  simp only [totalWeight_scale]
  exact mul_le_mul_of_nonneg_left (h.2.2 S hSG hS) hc.le

end LightSpanners
