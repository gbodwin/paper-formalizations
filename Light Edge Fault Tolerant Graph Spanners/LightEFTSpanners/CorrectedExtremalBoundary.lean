import LightEFTSpanners.ExactExtremalDefinition

/-! The corrected cloud lower bound includes stretch one, hence its extremal
parameter can equal two.  This file proves finiteness at that boundary directly
from actual cycles and tree paths, retaining the exact-order supremum. -/

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- A simple tree path uses each tree edge at most once. -/
theorem corrected_path_weight_le_tree {T : SimpleGraph V} {w : Sym2 V → ℝ}
    (hw : ∀ e ∈ T.edgeSet, 0 ≤ w e) {u v : V} (p : T.Walk u v)
    (hp : p.IsPath) : walkWeight w p ≤ totalWeight T w := by
  classical
  rw [walkWeight, ← List.sum_toFinset _ hp.isTrail.edges_nodup]
  exact sum_le_sum_of_subset_of_nonneg
    (fun e he => mem_edgeFinset.mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp he)))
    (fun e he _ => hw e (mem_edgeFinset.mp he))

/-- At weighted girth greater than or equal to two, every edge is no heavier
than a positive spanning tree.  The non-tree case uses its fundamental cycle. -/
theorem corrected_edge_weight_le_tree {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (hTG : T ≤ G) (hT : T.IsTree) (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    {g : ℝ} (hg : 2 ≤ g) (hG : WeightedGirthAbove G w g)
    {e : Sym2 V} (he : e ∈ G.edgeSet) : w e ≤ totalWeight T w := by
  classical
  by_cases heT : e ∈ T.edgeSet
  · exact single_le_sum (fun d hd => (hw d (edgeSet_mono hTG (mem_edgeFinset.mp hd))).le)
      (mem_edgeFinset.mpr heT)
  · induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : G.Adj u v := (mem_edgeSet G).mp he
      obtain ⟨p, hp⟩ := hT.connected.exists_isPath v u
      have hcyc : (Walk.cons huv (p.mapLe hTG)).IsCycle := by
        apply (Walk.cons_isCycle_iff _ _).mpr
        exact ⟨hp.mapLe hTG, fun h => heT (p.edges_subset_edgeSet (by simpa using h))⟩
      have hweight := hG u _ hcyc s(u,v) (by simp)
      simp only [walkWeight_cons, walkWeight_mapLe] at hweight
      have htwo : 2 * w s(u,v) ≤ g * w s(u,v) :=
        mul_le_mul_of_nonneg_right hg (hw _ he).le
      have hpweight := corrected_path_weight_le_tree
        (fun d hd => (hw d (edgeSet_mono hTG hd)).le) p hp
      linarith

/-- A coarse bound independent of the gap g-2, including g=2. -/
theorem corrected_lightness_le_edge_count {G T : SimpleGraph V} {w : Sym2 V → ℝ}
    (hT : IsMinimumSpanningTree G T w) (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    {g : ℝ} (hg : 2 ≤ g) (hG : WeightedGirthAbove G w g)
    (hn : 2 ≤ Fintype.card V) :
    lightness G T w ≤ (Fintype.card V).choose 2 := by
  have hpos : 0 < totalWeight T w := tree_totalWeight_pos hT.2.1 hn w
    (fun e he => hw e (edgeSet_mono hT.1 he))
  have hsum : totalWeight G w ≤ G.edgeFinset.card * totalWeight T w := by
    calc
      _ ≤ ∑ _e ∈ G.edgeFinset, totalWeight T w := sum_le_sum (fun e he =>
        corrected_edge_weight_le_tree hT.1 hT.2.1 hw hg hG (mem_edgeFinset.mp he))
      _ = _ := by simp
  have hcard : (G.edgeFinset.card : ℝ) ≤ (Fintype.card V).choose 2 := by
    exact_mod_cast G.card_edgeFinset_le_card_choose_two
  unfold lightness
  exact (div_le_iff₀ hpos).mpr
    (hsum.trans (mul_le_mul_of_nonneg_right hcard hpos.le))

/-- Finiteness of the exact-order extremal spectrum on the full g≥2 domain. -/
theorem corrected_lightnessSpectrum_bddAbove (n : ℕ) {g : ℝ} (hg : 2 ≤ g) :
    BddAbove (lightnessSpectrum n g) := by
  refine ⟨(n.choose 2 : ℝ), ?_⟩
  rintro x (rfl | ⟨G, T, w, hn, hT, hw, hG, rfl⟩)
  · positivity
  · simpa using corrected_lightness_le_edge_count hT hw hg hG (by simpa using hn)

theorem corrected_extremalLightness_nonneg (n : ℕ) {g : ℝ} (hg : 2 ≤ g) :
    0 ≤ extremalLightness n g :=
  le_csSup (corrected_lightnessSpectrum_bddAbove n hg) (Or.inl rfl)

/-- The same positive edge subdivision proves exact-order monotonicity at two. -/
theorem corrected_extremalLightness_mono {m n : ℕ} {g : ℝ}
    (hmn : m ≤ n) (hg : 2 ≤ g) :
    extremalLightness m g ≤ extremalLightness n g := by
  apply csSup_le (show (lightnessSpectrum m g).Nonempty from ⟨0, Or.inl rfl⟩)
  intro x hx
  exact le_csSup (corrected_lightnessSpectrum_bddAbove n hg)
    (lightnessSpectrum_mono hmn (by linarith) hx)

theorem corrected_lightness_le_extremal
    {G T : SimpleGraph V} {w : Sym2 V → ℝ} {g : ℝ} {n : ℕ}
    (hT : IsMinimumSpanningTree G T w) (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    (hG : WeightedGirthAbove G w g) (hg : 2 ≤ g)
    (hn : 2 ≤ Fintype.card V) (hcard : Fintype.card V ≤ n) :
    lightness G T w ≤ extremalLightness n g :=
  le_csSup (corrected_lightnessSpectrum_bddAbove n hg)
    (lightnessSpectrum_mono hcard (by linarith) (lightness_mem_spectrum hT hw hG hn rfl))

theorem corrected_extremalLightness_one_le {n : ℕ} {g : ℝ}
    (hn : 2 ≤ n) (hg : 2 ≤ g) : 1 ≤ extremalLightness n g := by
  obtain ⟨G, T, w, hT, hw, hG, heq⟩ := one_mem_actual_spectrum hn g
  exact le_csSup (corrected_lightnessSpectrum_bddAbove n hg)
    (Or.inr ⟨G, T, w, hn, hT, hw, hG, heq⟩)

/-- Every nontrivial exact order has an actual graph attaining more than half
the extremal lightness, with no attainment assumption for the supremum. -/
theorem corrected_exists_near_extremal {n : ℕ} {g : ℝ}
    (hn : 2 ≤ n) (hg : 2 ≤ g) :
    ∃ G T : SimpleGraph (Fin n), ∃ w : Sym2 (Fin n) → ℝ,
      IsMinimumSpanningTree G T w ∧ (∀ e ∈ G.edgeSet, 0 < w e) ∧
      WeightedGirthAbove G w g ∧ extremalLightness n g / 2 < lightness G T w := by
  have hpos : 0 < extremalLightness n g := lt_of_lt_of_le (by norm_num)
    (corrected_extremalLightness_one_le hn hg)
  obtain ⟨x, hx, hlt⟩ := exists_lt_of_lt_csSup
    (show (lightnessSpectrum n g).Nonempty from ⟨0, Or.inl rfl⟩)
    (show extremalLightness n g / 2 < extremalLightness n g by linarith)
  rcases hx with rfl | ⟨G, T, w, _, hT, hw, hG, rfl⟩
  · linarith
  · exact ⟨G, T, w, hT, hw, hG, hlt⟩

end LightEFTSpanners
