import LightEFTSpanners.ExtremalLightnessSpectrum

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
variable {V : Type*}
attribute [local instance] Classical.propDecidable

/-- Strict nonnegative weighted girth forces every cycle length above the same
threshold. Zero-weight cycles cannot satisfy the strict premise. -/
theorem nonnegative_cycle_length {G : SimpleGraph V} {w : Sym2 V → ℝ} {g : ℝ}
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) (hg : WeightedGirthAbove G w g)
    {u : V} (p : G.Walk u u) (hp : p.IsCycle) : g < (p.length : ℝ) := by
  obtain ⟨e,he,hmax⟩ := exists_max_cycle_edge w p hp
  have hle := walkWeight_le_length_mul p w (w e) hmax
  have hlt := hg u p hp e he
  have h0 := hw e (p.edges_subset_edgeSet he)
  have hpos : 0 < w e := by
    by_contra hn
    have hz : w e = 0 := le_antisymm (le_of_not_gt hn) h0
    rw [hz] at hlt hle
    linarith
  nlinarith

theorem walkWeight_add_constant {G : SimpleGraph V} (w : Sym2 V → ℝ) (d : ℝ)
    {u v : V} (p : G.Walk u v) :
    walkWeight (fun e => w e + d) p = walkWeight w p + p.length*d := by
  induction p with
  | nil => simp
  | cons h p ih => simp only [walkWeight_cons,ih,Walk.length_cons,Nat.cast_add,Nat.cast_one]; ring

/-- The same positive perturbation preserves girth for all cycles at once. -/
theorem nonnegative_girth_add_constant {G : SimpleGraph V} {w : Sym2 V → ℝ} {g : ℝ}
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) (hg : WeightedGirthAbove G w g)
    (d : ℝ) (hd : 0 ≤ d) : WeightedGirthAbove G (fun e => w e + d) g := by
  intro u p hp e he
  have h := hg u p hp e he
  have hl := nonnegative_cycle_length hw hg p hp
  rw [walkWeight_add_constant]
  nlinarith

/-- An elementary vanishing-perturbation step, with no division by a zero tree. -/
theorem le_of_positive_linear_perturbation {a b c : ℝ}
    (h : ∀ d : ℝ, 0 < d → a ≤ b + d*c) : a ≤ b := by
  by_contra hn
  have hgap : 0 < a-b := sub_pos.mpr (lt_of_not_ge hn)
  by_cases hc : c ≤ 0
  · have hh := h 1 (by norm_num); nlinarith
  · have hc' : 0 < c := lt_of_not_ge hc
    have hd : 0 < (a-b)/(2*c) := div_pos hgap (by positivity)
    have hh := h _ hd
    have heq : ((a-b)/(2*c))*(2*c) = a-b := div_mul_cancel₀ _ (by positivity)
    nlinarith

/-- The established positive-weight extremal theorem extends to nonnegative
weights and any retained spanning tree. Singleton and zero-total-tree cases are
included; an actual positive MST is constructed separately for each perturbation. -/
theorem nonnegative_extremal_tree_bound [Fintype V] {G T : SimpleGraph V}
    {w : Sym2 V → ℝ} {g : ℝ} {n : ℕ} (hTG : T ≤ G) (hT : T.IsTree)
    (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) (hgirth : WeightedGirthAbove G w g)
    (hg : 2 < g) (hcard : Fintype.card V ≤ n) :
    totalWeight G w ≤ extremalLightness n g * totalWeight T w := by
  classical
  have hL := extremalLightness_nonneg n hg
  by_cases hn : 2 ≤ Fintype.card V
  · have hbound : ∀ d : ℝ, 0 < d → totalWeight G w ≤
        extremalLightness n g * totalWeight T w + d *
          (extremalLightness n g * T.edgeFinset.card) := by
      intro d hd
      let wd := fun e => w e + d
      have hwd : ∀ e ∈ G.edgeSet, 0 < wd e := fun e he => by dsimp [wd]; linarith [hw e he]
      obtain ⟨K,hKG,hK,hbot⟩ := exists_bottleneck_spanning_tree G wd (hT.connected.mono hTG)
      have hmin := minimumSpanningTree_of_bottleneck hK hKG hbot
      have hKpos := tree_totalWeight_pos hK hn wd (fun e he => hwd e (edgeSet_mono hKG he))
      have hlight := lightness_le_extremal hmin hwd
        (nonnegative_girth_add_constant hw hgirth d hd.le) hg hn hcard
      have hmul : totalWeight G wd ≤ extremalLightness n g * totalWeight K wd :=
        (div_le_iff₀ hKpos).mp hlight
      have hupper := hmul.trans (mul_le_mul_of_nonneg_left (hmin.2.2 T hTG hT) hL)
      have hGsum : totalWeight G wd = totalWeight G w + G.edgeFinset.card*d := by
        simp [totalWeight,wd,sum_add_distrib,mul_comm]
      have hTsum : totalWeight T wd = totalWeight T w + T.edgeFinset.card*d := by
        simp [totalWeight,wd,sum_add_distrib,mul_comm]
      rw [hGsum,hTsum] at hupper
      have hcount : 0 ≤ (G.edgeFinset.card : ℝ) := by positivity
      nlinarith
    exact le_of_positive_linear_perturbation hbound
  · have hc : Fintype.card V ≤ 1 := by omega
    let : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hc
    have hGb : G = ⊥ := by
      ext u v
      simp [Subsingleton.elim u v]
    have hTb : T = ⊥ := le_bot_iff.mp (hGb ▸ hTG)
    subst G
    subst T
    simp [totalWeight]

end LightEFTSpanners
