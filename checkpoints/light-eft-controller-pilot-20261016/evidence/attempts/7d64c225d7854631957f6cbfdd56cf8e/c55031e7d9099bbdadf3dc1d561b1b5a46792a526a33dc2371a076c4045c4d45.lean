import LightEFTSpanners.ExtremalLightnessSpectrum

namespace LightEFTSpanners
open SimpleGraph Finset LightSpanners
attribute [local instance] Classical.propDecidable

/-- The literal exact-n positive-weight graph spectrum from Definition15,
with an actual minimum spanning tree supplying the normalization. -/
def actualLightnessSpectrum (n : ℕ) (g : ℝ) : Set ℝ :=
  {x | ∃ G T : SimpleGraph (Fin n), ∃ w : Sym2 (Fin n) → ℝ,
    IsMinimumSpanningTree G T w ∧ (∀ e∈G.edgeSet,0<w e) ∧
    WeightedGirthAbove G w g ∧ x=lightness G T w}

/-- A genuine unit-weight tree witnesses lightness one at every order n≥2. -/
theorem one_mem_actual_spectrum {n : ℕ} (hn : 2≤n) (g : ℝ) :
    1∈actualLightnessSpectrum n g := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨T,_,hT,_⟩ := exists_bottleneck_spanning_tree (⊤ : SimpleGraph (Fin n))
    (fun _ => 1) connected_top
  have hm : IsMinimumSpanningTree T T (fun _ => 1) :=
    minimumSpanningTree_of_bottleneck hT le_rfl (by
      intro u v huv
      exact ⟨huv.toWalk,by simp⟩)
  have hp := tree_totalWeight_pos hT (by simpa using hn) (fun _ => (1:ℝ)) (by simp)
  refine ⟨T,T,fun _ => 1,hm,by simp,?_,?_⟩
  · intro a p hc
    exact (hT.isAcyclic p hc).elim
  · simp [lightness,ne_of_gt hp]

/-- On the used domain n≥2 and g>2, the totalized definition is exactly the
supremum over actual n-vertex graphs, not an at-most-n envelope. -/
theorem extremalLightness_eq_actual_sup {n : ℕ} {g : ℝ} (hn : 2≤n) (hg : 2<g) :
    extremalLightness n g=sSup (actualLightnessSpectrum n g) := by
  have hsub : actualLightnessSpectrum n g⊆lightnessSpectrum n g := by
    rintro x ⟨G,T,w,hT,hw,hG,heq⟩
    exact Or.inr ⟨G,T,w,hn,hT,hw,hG,heq⟩
  have hbd := (lightnessSpectrum_bddAbove n hg).mono hsub
  have h1 := one_mem_actual_spectrum hn g
  apply le_antisymm
  · apply csSup_le (show (lightnessSpectrum n g).Nonempty from ⟨0,Or.inl rfl⟩)
    intro x hx
    rcases hx with rfl | ⟨G,T,w,_,hT,hw,hG,heq⟩
    · exact (by norm_num : (0:ℝ)≤1).trans (le_csSup hbd h1)
    · exact le_csSup hbd ⟨G,T,w,hT,hw,hG,heq⟩
  · apply csSup_le ⟨1,h1⟩
    intro x hx
    exact le_csSup (lightnessSpectrum_bddAbove n hg) (hsub hx)

/-- The actual extremal quantity also has the established coarse upper bound. -/
theorem extremalLightness_corrected_coarse_bound (n : ℕ) {eps : ℝ} {k : ℕ}
    (heps : 0<eps) (hk : 0<k) :
    extremalLightness n ((1+eps)*(2*k-1)+1) ≤
      8+2048/eps*(n:ℝ)^((k:ℝ)⁻¹) := by
  apply csSup_le (show (lightnessSpectrum n ((1+eps)*(2*k-1)+1)).Nonempty from ⟨0,Or.inl rfl⟩)
  intro x hx
  rcases hx with rfl | ⟨G,T,w,_,hT,hw,hG,rfl⟩
  · positivity
  · simpa using corrected_threshold_lightness hT hw heps hk hG
/-- Nonempty unit trees prevent a bound that vanishes as epsilon grows.
This is a uniform-constant statement, not a contradiction to O_epsilon bounds. -/
theorem no_uniform_inverse_epsilon_extremal_bound :
    ¬∃ C : ℝ,∀ eps : ℝ,0<eps → extremalLightness 2 ((1+eps)*2)≤C/eps*2 := by
  rintro ⟨C,hC⟩
  let eps := 2*|C|+1
  have heps : 0<eps := by dsimp [eps];positivity
  have hg : 2<(1+eps)*2 := by nlinarith
  obtain ⟨G,T,w,hT,hw,hG,heq⟩ := one_mem_actual_spectrum (show 2≤2 by omega) ((1+eps)*2)
  have h1 : (1:ℝ)≤extremalLightness 2 ((1+eps)*2) :=
    le_csSup (lightnessSpectrum_bddAbove 2 hg) (Or.inr ⟨G,T,w,by omega,hT,hw,hG,heq⟩)
  have hh := (mul_le_mul_of_nonneg_right (h1.trans (hC eps heps)) heps.le)
  have hc : C/eps*2*eps=2*C := by
    calc
      _ = (2*C)*(eps/eps) := by ring
      _ = _ := by rw [div_self (ne_of_gt heps),mul_one]
  rw [hc] at hh
  have habs := le_abs_self C
  dsimp [eps] at hh
  nlinarith
end LightEFTSpanners
