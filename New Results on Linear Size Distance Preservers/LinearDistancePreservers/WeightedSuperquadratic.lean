import LinearDistancePreservers.TheoremThreeExact
import Mathlib.Analysis.Asymptotics.Defs

namespace LinearDistancePreservers.TheoremThree
open SimpleGraph Finset WeightedDigraph Filter Asymptotics
open scoped NNReal ENNReal Topology
attribute [local instance] Classical.propDecidable

/-- Cubing loses no information for the nonnegative edge count. -/
theorem cube_forces_quadratic_factor {N T E A : ℝ}
    (hT : 0 < T) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hcap : (32768*A*T)^3 ≤ N^2)
    (hbound : T^3*N^2 ≤ 32768^3*E^3) : A*T^2 ≤ E := by
  have hc : (32768*(A*T^2))^3 ≤ (32768*E)^3 := by
    calc
      _ = T^3*(32768*A*T)^3 := by ring
      _ ≤ T^3*N^2 := mul_le_mul_of_nonneg_left hcap (by positivity)
      _ ≤ 32768^3*E^3 := hbound
      _ = _ := by ring
  have hh := (pow_le_pow_iff_left₀ (by positivity : 0 ≤ 32768*(A*T^2))
    (by positivity : 0 ≤ 32768*E) (by decide : (3 : ℕ) ≠ 0)).mp hc
  nlinarith only [hh]

/-- An explicit factor chosen before the exact vertex and terminal counts.
This is the finite quantitative form of the weighted superquadratic corollary. -/
theorem superquadratic_weighted_finite (B : ℝ) {N T : ℕ}
    (hT : 2 ≤ T) (hTN : T ≤ N)
    (hcap : (T : ℝ) ≤ (N : ℝ)^((2 : ℝ)/3)/(32768*(max B 0+1))) :
    ∃ (G : SimpleGraph (Fin N)) (w : Fin N → Fin N → ℝ≥0) (S : Finset (Fin N)),
      S.card=T ∧ (∀ u v, G.Adj u v → 0 < w u v ∧ w u v=w v u) ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S,
          distance H.Adj (fun u v => (w u v : ℝ≥0∞)) s t =
            distance G.Adj (fun u v => (w u v : ℝ≥0∞)) s t) →
        B*(T : ℝ)^2 < (H.edgeFinset.card : ℝ) := by
  let A := max B 0+1
  have hA : 1 ≤ A := by dsimp [A]; linarith [le_max_right B 0]
  have hAB : B < A := by dsimp [A]; linarith [le_max_left B 0]
  have hTp : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hc : 32768*A*(T : ℝ) ≤ (N : ℝ)^((2 : ℝ)/3) := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ)<32768*A)).mp hcap
    nlinarith only [h]
  have hpower : ((N : ℝ)^((2 : ℝ)/3))^3 = (N : ℝ)^2 := by
    rw [← Real.rpow_mul_natCast hN0]
    norm_num
  have hc3 : (32768*A*(T : ℝ))^3 ≤ (N : ℝ)^2 := by
    rw [← hpower]
    gcongr
  have hr : T^3 ≤ N^2 := by
    have hbase : (T : ℝ) ≤ 32768*A*T := by nlinarith
    have hh : (T : ℝ)^3 ≤ (N : ℝ)^2 := (pow_le_pow_left₀ hTp.le hbase 3).trans hc3
    exact_mod_cast hh
  obtain ⟨G,w,S,hS,hw,hg⟩ := bounded_range_lower_bound (C := 1) (by decide) hT hTN
    (by simpa using hr)
  refine ⟨G,w,S,hS,hw,?_⟩
  intro H hH hp
  have hb : (T : ℝ)^3*(N : ℝ)^2 ≤ (32768 : ℝ)^3*(H.edgeFinset.card : ℝ)^3 := by
    exact_mod_cast hg H hH hp
  have hh := cube_forces_quadratic_factor hTp (Nat.cast_nonneg _) (by linarith : 0 ≤ A) hc3 hb
  have ht2 : 0 < (T : ℝ)^2 := by positivity
  exact (mul_lt_mul_of_pos_right hAB ht2).trans_le hh

/-- For every terminal-count sequence of little-o size N^(2/3), every
fixed real factor is eventually exceeded, uniformly over all preservers
of the actual exact-size weighted witnesses. -/
theorem superquadratic_weighted_little_o (T : ℕ → ℕ)
    (hT : ∀ᶠ N in atTop, 2 ≤ T N) (hTN : ∀ᶠ N in atTop, T N ≤ N)
    (hsmall : (fun N : ℕ => (T N : ℝ)) =o[atTop]
      (fun N : ℕ => (N : ℝ)^((2 : ℝ)/3))) (B : ℝ) :
    ∀ᶠ N in atTop,
      ∃ (G : SimpleGraph (Fin N)) (w : Fin N → Fin N → ℝ≥0) (S : Finset (Fin N)),
        S.card=T N ∧ (∀ u v, G.Adj u v → 0 < w u v ∧ w u v=w v u) ∧
        ∀ H : SimpleGraph (Fin N), H ≤ G →
          (∀ s ∈ S, ∀ t ∈ S,
            distance H.Adj (fun u v => (w u v : ℝ≥0∞)) s t =
              distance G.Adj (fun u v => (w u v : ℝ≥0∞)) s t) →
          B*(T N : ℝ)^2 < (H.edgeFinset.card : ℝ) := by
  have hc : (0 : ℝ) < 1/(32768*(max B 0+1)) := by positivity
  filter_upwards [hT,hTN,hsmall.def hc] with N hT hTN hs
  apply superquadratic_weighted_finite B hT hTN
  simp only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (T N) : (0 : ℝ) ≤ T N),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) ((2 : ℝ)/3))] at hs
  simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hs

end LinearDistancePreservers.TheoremThree
