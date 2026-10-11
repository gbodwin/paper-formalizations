import MinorFreeSpanners.LogarithmicDensityWitness

/-! Explicit polynomial-in-log(h) loss for the constructed density witness.
The logarithmic clique threshold is proved constructively in this project. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

def densityPolylogLoss (h : ℕ) : ℝ :=
  densityWitnessLoss h*(24576*(Nat.log 2 h+2):ℕ)^2

theorem densityStepWidth_le_log (h : ℕ) (hh : 0<h) :
    densityStepWidth h ≤ 131104*(Nat.log 2 h+2) := by
  have hc := cliqueDensityScale_cover_budget h (6*cliqueDensityScale h) (by omega)
  have hc' : h*(48*densityHorizon h) ≤ h*(4096*(Nat.log 2 h+2)) := by
    simpa only [densityHorizon,cliqueDensityScale,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hc
  have hx := Nat.le_of_mul_le_mul_left hc' hh
  unfold densityStepWidth
  omega

theorem densityPolylogLoss_bound (h : ℕ) (hh : 0<h) :
    densityPolylogLoss h ≤
      (1600000*(131104:ℝ)^7*24576^2)*((Nat.log 2 h+2:ℕ):ℝ)^9 := by
  have hw : (densityStepWidth h:ℝ) ≤ 131104*((Nat.log 2 h+2:ℕ):ℝ) := by
    exact_mod_cast densityStepWidth_le_log h hh
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (densityStepWidth h)) hw 7
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤1600000 by norm_num))
    (show 0≤(24576*((Nat.log 2 h+2:ℕ):ℝ))^2 by positivity)
  unfold densityPolylogLoss densityWitnessLoss
  push_cast at hm ⊢
  convert hm using 1; ring

theorem polylogarithmic_density_witness {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h : ℕ) (d : ℝ) (hh : 0<h)
    (hfree : CliqueMinorFree G h) (hn : 0 < Fintype.card V)
    (hd : (densityStepWidth h:ℝ)^3 ≤ d)
    (hE : d*(Fintype.card V:ℝ) ≤ (G.edgeFinset.card:ℝ)) :
    ∃ T : Finset V, 0 < ((G.induce (T:Set V)).edgeFinset.card:ℝ) ∧
      d*(T.card:ℝ) ≤ densityPolylogLoss h*(h:ℝ)^2 ∧
      d*(T.card:ℝ) ≤ densityPolylogLoss h*((G.induce (T:Set V)).edgeFinset.card:ℝ) := by
  classical
  obtain ⟨T,hpos,hsize,hden⟩ := logarithmic_density_witness G h d hh hfree hn hd hE
  have hL : 0≤densityWitnessLoss h := by unfold densityWitnessLoss; positivity
  have hc : (1:ℝ) ≤ (24576*(Nat.log 2 h+2):ℕ)^2 := by
    have hx : 1 ≤ 24576*(Nat.log 2 h+2) := by omega
    have hxR : (1:ℝ) ≤ (24576*(Nat.log 2 h+2):ℕ) := by exact_mod_cast hx
    exact one_le_pow₀ hxR
  have hloss : densityWitnessLoss h ≤ densityPolylogLoss h := by
    unfold densityPolylogLoss
    nlinarith only [mul_le_mul_of_nonneg_left hc hL]
  have heq : densityWitnessLoss h*(6*cliqueDensityScale h:ℕ)^2 = densityPolylogLoss h*(h:ℝ)^2 := by
    unfold densityPolylogLoss cliqueDensityScale
    push_cast
    ring
  exact ⟨T,hpos,by simpa only [heq] using hsize,
    hden.trans (mul_le_mul_of_nonneg_right hloss (Nat.cast_nonneg _))⟩

end MinorFreeSpanners
