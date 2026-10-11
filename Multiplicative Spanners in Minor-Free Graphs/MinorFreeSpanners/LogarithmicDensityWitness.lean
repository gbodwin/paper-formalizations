import MinorFreeSpanners.BalancedCliqueWitness

/-! Internally chosen logarithmic horizon and increment width. The final
witness is an actual induced subgraph of the input, with explicit constants. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

def densityHorizon (h : ℕ) : ℕ := Nat.log 2 (6*cliqueDensityScale h)+1
def densityStepWidth (h : ℕ) : ℕ := 32*(densityHorizon h+1)
def densityWitnessLoss (h : ℕ) : ℝ := 1600000*(densityStepWidth h:ℝ)^7

theorem logarithmic_density_witness {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h : ℕ) (d : ℝ) (hh : 0<h)
    (hfree : CliqueMinorFree G h) (hn : 0 < Fintype.card V)
    (hd : (densityStepWidth h:ℝ)^3 ≤ d)
    (hE : d*(Fintype.card V:ℝ) ≤ (G.edgeFinset.card:ℝ)) :
    ∃ T : Finset V, 0 < ((G.induce (T:Set V)).edgeFinset.card:ℝ) ∧
      d*(T.card:ℝ) ≤ densityWitnessLoss h*(6*cliqueDensityScale h:ℕ)^2 ∧
      d*(T.card:ℝ) ≤ densityWitnessLoss h*((G.induce (T:Set V)).edgeFinset.card:ℝ) := by
  have hk : 32≤densityStepWidth h := by unfold densityStepWidth; omega
  have hkR : (32:ℝ)≤densityStepWidth h := by exact_mod_cast hk
  have hd1 : 1≤d := by
    have hp : (1:ℝ)≤(densityStepWidth h:ℝ)^3 := one_le_pow₀ (by linarith)
    exact hp.trans hd
  have hpow : (6*cliqueDensityScale h:ℕ) < 2^(densityHorizon h) :=
    Nat.lt_pow_succ_log_self (by omega) _
  have hpowR : (6*cliqueDensityScale h:ℕ) < (2:ℝ)^(densityHorizon h) := by exact_mod_cast hpow
  have hmul := mul_le_mul_of_nonneg_left hd1 (show 0≤(2:ℝ)^(densityHorizon h) by positivity)
  have horizon : (6*cliqueDensityScale h:ℕ) < (2:ℝ)^(densityHorizon h)*d := by
    nlinarith only [hpowR,hmul]
  exact balanced_clique_density_witness G (densityStepWidth h) h (densityHorizon h) d hk hh
    hfree hn hd hE (by unfold densityStepWidth; omega) horizon

end MinorFreeSpanners
