import LinearDistancePreservers.BalancedRadius
import LinearDistancePreservers.BalancedCoefficient
import LinearDistancePreservers.SphereTheorem
import LinearDistancePreservers.SphereComparison
import LinearDistancePreservers.GrowingDimension
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LinearDistancePreservers.TheoremFourGeneral

theorem absorb_exp_budget {P E K a b x : ℝ} (hE : 0≤E)
    (hK : K≤Real.exp (b*x)) (h : P*Real.exp (-a*x)≤K*E) :
    P*Real.exp (-(a+b)*x)≤E := by
  calc
    _ = (P*Real.exp (-a*x))*Real.exp (-b*x) := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ (K*E)*Real.exp (-b*x) := mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
    _ ≤ (Real.exp (b*x)*E)*Real.exp (-b*x) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK hE) (Real.exp_nonneg _)
    _ = E := by
      rw [mul_right_comm,← Real.exp_add,show b*x+(-b*x)=0 by ring,Real.exp_zero,one_mul]

end LinearDistancePreservers.TheoremFourGeneral

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Dimension-dependent bound from the balanced lattice geometry. -/
theorem balanced_displayed_lower_bound {N T : ℕ} (n : ℕ)
    (hT : 2≤T) (hTN : T≤N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card=T ∧
      ∀ H : SimpleGraph (Fin N), H≤G →
        (∀ s∈S, ∀ t∈S, H.edist s t=G.edist s t) →
        (N : ℝ)^((2 : ℝ)/(n+4)) *
          (T : ℝ)^((((2*(n+3)+1)*(n+2) : ℕ) : ℝ)/(((n+3)*(n+4) : ℕ) : ℝ)) *
          Real.exp (-4*Real.sqrt (Real.log N)) ≤
          ((n+3 : ℕ) : ℝ)^(1000*(n+3)^2)*(H.edgeFinset.card : ℝ) := by
  have hv := (LatticeHull.balanced_radius_vertices n).2
  obtain ⟨G,S,hS,hE⟩ := HigherProduct.displayed_lower_bound_root
    (C := LatticeHull.balancedRadius n) (d := n+3) (by omega)
    (by simpa [add_assoc] using hv) hT hTN
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  have hr := (hE H hH hp).trans (mul_le_mul_of_nonneg_right
    (HigherProduct.balanced_rateFactor_root_dimension_bound (by omega)
      (LatticeHull.balancedRadius_bound n)) (by positivity))
  have hn : (0 : ℝ)<(n+3 : ℕ) := by positivity
  have hc : 4*((n+3-1 : ℕ) : ℝ)/(n+3 : ℕ)≤4 := by
    apply (div_le_iff₀ hn).mpr
    have hh : ((n+3-1 : ℕ) : ℝ)≤(n+3 : ℕ) := by exact_mod_cast Nat.sub_le (n+3) 1
    linarith
  have hloss : Real.exp (-4*Real.sqrt (Real.log N))≤
      Real.exp (-(4*((n+3-1 : ℕ) : ℝ)/(n+3 : ℕ))*Real.sqrt (Real.log N)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (Real.log (N : ℝ)))
    linarith
  have hh := (mul_le_mul_of_nonneg_left hloss
    (by positivity : (0 : ℝ)≤(N : ℝ)^(2/((n+3 : ℕ)+1 : ℝ))*
      (T : ℝ)^((((2*(n+3)+1)*(n+3-1) : ℕ) : ℝ)/(((n+3)*((n+3)+1) : ℕ) : ℝ)))).trans hr
  convert hh using 1 <;> norm_num [Nat.cast_add,Nat.cast_ofNat,add_assoc]

/-- The balanced coefficient is absorbed uniformly in the small-dimension
regime. The dimension is an input, not a fixed hidden constant. -/
theorem balanced_uniform_lower_bound {N T : ℕ} (n : ℕ)
    (hT : 2≤T) (hTN : T≤N)
    (hbudget : ((n+3 : ℕ) : ℝ)^3≤Real.sqrt (Real.log N)) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card=T ∧
      ∀ H : SimpleGraph (Fin N), H≤G →
        (∀ s∈S, ∀ t∈S, H.edist s t=G.edist s t) →
        (N : ℝ)^((2 : ℝ)/(n+4)) *
          (T : ℝ)^((((2*(n+3)+1)*(n+2) : ℕ) : ℝ)/(((n+3)*(n+4) : ℕ) : ℝ)) *
          Real.exp (-1004*Real.sqrt (Real.log N)) ≤ (H.edgeFinset.card : ℝ) := by
  obtain ⟨G,S,hS,hE⟩ := balanced_displayed_lower_bound n hT hTN
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  have hd0 : (0 : ℝ)<(n+3 : ℕ) := by positivity
  have hl : Real.log ((n+3 : ℕ) : ℝ)≤((n+3 : ℕ) : ℝ) :=
    (Real.log_le_sub_one_of_pos hd0).trans (by linarith)
  have hcoef : (((n+3 : ℕ) : ℝ)^(1000*(n+3)^2))≤
      Real.exp (1000*Real.sqrt (Real.log N)) := by
    rw [← Real.exp_log hd0,← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hl
      (by positivity : (0 : ℝ)≤1000*(((n+3 : ℕ) : ℝ))^2)
    push_cast at hh hbudget ⊢
    nlinarith only [hh,hbudget]
  have hh := absorb_exp_budget (a := 4) (b := 1000)
    (x := Real.sqrt (Real.log N)) (by positivity) hcoef (hE H hH hp)
  norm_num at hh ⊢
  exact hh

end LinearDistancePreservers.TheoremFourGeneral

namespace LinearDistancePreservers.SphereScales
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Large dimensions are handled by the elementary-sphere construction.
The upper dimension constant A remains explicit in the exponential loss. -/
theorem uniform_large_dimension {N T d : ℕ} {A : ℝ} (hd : 3≤d)
    (hT : 2≤T) (hTN : 2*T≤N)
    (hcap : Real.log (T : ℝ)≤(2/3)*Real.log N)
    (hlarge : Real.sqrt (Real.log N)≤(d : ℝ)^3)
    (hupper : (d : ℝ)≤A*Real.sqrt (Real.log N)) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card=T ∧
      ∀ H : SimpleGraph (Fin N), H≤G →
        (∀ s∈S, ∀ t∈S, H.edist s t=G.edist s t) →
        (N : ℝ)^((2 : ℝ)/(d+1)) *
          (T : ℝ)^((((2*d+1)*(d-1) : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ)) *
          Real.exp (-(8+7*A)*Real.sqrt (Real.log N)) ≤ (H.edgeFinset.card : ℝ) := by
  have hdR : (3 : ℝ)≤d := by exact_mod_cast hd
  have hN1 : (1 : ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hT0 : (0 : ℝ)<T := by positivity
  have hcompare := SphereRate.polynomial_le_sphere hdR hN1 hT0 hcap hlarge
  obtain ⟨G,S,hS,hE⟩ := exact_size_lower_bound hd hT hTN
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  have hraw := hE H hH hp
  have hcoef : (sphereFactor d : ℝ)≤Real.exp ((7*A)*Real.sqrt (Real.log N)) :=
    (sphereFactor_le_exp hd).trans (Real.exp_le_exp.mpr (by nlinarith only [hupper]))
  have hraw' : (N : ℝ)^((2*(d : ℝ)-2)/((d : ℝ)^2-2))*
      (T : ℝ)^((2*(d : ℝ)+1)*((d : ℝ)-2)/((d : ℝ)^2-2))*
      Real.exp (-4*Real.sqrt (Real.log N)) ≤ (sphereFactor d : ℝ)*(H.edgeFinset.card : ℝ) := by
    simpa only [Nat.cast_sub (show 2≤2*d by omega),Nat.cast_sub (show 2≤d^2 by nlinarith),
      Nat.cast_sub (show 2≤d by omega),Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hraw
  have habsorb := TheoremFourGeneral.absorb_exp_budget (a := 4) (b := 7*A)
    (x := Real.sqrt (Real.log N)) (by positivity) hcoef hraw'
  have hh := (mul_le_mul_of_nonneg_right hcompare
    (Real.exp_nonneg (-(8+7*A)*Real.sqrt (Real.log N)))).trans_eq
    (show _ = ((N : ℝ)^((2*(d : ℝ)-2)/((d : ℝ)^2-2))*
      (T : ℝ)^((2*(d : ℝ)+1)*((d : ℝ)-2)/((d : ℝ)^2-2)))*
        Real.exp (-(4+7*A)*Real.sqrt (Real.log N)) by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring)
  have hfinal := hh.trans habsorb
  simpa only [Nat.cast_sub (show 1≤d by omega),Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hfinal

end LinearDistancePreservers.SphereScales

namespace LinearDistancePreservers.TheoremFourGeneral

theorem terminal_half_of_cap {N T : ℕ} (hN : 8≤N)
    (hcap : (T : ℝ)≤(N : ℝ)^((2 : ℝ)/3)) : 2*T≤N := by
  have hN0 : (0 : ℝ)≤N := Nat.cast_nonneg N
  have hc := pow_le_pow_left₀ (Nat.cast_nonneg T) hcap 3
  rw [← Real.rpow_mul_natCast hN0] at hc
  norm_num at hc
  have hn8 : (8 : ℝ)≤N := by exact_mod_cast hN
  have hn := mul_nonneg (sub_nonneg.mpr hn8) (sq_nonneg (N : ℝ))
  have hp : (2*(T : ℝ))^3≤(N : ℝ)^3 := by nlinarith only [hc,hn]
  have hh := (pow_le_pow_iff_left₀ (by positivity : (0 : ℝ)≤2*T)
    hN0 (by decide : (3 : ℕ)≠0)).mp hp
  exact_mod_cast hh

theorem log_cap_of_power {N T : ℕ} (hN : 0<N) (hT : 0<T)
    (hcap : (T : ℝ)≤(N : ℝ)^((2 : ℝ)/3)) :
    Real.log (T : ℝ)≤(2/3)*Real.log N := by
  have hh := Real.log_le_log (by exact_mod_cast hT) hcap
  rwa [Real.log_rpow (by exact_mod_cast hN)] at hh

theorem one_le_sqrt_log {N : ℕ} (hN : 8≤N) : 1≤Real.sqrt (Real.log N) := by
  have hn : (0 : ℝ)<N := by positivity
  have he : Real.exp 1≤(N : ℝ) := Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3≤N by omega))
  have hl : (1 : ℝ)≤Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  simpa using Real.sqrt_le_sqrt hl

end LinearDistancePreservers.TheoremFourGeneral

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem weaken_exp_loss {P E a b x : ℝ} (hP : 0≤P) (hx : 0≤x)
    (hab : a≤b) (h : P*Real.exp (-a*x)≤E) : P*Real.exp (-b*x)≤E := by
  apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hP).trans h
  have hh := mul_le_mul_of_nonneg_right hab hx
  linarith

/-- A uniform version of the displayed lower bound for every dimension
up to an arbitrary fixed multiple of sqrt(log N). The absolute constants
are explicit; the stronger printed near-threshold existential corollary
is a separate statement and is not inferred here. -/
theorem uniform_dimension_lower_bound {N T d : ℕ} {A : ℝ}
    (hA : 0≤A) (hN : 8≤N) (hT : 2≤T)
    (hcap : (T : ℝ)≤(N : ℝ)^((2 : ℝ)/3))
    (hd : 2≤d) (hdN : (d : ℝ)≤A*Real.sqrt (Real.log N)) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card=T ∧
      ∀ H : SimpleGraph (Fin N), H≤G →
        (∀ s∈S, ∀ t∈S, H.edist s t=G.edist s t) →
        (N : ℝ)^((2 : ℝ)/(d+1)) *
          (T : ℝ)^((((2*d+1)*(d-1) : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ)) *
          Real.exp (-(1004+7*A)*Real.sqrt (Real.log N)) ≤ (H.edgeFinset.card : ℝ) := by
  have hhalf := terminal_half_of_cap hN hcap
  have hTN : T≤N := by omega
  have hx0 := Real.sqrt_nonneg (Real.log (N : ℝ))
  by_cases hd2 : d=2
  · subst d
    obtain ⟨G,S,hS,hE⟩ := TheoremFourPlanar.displayed_lower_bound hT hTN
    refine ⟨G,S,hS,?_⟩
    intro H hH hp
    have htwo : (2 : ℝ)≤Real.exp 1 := by have hh := Real.add_one_le_exp (1 : ℝ); norm_num at hh; exact hh
    have hk : (100663296 : ℝ)≤Real.exp 27 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) htwo 27
      rw [← Real.exp_nat_mul] at hh
      norm_num at hh
      linarith
    have hcoef : (100663296 : ℝ)≤Real.exp (27*Real.sqrt (Real.log N)) :=
      hk.trans (Real.exp_le_exp.mpr (by have hh := one_le_sqrt_log hN; linarith))
    have hh := absorb_exp_budget (a := 2) (b := 27)
      (x := Real.sqrt (Real.log N)) (by positivity) hcoef (hE H hH hp)
    have hw := weaken_exp_loss (by positivity) hx0 (show (2 : ℝ)+27≤1004+7*A by linarith) hh
    norm_num at hw ⊢
    exact hw
  · have hd3 : 3≤d := by omega
    by_cases hsmall : (d : ℝ)^3≤Real.sqrt (Real.log N)
    · let n := d-3
      have hn : n+3=d := by dsimp [n]; omega
      obtain ⟨G,S,hS,hE⟩ := balanced_uniform_lower_bound (N := N) (T := T) n hT hTN (by simpa [hn] using hsmall)
      refine ⟨G,S,hS,?_⟩
      intro H hH hp
      have hh := weaken_exp_loss (by positivity) hx0 (show (1004 : ℝ)≤1004+7*A by linarith) (hE H hH hp)
      have hn2 : n+2=d-1 := by omega
      have hn4 : n+4=d+1 := by omega
      have hnr : (n : ℝ)+4=(d : ℝ)+1 := by exact_mod_cast hn4
      simpa only [hn,hn2,hn4,hnr,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hh
    · obtain ⟨G,S,hS,hE⟩ := SphereScales.uniform_large_dimension hd3 hT hhalf
        (log_cap_of_power (by omega) (by omega) hcap) (le_of_not_ge hsmall) hdN
      refine ⟨G,S,hS,?_⟩
      intro H hH hp
      exact weaken_exp_loss (by positivity) hx0 (by linarith : (8 : ℝ)+7*A≤1004+7*A) (hE H hH hp)

end LinearDistancePreservers.TheoremFourGeneral

