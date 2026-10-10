import LinearDistancePreservers.HigherBehrend
import LinearDistancePreservers.ExplicitLatticeRadius

namespace LinearDistancePreservers.HigherRate

/-- Take the exact positive root of the power coefficient instead of
retaining the full coefficient. This is quantitative algebra, not a bound
on the dimension dependence of the geometric input. -/
theorem rate_of_power_root {N T E K p q e D : ℕ} (hD : D ≠ 0)
    (h : (T : ℝ)^p*(N : ℝ)^q*(Real.exp (-4*Real.sqrt (Real.log T)))^e ≤
      (K : ℝ)*(E : ℝ)^D) :
    (N : ℝ)^((q : ℝ)/D)*(T : ℝ)^((p : ℝ)/D)*
      Real.exp (-(4*(e : ℝ)/D)*Real.sqrt (Real.log T)) ≤ (K : ℝ)^((D : ℝ)⁻¹)*(E : ℝ) := by
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  have hn : ((N : ℝ)^((q : ℝ)/D))^D = (N : ℝ)^q := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N),div_mul_cancel₀ _ hDr,Real.rpow_natCast]
  have ht : ((T : ℝ)^((p : ℝ)/D))^D = (T : ℝ)^p := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg T),div_mul_cancel₀ _ hDr,Real.rpow_natCast]
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) hD).mp
  rw [mul_pow,mul_pow,hn,ht,← Real.exp_nat_mul,mul_pow,
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg K) hD]
  have hh : (D : ℝ)*(-(4*(e : ℝ)/D)*Real.sqrt (Real.log T)) =
      (e : ℝ)*(-4*Real.sqrt (Real.log T)) := by field_simp
  rw [hh,Real.exp_nat_mul]
  simpa [mul_assoc,mul_comm,mul_left_comm] using h


theorem dimension_rate_root {N T E K d : ℕ} (hd : 1 ≤ d) (hT : 0 < T) (hTN : T ≤ N)
    (h : (T : ℝ)^(d*(d-1)+(d^2-1))*(N : ℝ)^(2*d)*
      (Real.exp (-4*Real.sqrt (Real.log T)))^(d^2-1) ≤
      (K : ℝ)*(E : ℝ)^(d*(d+1))) :
    (N : ℝ)^((2 : ℝ)/(d+1)) *
      (T : ℝ)^((((2*d+1)*(d-1) : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ)) *
      Real.exp (-(4*((d-1 : ℕ) : ℝ)/d)*Real.sqrt (Real.log N)) ≤ (K : ℝ)^(((d*(d+1) : ℕ) : ℝ)⁻¹)*(E : ℝ) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hd1 : (d : ℝ)+1 ≠ 0 := by positivity
  have hds : 1 ≤ d^2 := by nlinarith
  have hs1 := Nat.sub_add_cancel hd
  have hs2 := Nat.sub_add_cancel hds
  have hp : d*(d-1)+(d^2-1)=(2*d+1)*(d-1) := by nlinarith
  have he : d^2-1=(d-1)*(d+1) := by nlinarith
  have hnexp : ((2*d : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ) = (2 : ℝ)/(d+1) := by
    push_cast
    field_simp
  have heexp : 4*((d^2-1 : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ) = 4*((d-1 : ℕ) : ℝ)/d := by
    rw [he]
    push_cast
    field_simp
  have hr := rate_of_power_root (N := N) (T := T) (E := E) (K := K)
    (by positivity : d*(d+1) ≠ 0) h
  rw [hp,hnexp,heexp] at hr
  have hlog : Real.log (T : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast hT) (by exact_mod_cast hTN)
  have hloss : Real.exp (-(4*((d-1 : ℕ) : ℝ)/d)*Real.sqrt (Real.log N)) ≤
      Real.exp (-(4*((d-1 : ℕ) : ℝ)/d)*Real.sqrt (Real.log T)) := by
    apply Real.exp_le_exp.mpr
    have hsq := Real.sqrt_le_sqrt hlog
    have hcoef : 0 ≤ 4*((d-1 : ℕ) : ℝ)/d := by positivity
    nlinarith
  exact (mul_le_mul_of_nonneg_left hloss (by positivity)).trans hr

end LinearDistancePreservers.HigherRate

namespace LinearDistancePreservers.HigherProduct
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Sharper explicit coefficient in the actual graph theorem. The concrete
lattice-count premise can be supplied by LatticeHull.uniform_vertices;
a numerical upper bound for its radius constant is still a separate step. -/
theorem displayed_lower_bound_root {N T C d : ℕ} (hd : 1 ≤ d)
    (hvertices : ∀ b : ℕ, 0 < b →
      b^(d*(d-1)) ≤ (LatticeHull.vertices (LatticeHull.ball d (C*b^(d+1)))).card)
    (hT : 2 ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        (N : ℝ)^((2 : ℝ)/(d+1)) *
          (T : ℝ)^((((2*d+1)*(d-1) : ℕ) : ℝ)/((d*(d+1) : ℕ) : ℝ)) *
          Real.exp (-(4*((d-1 : ℕ) : ℝ)/d)*Real.sqrt (Real.log N)) ≤
          (rateFactor C d : ℝ)^(((d*(d+1) : ℕ) : ℝ)⁻¹)*(H.edgeFinset.card : ℝ) := by
  obtain ⟨G,S,hS,hE⟩ := exact_size_lower_bound hd hvertices hT hTN
  refine ⟨G,S,hS,?_⟩
  intro H hH hp
  exact HigherRate.dimension_rate_root hd (by omega) hTN (hE H hH hp)

end LinearDistancePreservers.HigherProduct

namespace LinearDistancePreservers.TheoremFourGeneral
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Actual fixed-dimensional graph theorem with a closed, fully explicit
coefficient. No geometric premise or existential constant is left here;
a useful growing-d upper bound for the coefficient is still separate. -/
theorem displayed_lower_bound_explicit {N T : ℕ} (n : ℕ)
    (hT : 2 ≤ T) (hTN : T ≤ N) :
    ∃ (G : SimpleGraph (Fin N)) (S : Finset (Fin N)), S.card = T ∧
      ∀ H : SimpleGraph (Fin N), H ≤ G →
        (∀ s ∈ S, ∀ t ∈ S, H.edist s t = G.edist s t) →
        (N : ℝ)^((2 : ℝ)/(n+4)) *
          (T : ℝ)^((((2*(n+3)+1)*(n+2) : ℕ) : ℝ)/(((n+3)*(n+4) : ℕ) : ℝ)) *
          Real.exp (-(4*(n+2 : ℕ)/((n+3 : ℕ) : ℝ))*Real.sqrt (Real.log N)) ≤
          (HigherProduct.rateFactor (LatticeHull.explicitRadius n) (n+3) : ℝ)^
            ((((n+3)*(n+4) : ℕ) : ℝ)⁻¹)*(H.edgeFinset.card : ℝ) := by
  have hv := (LatticeHull.uniform_vertices_explicit n).2
  have hh := HigherProduct.displayed_lower_bound_root (C := LatticeHull.explicitRadius n)
    (d := n+3) (by omega) (by simpa [add_assoc] using hv) hT hTN
  convert hh using 1 <;> norm_num [Nat.cast_add,Nat.cast_ofNat,add_assoc]

end LinearDistancePreservers.TheoremFourGeneral
