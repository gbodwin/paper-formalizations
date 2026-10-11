import MinorFreeSpanners.BalancedDensityEscalation
import MinorFreeSpanners.LogarithmicCliqueThreshold
import Mathlib.Algebra.Order.Ring.Pow

/-! A numerical horizon forces actual iteration to stop. The original-host
pullback loses only a factor two when the cumulative multiplicative loss
is bounded using Bernoulli's inequality. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem balanced_clique_density_witness {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k h t : ℕ) (d : ℝ) (hk : 32 ≤ k) (hh : 0<h)
    (hfree : CliqueMinorFree G h) (hn : 0 < Fintype.card V)
    (hd : (k:ℝ)^3 ≤ d) (hE : d*(Fintype.card V:ℝ) ≤ (G.edgeFinset.card:ℝ))
    (hsafe : 32*t ≤ k) (horizon : (6*cliqueDensityScale h:ℕ) < (2:ℝ)^t*d) :
    ∃ T : Finset V, 0 < ((G.induce (T:Set V)).edgeFinset.card:ℝ) ∧
      d*(T.card:ℝ) ≤ 1600000*(k:ℝ)^7*(6*cliqueDensityScale h:ℕ)^2 ∧
      d*(T.card:ℝ) ≤ 1600000*(k:ℝ)^7*((G.induce (T:Set V)).edgeFinset.card:ℝ) := by
  classical
  have hkR : (32:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ)<k := by linarith
  have hdpos : 0<d := lt_of_lt_of_le (by positivity : (0:ℝ)<(k:ℝ)^3) hd
  let C : ℝ := (6*cliqueDensityScale h:ℕ)
  have hC : 0≤C := by positivity
  have cap : ∀ (n:ℕ) (Q:SimpleGraph (Fin n)) (M:MinorModel Q G),
      (Q.edgeFinset.card:ℝ) ≤ C*(n:ℝ) := by
    intro n Q M
    have hb := (hfree.of_minor M).edge_count_le_logarithmic hh
    dsimp [C]
    exact_mod_cast (by simpa only [Fintype.card_fin] using hb : Q.edgeFinset.card ≤ (6*cliqueDensityScale h)*n)
  have hw : BalancedDensityWitness G k d t := by
    rcases balanced_density_escalation G k d hk hn hd hE t with hw | hs
    · exact hw
    · obtain ⟨W,n,Q,M,hW,hn,hM,hgrow,hden⟩ := hs
      have hcap := cap n Q M
      have hnR : (0:ℝ)<n := by exact_mod_cast hn
      have hlow := mul_le_mul_of_nonneg_right hgrow hnR.le
      have hstrict := mul_lt_mul_of_pos_right horizon hnR
      dsimp [C] at hcap
      linarith
  obtain ⟨j,hj,W,n,Q,M,hW,hn,hM,hgrow,hden,S,hsize,hpositive,hS⟩ := hw
  let δ : ℝ := (1-16/(k:ℝ))^j*W*d
  have hδ0 : 0≤δ := by
    have ha : 0 ≤ 1-16/(k:ℝ) := sub_nonneg.mpr ((div_le_one hkpos).mpr (by linarith))
    positivity
  have hcap := cap n Q M
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hδC : δ≤C := (mul_le_mul_iff_of_pos_right hnR).mp (hden.trans hcap)
  have hjsafe : (32:ℝ)*j ≤ k := by exact_mod_cast (show 32*j≤k by omega)
  have hfrac : (j:ℝ)*(16/(k:ℝ)) ≤ 1/2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hkpos).mpr
    linarith
  have hbern := one_add_mul_le_pow (show (-2:ℝ) ≤ -(16/(k:ℝ)) by
    have hh : 16/(k:ℝ) ≤ 1 := (div_le_one hkpos).mpr (by linarith)
    linarith) j
  have halpha : (1:ℝ)/2 ≤ (1-16/(k:ℝ))^j := by
    simp only [← sub_eq_add_neg,mul_neg] at hbern
    linarith
  have hWd : (W:ℝ)*d ≤ 2*δ := by
    have hx := mul_le_mul_of_nonneg_right halpha (show 0≤(W:ℝ)*d by positivity)
    dsimp [δ]
    nlinarith only [hx]
  obtain ⟨T,hcard,hedge⟩ := MinorModel.IsBounded.exists_host_subgraph (M.induceTarget (S:Set (Fin n)))
    (MinorModel.IsBounded.induceTarget M hM (S:Set (Fin n)))
  have hc : (T.card:ℝ) ≤ (W:ℝ)*(S.card:ℝ) := by
    exact_mod_cast (by simpa only [← Set.toFinset_card,Finset.toFinset_coe] using hcard : T.card≤W*S.card)
  have he : ((Q.induce (S:Set (Fin n))).edgeFinset.card:ℝ) ≤
      ((G.induce (T:Set V)).edgeFinset.card:ℝ) := by exact_mod_cast hedge
  have hB : (0:ℝ)<800000*(k:ℝ)^7 := by positivity
  have hS' : δ*(S.card:ℝ) ≤ 800000*(k:ℝ)^7*((Q.induce (S:Set (Fin n))).edgeFinset.card:ℝ) := by
    rw [div_mul_eq_mul_div] at hS
    simpa only [δ,mul_comm] using (div_le_iff₀ hB).mp hS
  have hc' := mul_le_mul_of_nonneg_left hc hdpos.le
  have hmS := mul_le_mul_of_nonneg_right hWd (Nat.cast_nonneg S.card)
  have he' := mul_le_mul_of_nonneg_left he (show 0≤1600000*(k:ℝ)^7 by positivity)
  have hdense : d*(T.card:ℝ) ≤ 1600000*(k:ℝ)^7*((G.induce (T:Set V)).edgeFinset.card:ℝ) := by
    nlinarith only [hc',hmS,hS',he']
  have hsize' := mul_le_mul_of_nonneg_left hsize (show 0≤(W:ℝ)*d by positivity)
  have hWd' := mul_le_mul_of_nonneg_right hWd (show 0≤12*(k:ℝ)^5*δ by positivity)
  have hsq : δ^2 ≤ C^2 := (sq_le_sq₀ hδ0 hC).mpr hδC
  have hsq' := mul_le_mul_of_nonneg_left hsq (show 0≤24*(k:ℝ)^5 by positivity)
  have hcoef : 24*(k:ℝ)^5 ≤ 1600000*(k:ℝ)^7 := by
    have hp : (1:ℝ)≤(k:ℝ)^2 := one_le_pow₀ (by linarith)
    have hm := mul_le_mul_of_nonneg_left hp (show 0≤(k:ℝ)^5 by positivity)
    nlinarith [show (k:ℝ)^5*(k:ℝ)^2=(k:ℝ)^7 by ring]
  have hlast := mul_le_mul_of_nonneg_right hcoef (sq_nonneg C)
  refine ⟨T,hpositive.trans_le he,?_,hdense⟩
  change d*(T.card:ℝ) ≤ 1600000*(k:ℝ)^7*C^2
  nlinarith only [hc',hsize',hWd',hsq',hlast]

end MinorFreeSpanners
