import MinorFreeSpanners.PolylogarithmicDensityWitness

/-! Include low-density inputs using a literal original edge. Thus the
actual density witness requires no lower threshold on the positive density. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

def fullDensityLoss (h : ℕ) : ℝ := densityPolylogLoss h+2*(densityStepWidth h:ℝ)^3

theorem full_density_witness {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h : ℕ) (d : ℝ) (hh : 0<h)
    (hfree : CliqueMinorFree G h) (hn : 0 < Fintype.card V) (hd : 0<d)
    (hE : d*(Fintype.card V:ℝ) ≤ (G.edgeFinset.card:ℝ)) :
    ∃ T : Finset V, 0 < ((G.induce (T:Set V)).edgeFinset.card:ℝ) ∧
      d*(T.card:ℝ) ≤ fullDensityLoss h*(h:ℝ)^2 ∧
      d*(T.card:ℝ) ≤ fullDensityLoss h*((G.induce (T:Set V)).edgeFinset.card:ℝ) := by
  classical
  have hpoly : 0 ≤ densityPolylogLoss h := by
    unfold densityPolylogLoss densityWitnessLoss
    positivity
  have hL : 0 ≤ fullDensityLoss h := by unfold fullDensityLoss; positivity
  have hlargeL : densityPolylogLoss h ≤ fullDensityLoss h := by unfold fullDensityLoss; exact le_add_of_nonneg_right (by positivity)
  by_cases hhigh : (densityStepWidth h:ℝ)^3 ≤ d
  · obtain ⟨T,hpos,hs,he⟩ := polylogarithmic_density_witness G h d hh hfree hn hhigh hE
    exact ⟨T,hpos,hs.trans (mul_le_mul_of_nonneg_right hlargeL (sq_nonneg _)),
      he.trans (mul_le_mul_of_nonneg_right hlargeL (Nat.cast_nonneg _))⟩
  · have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
    have hepos : 0 < G.edgeFinset.card := by
      have hx := (mul_pos hd hnR).trans_le hE
      exact_mod_cast hx
    obtain ⟨u,v,huv⟩ := G.ne_bot_iff_exists_adj.mp
      (G.edgeFinset_nonempty.mp (Finset.card_pos.mp hepos))
    let T : Finset V := {u,v}
    have hT : T.card=2 := by simp [T,huv.ne]
    let a : (T:Set V) := ⟨u,by simp [T]⟩
    let b : (T:Set V) := ⟨v,by simp [T]⟩
    have hab : (G.induce (T:Set V)).Adj a b := huv
    have hmem : s(a,b) ∈ (G.induce (T:Set V)).edgeFinset := mem_edgeFinset.mpr hab
    have hcount : 1 ≤ (G.induce (T:Set V)).edgeFinset.card := Finset.card_pos.mpr ⟨_,hmem⟩
    have hcountR : (1:ℝ) ≤ (G.induce (T:Set V)).edgeFinset.card := by exact_mod_cast hcount
    have hbase : 2*d ≤ fullDensityLoss h := by
      unfold fullDensityLoss
      linarith
    have hhR : (1:ℝ)≤h := by exact_mod_cast hh
    have hh2 : (1:ℝ)≤(h:ℝ)^2 := one_le_pow₀ hhR
    have hs := mul_le_mul_of_nonneg_left hh2 hL
    have he := mul_le_mul_of_nonneg_left hcountR hL
    refine ⟨T,by linarith,?_,?_⟩ <;> rw [hT] <;> norm_num only [Nat.cast_ofNat]
    · nlinarith only [hbase,hs]
    · nlinarith only [hbase,he]

/-- A literal degree-nine polynomial in log₂(h)+2 bounds the loss; the
coefficient is independent of the girth/stretch parameter. -/
theorem fullDensityLoss_polylog (h : ℕ) (hh : 0<h) :
    fullDensityLoss h ≤
      (1600000*(131104:ℝ)^7*24576^2+2*(131104:ℝ)^3)*((Nat.log 2 h+2:ℕ):ℝ)^9 := by
  have hpoly := densityPolylogLoss_bound h hh
  have hw : (densityStepWidth h:ℝ) ≤ 131104*((Nat.log 2 h+2:ℕ):ℝ) := by
    exact_mod_cast densityStepWidth_le_log h hh
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg (densityStepWidth h)) hw 3
  have hq : (1:ℝ)≤((Nat.log 2 h+2:ℕ):ℝ) := by exact_mod_cast (show 1≤Nat.log 2 h+2 by omega)
  have hpow := pow_le_pow_right₀ hq (show 3≤9 by omega)
  have hscale := mul_le_mul_of_nonneg_left hpow (show (0:ℝ)≤2*131104^3 by norm_num)
  unfold fullDensityLoss
  nlinarith only [hpoly,hp,hscale]

end MinorFreeSpanners
