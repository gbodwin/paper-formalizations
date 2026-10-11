import MinorFreeSpanners.FullDensityWitness
import MinorFreeSpanners.DensityLinearLoss
import MinorFreeSpanners.Moore
import MinorFreeSpanners.GirthComponents

/-! The graph-level high-girth minor-free density bound. The density witness
is now constructed internally, rather than supplied as numerical premises. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem girth_minor_free_density {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r h : ℕ) (d : ℝ) (hr : 1≤r) (hh : 0<h)
    (hfree : CliqueMinorFree G h) (hg : GirthAbove G (2*r))
    (hn : 0 < Fintype.card V) (hd : 0<d)
    (hE : d*(Fintype.card V:ℝ) ≤ (G.edgeFinset.card:ℝ)) :
    d ≤ 2*fullDensityLoss h*(h:ℝ)^(2/(r+1:ℝ)) := by
  classical
  obtain ⟨T,hpos,hsize,hden⟩ := full_density_witness G h d hh hfree hn hd hE
  let Q := G.induce (T:Set V)
  let f : Q →g G := {toFun := Subtype.val,map_rel' := fun a => a}
  have hqg : GirthAbove Q (2*r) := hg.of_embedding f Subtype.val_injective
  have hpowN := theorem11_power Q r hr hqg
  have hpow : (Q.edgeFinset.card:ℝ)^r ≤ (2:ℝ)^r*(T.card:ℝ)^(r+1) := by
    simp only [← Set.toFinset_card,Finset.toFinset_coe] at hpowN
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hpowN ⊢
    exact_mod_cast hpowN
  have htpos : 0<T.card := by
    have hb := Q.card_edgeFinset_le_card_choose_two
    have hb' : Q.edgeFinset.card ≤ T.card.choose 2 := by
      simpa only [← Set.toFinset_card,Finset.toFinset_coe] using hb
    have he : 0<Q.edgeFinset.card := by exact_mod_cast hpos
    by_contra hz
    have ht : T.card=0 := by omega
    simp only [ht,Nat.choose_eq_zero_of_lt (by omega : 0<2)] at hb'
    omega
  have hL : 0≤fullDensityLoss h := by
    unfold fullDensityLoss densityPolylogLoss densityWitnessLoss
    positivity
  exact density_increment_linear_loss r d T.card Q.edgeFinset.card (fullDensityLoss h) h
    hd.le (by exact_mod_cast htpos) (Nat.cast_nonneg _) hL (Nat.cast_nonneg _)
    (by simpa only [mul_comm] using hden) (by simpa only [mul_comm] using hsize) hpow

theorem girth_minor_free_edge_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (r h : ℕ) (hr : 1≤r) (hh : 0<h)
    (hfree : CliqueMinorFree G h) (hg : GirthAbove G (2*r)) :
    (G.edgeFinset.card:ℝ) ≤
      (2*fullDensityLoss h*(h:ℝ)^(2/(r+1:ℝ)))*(Fintype.card V:ℝ) := by
  classical
  have hL : 0≤fullDensityLoss h := by
    unfold fullDensityLoss densityPolylogLoss densityWitnessLoss
    positivity
  by_cases he : G.edgeFinset.card=0
  · rw [he]
    simp only [Nat.cast_zero]
    positivity
  · have heR : (0:ℝ)<G.edgeFinset.card := by exact_mod_cast (show 0<G.edgeFinset.card by omega)
    have hn : 0<Fintype.card V := by
      obtain ⟨u,v,huv⟩ := G.ne_bot_iff_exists_adj.mp
        (G.edgeFinset_nonempty.mp (Finset.card_pos.mp (by omega)))
      exact Fintype.card_pos_iff.mpr ⟨u⟩
    have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
    let d : ℝ := (G.edgeFinset.card:ℝ)/(Fintype.card V:ℝ)
    have hd : 0<d := div_pos heR hnR
    have hEq : d*(Fintype.card V:ℝ)=(G.edgeFinset.card:ℝ) := div_mul_cancel₀ _ (ne_of_gt hnR)
    have hb := girth_minor_free_density G r h d hr hh hfree hg hn hd hEq.le
    simpa only [hEq] using mul_le_mul_of_nonneg_right hb hnR.le

end MinorFreeSpanners
