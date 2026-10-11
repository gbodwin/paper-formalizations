import MinorFreeSpanners.DensestCoreTrichotomy
import MinorFreeSpanners.RealBipartiteIncrement
import MinorFreeSpanners.GeneralInverseParameters

/-! Discharge the actual bipartite branch and every parameter premise of
the general density construction. The selected scale is still displayed
explicitly, along with its actual original induced core. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Every nonempty graph above the explicit k³ density threshold has an
actual dense original witness or a genuine positive k-bounded minor with
factor k/16 at the internally selected density. -/
theorem selected_scale_density_increment {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (d0 : ℝ) (hk : 16 ≤ k)
    (hn : 0 < Fintype.card V) (hd0 : (k:ℝ)^3 ≤ d0)
    (hE : d0*(Fintype.card V:ℝ) ≤ (G.edgeFinset.card:ℝ)) :
    ∃ d : ℝ, ∃ U : Finset V, d0 ≤ d ∧ U.Nonempty ∧
      ((G.induce (U:Set V)).edgeFinset.card:ℝ)=d*(U.card:ℝ) ∧
      ((∃ S : Finset V, (S.card:ℝ) ≤ 12*(k:ℝ)^4*d ∧
        0 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
        d/(800000*(k:ℝ)^7)*(S.card:ℝ) ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
      (∃ n : ℕ, ∃ Q : SimpleGraph (Fin n), ∃ M : MinorModel Q G,
        0<n ∧ M.IsBounded k ∧ ((k:ℝ)/16)*d*n ≤ (Q.edgeFinset.card:ℝ))) := by
  classical
  obtain ⟨hd1,he1,he1',he2,hq,hkd,hcoef⟩ := general_inverse_parameters k d0 hk hd0
  obtain ⟨_hell,hfit,_hwidth,_hfactor⟩ := general_increment_imbalance k hk
  obtain ⟨d,hdd,U,hU,hcore,hAlt⟩ := exists_densest_core_trichotomy G k (k/4)
    (4*(k:ℝ)^2) (1/(k:ℝ)^2) (1/(k:ℝ)) d0 (by omega) hfit hn (by rfl)
    hd1 he1 he1' he2 hq hkd hcoef hE
  refine ⟨d,U,hdd,hU,hcore,?_⟩
  have hkR : (16:ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0:ℝ) < k := by linarith
  have hd : (k:ℝ)^3 ≤ d := hd0.trans hdd
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity : (0:ℝ) < (k:ℝ)^3) hd
  rcases hAlt with hs | hb | hm
  · obtain ⟨S,hS,habs⟩ := hs
    have hsize : (S.card:ℝ) ≤ 12*(k:ℝ)^4*d := by nlinarith only [hS]
    have heq : (1/(k:ℝ)^2)*(1/(k:ℝ))*d^2/2=d^2/(2*(k:ℝ)^3) := by
      field_simp [ne_of_gt hpos]
    rw [heq] at habs
    obtain ⟨hpositive,hratio⟩ := absolute_dense_witness_ratio (k:ℝ) d S.card _ hpos hdpos hsize habs
    exact Or.inl ⟨S,hsize,hpositive,hratio⟩
  · obtain ⟨A,B,H,hHG,hH,hA,hsize,hdegree⟩ := hb
    obtain hs | hm := real_bipartite_increment H A B k d hk hd hH hA hsize hdegree
    · obtain ⟨S,hS,hpositive,hratio⟩ := hs
      let f : H →g G := {toFun := Subtype.val, map_rel' := fun h => hHG h}
      obtain ⟨hc,hcount⟩ := induced_witness_map f Subtype.val_injective S
      have hcountR : ((H.induce (S:Set U)).edgeFinset.card:ℝ) ≤
          (G.induce ((S.image f:Finset V):Set V)).edgeFinset.card := by exact_mod_cast hcount
      have hpow := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ k by linarith)
        (show 0 ≤ 10*(k:ℝ)^3*d by positivity)
      have hsize' : (S.card:ℝ) ≤ 12*(k:ℝ)^4*d := by nlinarith only [hS,hpow]
      have hratio' := mul_le_mul_of_nonneg_right
        (bipartite_density_denominator (k:ℝ) d (by linarith) hdpos.le) (Nat.cast_nonneg S.card)
      refine Or.inl ⟨S.image f,?_,hpositive.trans_le hcountR,?_⟩
      · simpa only [hc] using hsize'
      · simpa only [hc] using (hratio'.trans hratio).trans hcountR
    · obtain ⟨n,Q,M,hpositive,hM,hden⟩ := hm
      let f : H →g G := {toFun := Subtype.val, map_rel' := fun h => hHG h}
      exact Or.inr ⟨n,Q,M.mapHost f Subtype.val_injective,hpositive,
        MinorModel.IsBounded.mapHost M f Subtype.val_injective hM,hden⟩
  · obtain ⟨n,Q,M,hpositive,hM,hden⟩ := hm
    have hfac : (k:ℝ)/16 ≤ (k:ℝ)-7 := by linarith
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac hdpos.le) (Nat.cast_nonneg n)
    exact Or.inr ⟨n,Q,M,hpositive,hM,hh.trans hden⟩

end MinorFreeSpanners
