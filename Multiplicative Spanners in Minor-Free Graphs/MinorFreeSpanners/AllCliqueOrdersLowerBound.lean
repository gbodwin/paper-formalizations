import MinorFreeSpanners.GirthConjectureLowerBound
import MinorFreeSpanners.StarLowerBound

namespace MinorFreeSpanners
open SimpleGraph
attribute [local instance] Classical.propDecidable

/-- Lower bounds can be weakened without changing the constructed graph. -/
theorem SparseLowerWitness.mono {n k h : ℕ} {a b : ℝ}
    (hw : SparseLowerWitness n k h a) (hba : b ≤ a) :
    SparseLowerWitness n k h b := by
  obtain ⟨X,inst,G,hcard,hminor,hgirth,hbound⟩ := hw
  exact ⟨X,inst,G,hcard,hminor,hgirth,fun H hH => hba.trans (hbound H hH)⟩

/-- Stars supply all bounded clique orders without a conjectural core. -/
theorem star_sparse_lower_bound (n k h : ℕ) (hn : 2 ≤ n) (hh : 3 ≤ h) :
    SparseLowerWitness n k h ((n:ℝ)/2) := by
  classical
  let r : Fin n := ⟨0,by omega⟩
  refine ⟨Fin n,inferInstance,starGraph r,Fintype.card_fin _,
    star_minorFree r h hh,star_girth r (2*k),?_⟩
  intro H hH
  have he := star_spanner_edges r k H hH
  simp only [Fintype.card_fin] at he
  have heR : (H.edgeFinset.card:ℝ)+1 = n := by exact_mod_cast he
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- The complete fixed-k sparsity lower-bound family, with the necessary
h≥3 boundary and only the source's Erdős girth conjecture as a hypothesis.
For each excluded clique order, every sufficiently large graph size is attained. -/
theorem girth_conjecture_sparse_lower_bound_all_h (k : ℕ) (hk : 1 ≤ k)
    (hconj : ErdosGirthConjecture k) :
    ∃ c : ℝ, 0 < c ∧ ∀ h : ℕ, 3 ≤ h →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        SparseLowerWitness n k h (c*(n:ℝ)*(h:ℝ)^(2/((k:ℝ)+1))) := by
  obtain ⟨c,hc,H,hlarge⟩ := girth_conjecture_sparse_lower_bound k hk hconj
  let H' := max 3 H
  let γ := 2/((k:ℝ)+1)
  let C := min c (1/(2*(H':ℝ)^γ))
  have hHpos : (0:ℝ) < H' := by exact_mod_cast (show 0 < H' by dsimp [H']; omega)
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  have hC : 0 < C := lt_min hc (by positivity)
  have hCc : C ≤ c := min_le_left _ _
  have hCH : C ≤ 1/(2*(H':ℝ)^γ) := min_le_right _ _
  refine ⟨C,hC,?_⟩
  intro h hh
  by_cases hbig : H' ≤ h
  · obtain ⟨N,hN⟩ := hlarge h ((le_max_right _ _).trans hbig)
    refine ⟨N,?_⟩
    intro n hn
    apply (hN n hn).mono
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc (Nat.cast_nonneg n))
      (Real.rpow_nonneg (Nat.cast_nonneg h) _)
  · refine ⟨2,?_⟩
    intro n hn
    apply (star_sparse_lower_bound n k h hn hh).mono
    have hpow : (h:ℝ)^γ ≤ (H':ℝ)^γ := Real.rpow_le_rpow (Nat.cast_nonneg h)
      (by exact_mod_cast (show h ≤ H' by omega)) hγ
    have hb : C*(h:ℝ)^γ ≤ (1:ℝ)/2 := by
      calc
        _ ≤ C*(H':ℝ)^γ := mul_le_mul_of_nonneg_left hpow hC.le
        _ ≤ (1/(2*(H':ℝ)^γ))*(H':ℝ)^γ :=
          mul_le_mul_of_nonneg_right hCH (Real.rpow_nonneg hHpos.le γ)
        _ = 1/2 := by field_simp [(Real.rpow_pos_of_pos hHpos γ).ne']
    have hb' := mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg n)
    dsimp [γ] at hb'
    nlinarith only [hb']

end MinorFreeSpanners
