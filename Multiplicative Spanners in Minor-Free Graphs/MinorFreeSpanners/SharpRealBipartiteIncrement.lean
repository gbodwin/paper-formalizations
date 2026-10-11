import MinorFreeSpanners.SharpIncrementParameters

/-! Join the proved real left-degree lower bound to the existing genuine
natural-degree bipartite increment, including imbalance and rounding loss. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- Preserve the actual bipartite branch width and its near-matching
density gain, or construct the same small positive-density witness. -/
theorem sharp_real_bipartite_increment {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ) (d : ℝ)
    (hk : 32 ≤ k) (hd : (k:ℝ)^3 ≤ d)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hA : A.Nonempty)
    (hsize : (k/4)*B.card ≤ A.card)
    (hdegree : ∀ x∈A, d-(2+3*(k:ℝ))*(1/(k:ℝ)^2)*d ≤ (G.degree x:ℝ)) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 10*(k:ℝ)^3*d ∧
      0 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
      d/(800000*(k:ℝ)^5)*(S.card:ℝ) ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ n : ℕ, ∃ Q : SimpleGraph (Fin n), ∃ M : MinorModel Q G,
      0<n ∧ M.IsBounded (k/4+1) ∧ (((k/4+1:ℕ):ℝ)*(1-16/(k:ℝ)))*d*n ≤ (Q.edgeFinset.card:ℝ)) := by
  classical
  let D := ⌈d-(2+3*(k:ℝ))*(1/(k:ℝ)^2)*d⌉₊
  obtain ⟨hkD,hlow,hhigh,hfloor⟩ := sharp_increment_degree k d hk hd
  obtain ⟨hell,hfit,hwidth,hfactor⟩ := general_increment_imbalance k (by omega)
  have hkR : (32:ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0:ℝ) < k := by linarith
  have hdpos : 0 ≤ d := (by positivity : (0:ℝ) ≤ (k:ℝ)^3).trans hd
  have hdegreeNat : ∀ x∈A, D ≤ G.degree x := by
    intro x hx
    exact (Nat.ceil_le).mpr (hdegree x hx)
  have hfitR : 4*(k/4:ℕ) ≤ (k:ℝ) := by exact_mod_cast hfit
  obtain hs | hm := bipartite_density_increment G A B (k/4) D (k:ℝ)
    hpos hell hfitR hkD hG hA hsize hdegreeNat
  · obtain ⟨S,hS,hE,hden⟩ := hs
    have hsizeR : (S.card:ℝ) ≤ 10*(k:ℝ)^3*d := hS.trans
      (mul_le_mul_of_nonneg_left hhigh (by positivity))
    have hdenpos : 0 < 400000*(k:ℝ)^5 := by positivity
    have hratio : d/(800000*(k:ℝ)^5) ≤ (D:ℝ)/(400000*(k:ℝ)^5) := by
      have h := div_le_div_of_nonneg_right hlow hdenpos.le
      convert h using 1; ring
    exact Or.inl ⟨S,hsizeR,hE,(mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)).trans hden⟩
  · obtain ⟨n,Q,M,hn,hM,hden⟩ := hm
    have hprod := sharp_increment_factor k d (D:ℝ) hk hdpos hfloor
    exact Or.inr ⟨n,Q,M,hn,hM,
      (mul_le_mul_of_nonneg_right hprod (Nat.cast_nonneg n)).trans hden⟩

end MinorFreeSpanners
