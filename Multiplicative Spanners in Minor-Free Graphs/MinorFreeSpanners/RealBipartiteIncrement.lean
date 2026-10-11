import MinorFreeSpanners.GeneralIncrementParameters

/-! Join the proved real left-degree lower bound to the existing genuine
natural-degree bipartite increment, including imbalance and rounding loss. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- The real-degree bipartite branch gives an actual bounded minor with
factor k/16, or an actual small positive-density induced witness. -/
theorem real_bipartite_increment {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ) (d : ℝ)
    (hk : 16 ≤ k) (hd : (k:ℝ)^3 ≤ d)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hA : A.Nonempty)
    (hsize : (k/4)*B.card ≤ A.card)
    (hdegree : ∀ x∈A, d-(2+3*(k:ℝ))*(1/(k:ℝ)^2)*d ≤ (G.degree x:ℝ)) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 10*(k:ℝ)^3*d ∧
      0 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
      d/(800000*(k:ℝ)^5)*(S.card:ℝ) ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ n : ℕ, ∃ Q : SimpleGraph (Fin n), ∃ M : MinorModel Q G,
      0<n ∧ M.IsBounded k ∧ ((k:ℝ)/16)*d*n ≤ (Q.edgeFinset.card:ℝ)) := by
  classical
  let D := ⌈d/2⌉₊
  obtain ⟨hkD,hlow,hhigh,hfloor⟩ := general_increment_rounded_degree k d hk hd
  obtain ⟨hell,hfit,hwidth,hfactor⟩ := general_increment_imbalance k hk
  have hkR : (16:ℝ) ≤ k := by exact_mod_cast hk
  have hpos : (0:ℝ) < k := by linarith
  have hdpos : 0 ≤ d := (by positivity : (0:ℝ) ≤ (k:ℝ)^3).trans hd
  have hdegreeNat : ∀ x∈A, D ≤ G.degree x := by
    intro x hx
    exact_mod_cast hfloor.trans (hdegree x hx)
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
    have hfacpos : (0:ℝ) ≤ (k/4:ℕ)-1 := by linarith
    have hprod := mul_le_mul hfactor hlow (show 0 ≤ d/2 by positivity) hfacpos
    have hprod' : (k:ℝ)/16*d ≤ ((k/4:ℕ)-1)*(D:ℝ) := by convert hprod using 1; ring
    exact Or.inr ⟨n,Q,M,hn,(fun i => (hM i).trans hwidth),
      (mul_le_mul_of_nonneg_right hprod' (Nat.cast_nonneg n)).trans hden⟩

end MinorFreeSpanners
