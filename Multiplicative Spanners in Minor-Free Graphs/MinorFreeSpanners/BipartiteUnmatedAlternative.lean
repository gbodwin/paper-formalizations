import MinorFreeSpanners.RegularBipartiteMinor

/-! Reapply the genuine small-dense-or-Unmated graph theorem on the regular
host. The resulting induced graph has an explicit positive edge count. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

theorem bipartite_mate_witness_scale (k d N E : ℝ)
    (hk : 4 ≤ k) (hd : 0 < d) (hN : N ≤ 15*k^2*d)
    (hE : d^2/(20000*k^3) ≤ E) :
    N ≤ 10*k^3*d ∧ 0 < E ∧ d/(400000*k^5)*N ≤ E := by
  have hk0 : 0 < k := by linarith
  have hkne : k≠0 := ne_of_gt hk0
  have hfirst : 15*k^2*d ≤ 10*k^3*d := by
    have hh := mul_nonneg (show 0 ≤ 10*k-15 by linarith)
      (show 0 ≤ k^2*d by positivity)
    nlinarith
  have hpos : 0 < d^2/(20000*k^3) := by positivity
  refine ⟨hN.trans hfirst,hpos.trans_le hE,?_⟩
  calc
    _ ≤ d/(400000*k^5)*(15*k^2*d) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    _ = (3/4)*(d^2/(20000*k^3)) := by field_simp; ring
    _ ≤ d^2/(20000*k^3) := by linarith
    _ ≤ E := hE

/-- Literal unmatedness is now obtained by an actual graph alternative,
with no hereditary assertion. The full initial family remains explicit. -/
theorem exists_regular_bipartite_dense_or_density_minor_without_unmated
    (G : SimpleGraph V) (A B : Finset V) (ell m : ℕ)
    (k d : ℝ) (hk : 0 < k) (hell : 1 ≤ ell) (hellk : 4*(ell:ℝ) ≤ k)
    (hd : k ≤ d) (hmd : (m:ℝ) ≤ d) (hm : (1-1/(100*k))*d ≤ m)
    (L : V → Finset V) (hG : G.IsBipartiteWith (A:Set V) (B:Set V))
    (hB : B.Nonempty) (hcover : A ∪ B=Finset.univ) (hsize : A.card=ell*B.card)
    (hL : IsStarPacking G A B ell L) (hfull : ∀ b ∈ B, (L b).card=ell)
    (hfree : ∀ b ∈ B, MateFreeOn G (d/(100*k^2)) (insert b (L b:Set V)))
    (hreg : ∀ a ∈ A, G.degree a=m) :
    (∃ H : Finset V, (H.card:ℝ) ≤ 10*k^3*d ∧
      0 < ((G.induce (H:Set V)).edgeFinset.card:ℝ) ∧
      d/(400000*k^5)*(H.card:ℝ) ≤ ((G.induce (H:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ C : Finset V, ∃ M : V → Finset V, C ⊆ B ∧
      IsStarPacking G A C ell M ∧ (∀ b ∈ C, (M b).card=ell) ∧
      0 < Fintype.card {i : StarContractionVertex C M // i ∈ rightStarKeep B C M} ∧
      Fintype.card {i : StarContractionVertex C M // i ∈ rightStarKeep B C M}=B.card ∧
      ∃ model : MinorModel (rightStarQuotient G B C M) G,
        model.IsBounded (ell+1) ∧
        ((ell:ℝ)-1)*d*B.card ≤ (rightStarQuotient G B C M).edgeFinset.card) := by
  classical
  have hellR : (1:ℝ) ≤ ell := by exact_mod_cast hell
  have hk4 : 4 ≤ k := by linarith
  have hd0 : 0 < d := hk.trans_le hd
  have he1 : 1/(100*k) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  obtain hs | hu := postle_small_dense_or_unmated G (5*k^2) d
    (1/(100*k)) (1/(100*k^2)) (by nlinarith) (by linarith) (by positivity) he1 (by positivity)
  · obtain ⟨H,hN,hE⟩ := hs
    have hE' : d^2/(20000*k^3) ≤ ((G.induce (H:Set V)).edgeFinset.card:ℝ) := by
      convert hE using 1
      ring
    have hN' : (H.card:ℝ) ≤ 15*k^2*d := by nlinarith
    exact Or.inl ⟨H,bipartite_mate_witness_scale k d H.card
      (G.induce (H:Set V)).edgeFinset.card hk4 hd0 hN' hE'⟩
  · obtain hs | hm := exists_regular_bipartite_dense_or_density_minor G A B ell m k d hk
      hell hellk hd hmd hm hu L hG hB hcover hsize hL hfull hfree hreg
    · obtain ⟨H,hN,hE,hD⟩ := hs
      have hp : 0 < (d/(100*k))^2 := by positivity
      exact Or.inl ⟨H,hN,by nlinarith,hD⟩
    · exact Or.inr hm

end MinorFreeSpanners
