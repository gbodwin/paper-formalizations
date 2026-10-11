import MinorFreeSpanners.BipartiteDensityGain
import MinorFreeSpanners.RegularStarRestriction

/-! An actual density-increasing minor from a regular bipartite host and a
supplied full mate-free star family. Low-degree center selection, quantitative
cleaning and deletion of uncovered singleton left branches are all internal. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

/-- The explicit regular bipartite domain produces a genuine small dense
induced witness, or a bounded minor of density at least (ell-1)*d. The initial
full mate-free family and literal Unmated predicate remain explicit. -/
theorem exists_regular_bipartite_dense_or_density_minor
    (G : SimpleGraph V) (A B : Finset V) (ell m : ℕ)
    (k d : ℝ) (hk : 0 < k) (hell : 1 ≤ ell) (hellk : 4*(ell:ℝ) ≤ k)
    (hd : k ≤ d) (hmd : (m:ℝ) ≤ d) (hm : (1-1/(100*k))*d ≤ m)
    (hUnmated : Unmated G (5*k^2) (1/(100*k)) (1/(100*k^2)) d)
    (L : V → Finset V) (hG : G.IsBipartiteWith (A:Set V) (B:Set V))
    (hB : B.Nonempty) (hcover : A ∪ B=Finset.univ) (hsize : A.card=ell*B.card)
    (hL : IsStarPacking G A B ell L) (hfull : ∀ b ∈ B, (L b).card=ell)
    (hfree : ∀ b ∈ B, MateFreeOn G (d/(100*k^2)) (insert b (L b:Set V)))
    (hreg : ∀ a ∈ A, G.degree a=m) :
    (∃ H : Finset V, (H.card:ℝ) ≤ 10*k^3*d ∧
      (d/(100*k))^2 ≤ 4*((G.induce (H:Set V)).edgeFinset.card:ℝ) ∧
      d/(400000*k^5)*(H.card:ℝ) ≤ ((G.induce (H:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ C : Finset V, ∃ M : V → Finset V, C ⊆ B ∧
      IsStarPacking G A C ell M ∧ (∀ b ∈ C, (M b).card=ell) ∧
      0 < Fintype.card {i : StarContractionVertex C M // i ∈ rightStarKeep B C M} ∧
      Fintype.card {i : StarContractionVertex C M // i ∈ rightStarKeep B C M}=B.card ∧
      ∃ model : MinorModel (rightStarQuotient G B C M) G,
        model.IsBounded (ell+1) ∧
        ((ell:ℝ)-1)*d*B.card ≤ (rightStarQuotient G B C M).edgeFinset.card) := by
  classical
  have hd0 : 0 < d := hk.trans_le hd
  have hellR : (1:ℝ) ≤ ell := by exact_mod_cast hell
  have hK : 1 ≤ 5*k^2 := by nlinarith
  obtain ⟨C,M,hCB,hM,hMf,hMn,hsmall,hcount⟩ :=
    exists_regular_small_star_centers G A B ell m (5*k^2) d (d/(100*k^2)) L
      hG hK hd0 hmd hreg hsize hL hfull hfree
  let D : ℕ := ⌊5*k^2*d⌋₊
  have hD : (D:ℝ) ≤ 5*k^2*d := Nat.floor_le (by positivity)
  have hsmallN : ∀ x ∈ C ∪ C.biUnion M, G.degree x ≤ D := by
    intro x hx
    exact Nat.le_floor (hsmall x hx)
  obtain hs | ⟨N,hN,hNf,_hcov,hn,model,hw,he⟩ :=
    exists_bipartite_dense_induced_or_right_minor G A B C ell D m k d hk hell
      hellk hd hD hUnmated M hG hCB hcover hM hMf hMn hsmallN hreg
  · exact Or.inl hs
  · have hnpos : 0 < Fintype.card {i : StarContractionVertex C N // i ∈ rightStarKeep B C N} := by
      rw [hn]
      exact Finset.card_pos.mpr hB
    refine Or.inr ⟨C,N,hCB,hN,hNf,hnpos,hn,model,hw,?_⟩
    exact bipartite_right_density_gain k ell d m B.card C.card
      (rightStarQuotient G B C N).edgeFinset.card hk (Nat.cast_nonneg _) hellk hd0.le
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast Finset.card_le_card hCB)
      hcount hm he

end MinorFreeSpanners
