import MinorFreeSpanners.BipartiteUnmatedAlternative
import MinorFreeSpanners.FiniteBoundedMinor
import MinorFreeSpanners.SelectedRegularDegree

/-! The selected regular graph is constructed inside the original host.
Both alternatives are then transported back to that host with literal
branch sets and actual induced simple edges. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

/-- An actual full selected family with a small exterior boundary gives a
small dense induced graph or a bounded density-increasing minor of the
original graph. Global unmatedness is neither supplied nor inherited. -/
theorem selected_bipartite_dense_or_density_minor {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A B C : Finset V) (ell d : ℕ) (k : ℝ)
    (hk : 0 < k) (hell : 1 ≤ ell) (hellk : 4*(ell:ℝ) ≤ k) (hkd : k ≤ d)
    (L : V → Finset V) (hG : G.IsBipartiteWith (A:Set V) (B:Set V))
    (hCB : C ⊆ B) (hC : C.Nonempty) (hL : IsStarPacking G A C ell L)
    (hfull : ∀ b ∈ C, (L b).card=ell)
    (hfree : ∀ b ∈ C, MateFreeOn G ((d:ℝ)/(100*k^2)) (insert b (L b:Set V)))
    (hdegree : ∀ x ∈ A, d ≤ G.degree x)
    (hboundary : ∀ x ∈ C.biUnion L,
      ((B \ C).filter fun y => G.Adj x y).card ≤ ⌊(1/(100*k))*(d:ℝ)⌋₊) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 10*k^3*d ∧
      0 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
      (d:ℝ)/(400000*k^5)*S.card ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ n : ℕ, ∃ Q : SimpleGraph (Fin n), ∃ M : MinorModel Q G,
      0 < n ∧ M.IsBounded (ell+1) ∧
      ((ell:ℝ)-1)*d*n ≤ (Q.edgeFinset.card:ℝ)) := by
  classical
  have hd0 : 0 < d := by exact_mod_cast hk.trans_le hkd
  have hellR : (1:ℝ) ≤ ell := by exact_mod_cast hell
  have hk4 : 4 ≤ k := by linarith
  have he0 : (0:ℝ) ≤ 1/(100*k) := by positivity
  have he1 : (1:ℝ)/(100*k) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  obtain ⟨hm0,hmd,hm,heq⟩ := selected_regular_degree_bounds d (1/(100*k)) hd0 he0 he1
  obtain ⟨H,_hFH,hHG,hH,hreg,_hcard,hLH,hfullH,hfreeH,_hcoverH,hsizeH⟩ :=
    hL.regularize_selected_host_integer hG hCB hfull ((d:ℝ)/(100*k^2)) d
      ⌊(1/(100*k))*(d:ℝ)⌋₊ hfree hdegree hboundary
      (d-⌊(1/(100*k))*(d:ℝ)⌋₊) hm0 heq.le
  let f : H →g G := { toFun := Subtype.val, map_rel' := fun h => hHG h }
  have hf : Function.Injective f := Subtype.val_injective
  obtain hs | hn := exists_regular_bipartite_dense_or_density_minor_without_unmated
    H (selectedStarLeaves C L) (selectedStarCenters C L) ell
    (d-⌊(1/(100*k))*(d:ℝ)⌋₊) k d hk hell hellk hkd
    (by exact_mod_cast hmd) hm (selectedStarAssignment C L) hH
    (selected_star_centers_nonempty C L hC) (by
      convert selected_star_domains_cover C L using 1
      ext x
      simp)
    hsizeH hLH hfullH hfreeH hreg
  · obtain ⟨S,hN,hE,hD⟩ := hs
    obtain ⟨hcard,hcount⟩ := induced_witness_map f hf S
    have hcountR : ((H.induce (S:Set (SelectedStarVertex C L))).edgeFinset.card:ℝ) ≤
        (G.induce ((S.image f:Finset V):Set V)).edgeFinset.card := by exact_mod_cast hcount
    refine Or.inl ⟨S.image f,?_,hE.trans_le hcountR,?_⟩
    · simpa only [hcard] using hN
    · simpa only [hcard] using hD.trans hcountR
  · obtain ⟨C',L',_hC',_hL',_hf',hpos,hcard,M,hM,hD⟩ := hn
    refine Or.inr (exists_finite_bounded_dense_minor _ G (ell+1) (((ell:ℝ)-1)*d)
      (M.mapHost f hf) (MinorModel.IsBounded.mapHost M f hf hM) hpos ?_)
    rw [hcard]
    exact hD

end MinorFreeSpanners
