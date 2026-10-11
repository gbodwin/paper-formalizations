import MinorFreeSpanners.UnmatedDenseWitness

/-! A genuine small dense induced subgraph or a quantitative local
unmated-incidence bound. The threshold relation is explicit; this does
not infer absence of the dense witness from the Unmated predicate. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- All branch vertices remain small when the finite minimum preserves
exactly the original covered leaves. The alternative uses a real induced
subgraph, with its actual vertex and edge cardinalities. -/
theorem exists_dense_induced_or_unmated_leaf_bound
    (G : SimpleGraph V) (A B C : Finset V) (ell D : ℕ) (q r : ℝ)
    (hq : 0 ≤ q) (hr : 4*ell*q ≤ r)
    (L : V → Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hAC : Disjoint A C)
    (hL : IsStarPacking G A C ell L) (hfull : ∀ b ∈ C, (L b).card=ell)
    (hfree : ∀ b ∈ C, MateFreeOn G q (insert b (L b : Set V)))
    (hsmall : ∀ x ∈ C ∪ C.biUnion L, G.degree x ≤ D) :
    (∃ H : Finset V, H.card ≤ 2*(ell+1)*D ∧
      r^2 ≤ 4*((G.induce (H:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ M : V → Finset V,
      IsStarPacking G A C ell M ∧ (∀ b ∈ C, (M b).card=ell) ∧
      (∀ b ∈ C, MateFreeOn G q (insert b (M b : Set V))) ∧
      C.biUnion M=C.biUnion L ∧
      ∀ b ∈ C, ∀ u ∈ M b,
        ((unmatedBadLeafCenters G q C M b u).card:ℝ) < r) := by
  classical
  by_cases hdense : ∃ H : Finset V, H.card ≤ 2*(ell+1)*D ∧
      r^2 ≤ 4*((G.induce (H:Set V)).edgeFinset.card:ℝ)
  · exact Or.inl hdense
  right
  obtain ⟨M,hM,hMf,hMn,hcov,hbudget⟩ :=
    exists_family_with_unmated_dense_witness G A B C ell q hq L hG hAC hL hfull hfree
  refine ⟨M,hM,hMf,hMn,hcov,?_⟩
  intro b hb u hu
  have hdb := hsmall b (Finset.mem_union_left _ hb)
  have hum : u ∈ C.biUnion M := Finset.mem_biUnion.mpr ⟨b,hb,hu⟩
  rw [hcov] at hum
  have hdu := hsmall u (Finset.mem_union_right _ hum)
  obtain ⟨hv,_,he⟩ := hbudget b hb u hu
  have hsize : (swapWitnessVertices G C M b u).card ≤ 2*(ell+1)*D := by
    calc
      _ ≤ (ell+1)*(G.degree u+G.degree b) := hv
      _ ≤ (ell+1)*(D+D) := Nat.mul_le_mul_left _ (Nat.add_le_add hdu hdb)
      _ = _ := by ring
  by_contra hn
  have hcount := le_of_not_gt hn
  have hlarge := he (hr.trans hcount)
  have hr0 : 0 ≤ r := le_trans (by positivity) hr
  have hsquare : r^2 ≤ ((unmatedBadLeafCenters G q C M b u).card:ℝ)^2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hcount)
      (add_nonneg (Nat.cast_nonneg (unmatedBadLeafCenters G q C M b u).card) hr0)
    nlinarith
  exact hdense ⟨swapWitnessVertices G C M b u,hsize,hsquare.trans hlarge⟩

end MinorFreeSpanners
