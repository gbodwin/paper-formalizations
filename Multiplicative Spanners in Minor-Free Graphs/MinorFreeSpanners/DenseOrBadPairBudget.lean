import MinorFreeSpanners.DenseWitnessAlternative
import MinorFreeSpanners.BadPairIncidenceBound

/-! Combine the actual dense-witness alternative with literal Unmated mate
counts and unique-leaf incidences. This bounds selected-star surplus only;
residual quotient fibers and the density increment remain separate. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- Internally choose the valid minimizing family and derive its complete
ordered bad-pair and selected-star surplus budgets, or exhibit the actual
small dense induced graph. The threshold and smallness premises are explicit. -/
theorem exists_dense_induced_or_bad_pair_budget
    (G : SimpleGraph V) (A B C : Finset V) (ell D : ℕ)
    (K eps1 eps2 d r : ℝ) (hq : 0 ≤ eps2*d) (hr : 4*ell*(eps2*d) ≤ r)
    (hD : (D:ℝ) ≤ K*d) (hUnmated : Unmated G K eps1 eps2 d)
    (L : V → Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hAC : Disjoint A C)
    (hL : IsStarPacking G A C ell L) (hfull : ∀ b ∈ C, (L b).card=ell)
    (hfree : ∀ b ∈ C, MateFreeOn G (eps2*d) (insert b (L b : Set V)))
    (hsmall : ∀ x ∈ C ∪ C.biUnion L, G.degree x ≤ D) :
    (∃ H : Finset V, H.card ≤ 2*(ell+1)*D ∧
      r^2 ≤ 4*((G.induce (H:Set V)).edgeFinset.card:ℝ)) ∨
    (∃ M : V → Finset V,
      IsStarPacking G A C ell M ∧ (∀ b ∈ C, (M b).card=ell) ∧
      (∀ b ∈ C, MateFreeOn G (eps2*d) (insert b (M b : Set V))) ∧
      C.biUnion M=C.biUnion L ∧
      (badStarPairCount G C M:ℝ) ≤ C.card*((ell+1)*eps1*d+ell*r) ∧
      (orderedStarSurplus G C M:ℝ) ≤
        (2*(ell*(ell-1):ℕ)*(eps2*d)+(ell+1)*eps1*d+ell*r)*C.card) := by
  classical
  obtain hd | ⟨M,hM,hMf,hMn,hcov,hlocal⟩ :=
    exists_dense_induced_or_unmated_leaf_bound G A B C ell D (eps2*d) r hq hr
      L hG hAC hL hfull hfree hsmall
  · exact Or.inl hd
  right
  have hsmallM : ∀ x ∈ C ∪ C.biUnion M, (G.degree x:ℝ) ≤ K*d := by
    intro x hx
    rw [hcov] at hx
    exact (Nat.cast_le.mpr (hsmall x hx)).trans hD
  have hmated : ∀ b ∈ C,
      ((matedStarCenters G (eps2*d) C M b).card:ℝ) ≤ (ell+1)*eps1*d := by
    intro b hb
    apply hM.matedStarCenters_bound hAC K eps1 eps2 d hUnmated hb (hMf b hb)
    intro x hx
    rcases Finset.mem_insert.mp hx with hxb | hx
    · subst x
      exact hsmallM b (Finset.mem_union_left _ hb)
    · exact hsmallM x (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b,hb,hx⟩))
  have hscore := badStarPairCount_le_incidence_budget G C M ell (eps2*d)
    ((ell+1)*eps1*d) r hMf hmated (fun b hb u hu => (hlocal b hb u hu).le)
  have hleaffree : ∀ b ∈ C, MateFreeOn G (eps2*d) (M b:Set V) := by
    intro b hb x hx y hy hxy
    exact hMn b hb x (Set.mem_insert_of_mem b hx) y (Set.mem_insert_of_mem b hy) hxy
  have hsurplus := orderedStarSurplus_mateFree G C M ell (eps2*d) hMf hleaffree
  refine ⟨M,hM,hMf,hMn,hcov,hscore,?_⟩
  nlinarith

end MinorFreeSpanners
