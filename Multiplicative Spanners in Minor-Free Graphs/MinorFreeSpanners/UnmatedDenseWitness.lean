import MinorFreeSpanners.StarPartnerDegreeSum

/-! An internally chosen actual minimum family yields a quadratic edge
budget in its literal induced neighbor-star graph. This does not assert
the final cleaning bound or silently impose its additional parameters. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
variable {V : Type*} [Fintype V]
attribute [local instance] Classical.propDecidable

/-- The real induced witness simultaneously has the proved small vertex
budget and the quadratic edge lower budget forced by actual star swaps.
Both the minimizing assignment and each partner leaf are constructed. -/
theorem exists_family_with_unmated_dense_witness
    (G : SimpleGraph V) (A B C : Finset V) (ell : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (L : V → Finset V) (hG : G.IsBipartiteWith (A : Set V) (B : Set V))
    (hAC : Disjoint A C)
    (hL : IsStarPacking G A C ell L) (hfull : ∀ b ∈ C, (L b).card=ell)
    (hfree : ∀ b ∈ C, MateFreeOn G q (insert b (L b : Set V))) :
    ∃ M : V → Finset V,
      IsStarPacking G A C ell M ∧ (∀ b ∈ C, (M b).card=ell) ∧
      (∀ b ∈ C, MateFreeOn G q (insert b (M b : Set V))) ∧
      C.biUnion M=C.biUnion L ∧
      ∀ b ∈ C, ∀ u ∈ M b,
        let S := unmatedBadLeafCenters G q C M b u
        let H := swapWitnessVertices G C M b u
        H.card ≤ (ell+1)*(G.degree u+G.degree b) ∧
        (S.card:ℝ)*((S.card:ℝ)-2*ell*q) ≤
          2*((G.induce (H:Set V)).edgeFinset.card:ℝ) ∧
        (4*ell*q ≤ (S.card:ℝ) → (S.card:ℝ)^2 ≤
          4*((G.induce (H:Set V)).edgeFinset.card:ℝ)) := by
  classical
  obtain ⟨M,hM,hMf,hMn,hcov,hdegree⟩ :=
    exists_family_with_unmated_induced_degree_budget G A B C ell q hq L hG hL hfull hfree
  refine ⟨M,hM,hMf,hMn,hcov,?_⟩
  intro b hb u hu
  dsimp only
  refine ⟨hM.neighbor_star_union_card hAC u b,?_⟩
  let S := unmatedBadLeafCenters G q C M b u
  let H := swapWitnessVertices G C M b u
  have hdata : ∀ c : S, ∃ vv cc : (H : Set V),
      vv.val ∈ M c.val ∧ cc.val=c.val ∧
      (S.card:ℝ) ≤ (G.induce (H:Set V)).degree vv+
        ((G.induce (H:Set V)).degree cc:ℝ)+2*ell*q := by
    intro c
    obtain ⟨v,hv,_,_,vv,cc,hvv,hcc,hd⟩ := hdegree b hb u hu c.val c.property
    exact ⟨vv,cc,by simpa only [hvv] using hv,hcc,hd⟩
  choose f g hleaf hcenter hdeg using hdata
  have hgi : Function.Injective (fun i : S => (g i).val) := by
    intro i j he
    apply Subtype.ext
    exact (hcenter i).symm.trans (he.trans (hcenter j))
  have hgC : ∀ i : S, (g i).val ∈ C := by
    intro i
    rw [hcenter i]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp i.property).1).1
  have hfL : ∀ i : S, (f i).val ∈ M (g i).val := by
    intro i
    rw [hcenter i]
    exact hleaf i
  have hp := hM.partner_vertex_injections hAC (fun i => (g i).val)
    (fun i => (f i).val) hgi hgC hfL
  have hginj : Function.Injective g := fun i j he => hgi (congrArg Subtype.val he)
  have hfinj : Function.Injective f := fun i j he => hp.1 (congrArg Subtype.val he)
  have hdis : ∀ i j, g i ≠ f j := fun i j he => hp.2 i j (congrArg Subtype.val he)
  have hquad := partner_degree_quadratic (G.induce (H:Set V)) g f hginj hfinj hdis
    (2*ell*q) (fun i => by
      simp only [Fintype.card_coe]
      have hi := hdeg i
      simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hi ⊢
      linarith)
  simp only [Fintype.card_coe] at hquad
  have hfinal : (S.card:ℝ)*((S.card:ℝ)-2*ell*q) ≤
      2*((G.induce (H:Set V)).edgeFinset.card:ℝ) := by
    simp only [SimpleGraph.edgeFinset_card,← Nat.card_eq_fintype_card] at hquad ⊢
    exact hquad
  refine ⟨hfinal,?_⟩
  intro hlarge
  have hm : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
  have hx := mul_nonneg hm (sub_nonneg.mpr hlarge)
  nlinarith

end MinorFreeSpanners
