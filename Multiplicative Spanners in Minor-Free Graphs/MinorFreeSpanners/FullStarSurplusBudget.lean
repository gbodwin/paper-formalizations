import MinorFreeSpanners.ResidualBranchFiber
import MinorFreeSpanners.QuotientSurplusPairs

/-! Cover every actual quotient fiber, including the residual singleton
branches, by real directed leaf collisions and ordered bad-star pairs. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V]

noncomputable def fullStarFiberLoss (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (i j : StarContractionVertex C L) : ℕ :=
  (((quotientCrossEdges G (fullStarLabel C L)).filter fun e =>
    Sym2.map (fullStarLabel C L) e=s(i,j)).card-1)

theorem fullStarFiberLoss_symm (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (i j : StarContractionVertex C L) :
    fullStarFiberLoss G C L i j=fullStarFiberLoss G C L j i := by
  simp only [fullStarFiberLoss,Sym2.eq_swap (a:=i) (b:=j)]

theorem fullStarFiberLoss_self (G : SimpleGraph V) (C : Finset V)
    (L : V → Finset V) (i : StarContractionVertex C L) :
    fullStarFiberLoss G C L i i=0 := by
  classical
  unfold fullStarFiberLoss
  have he : ((quotientCrossEdges G (fullStarLabel C L)).filter fun e =>
      Sym2.map (fullStarLabel C L) e=s(i,i))=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e hm
    obtain ⟨hm,hi⟩ := Finset.mem_filter.mp hm
    have hn := (Finset.mem_filter.mp hm).2
    rw [hi] at hn
    exact hn (by simp)
  simp only [he,Finset.card_empty,Nat.zero_sub]

/-- All ordered selected/selected losses are exactly the previously
counted selected-star surplus, with diagonal fibers contributing zero. -/
theorem IsStarPacking.selected_loss_sum {G : SimpleGraph V}
    {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hCB : C ⊆ B) :
    (∑ b : C, ∑ c : C, fullStarFiberLoss G C L (.inl b) (.inl c)) =
      orderedStarSurplus G C L := by
  classical
  let F (b c : V) : ℕ := if b≠c then
    (starCrossLeaves G L b c).card+(starCrossLeaves G L c b).card-1 else 0
  have hp (b c : C) : fullStarFiberLoss G C L (.inl b) (.inl c) = F b.val c.val := by
    by_cases hn : b.val=c.val
    · have he : b=c := Subtype.ext hn
      subst c
      simp [F,fullStarFiberLoss_self]
    · have hbc : b≠c := fun he => hn (congrArg Subtype.val he)
      change _ = if b.val≠c.val then _ else 0
      rw [ite_eq_left hn]
      exact congrArg (fun n : ℕ => n-1) (h.selected_edge_fiber_card hG hCB b c hbc)
  have hc (b : V) : (∑ c : C, F b c.val) = ∑ c ∈ C, F b c :=
    (Finset.sum_subtype C (fun _ => Iff.rfl) (F b)).symm
  have hb : (∑ b : C, ∑ c ∈ C, F b.val c) = ∑ b ∈ C, ∑ c ∈ C, F b c :=
    (Finset.sum_subtype C (fun _ => Iff.rfl) (fun b => ∑ c ∈ C, F b c)).symm
  calc
    _ = ∑ b : C, ∑ c : C, F b.val c.val := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_congr rfl (fun c _ => hp b c)
    _ = ∑ b : C, ∑ c ∈ C, F b.val c := Finset.sum_congr rfl (fun b _ => hc b.val)
    _ = _ := hb

/-- Every selected/residual fiber is paid for by a genuine collision count. -/
theorem IsStarPacking.selected_residual_loss {G : SimpleGraph V}
    {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hCB : C ⊆ B)
    (b : C) (z : starResidual C L) :
    fullStarFiberLoss G C L (.inl b) (.inr z) ≤ starCollision G L b.val z.val := by
  classical
  have hAC : Disjoint A C := (Finset.disjoint_coe.mp hG.disjoint).mono_right hCB
  rw [fullStarFiberLoss,h.branch_edge_fiber hAC (.inl b) (.inr z) (by simp)]
  exact h.selected_residual_fiber_surplus hG hCB b z

/-- Residual/residual branches never lose a parallel copy. -/
theorem IsStarPacking.residual_loss_zero {G : SimpleGraph V}
    {A C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L) (hAC : Disjoint A C)
    (x y : starResidual C L) : fullStarFiberLoss G C L (.inr x) (.inr y)=0 := by
  classical
  by_cases hxy : x=y
  · subst y; exact fullStarFiberLoss_self G C L _
  rw [fullStarFiberLoss,h.branch_edge_fiber hAC (.inr x) (.inr y) (by simpa using hxy)]
  exact Nat.sub_eq_zero_of_le (residual_branch_fiber_card_le_one G C L x y)

/-- A conservative full-covering contraction bound. Every actual fiber
is included; the factor four safely pays for both ordered orientations. -/
theorem IsStarPacking.full_ordered_fiber_loss_le {G : SimpleGraph V}
    {A B C : Finset V} {ell : ℕ} {L : V → Finset V}
    (h : IsStarPacking G A C ell L)
    (hG : G.IsBipartiteWith (A:Set V) (B:Set V)) (hCB : C ⊆ B) :
    (∑ i : StarContractionVertex C L, ∑ j : StarContractionVertex C L,
      fullStarFiberLoss G C L i j) ≤
      4*(∑ b ∈ C, ∑ z : V, starCollision G L b z)+badStarPairCount G C L := by
  classical
  have hAC : Disjoint A C := (Finset.disjoint_coe.mp hG.disjoint).mono_right hCB
  have hCR : (∑ b : C, ∑ z : starResidual C L,
      fullStarFiberLoss G C L (.inl b) (.inr z)) ≤
      ∑ b ∈ C, ∑ z : V, starCollision G L b z := by
    calc
      _ ≤ ∑ b : C, ∑ z : starResidual C L, starCollision G L b.val z.val := by
        apply Finset.sum_le_sum
        intro b _
        exact Finset.sum_le_sum (fun z _ => h.selected_residual_loss hG hCB b z)
      _ ≤ _ := by
        have hb : (∑ b : C, ∑ z : V, starCollision G L b.val z) =
            ∑ b ∈ C, ∑ z : V, starCollision G L b z :=
          (Finset.sum_subtype C (fun _ => Iff.rfl) (fun b => ∑ z : V, starCollision G L b z)).symm
        rw [← hb]
        apply Finset.sum_le_sum
        intro b _
        have hz : (∑ z : starResidual C L, starCollision G L b.val z.val) =
            ∑ z ∈ starResidual C L, starCollision G L b.val z :=
          (Finset.sum_subtype (starResidual C L) (fun _ => Iff.rfl) (starCollision G L b.val)).symm
        rw [hz]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hRC : (∑ z : starResidual C L, ∑ b : C,
      fullStarFiberLoss G C L (.inr z) (.inl b)) ≤
      ∑ b ∈ C, ∑ z : V, starCollision G L b z := by
    simp_rw [fullStarFiberLoss_symm G C L (Sum.inr _) (Sum.inl _)]
    rw [Finset.sum_comm]
    exact hCR
  have hRR : (∑ x : starResidual C L, ∑ y : starResidual C L,
      fullStarFiberLoss G C L (.inr x) (.inr y))=0 := by
    simp only [h.residual_loss_zero hAC,Finset.sum_const_zero]
  have hSS := h.selected_loss_sum hG hCB
  have hselected := orderedStarSurplus_le G C L
  simp only [Fintype.sum_sum_type,Finset.sum_add_distrib]
  omega

end MinorFreeSpanners
