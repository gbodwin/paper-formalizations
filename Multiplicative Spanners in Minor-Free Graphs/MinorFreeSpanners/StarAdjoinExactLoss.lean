import MinorFreeSpanners.ProtectedStarConstruction
import MinorFreeSpanners.GeneralStarInsertion
import MinorFreeSpanners.MaximumCleanStarForest
import MinorFreeSpanners.BranchPartitionComparison
import MinorFreeSpanners.FullCoverCardinality

/-! Canonicalize protected residual-star growth with its precise incremental
edge loss, without assuming a clean budget for the input family. This permits
uncontracting an old star before paying for two replacement stars. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem CleanStarState.adjoin_forest_with_loss {G : SimpleGraph V} {k : ℕ}
    {C T : Finset V} {L : V → Finset V} {c : V} {D q : ℝ}
    (h : IsGeneralStarForest G k C L)
    (hOldSmall : ∀ x ∈ C.biUnion (fun b => insert b (L b)), (G.degree x:ℝ) ≤ D)
    (hcR : c ∈ starResidual C L) (hTR : T ⊆ starResidual C L)
    (s : CleanStarState G k c T q (Fintype.card (StarContractionVertex C L))
      (fullStarContraction G C L).edgeFinset.card k)
    (hold : CleanStarState.OldBranchInvariant h.fullMinorModel s)
    (hadj : ∀ x ∈ T, G.Adj c x)
    (hsmall : ∀ x ∈ (insert c T:Set V), (G.degree x:ℝ) ≤ D) :
    ∃ L' : V → Finset V, IsGeneralStarForest G k (insert c C) L' ∧
      (∀ b ∈ C, L' b=L b) ∧
      insert c (L' c) ⊆ insert c T ∧
      (∀ x ∈ (insert c C).biUnion (fun b => insert b (L' b)), (G.degree x:ℝ) ≤ D) ∧
      ((fullStarContraction G C L).edgeFinset.card:ℝ) ≤
        (fullStarContraction G (insert c C) L').edgeFinset.card + 2*((k-1:ℕ):ℝ)*q := by
  classical
  let S := (s.model.branch s.center).toFinset
  let L' := adjoinStarLeaves L c S
  have hcS : c ∈ S := Set.mem_toFinset.mpr s.center_mem
  have hSR : S ⊆ starResidual C L := by
    intro x hx
    rcases s.center_subset (Set.mem_toFinset.mp hx) with hx | hx
    · simpa only [hx] using hcR
    · exact hTR hx
  have hdis : Disjoint S (C.biUnion fun b => insert b (L b)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxc
    exact (Finset.mem_sdiff.mp (hSR hx)).2 hxc
  have hcC := star_center_not_covered hcS hdis
  have hbc : ∀ b ∈ C, b ≠ c := fun b hb he => hcC (he ▸ hb)
  have hnew : IsGeneralStarForest G k (insert c C) L' :=
    h.adjoin hcS s.center_card
      (fun x hx hxc => s.center_adj hadj (Set.mem_toFinset.mp hx) hxc) hdis
  let N := hnew.fullMinorModel
  have hmatch : ∀ i, ∃ j, s.model.branch i=N.branch j := by
    intro i
    by_cases hi : i=s.center
    · subst i
      refine ⟨.inl ⟨c,Finset.mem_insert_self c C⟩,?_⟩
      simp only [N,IsGeneralStarForest.fullMinorModel,fullStarBranch,L',
        adjoinStar_branch_center L c S hcS,S,Set.coe_toFinset]
    · obtain ⟨j,hj⟩ := hold i hi
      cases j with
      | inl b =>
        refine ⟨.inl ⟨b.val,Finset.mem_insert_of_mem b.property⟩,?_⟩
        rw [hj]
        simp only [N,IsGeneralStarForest.fullMinorModel,fullStarBranch,L',
          adjoinStar_branch_old L c S (hbc b.val b.property)]
      | inr x =>
        have hx : s.model.branch i={x.val} := by
          simpa only [IsGeneralStarForest.fullMinorModel,fullStarBranch,Finset.coe_singleton] using hj
        have hxS : x.val ∉ S := by
          intro hxs
          have hxi : x.val ∈ s.model.branch i := by rw [hx];simp
          exact hi (s.model.branch_unique hxi (Set.mem_toFinset.mp hxs))
        have hxR : x.val ∈ starResidual (insert c C) L' := by
          have old := (Finset.mem_sdiff.mp x.property).2
          simp [starResidual,L',adjoinStar_covered C S L c hcS hcC,hxS,old]
        refine ⟨.inr ⟨x.val,hxR⟩,?_⟩
        simpa only [N,IsGeneralStarForest.fullMinorModel,fullStarBranch,Finset.coe_singleton] using hx
  have hedge := s.model.edge_count_le_of_branch_match N hnew.fullMinorModel_full hmatch
  refine ⟨L',hnew,?_,?_,?_,?_⟩
  · intro b hb
    simp [L',adjoinStarLeaves,hbc b hb]
  · rw [show insert c (L' c)=S by exact adjoinStar_branch_center L c S hcS]
    intro x hx
    simpa only [Finset.mem_insert,Set.mem_insert_iff,Finset.mem_coe] using
      s.center_subset (Set.mem_toFinset.mp hx)
  · intro x hx
    change x ∈ (insert c C).biUnion (fun b => insert b (adjoinStarLeaves L c S b)) at hx
    rw [adjoinStar_covered C S L c hcS hcC] at hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hsmall x (s.center_subset (Set.mem_toFinset.mp hx))
    · exact hOldSmall x hx
  · have heR : (s.graph.edgeFinset.card:ℝ) ≤ (fullStarContraction G (insert c C) L').edgeFinset.card := by
      exact_mod_cast hedge
    have he := s.edge_budget
    linarith

end MinorFreeSpanners
