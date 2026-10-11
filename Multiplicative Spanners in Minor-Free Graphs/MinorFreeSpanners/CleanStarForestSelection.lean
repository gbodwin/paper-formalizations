import MinorFreeSpanners.CleanStarConstruction
import MinorFreeSpanners.FullCoverCardinality
import MinorFreeSpanners.MaximumCleanStarForest
import MinorFreeSpanners.BranchPartitionComparison

/-! Transport the constructed clean star into the canonical finite-family
quotient, then select a genuinely nonempty maximum clean family. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A grown identity-started star is an actual admissible one-star family.
Branch matching proves that canonicalization preserves its edge budget. -/
theorem CleanStarState.exists_small_clean_family {G : SimpleGraph V}
    {k : ℕ} {c : V} {T : Finset V} {q D : ℝ}
    (s : CleanStarState G k c T q (Fintype.card V) G.edgeFinset.card k)
    (hq : 0 ≤ q) (hadj : ∀ x ∈ T, G.Adj c x)
    (hsmall : ∀ x ∈ (insert c T:Set V), (G.degree x:ℝ) ≤ D) :
    ∃ L : V → Finset V, SmallCleanStarForest G k D (4*q) {c} L := by
  classical
  let S := (s.model.branch s.center).toFinset
  let L : V → Finset V := fun x => if x=c then S.erase c else ∅
  have hcS : c ∈ S := Set.mem_toFinset.mpr s.center_mem
  have hbranch : insert c (L c)=S := by simp [L,Finset.insert_erase hcS]
  have hforest : IsGeneralStarForest G k {c} L := by
    refine ⟨?_,?_,?_⟩
    · intro b hb x hx
      have he : b=c := Finset.mem_singleton.mp hb
      subst b
      have hx' : x ≠ c ∧ x ∈ S := by simpa [L] using hx
      exact s.center_adj hadj (Set.mem_toFinset.mp hx'.2) hx'.1
    · intro b hb
      have he : b=c := Finset.mem_singleton.mp hb
      subst b
      rw [hbranch]
      exact s.center_card
    · intro b hb a ha hba
      exact (hba ((Finset.mem_singleton.mp hb).trans (Finset.mem_singleton.mp ha).symm)).elim
  let N := hforest.fullMinorModel
  have hmatch : ∀ i, ∃ j, s.model.branch i=N.branch j := by
    intro i
    by_cases hi : i=s.center
    · subst i
      refine ⟨.inl ⟨c,Finset.mem_singleton_self c⟩,?_⟩
      simp only [N,IsGeneralStarForest.fullMinorModel,fullStarBranch,hbranch,S,Set.coe_toFinset]
    · obtain ⟨x,hx⟩ := s.other_singleton i hi
      have hxS : x ∉ S := by
        intro hxc
        have hxi : x ∈ s.model.branch i := by rw [hx];simp
        exact hi (s.model.branch_unique hxi (Set.mem_toFinset.mp hxc))
      have hres : x ∈ starResidual {c} L := by
        simp [starResidual,hbranch,hxS]
      refine ⟨.inr ⟨x,hres⟩,?_⟩
      simpa only [N,IsGeneralStarForest.fullMinorModel,fullStarBranch,Finset.coe_singleton] using hx
  have he := s.model.edge_count_le_of_branch_match N hforest.fullMinorModel_full hmatch
  refine ⟨L,hforest,?_,?_⟩
  · intro x hx
    have hxS : x ∈ S := by simpa only [Finset.singleton_biUnion,hbranch] using hx
    exact hsmall x (s.center_subset (Set.mem_toFinset.mp hxS))
  · have heR : (s.graph.edgeFinset.card:ℝ) ≤ (fullStarContraction G {c} L).edgeFinset.card := by
      exact_mod_cast he
    have hb := s.edge_budget
    have hkR : ((k-1:ℕ):ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    have hm := mul_le_mul_of_nonneg_right hkR hq
    have hz := mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) hq
    simp only [Finset.card_singleton,Nat.mul_one]
    nlinarith

/-- The actual single-star construction forces the finitely selected
maximum clean family to be nonempty. Its residual-degree properties still
require the separate extension/replacement proofs. -/
theorem clean_star_or_nonempty_maximum_forest (G : SimpleGraph V)
    (k : ℕ) (c : V) (T : Finset V) (K eps1 eps2 d : ℝ)
    (hk : 1 ≤ k) (hK : 1 ≤ K) (hd : 1 ≤ d)
    (he1 : 0 ≤ eps1) (he1' : eps1 ≤ 1) (he2 : 0 ≤ eps2)
    (hq : 1 ≤ eps2*d) (hkd : (k:ℝ) ≤ eps1*d)
    (hT : 2*eps1*d ≤ (T.card:ℝ)) (hadj : ∀ x ∈ T, G.Adj c x)
    (hsmall : ∀ x ∈ (insert c T:Set V), (G.degree x:ℝ) ≤ K*d) :
    (∃ S : Finset V, (S.card:ℝ) ≤ 3*k*(K*k)*d ∧
      eps1*eps2*d^2/2 ≤ ((G.induce (S:Set V)).edgeFinset.card:ℝ)) ∨
    ∃ C : Finset V, ∃ L : V → Finset V,
      SmallCleanStarForest G k (K*d) (4*(eps2*d)) C L ∧ C.Nonempty ∧
      ∀ C' L', SmallCleanStarForest G k (K*d) (4*(eps2*d)) C' L' → C'.card ≤ C.card := by
  classical
  have result := exists_clean_star_or_dense G k c T K eps1 eps2 d hk hK hd he1 he1' he2 hq hkd hT hadj hsmall
  cases result with
  | inl hDense => exact Or.inl hDense
  | inr hs =>
    obtain ⟨s⟩ := hs
    obtain ⟨L0,h0⟩ := s.exists_small_clean_family (by linarith) hadj hsmall
    obtain ⟨C,L,hCL,hmax⟩ := exists_maximum_small_clean_star_forest G k (K*d) (4*(eps2*d))
    have hc := hmax {c} L0 h0
    have hC : C.Nonempty := Finset.one_le_card.mp (by simpa using hc)
    exact Or.inr ⟨C,L,hCL,hC,hmax⟩

end MinorFreeSpanners
