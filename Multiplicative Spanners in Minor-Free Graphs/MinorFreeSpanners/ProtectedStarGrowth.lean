import MinorFreeSpanners.CleanStarConstruction

/-! Preserve the actual initial branch partition during clean-star growth.
Every noncenter output branch is literally an initial branch; this is proved
for the same edge contractions that establish the size and edge-loss bounds. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
universe u
namespace CleanStarState
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {k r N E : ℕ} {c : V} {T : Finset V} {K eps1 eps2 d : ℝ}

/-- No untouched initial branch may be silently repartitioned. -/
def OldBranchInvariant {q : ℝ} {I0 : Type u} {F0 : SimpleGraph I0}
    (M0 : MinorModel F0 G) (s : CleanStarState G k c T q N E r) : Prop :=
  ∀ i, i ≠ s.center → ∃ j, s.model.branch i=M0.branch j

/-- The new graph, original branch sets, exact size and edge budget are all
constructed. Its mate hypothesis concerns this actual current quotient. -/
theorem step_preserving {I0 : Type u} {F0 : SimpleGraph I0}
    (M0 : MinorModel F0 G) (s : CleanStarState G k c T (eps2*d) N E r)
    (hold : OldBranchInvariant M0 s)
    (hr : r < k) (hK : 0 ≤ K) (hd : 0 ≤ d) (hq : 1 ≤ eps2*d)
    (hkd : (k:ℝ) ≤ eps1*d) (hT : 2*eps1*d ≤ (T.card:ℝ))
    (hadj : ∀ x ∈ T, G.Adj c x)
    (hsmall : ∀ x ∈ (insert c T:Set V), (G.degree x:ℝ) ≤ K*d)
    (hun : Unmated s.graph (K*k) eps1 eps2 d) :
    ∃ s' : CleanStarState G k c T (eps2*d) N E (r+1), OldBranchInvariant M0 s' := by
  classical
  let R := T \ (s.model.branch s.center).toFinset
  have hcard : T.card ≤ R.card+r := by
    have hs : T ⊆ R ∪ (s.model.branch s.center).toFinset := by
      intro x hx
      by_cases hb : x ∈ (s.model.branch s.center).toFinset
      · exact Finset.mem_union_right _ hb
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx,hb⟩)
    have hh := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
    rwa [s.center_card] at hh
  have hR : eps1*d ≤ (R.card:ℝ) := by
    have hcardR : (T.card:ℝ) ≤ R.card+r := by exact_mod_cast hcard
    have hrR : (r:ℝ) < k := by exact_mod_cast hr
    nlinarith
  have hdeg : (s.graph.degree s.center:ℝ) ≤ (K*k)*d := by
    have hh := s.model.degree_le_of_branch_small s.center k (K*d)
      (mul_nonneg hK hd) (s.bounded s.center)
      (fun x hx => hsmall x (s.center_subset hx))
    convert hh using 1
    ring
  obtain ⟨x,hx,v,hv,huv,hnon⟩ := s.model.exists_singleton_nonmate s.full
    s.center c s.center_mem R
    (fun x hx => hadj x (Finset.mem_sdiff.mp hx).1)
    (fun x hx => fun hb => (Finset.mem_sdiff.mp hx).2 (Set.mem_toFinset.mpr hb))
    (fun x hx => s.unused_singleton x (Finset.mem_sdiff.mp hx).1
      (fun hb => (Finset.mem_sdiff.mp hx).2 (Set.mem_toFinset.mpr hb)))
    (K*k) eps1 eps2 d hun hdeg hR
  have hxT : x ∈ T := (Finset.mem_sdiff.mp hx).1
  have hsize : (s.model.branch s.center).toFinset.card+
      (s.model.branch v).toFinset.card ≤ k := by
    rw [s.center_card,hv]
    simp only [Set.toFinset_singleton,Finset.card_singleton]
    omega
  have hbudget : (E:ℝ) ≤ (contractEdge s.graph s.center v).edgeFinset.card+
      2*((r+1-1:ℕ):ℝ)*(eps2*d) := by
    have he := contractEdge_edge_count s.graph s.center v huv
    have heR : ((contractEdge s.graph s.center v).edgeFinset.card:ℝ)+1+
        Fintype.card (s.graph.commonNeighbors s.center v) = s.graph.edgeFinset.card := by
      exact_mod_cast he
    have hrEq : ((r-1:ℕ):ℝ)+1=r := by
      exact_mod_cast Nat.sub_add_cancel (Nat.succ_le_of_lt s.positive)
    have hb := s.edge_budget
    simp only [Nat.add_sub_cancel]
    nlinarith
  refine ⟨{ Index := {i : s.Index // i ≠ v}
            finiteIndex := inferInstance
            vertex_count := ?_
            graph := contractEdge s.graph s.center v
            model := s.model.mergeEdge huv
            covers := s.model.mergeEdge_covers huv s.covers
            full := s.model.mergeEdge_full huv s.full
            bounded := s.model.mergeEdge_bounded huv k s.bounded hsize
            center := ⟨s.center,huv.ne⟩
            center_mem := ?_
            center_subset := ?_
            center_card := ?_
            positive := by omega
            unused_singleton := ?_
            edge_budget := by
              simp only [edgeFinset_card, ← Nat.card_eq_fintype_card] at hbudget ⊢
              exact hbudget },?_⟩
  · have hvcount := contractEdge_vertex_card v
    have hn : 0 < Fintype.card s.Index := Fintype.card_pos_iff.mpr ⟨s.center⟩
    have hbase := s.vertex_count
    omega
  · rw [s.model.mergeEdge_branch_center huv]
    exact Or.inl s.center_mem
  · rw [s.model.mergeEdge_branch_center huv,hv]
    intro y hy
    rcases hy with hy | hy
    · exact s.center_subset hy
    · have hy' : y=x := hy
      subst y
      exact Or.inr hxT
  · rw [s.model.mergeEdge_singleton_card huv hv,s.center_card]
  · intro y hy hout
    have houtOld : y ∉ s.model.branch s.center := by
      intro hb
      apply hout
      rw [s.model.mergeEdge_branch_center huv]
      exact Or.inl hb
    obtain ⟨j,hj⟩ := s.unused_singleton y hy houtOld
    have hju : j ≠ s.center := by
      intro he
      apply houtOld
      rw [← he,hj]
      simp
    have hjv : j ≠ v := by
      intro he
      apply hout
      rw [s.model.mergeEdge_branch_center huv]
      apply Or.inr
      rw [← he,hj]
      simp
    refine ⟨⟨j,hjv⟩,?_⟩
    rw [s.model.mergeEdge_branch_other huv _ hju]
    exact hj

  · intro i hi
    have hiu : i.val ≠ s.center := fun he => hi (Subtype.ext he)
    change ∃ j, (s.model.mergeEdge huv).branch i=M0.branch j
    rw [s.model.mergeEdge_branch_other huv i hiu]
    exact hold i.val hiu

end CleanStarState
end MinorFreeSpanners
