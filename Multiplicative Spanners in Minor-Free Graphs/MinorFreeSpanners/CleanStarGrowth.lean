import MinorFreeSpanners.CleanStarState

/-! One genuine greedy star extension. A real unused singleton is chosen
outside the current quotient's actual mate set, then contracted into the
center; the original branch grows by one and the literal edge loss is paid. -/
namespace MinorFreeSpanners
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
universe u
namespace CleanStarState
variable {V : Type u} [Fintype V] {G : SimpleGraph V}
variable {k r N E : ℕ} {c : V} {T : Finset V} {K eps1 eps2 d : ℝ}

/-- Start at an actual singleton center in a full covering contraction. -/
noncomputable def initial {I : Type u} [Fintype I] (F : SimpleGraph I)
    (M : MinorModel F G) (hcover : M.Covers) (hfull : M.IsFull)
    (hbound : M.IsBounded k) (i : I) (hc : M.branch i={c})
    (hsingle : ∀ x ∈ T, ∃ j, M.branch j={x}) (q : ℝ) :
    CleanStarState G k c T q (Fintype.card I) F.edgeFinset.card 1 where
  Index := I
  finiteIndex := inferInstance
  vertex_count := rfl
  graph := F
  model := M
  covers := hcover
  full := hfull
  bounded := hbound
  center := i
  center_mem := by rw [hc]; simp
  center_subset := by rw [hc]; simp
  center_card := by rw [hc]; simp
  positive := by omega
  unused_singleton := fun x hx _ => hsingle x hx
  edge_budget := by simp

/-- The new graph, original branch sets, exact size and edge budget are all
constructed. Its mate hypothesis concerns this actual current quotient. -/
theorem step (s : CleanStarState G k c T (eps2*d) N E r)
    (hr : r < k) (hK : 0 ≤ K) (hd : 0 ≤ d) (hq : 1 ≤ eps2*d)
    (hkd : (k:ℝ) ≤ eps1*d) (hT : 2*eps1*d ≤ (T.card:ℝ))
    (hadj : ∀ x ∈ T, G.Adj c x)
    (hsmall : ∀ x ∈ (insert c T:Set V), (G.degree x:ℝ) ≤ K*d)
    (hun : Unmated s.graph (K*k) eps1 eps2 d) :
    Nonempty (CleanStarState G k c T (eps2*d) N E (r+1)) := by
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
              exact hbudget }⟩
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

end CleanStarState
end MinorFreeSpanners
