import LightEFTSpanners.SubdivisionCoreProjection

namespace LightEFTSpanners.ParallelSubdivision
open SimpleGraph Finset
variable {V I K : Type*} [Fintype I] [DecidableEq K] (C : SimpleGraph V)
attribute [local instance] Classical.propDecidable

omit [Fintype I] in
/-- With fixed original endpoints, the branch witness is necessarily a copy
of that exact original edge. -/
theorem projection_adj_canonical {T : SimpleGraph (Vertex (I:=I) C)}
    (hT : T≤graph C) {a b : V} (hab : C.Adj a b)
    (hp : (coreProjection C T).Adj a b) :
    ∃ j : I, T.Adj (Sum.inl a)
      (Sum.inr (⟨s(a,b),(mem_edgeSet C).mpr hab⟩,j)) := by
  obtain ⟨_,d,j,ha,hb⟩ := hp
  have hd : (d:Sym2 V)=s(a,b) :=
    (Sym2.mem_and_mem_iff hab.ne).mp ⟨hT ha,hT hb⟩
  have heq : d=⟨s(a,b),(mem_edgeSet C).mpr hab⟩ := Subtype.ext hd
  exact ⟨j,heq ▸ ha⟩

/-- Pairwise edge-disjoint subdivision subgraphs project with congestion at
most the number of copies. The proof charges each host to an actual half-edge. -/
theorem projection_congestion_le (indices : Finset K)
    (T : K → SimpleGraph (Vertex (I:=I) C))
    (hT : ∀ i∈indices,T i≤graph C)
    (hdisj : (indices:Set K).PairwiseDisjoint T) (e : Sym2 V) :
    (indices.filter (fun i => e∈(coreProjection C (T i)).edgeSet)).card ≤ Fintype.card I := by
  classical
  rcases e with ⟨a,b⟩
  let hosts := indices.filter (fun i => s(a,b)∈(coreProjection C (T i)).edgeSet)
  by_cases hempty : hosts=∅
  · change hosts.card≤_
    simp [hempty]
  have hex : ∀ i : {i // i∈hosts}, ∃ (hab : C.Adj a b) (j : I),
      (T i).Adj (Sum.inl a) (Sum.inr (⟨s(a,b),(mem_edgeSet C).mpr hab⟩,j)) := by
    intro i
    have hi := mem_filter.mp i.2
    have hp := (mem_edgeSet _).mp hi.2
    have hab := coreProjection_le C (hT i hi.1) hp
    obtain ⟨j,hj⟩ := projection_adj_canonical C (hT i hi.1) hab hp
    exact ⟨hab,j,hj⟩
  let color : {i // i∈hosts} → I := fun i => (hex i).choose_spec.choose
  have hinj : Function.Injective color := by
    intro i j hij
    by_contra hne
    have hne' : i.val≠j.val := fun h => hne (Subtype.ext h)
    have hd := hdisj (mem_filter.mp i.2).1 (mem_filter.mp j.2).1 hne'
    have hi := (hex i).choose_spec.choose_spec
    have hj := (hex j).choose_spec.choose_spec
    have hc : (hex i).choose_spec.choose=(hex j).choose_spec.choose := hij
    rw [hc] at hi
    exact (SimpleGraph.disjoint_left.mp hd) _ _ hi hj
  have hc := Fintype.card_le_of_injective color hinj
  simpa [hosts] using hc

/-- The actual projected and trimmed family inherits all core connectivity
and at most r congestion from r subdivision copies. Acyclicity of the supplied
subdivision subgraphs is unnecessary because native spanning forests are built. -/
theorem exists_projected_forest_family (indices : Finset K)
    (T : K → SimpleGraph (Vertex (I:=I) C))
    (hT : ∀ i∈indices,T i≤graph C)
    (hdisj : (indices:Set K).PairwiseDisjoint T) :
    ∃ F : K → SimpleGraph V,
      (∀ i∈indices,F i≤C ∧ (F i).IsAcyclic) ∧
      (∀ i∈indices,∀ u v,(T i).Reachable (Sum.inl u) (Sum.inl v) → (F i).Reachable u v) ∧
      (∀ e : Sym2 V,(indices.filter (fun i => e∈(F i).edgeSet)).card≤Fintype.card I) := by
  classical
  have hex := fun i : K => (coreProjection C (T i)).exists_isAcyclic_reachable_eq_le
  choose F hsub hac hr using hex
  refine ⟨F,?_,?_,?_⟩
  · intro i hi
    exact ⟨(hsub i).trans (coreProjection_le C (hT i hi)),hac i⟩
  · intro i hi u v ⟨p⟩
    rw [hr i]
    exact walk_coreProjection C (hT i hi) p
  · intro e
    apply le_trans (card_le_card ?_) (projection_congestion_le C indices T hT hdisj e)
    intro i hi
    obtain ⟨hi,he⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hi,edgeSet_mono (hsub i) he⟩

end LightEFTSpanners.ParallelSubdivision
