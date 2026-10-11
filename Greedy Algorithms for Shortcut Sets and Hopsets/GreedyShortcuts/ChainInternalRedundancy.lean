import GreedyShortcuts.ChainSaturatedRedundancy

/-! Original forward same-chain edges are globally redundant because the
actual preprocessing supplies a route with no additional chain labels. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst ChainNormalization CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

private theorem support_label_of_internal {a b : V} (p : DWalk a b) {c : I}
    (hc : label T.chains a=some c)
    (hp : ∀ d∈p.darts,label T.chains d.fst=label T.chains d.snd) :
    ∀ x∈p.support,label T.chains x=some c := by
  revert hc hp
  induction p with
  | nil => intro hc _;simpa using hc
  | @cons a b t hab p ih =>
    intro hc hp
    have he : label T.chains a=label T.chains b := hp ⟨(a,b),hab⟩ (by simp)
    have ht : ∀ d∈p.darts,label T.chains d.fst=label T.chains d.snd :=
      fun d hd => hp d (by simp [hd])
    have hh := ih (he.symm.trans hc) ht
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc
    · exact hh x hx

/-- An explicitly supplied old route with endpoint-only chain labels replaces
all inserted-edge uses for a fixed source, without increasing its chain set. -/
theorem eliminate_label_redundant_edge (H : Finset (V × V)) {u v s : V}
    (q : DWalk u v) (hq : Allowed (T.graph H s) q)
    (hset : T.chainSet q ⊆ (label T.chains u).toFinset ∪ (label T.chains v).toFinset)
    {a b : V} (p : DWalk a b) (hp : Allowed (T.graph (insert (u,v) H) s) p) :
    ∃ r : DWalk a b,Allowed (T.graph H s) r ∧ T.chainSet r ⊆ T.chainSet p := by
  classical
  revert hp
  induction p with
  | nil => intro hp;exact ⟨.nil,allowed_nil _ _,Finset.Subset.refl _⟩
  | @cons a b t hab p ih =>
    intro hp
    obtain ⟨hedge,hp⟩ := (allowed_cons _ hab p).mp hp
    obtain ⟨tail,htail,hsubtail⟩ := ih hp
    let one : DWalk a b := .cons hab .nil
    have hpiece : ∃ r : DWalk a b,Allowed (T.graph H s) r ∧ T.chainSet r ⊆ T.chainSet one := by
      by_cases he : (a,b)=(u,v)
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
        refine ⟨q,hq,?_⟩
        intro j hj
        rcases Finset.mem_union.mp (hset hj) with hj | hj
        · exact (T.mem_chainSet one j).mpr ⟨a,one.start_mem_support,by simpa using hj⟩
        · exact (T.mem_chainSet one j).mpr ⟨b,one.end_mem_support,by simpa using hj⟩
      · have hold : T.graph H s a b := by
          refine ⟨?_,hedge.2⟩
          rcases hedge.1 with hg | hh
          · exact Or.inl hg
          rcases Finset.mem_union.mp hh with hb | hi
          · exact Or.inr (Finset.mem_union_left _ hb)
          exact Or.inr (Finset.mem_union_right _ ((Finset.mem_insert.mp hi).resolve_left he))
        exact ⟨one,(allowed_cons _ _ _).mpr ⟨hold,allowed_nil _ _⟩,Finset.Subset.refl _⟩
    obtain ⟨head,hhead,hsubhead⟩ := hpiece
    refine ⟨head.append tail,(allowed_append _ _ _).mpr ⟨hhead,htail⟩,?_⟩
    change T.chainSet (head.append tail) ⊆ T.chainSet (one.append p)
    rw [T.chainSet_append,T.chainSet_append]
    exact Finset.union_subset_union hsubhead hsubtail

/-- The real within-chain preprocessing gives an old route for every source
filter, with exactly the one covered endpoint label. -/
theorem internal_route_all_sources (H : Finset (V × V)) {u v : V}
    (huv : Reachable T.G u v) {c : I}
    (hu : label T.chains u=some c) (hv : label T.chains v=some c) :
    ∃ q : DWalk u v,T.chainSet q={c} ∧ ∀ s,Allowed (T.graph H s) q := by
  obtain ⟨q,hq,hcol⟩ := internal_walk T.acyclic T.chains T.disjoint T.witnesses u v
    (reachable_augment T.G T.base huv) (hu.trans hv.symm) (by simp [hv])
  have hsupport := T.support_label_of_internal q hu hcol
  refine ⟨q,T.chainSet_single_color q hsupport,?_⟩
  intro s
  apply T.allowed_internal q _ hsupport
  refine allowed_mono (H := augment T.G (T.base ∪ H)) ?_ hq
  intro a b hab
  exact hab.elim Or.inl (fun he => Or.inr (Finset.mem_union_left H he))

/-- Every original forward covered same-chain insertion preserves every
normalized distance, even if the remaining shortcut state is arbitrary. -/
theorem distance_insert_internal_eq (H : Finset (V × V)) {u v : V}
    (huv : Reachable T.G u v) {c : I}
    (hu : label T.chains u=some c) (hv : label T.chains v=some c) (s t : V) :
    T.distance (insert (u,v) H) s t=T.distance H s t := by
  classical
  apply Nat.le_antisymm (T.distance_antitone s t (Finset.subset_insert _ _))
  by_cases hr : Reachable T.G s t
  · obtain ⟨q,hset,hq⟩ := T.internal_route_all_sources H huv hu hv
    obtain ⟨p,hp,hpc⟩ := T.distance_spec (insert (u,v) H) hr
    have hsub : T.chainSet q ⊆ (label T.chains u).toFinset ∪ (label T.chains v).toFinset := by
      simp [hset,hu,hv]
    obtain ⟨r,hrvalid,hrsub⟩ := T.eliminate_label_redundant_edge H q (hq s) hsub p hp
    exact (T.distance_le_walk H hr r hrvalid).trans ((Finset.card_le_card hrsub).trans_eq hpc)
  · simp [distance,hr]

theorem potential_insert_internal_eq (H : Finset (V × V)) {u v : V}
    (huv : Reachable T.G u v) {c : I}
    (hu : label T.chains u=some c) (hv : label T.chains v=some c) :
    T.potential (insert (u,v) H)=T.potential H := by
  apply Finset.sum_congr rfl
  intro st _
  exact T.distance_insert_internal_eq H huv hu hv st.1 st.2

end GreedyShortcuts.ChainDistance.Context
