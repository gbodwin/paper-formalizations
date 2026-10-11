import GreedyShortcuts.ChainSaturatedTransport
import GreedyShortcuts.ChainWindowRoutes

/-! Legality and acyclicity strengthen saturated-route transfer. They do not
supply reverse validity for a route above its endpoint floor. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- A legal saturated route cannot re-enter its starting chain. Therefore
its transfer needs the destination entry convention, but not the tail entry. -/
theorem saturated_route_transfer_of_first {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u v : V} (hsv : first T.chains s v=v) (huv : (u,v)∈T.important)
    (q : DWalk u v) (hq : Allowed (T.graph H u) q)
    (hcount : T.count q=T.endpointFloor u v) : Allowed (T.graph H s) q := by
  classical
  have hset := T.chainSet_eq_endpoints_of_saturated q hcount
  intro d hd
  have hh := hq d hd
  refine ⟨hh.1,?_⟩
  rcases hh.2 with he | hn | hf
  · exact Or.inl he
  · exact Or.inr (Or.inl hn)
  · by_cases hn : label T.chains d.snd=none
    · exact Or.inr (Or.inl hn)
    · obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hn
      have hmem : c∈T.chainSet q := (T.mem_chainSet q c).mpr
        ⟨d.snd,q.dart_snd_mem_support_of_mem_darts hd,hc⟩
      rw [hset] at hmem
      have hlabels : label T.chains u=some c ∨ label T.chains v=some c := by
        simpa using hmem
      rcases hlabels with hu | hv
      · have hfirst := (first_constant T.chains u d.snd u (hc.trans hu.symm)).trans (T.first_self u)
        have hdu : d.snd=u := hf.symm.trans hfirst
        have hr : Reachable T.G u d.fst :=
          (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
            ⟨q.takeUntil d.fst (q.dart_fst_mem_support_of_mem_darts hd),
              allowed_mono (fun _ _ h => h.1) (allowed_subwalk hq
                (q.isSubwalk_takeUntil (q.dart_fst_mem_support_of_mem_darts hd)))⟩
        have he : Reachable T.G d.fst u := by
          have h := (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
            (reachable_edge hh.1)
          simpa only [hdu] using h
        have huf := (acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hr he
        exact (d.fst_ne_snd (huf.symm.trans hdu.symm)).elim
      · have hs := (first_constant T.chains s d.snd v (hc.trans hv.symm)).trans
          hsv
        have ht := (first_constant T.chains u d.snd v (hc.trans hv.symm)).trans
          (T.important_spec huv).2
        exact Or.inr (Or.inr (hs.trans (ht.symm.trans hf)))

/-- Important destinations supply the required original-source entry. -/
theorem saturated_route_transfer_legal {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u v : V} (hsv : (s,v)∈T.important) (huv : (u,v)∈T.important)
    (q : DWalk u v) (hq : Allowed (T.graph H u) q)
    (hcount : T.count q=T.endpointFloor u v) : Allowed (T.graph H s) q :=
  T.saturated_route_transfer_of_first hH (T.important_spec hsv).2 huv q hq hcount

/-- Replacing every use of a saturated important edge preserves validity
and introduces no chain label absent from the original walk. -/
theorem eliminate_saturated_important_edge {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v : V} (huv : (u,v)∈T.important)
    (q : DWalk u v) (hq : Allowed (T.graph H u) q)
    (hcount : T.count q=T.endpointFloor u v) (s : V)
    {a b : V} (p : DWalk a b) (hp : Allowed (T.graph (insert (u,v) H) s) p) :
    ∃ r : DWalk a b,Allowed (T.graph H s) r ∧ T.chainSet r ⊆ T.chainSet p := by
  classical
  revert hp
  induction p with
  | nil => intro hp; exact ⟨.nil,allowed_nil _ _,Finset.Subset.refl _⟩
  | @cons a b t hab p ih =>
    intro hp
    obtain ⟨hedge,hp⟩ := (allowed_cons _ hab p).mp hp
    obtain ⟨tail,htail,hsubtail⟩ := ih hp
    let one : DWalk a b := .cons hab .nil
    have hpiece : ∃ r : DWalk a b,Allowed (T.graph H s) r ∧
        T.chainSet r ⊆ T.chainSet one := by
      by_cases he : (a,b)=(u,v)
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
        have hlabels : label T.chains a ≠ label T.chains b := by
          intro hh
          have hf := (first_constant T.chains a b a hh.symm).trans (T.first_self a)
          have heq := (T.important_spec huv).2.symm.trans hf
          exact (by simpa using hab : a≠b) heq.symm
        obtain ⟨c,hc⟩ := T.important_covered huv
        have hf := hedge.2.resolve_left hlabels |>.resolve_left (by simp [hc])
        refine ⟨q,T.saturated_route_transfer_of_first hH hf huv q hq hcount,?_⟩
        rw [T.chainSet_eq_endpoints_of_saturated q hcount]
        intro j hj
        rcases Finset.mem_union.mp hj with hj | hj
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

/-- A saturated important edge is globally redundant for every source's
normalized distance in a legal state. The original entry selectors stay fixed. -/
theorem distance_insert_saturated_eq {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v : V} (huv : (u,v)∈T.important)
    (hsat : T.distance H u v=T.endpointFloor u v) (s t : V) :
    T.distance (insert (u,v) H) s t=T.distance H s t := by
  classical
  apply Nat.le_antisymm (T.distance_antitone s t (Finset.subset_insert _ _))
  by_cases hr : Reachable T.G s t
  · obtain ⟨q,hq,hqc⟩ := T.distance_spec H (T.important_spec huv).1
    obtain ⟨p,hp,hpc⟩ := T.distance_spec (insert (u,v) H) hr
    obtain ⟨r,hrvalid,hsub⟩ := T.eliminate_saturated_important_edge hH huv q hq
      (hqc.trans hsat) s p hp
    exact (T.distance_le_walk H hr r hrvalid).trans ((Finset.card_le_card hsub).trans_eq hpc)
  · simp [distance,hr]

theorem potential_insert_saturated_eq {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {u v : V} (huv : (u,v)∈T.important)
    (hsat : T.distance H u v=T.endpointFloor u v) :
    T.potential (insert (u,v) H)=T.potential H := by
  apply Finset.sum_congr rfl
  intro st _
  exact T.distance_insert_saturated_eq hH huv hsat st.1 st.2

/-- Every important candidate with positive raw saving is itself unsaturated.
The conclusion concerns the actual whole raw objective, not one source row. -/
theorem positive_important_edge_unsaturated {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v : V} (huv : (u,v)∈T.important)
    (hdrop : T.potential (insert (u,v) H)<T.potential H) : (u,v)∈T.unsaturated H := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨huv,?_⟩
  by_contra hn
  change ¬T.endpointFloor u v<T.distance H u v at hn
  have hlo := T.endpointFloor_le_distance H (T.important_spec huv).1
  have hsat : T.distance H u v=T.endpointFloor u v := by omega
  rw [T.potential_insert_saturated_eq hH huv hsat] at hdrop
  exact (Nat.lt_irrefl _ hdrop)

/-- Saturation permanently retires an important candidate in every later
legal superstate; fixed original selectors are essential to this statement. -/
theorem saturated_edge_stays_redundant {H J : Finset (V × V)}
    (hJ : J ⊆ candidates T.G) (hHJ : H ⊆ J) {u v : V} (huv : (u,v)∈T.important)
    (hsat : T.distance H u v=T.endpointFloor u v) :
    T.potential (insert (u,v) J)=T.potential J := by
  apply T.potential_insert_saturated_eq hJ huv
  exact Nat.le_antisymm ((T.distance_antitone u v hHJ).trans_eq hsat)
    (T.endpointFloor_le_distance J (T.important_spec huv).1)

end GreedyShortcuts.ChainDistance.Context
