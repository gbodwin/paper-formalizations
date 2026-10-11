import GreedyShortcuts.ChainTailRowSupport

/-! Actual first-insertion and first-covered-entry decompositions for native
walks. These are route foundations, without a numerical progress hypothesis. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst CanonicalSegments ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

private theorem first_disallowed_decomposition {A B : V → V → Prop} {s t : V}
    (p : DWalk s t) (hp : Allowed A p) (hb : ¬Allowed B p) :
    ∃ a b,(∃ (h : (⊤ : SimpleGraph V).Adj a b) (l : DWalk s a) (r : DWalk b t),
      p=l.append (.cons h r) ∧ Allowed B l ∧ A a b ∧ ¬B a b ∧ Allowed A r) := by
  classical
  induction p with
  | nil => exact (hb (allowed_nil _ _)).elim
  | @cons s u t h p ih =>
    obtain ⟨hs,hp⟩ := (allowed_cons _ h p).mp hp
    by_cases hsB : B s u
    · have hb' : ¬Allowed B p := fun hp' => hb ((allowed_cons _ _ _).mpr ⟨hsB,hp'⟩)
      obtain ⟨a,b,h',l,r,he,hl,ha,hnb,hr⟩ := ih hp hb'
      refine ⟨a,b,h',.cons h l,r,?_,(allowed_cons _ _ _).mpr ⟨hsB,hl⟩,ha,hnb,hr⟩
      simp only [he,Walk.cons_append]
    · exact ⟨s,u,h,.nil,p,rfl,allowed_nil _ _,hs,hsB,hp⟩

/-- A legal one-edge improvement has a literal old prefix and old suffix.
A second use of the inserted dart would contradict original DAG acyclicity. -/
theorem improved_walk_insertion_decomposition {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {u v s t : V} (he : (u,v)∈candidates T.G)
    (p : DWalk s t) (hp : Allowed (T.graph (insert (u,v) H) s) p)
    (hb : ¬Allowed (T.graph H s) p) :
    ∃ (h : (⊤ : SimpleGraph V).Adj u v) (l : DWalk s u) (r : DWalk v t),
      p=l.append (.cons h r) ∧ Allowed (T.graph H s) l ∧
      T.graph (insert (u,v) H) s u v ∧ Allowed (T.graph H s) r := by
  classical
  have hlegal := Finset.insert_subset he hH
  obtain ⟨a,b,h,l,r,heq,hl,hab,hnot,hr⟩ := first_disallowed_decomposition p hp hb
  have habuv : (a,b)=(u,v) := by
    rcases hab.1 with hg | hh
    · exact (hnot ⟨Or.inl hg,hab.2⟩).elim
    rcases Finset.mem_union.mp hh with hc | hi
    · exact (hnot ⟨Or.inr (Finset.mem_union_left _ hc),hab.2⟩).elim
    rcases Finset.mem_insert.mp hi with heq | hm
    · exact heq
    · exact (hnot ⟨Or.inr (Finset.mem_union_right _ hm),hab.2⟩).elim
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj habuv
  refine ⟨h,l,r,heq,hl,hab,?_⟩
  intro d hd
  have hh := hr d hd
  refine ⟨?_,hh.2⟩
  rcases hh.1 with hg | hh'
  · exact Or.inl hg
  rcases Finset.mem_union.mp hh' with hc | hi
  · exact Or.inr (Finset.mem_union_left _ hc)
  rcases Finset.mem_insert.mp hi with hnew | hold
  · have hdu : d.fst=a := congrArg Prod.fst hnew
    have hback : Reachable T.G b a := by
      have hb' : Reachable T.G b d.fst :=
        (reachable_augment_iff T.G _ (T.augmentation_legal hlegal) _ _).mp
          ⟨r.takeUntil d.fst (r.dart_fst_mem_support_of_mem_darts hd),
            allowed_mono (fun _ _ h => h.1) (allowed_subwalk hr
              (r.isSubwalk_takeUntil (r.dart_fst_mem_support_of_mem_darts hd)))⟩
      simpa only [hdu] using hb'
    have hforward : Reachable T.G a b := (Finset.mem_filter.mp he).2.2
    exact (h.ne ((acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hforward hback)).elim
  · exact Or.inr (Finset.mem_union_right _ hold)

/-- A walk starting outside the cover and ending inside it has an actual
first-covered prefix. Its only chain label is the final one, and the fixed
source convention admits that literal entry. -/
theorem first_covered_prefix {H : Finset (V × V)} {s v t : V}
    (r : DWalk v t) (hr : Allowed (T.graph H s) r)
    (hv : label T.chains v=none) (ht : label T.chains t≠none) :
    ∃ (w : V) (c : I) (a : DWalk v w) (b : DWalk w t),
      r=a.append b ∧ label T.chains w=some c ∧ T.chainSet a={c} ∧
      first T.chains s w=w := by
  classical
  revert hr hv
  induction r with
  | nil => intro _ hv;exact (ht hv).elim
  | @cons v w t h r ih =>
    intro hr hv
    obtain ⟨hh,hr⟩ := (allowed_cons _ h r).mp hr
    by_cases hw : label T.chains w=none
    · obtain ⟨x,c,a,b,he,hxc,hset,hfirst⟩ := ih ht hr hw
      refine ⟨x,c,.cons h a,b,?_,hxc,?_,hfirst⟩
      · simp only [he,Walk.cons_append]
      · ext j
        rw [← hset]
        simp [T.mem_chainSet,hv]
    · obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hw
      refine ⟨w,c,.cons h .nil,r,rfl,hc,?_,?_⟩
      · ext j
        simp [T.mem_chainSet,hv,hc,eq_comm]
      · have hne : label T.chains v≠label T.chains w := by simp [hv,hc]
        exact hh.2.resolve_left hne |>.resolve_left hw

end GreedyShortcuts.ChainDistance.Context
