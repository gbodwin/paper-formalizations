import GreedyShortcuts.ChainCounting
import GreedyShortcuts.ChainHopCorrectness

/-! A genuine obstruction to source rebasing gives an earlier important target
with large normalized distance. This supplies no multiplicity or cubic-progress
bound, and never assumes hereditary optimality. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths CanonicalSegments ChainFirst ChainCover ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem last_disallowed_edge {A B : V → V → Prop} {u t : V}
    (q : DWalk u t) (hq : Allowed A q) (hbad : ¬ Allowed B q) :
    ∃ a b, A a b ∧ ¬ B a b ∧ ∃ r : DWalk b t,r.IsSubwalk q ∧ Allowed B r := by
  classical
  induction q with
  | nil => exact False.elim (hbad (allowed_nil _ _))
  | @cons u v t ha q ih =>
    have hqa := (allowed_cons A ha q).mp hq
    by_cases hqb : Allowed B q
    · refine ⟨u,v,hqa.1,?_,q,(Walk.isSubwalk_rfl q).cons ha,hqb⟩
      intro huv
      exact hbad ((allowed_cons B ha q).mpr ⟨huv,hqb⟩)
    · obtain ⟨a,b,hab,hnb,r,hr,hbr⟩ := ih hqa.2 hqb
      exact ⟨a,b,hab,hnb,r,hr.cons ha,hbr⟩

variable (T : ChainDistance.Context V I)

/-- Any path that cannot be moved to an ancestor's entry convention yields
an earlier important guard, with a precise distance loss. -/
theorem incompatible_guard {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t : V} (hsu : Reachable T.G s u) (q : DWalk u t)
    (hq : Allowed (T.graph H u) q) (hbad : ¬ Allowed (T.graph H s) q) :
    ∃ z, (s,z) ∈ T.important ∧ Reachable T.G s z ∧ Reachable T.G z t ∧
      ¬ Reachable T.G u z ∧ T.distance H s t+1 ≤ T.distance H s z+T.count q := by
  classical
  obtain ⟨a,b,hab,hnb,r,hr,hbr⟩ := last_disallowed_edge q hq hbad
  have hdiff : label T.chains a ≠ label T.chains b := by
    intro he; exact hnb ⟨hab.1,Or.inl he⟩
  have hcovered : label T.chains b ≠ none := by
    intro he; exact hnb ⟨hab.1,Or.inr (Or.inl he)⟩
  have hfirst : first T.chains u b = b := hab.2.resolve_left hdiff |>.resolve_left hcovered
  have hnfirst : first T.chains s b ≠ b := by
    intro he; exact hnb ⟨hab.1,Or.inr (Or.inr he)⟩
  obtain ⟨c,hbc⟩ := Option.ne_none_iff_exists'.mp hcovered
  have hbq : b ∈ q.support :=
    (Walk.isSubwalk_iff_support_isInfix.mp hr).subset r.start_mem_support
  have haug : Allowed (augment T.G (T.base ∪ H)) q :=
    allowed_mono (fun _ _ h => h.1) hq
  have hub : Reachable T.G u b :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨q.takeUntil b hbq,allowed_subwalk haug (q.isSubwalk_takeUntil hbq)⟩
  have hsb := reachable_trans hsu hub
  have hf := first_spec T.chains T.disjoint s b hsb hcovered
  let z := first T.chains s b
  have hzc : label T.chains z = some c := hf.2.2.trans hbc
  have hbt : Reachable T.G b t :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨r,allowed_mono (fun _ _ h => h.1) hbr⟩
  have hnuz : ¬ Reachable T.G u z := by
    intro huz
    have huf := first_spec T.chains T.disjoint u z huz (by simp [hzc])
    have he : first T.chains u z = b :=
      (first_constant T.chains u z b hf.2.2).trans hfirst
    rw [he] at huf
    have heq : z = b := (acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _ hf.2.1 huf.2.1
    exact hnfirst heq
  obtain ⟨p,hp,hpc⟩ := T.distance_spec H hf.1
  obtain ⟨w,hw,hw4,hwc⟩ := internal_short T hH hf.2.1 hzc hbc
  have hw' : Allowed (T.graph H s) w := T.allowed_internal w hw hwc
  have hall := (allowed_append _ _ _).mpr
    ⟨(allowed_append _ _ _).mpr ⟨hp,hw'⟩,hbr⟩
  have hdist := T.distance_le_walk H (reachable_trans hf.1 (reachable_trans hf.2.1 hbt))
    ((p.append w).append r) hall
  have hcount := T.count_append_covered (p.append w) r hbc
  rw [T.count_append_internal p w hwc,hpc] at hcount
  have hsub := T.count_subwalk hr
  exact ⟨z,T.first_important hsb hbc,hf.1,reachable_trans hf.2.1 hbt,hnuz,by dsimp only [z]; omega⟩

/-- A cheap rebased minimum either gives a true triangle inequality, or a
high-distance earlier important guard. This is only a dichotomy, not a
charging theorem. -/
theorem distance_guard_dichotomy {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {s u t : V} (hsu : Reachable T.G s u) (hut : Reachable T.G u t) :
    T.distance H s t ≤ T.distance H s u+T.distance H u t ∨
    ∃ z, (s,z) ∈ T.important ∧ Reachable T.G s z ∧ Reachable T.G z t ∧
      ¬ Reachable T.G u z ∧ T.distance H s t+1 ≤ T.distance H s z+T.distance H u t := by
  classical
  obtain ⟨q,hq,hqc⟩ := T.distance_spec H hut
  by_cases hqs : Allowed (T.graph H s) q
  · obtain ⟨p,hp,hpc⟩ := T.distance_spec H hsu
    have hd := T.distance_le_walk H (reachable_trans hsu hut) (p.append q)
      ((allowed_append _ _ _).mpr ⟨hp,hqs⟩)
    have hc := T.count_append_le p q
    rw [hpc,hqc] at hc
    exact Or.inl (hd.trans hc)
  · right
    simpa only [hqc] using T.incompatible_guard hH hsu q hq hqs

end GreedyShortcuts.ChainDistance.Context
