import GreedyShortcuts.ChainSharedPivotRootProjectionV2
import GreedyShortcuts.ChainGuardCone

/-! SOURCE ONLY, UNCOMPILED. Physical head representation of the EXISTING
fixed-root coneChains, and the actual parent/child cut of one projected
guard family. No normalized-history structure, rank or owner field is invented. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- New physical-head representation of the existing native label cone. -/
noncomputable def rootHeadCone (root W : V) : Finset V :=
  T.certifiedRootProjection root (T.coneChains root W)

theorem mem_rootHeadCone_iff {root W head : V} :
    head ∈ T.rootHeadCone root W ↔
      (root,head) ∈ T.important ∧ Reachable T.G head W ∧
        ∃ c,label T.chains head=some c := by
  classical
  constructor
  · intro hh
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨hsource,hreach⟩ := Finset.mem_filter.mp hc
    obtain ⟨_hu,hlabel,hip⟩ := Finset.mem_filter.mp hsource
    exact ⟨hip,hreach,c,hlabel⟩
  · rintro ⟨hip,hreach,c,hlabel⟩
    have hfirst := (T.important_spec hip).2
    have he : entry T.chains root c=head := by
      simpa only [first,hlabel] using hfirst
    refine Finset.mem_image.mpr ⟨c,?_,he⟩
    refine Finset.mem_filter.mpr ⟨?_,?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
      · simpa only [he] using hlabel
      · simpa only [he] using hip
    · simpa only [he] using hreach

theorem rootHeadCone_mono {root U W : V} (hUW : Reachable T.G U W) :
    T.rootHeadCone root U ⊆ T.rootHeadCone root W := by
  classical
  intro head hh
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hh
  exact Finset.mem_image.mpr ⟨c,T.coneChains_mono hUW hc,rfl⟩

/-- Membership in the TRUE parent is derived from the same guard/target
routes, not assumed as a substitute for child or excess ownership. -/
theorem projected_guard_subset_parent {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root s z v t W : V}
    (hroot : Reachable T.G root s)
    (repair : DWalk s z) (hrepair : Allowed (T.graph H s) repair)
    (reference : DWalk s v) (href : Allowed (T.graph H s) reference)
    (hzt : Reachable T.G z t) (htW : Reachable T.G t W) :
    T.certifiedRootProjection root (T.chainSet repair \ T.chainSet reference) ⊆
      T.rootHeadCone root W := by
  intro head hh
  obtain ⟨c,_hc,_heq,hlabel,_hr,_hf,hip,hheadz,_hnref,_he⟩ :=
    (T.certifiedRootProjection_difference hH hroot repair hrepair reference href).2.2 head hh
  exact T.mem_rootHeadCone_iff.mpr
    ⟨hip,reachable_trans hheadz (reachable_trans hzt htW),c,hlabel⟩

private theorem projectedCone_physical_partition (P C child old : Finset V)
    (hPC : P ⊆ C) :
    ((P \ old) ∩ child) ∪ ((P \ old) ∩ (C \ child))=P \ old ∧
      Disjoint ((P \ old) ∩ child) ((P \ old) ∩ (C \ child)) ∧
      P.card=(P ∩ old).card+((P \ old) ∩ child).card+
        ((P \ old) ∩ (C \ child)).card := by
  classical
  have hunion : ((P \ old) ∩ child) ∪ ((P \ old) ∩ (C \ child))=P \ old := by
    ext head
    constructor
    · intro hh
      rcases Finset.mem_union.mp hh with hh | hh
      · exact (Finset.mem_inter.mp hh).1
      · exact (Finset.mem_inter.mp hh).1
    · intro hh
      by_cases hc : head ∈ child
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hh,hc⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
          ⟨hh,Finset.mem_sdiff.mpr ⟨hPC (Finset.mem_sdiff.mp hh).1,hc⟩⟩)
  have hdisjoint : Disjoint ((P \ old) ∩ child) ((P \ old) ∩ (C \ child)) := by
    apply Finset.disjoint_left.mpr
    intro head hh hc
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hc).2).2 (Finset.mem_inter.mp hh).2
  have hcut := Finset.card_union_of_disjoint hdisjoint
  rw [hunion] at hcut
  have hold := Finset.card_sdiff_add_card_inter P old
  exact ⟨hunion,hdisjoint,by omega⟩

/-- One projected family, actual parent/child cones, and the exact old-stock
debit. Retention/removal depends on the HEAD reaching U, not on its possibly
later source-important entry. The temporal first-removal selector is not
part of the current native API and is not asserted by this one-cut lemma. -/
theorem projected_guard_owner_cut {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root s z v t U W : V}
    (hroot : Reachable T.G root s)
    (repair : DWalk s z) (hrepair : Allowed (T.graph H s) repair)
    (reference : DWalk s v) (href : Allowed (T.graph H s) reference)
    (hzt : Reachable T.G z t) (htW : Reachable T.G t W)
    (hUW : Reachable T.G U W) (old : Finset V) :
    let P := T.certifiedRootProjection root (T.chainSet repair \ T.chainSet reference)
    P ⊆ T.rootHeadCone root W ∧ T.rootHeadCone root U ⊆ T.rootHeadCone root W ∧
      ((P \ old) ∩ T.rootHeadCone root U) ∪
        ((P \ old) ∩ (T.rootHeadCone root W \ T.rootHeadCone root U))=P \ old ∧
      Disjoint ((P \ old) ∩ T.rootHeadCone root U)
        ((P \ old) ∩ (T.rootHeadCone root W \ T.rootHeadCone root U)) ∧
      P.card=(P ∩ old).card+((P \ old) ∩ T.rootHeadCone root U).card+
        ((P \ old) ∩ (T.rootHeadCone root W \ T.rootHeadCone root U)).card ∧
      ∀ head ∈ P,
        (head ∈ T.rootHeadCone root U ↔ Reachable T.G head U) ∧
        (head ∈ T.rootHeadCone root W \ T.rootHeadCone root U ↔
          ¬ Reachable T.G head U) := by
  classical
  dsimp only
  let P := T.certifiedRootProjection root (T.chainSet repair \ T.chainSet reference)
  have hparent : P ⊆ T.rootHeadCone root W :=
    T.projected_guard_subset_parent hH hroot repair hrepair reference href hzt htW
  obtain ⟨hunion,hdisjoint,hcard⟩ := projectedCone_physical_partition
    P (T.rootHeadCone root W) (T.rootHeadCone root U) old hparent
  refine ⟨hparent,T.rootHeadCone_mono hUW,hunion,hdisjoint,hcard,?_⟩
  intro head hh
  obtain ⟨hip,_hW,hlabel⟩ := T.mem_rootHeadCone_iff.mp (hparent hh)
  have hchild : head ∈ T.rootHeadCone root U ↔ Reachable T.G head U := by
    constructor
    · intro hc
      exact (T.mem_rootHeadCone_iff.mp hc).2.1
    · intro hu
      exact T.mem_rootHeadCone_iff.mpr ⟨hip,hu,hlabel⟩
  refine ⟨hchild,?_⟩
  constructor
  · intro hd hu
    exact (Finset.mem_sdiff.mp hd).2 (hchild.mpr hu)
  · intro hn
    exact Finset.mem_sdiff.mpr ⟨hparent hh,fun hc => hn (hchild.mp hc)⟩

end GreedyShortcuts.ChainDistance.Context
