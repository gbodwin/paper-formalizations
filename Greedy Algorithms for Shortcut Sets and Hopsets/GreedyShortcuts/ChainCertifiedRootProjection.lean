import GreedyShortcuts.ChainEntries
import GreedyShortcuts.ChainFirst

/-! SOURCE ONLY, UNCOMPILED. Project actual reachable chain labels to the
original earliest entries of an explicitly parameterized root. No ROOT
field, rank, critical cone or physical-owner assertion is introduced. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def certifiedRootProjection (root : V) (C : Finset I) : Finset V :=
  C.image (entry T.chains root)

/-- Root-to-source reachability makes every visited chain genuinely root
reachable. The source-important entry and its ROOT projection are retained
as different vertices, related only by actual original reachability. -/
theorem root_projection_entry_on_walk {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root s z : V}
    (hroot : Reachable T.G root s) (walk : DWalk s z)
    (hwalk : Allowed (T.graph H s) walk) {c : I} (hc : c ∈ T.chainSet walk) :
    label T.chains (entry T.chains root c)=some c ∧
      Reachable T.G root (entry T.chains root c) ∧
      first T.chains root (entry T.chains root c)=entry T.chains root c ∧
      (root,entry T.chains root c) ∈ T.important ∧
      Reachable T.G (entry T.chains root c) z ∧
      ∃ e, e=entry T.chains s c ∧ e ∈ walk.support ∧
        label T.chains e=some c ∧ (s,e) ∈ T.important ∧
        Reachable T.G (entry T.chains root c) e ∧ Reachable T.G e z := by
  classical
  let e := entry T.chains s c
  have heEntry : e ∈ T.pathEntries walk := Finset.mem_image.mpr ⟨c,hc,rfl⟩
  obtain ⟨heMem,heImportant⟩ := T.pathEntries_mem hH walk hwalk heEntry
  have heLabel : label T.chains e=some c := T.entry_label hH walk hwalk hc
  have hse : Reachable T.G s e :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨walk.takeUntil e heMem,allowed_mono (fun _ _ h => h.1)
        (allowed_subwalk hwalk (walk.isSubwalk_takeUntil heMem))⟩
  have hez : Reachable T.G e z :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨walk.dropUntil e heMem,allowed_mono (fun _ _ h => h.1)
        (allowed_subwalk hwalk (walk.isSubwalk_dropUntil heMem))⟩
  have hre := reachable_trans hroot hse
  have hf := first_spec T.chains T.disjoint root e hre (by simp [heLabel])
  have hlabel : label T.chains (entry T.chains root c)=some c := by
    simpa only [first,heLabel] using hf.2.2.trans heLabel
  have hrhead : Reachable T.G root (entry T.chains root c) := by
    simpa only [first,heLabel] using hf.1
  have hheadE : Reachable T.G (entry T.chains root c) e := by
    simpa only [first,heLabel] using hf.2.1
  have hfirst : first T.chains root (entry T.chains root c)=entry T.chains root c := by
    simp only [first,hlabel]
  have himportant : (root,entry T.chains root c) ∈ T.important := by
    simpa only [first,heLabel] using T.first_important hre heLabel
  exact ⟨hlabel,hrhead,hfirst,himportant,reachable_trans hheadE hez,
    e,rfl,heMem,heLabel,heImportant,hheadE,hez⟩

/-- Injectivity is proved only on actually visited, root-reachable labels.
There is no claim that the total entry selector is injective on unreachable
chains, whose fallback may be the root itself. -/
theorem certifiedRootProjection_card {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root s z : V}
    (hroot : Reachable T.G root s) (walk : DWalk s z)
    (hwalk : Allowed (T.graph H s) walk) (C : Finset I)
    (hC : C ⊆ T.chainSet walk) :
    (T.certifiedRootProjection root C).card=C.card := by
  classical
  unfold certifiedRootProjection
  apply Finset.card_image_iff.mpr
  intro c hc d hd he
  have hlc := (T.root_projection_entry_on_walk hH hroot walk hwalk (hC hc)).1
  have hld := (T.root_projection_entry_on_walk hH hroot walk hwalk (hC hd)).1
  exact Option.some.inj (hlc.symm.trans ((congrArg (label T.chains) he).trans hld))

/-- Absent CHAIN labels, not merely absent source-entry vertices, yield
disjoint ROOT projection sets. All forward membership/reachability facts
refer to the same actual source walk and guard endpoint z. -/
theorem certifiedRootProjection_difference {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root s z v : V}
    (hroot : Reachable T.G root s)
    (repair : DWalk s z) (hrepair : Allowed (T.graph H s) repair)
    (reference : DWalk s v) (href : Allowed (T.graph H s) reference) :
    (T.certifiedRootProjection root (T.chainSet repair \ T.chainSet reference)).card=
      (T.chainSet repair \ T.chainSet reference).card ∧
      Disjoint (T.certifiedRootProjection root (T.chainSet repair \ T.chainSet reference))
        (T.certifiedRootProjection root (T.chainSet reference)) ∧
      ∀ head ∈ T.certifiedRootProjection root (T.chainSet repair \ T.chainSet reference),
        ∃ c ∈ T.chainSet repair \ T.chainSet reference,
          head=entry T.chains root c ∧ label T.chains head=some c ∧
          Reachable T.G root head ∧ first T.chains root head=head ∧
          (root,head) ∈ T.important ∧ Reachable T.G head z ∧
          head ∉ reference.support ∧
          ∃ e, e=entry T.chains s c ∧ e ∈ repair.support ∧
            label T.chains e=some c ∧ (s,e) ∈ T.important ∧
            Reachable T.G head e ∧ Reachable T.G e z := by
  classical
  have hcard := T.certifiedRootProjection_card hH hroot repair hrepair
    (T.chainSet repair \ T.chainSet reference) (fun _ hc => (Finset.mem_sdiff.mp hc).1)
  have hdisjoint : Disjoint
      (T.certifiedRootProjection root (T.chainSet repair \ T.chainSet reference))
      (T.certifiedRootProjection root (T.chainSet reference)) := by
    apply Finset.disjoint_left.mpr
    intro head hh hr
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨d,hd,he⟩ := Finset.mem_image.mp hr
    have hlc := (T.root_projection_entry_on_walk hH hroot repair hrepair
      (Finset.mem_sdiff.mp hc).1).1
    have hld := (T.root_projection_entry_on_walk hH hroot reference href hd).1
    have hdc : d=c :=
      Option.some.inj (hld.symm.trans ((congrArg (label T.chains) he).trans hlc))
    exact (Finset.mem_sdiff.mp hc).2 (hdc ▸ hd)
  refine ⟨hcard,hdisjoint,?_⟩
  intro head hh
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨hlabel,hrhead,hfirst,himportant,hheadz,he⟩ :=
    T.root_projection_entry_on_walk hH hroot repair hrepair (Finset.mem_sdiff.mp hc).1
  have hnref : entry T.chains root c ∉ reference.support := by
    intro hm
    exact (Finset.mem_sdiff.mp hc).2
      ((T.mem_chainSet reference c).mpr ⟨entry T.chains root c,hm,hlabel⟩)
  exact ⟨c,hc,rfl,hlabel,hrhead,hfirst,himportant,hheadz,hnref,he⟩

/-- An explicitly supplied actual guard-to-target route extends the forward
reachability of each projected head. No ROOT rank or cone owner is inferred. -/
theorem certifiedRootProjection_reaches_target {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root s z v t : V}
    (hroot : Reachable T.G root s)
    (repair : DWalk s z) (hrepair : Allowed (T.graph H s) repair)
    (reference : DWalk s v) (href : Allowed (T.graph H s) reference)
    (hzt : Reachable T.G z t) :
    ∀ head ∈ T.certifiedRootProjection root (T.chainSet repair \ T.chainSet reference),
      Reachable T.G head t := by
  intro head hh
  obtain ⟨c,hc,_heq,_hlabel,_hroot,_hfirst,_hip,hheadz,_hnref,_he⟩ :=
    (T.certifiedRootProjection_difference hH hroot repair hrepair reference href).2.2 head hh
  exact reachable_trans hheadz hzt

end GreedyShortcuts.ChainDistance.Context
