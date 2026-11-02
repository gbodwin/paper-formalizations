import GreedyShortcuts.ChainCanonicalStepSummation

/-! SOURCE ONLY, UNCOMPILED. Actual owner population from the literal
ROOT-admitted selected k-level corridor prefix, not rank=cone cardinality
or a new population field. Original corridor/minimum/owner ties unchanged. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

theorem rootOwner_card_eq (root a : V) :
    Fintype.card (T.RootOwner root a)=(T.rootHeadCone root a).card := by
  classical
  have hinj : Function.Injective (fun y : T.RootOwner root a => y.val) :=
    fun _ _ he => Subtype.ext he
  have he : (Finset.univ : Finset (T.RootOwner root a)).image (fun y => y.val)=
      T.rootHeadCone root a := by
    ext v
    constructor
    · intro hv
      obtain ⟨y,_hy,rfl⟩ := Finset.mem_image.mp hv
      exact y.property
    · intro hv
      exact Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩
  have hc := Finset.card_image_of_injective (Finset.univ : Finset (T.RootOwner root a)) hinj
  rw [he,Finset.card_univ] at hc
  exact hc.symm

/-- The prefix has exactly k distinct ORIGINAL ROOT-heads, each reaching
the actual selected anchor. Covered/uncovered ROOT is not assigned a free
marker: the native selected prefix count and projection cardinal are exact. -/
theorem originalSelector_owner_prefix_heads {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U) :
    let heads := T.rootTailHeads root (d.corridor.take d.index)
    heads.card=k ∧ heads ⊆ T.rootHeadCone root (d.corridor.getVert d.index) := by
  have hroot : Reachable T.G root root := ⟨.nil,allowed_nil _ _⟩
  have hp := allowed_subwalk d.corridorAllowed (d.corridor.isSubwalk_take d.index)
  exact ⟨(T.rootTailHeads_card hH hroot _ hp).trans d.entryCount,
    T.rootTailHeads_subset_parent hH hroot _ hp⟩

/-- Actual SAME-ROOT minimum prefix rank and population inequality are
different outputs. No equality of rank and cone/owner cardinal is inferred. -/
theorem originalSelector_owner_population {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U) :
    T.distance H root (d.corridor.getVert d.index)=k ∧
      k≤Fintype.card (T.RootOwner root (d.corridor.getVert d.index)) := by
  have hrank := (T.root_minimum_prefix_price hH d.corridor d.corridorAllowed
    d.corridorMinimum d.index).symm.trans d.entryCount
  obtain ⟨hc,hsub⟩ := T.originalSelector_owner_prefix_heads hH d
  have hcard := Finset.card_le_card hsub
  rw [hc] at hcard
  rw [T.rootOwner_card_eq]
  exact ⟨hrank,hcard⟩

end GreedyShortcuts.ChainDistance.Context
