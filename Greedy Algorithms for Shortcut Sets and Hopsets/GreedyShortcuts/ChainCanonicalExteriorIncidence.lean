import GreedyShortcuts.ChainCanonicalOwnerCut

/-! SOURCE ONLY, UNCOMPILED. Physical heads on the separately displayed
canonical tails, exact possible nonphysical marker debit and SAME-child
full-cut incidence. Original owner walks/ties are never replaced. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

private theorem coverage_heads_physical {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W : V} (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) (hb : (root,b) ∈ T.important) :
    T.rootTailHeads root q ⊆ q.support.toFinset := by
  intro t ht
  by_cases he : t=b
  · simpa only [he] using List.mem_toFinset.mpr q.start_mem_support
  · have hn : t≠first T.chains root b := by simpa only [(T.important_spec hb).2] using he
    exact List.mem_toFinset.mpr
      (T.rootTailHead_nonmarker_physical hH (T.important_spec hb).1 q hq ht hn).2

private theorem coverage_important_mem_heads {root b W t : V} (q : DWalk b W)
    (hip : (root,t) ∈ T.important) (ht : t ∈ q.support) :
    t ∈ T.rootTailHeads root q := by
  classical
  obtain ⟨c,hc⟩ := T.important_covered hip
  have he : entry T.chains root c=t := by simpa only [first,hc] using (T.important_spec hip).2
  exact Finset.mem_image.mpr ⟨c,(T.mem_chainSet q c).mpr ⟨t,ht,hc⟩,he⟩

noncomputable def rootTailPhysicalExterior (root U : V) {b W : V}
    (q : DWalk b W) : Finset V := T.rootTailExterior root U q ∩ q.support.toFinset

/-- The ONLY possibly nonphysical projected head is the initial projection.
The formula has no covered-marker premise: the debit is exactly its actual
exterior/nonphysical membership, not an automatic free unit. -/
theorem rootTailExterior_physical_marker {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W U : V}
    (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) :
    let E := T.rootTailExterior root U q
    let m := first T.chains root b
    E \ q.support.toFinset ⊆ {m} ∧
      E.card=(T.rootTailPhysicalExterior root U q).card+
        (if m ∈ E ∧ m ∉ q.support then 1 else 0) ∧
      E.card≤(T.rootTailPhysicalExterior root U q).card+1 := by
  classical
  let E := T.rootTailExterior root U q
  let m := first T.chains root b
  let missing := E \ q.support.toFinset
  have hsub : missing ⊆ {m} := by
    intro t ht
    obtain ⟨htE,htQ⟩ := Finset.mem_sdiff.mp ht
    by_contra hn
    have hne : t≠first T.chains root b := by simpa only [Finset.mem_singleton] using hn
    have hphys := (T.rootTailHead_nonmarker_physical hH hrootb q hq
      (Finset.mem_sdiff.mp htE).1 hne).2
    exact htQ (List.mem_toFinset.mpr hphys)
  have hmc : missing.card=(if m ∈ E ∧ m ∉ q.support then 1 else 0) := by
    by_cases hm : m ∈ E ∧ m ∉ q.support
    · have hmem : m ∈ missing := Finset.mem_sdiff.mpr ⟨hm.1,by simpa using hm.2⟩
      have he : missing={m} := Finset.Subset.antisymm hsub (by
        intro t ht;simpa only [Finset.mem_singleton.mp ht] using hmem)
      simp only [he,Finset.card_singleton,if_pos hm]
    · have he : missing=∅ := by
        ext t
        simp only [Finset.notMem_empty,iff_false]
        intro ht
        have htM := Finset.mem_singleton.mp (hsub ht)
        have hmem : m ∈ missing := htM ▸ ht
        obtain ⟨hmE,hmQ⟩ := Finset.mem_sdiff.mp hmem
        exact hm ⟨hmE,by simpa using hmQ⟩
      simp only [he,Finset.card_empty,if_neg hm]
  have hc := Finset.card_sdiff_add_card_inter E q.support.toFinset
  have he : E.card=(T.rootTailPhysicalExterior root U q).card+
      (if m ∈ E ∧ m ∉ q.support then 1 else 0) := by
    change missing.card+(T.rootTailPhysicalExterior root U q).card=E.card at hc
    rw [hmc] at hc
    omega
  refine ⟨hsub,he,?_⟩
  rw [he]
  split_ifs <;> omega

/-- A genuine ROOT-first start discharges the initial projection issue. -/
theorem rootTailPhysicalExterior_of_important_start {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W U : V} (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) (hb : (root,b) ∈ T.important) :
    T.rootTailPhysicalExterior root U q=T.rootTailExterior root U q := by
  apply Finset.inter_eq_left.mpr
  exact fun _ ht => coverage_heads_physical T hH q hq hb (Finset.mem_sdiff.mp ht).1

noncomputable def originalCanonicalPhysicalExterior {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) : Finset V :=
  T.rootTailPhysicalExterior root U (T.originalOwnerCanonicalTail d y)

/-- Actual canonical root admission and root-to-physical-LAST-entry access.
These are the displayed ROOT minimum's contracts, not an own-entry optimum. -/
theorem originalCanonicalTail_root {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    Reachable T.G root (d.tails y).entry ∧
      T.FixedRootSuffixMinimum H root (T.originalOwnerCanonicalTail d y) := by
  have hrootb := (T.originalOwnerTail_entry_and_fixed_minimum hH d y).1
  exact ⟨hrootb,T.rootCanonicalSuffix_native_minimum hH hrootb
    ⟨(d.tails y).tail,(d.tails y).rootTail⟩⟩

theorem originalCanonicalExterior_subset_cut {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    T.rootTailExterior root U (T.originalOwnerCanonicalTail d y) ⊆ T.originalStepFullCut d := by
  obtain ⟨hrootb,hr⟩ := T.originalCanonicalTail_root hH d y
  intro v hv
  obtain ⟨hvP,hvU⟩ := Finset.mem_sdiff.mp hv
  exact Finset.mem_sdiff.mpr ⟨T.rootTailHeads_subset_parent hH hrootb _ hr.1 hvP,hvU⟩

/-- The physical exterior incidence is EXACTLY cut membership and the
already defined physical canonical group. A mere projected image is not
silently promoted to a group member. -/
theorem mem_originalCanonicalPhysicalExterior {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U v : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    v ∈ T.originalCanonicalPhysicalExterior d y ↔
      v ∈ T.originalStepFullCut d ∧ y ∈ T.originalOwnerCanonicalGroup d v := by
  obtain ⟨hrootb,hr⟩ := T.originalCanonicalTail_root hH d y
  constructor
  · intro hv
    obtain ⟨hvE,hvQ⟩ := Finset.mem_inter.mp hv
    obtain ⟨hvP,hvU⟩ := Finset.mem_sdiff.mp hvE
    exact ⟨Finset.mem_sdiff.mpr
      ⟨T.rootTailHeads_subset_parent hH hrootb _ hr.1 hvP,hvU⟩,
      (T.mem_originalOwnerCanonicalGroup d y).mpr (List.mem_toFinset.mp hvQ)⟩
  · rintro ⟨hvCut,hy⟩
    obtain ⟨hvParent,hvU⟩ := Finset.mem_sdiff.mp hvCut
    have hvQ := (T.mem_originalOwnerCanonicalGroup d y).mp hy
    have hvP := coverage_important_mem_heads T _ (T.mem_rootHeadCone_iff.mp hvParent).1 hvQ
    exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hvP,hvU⟩,List.mem_toFinset.mpr hvQ⟩

/-- The canonical display has its OWN head set. Its exterior rank bound
is imported only after the explicit equal-price SAME-owner splice. The
physical set pays the exact possible marker, at most one, not a new budget. -/
theorem originalCanonicalPhysicalExterior_drop {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    let r := T.originalOwnerCanonicalTail d y
    let E := T.rootTailExterior root U r
    let C := T.originalCanonicalPhysicalExterior d y
    E.card=C.card+(if first T.chains root (d.tails y).entry ∈ E ∧
      first T.chains root (d.tails y).entry ∉ r.support then 1 else 0) ∧
      T.distance H root W-T.distance H root U≤C.card+1 ∧
      C ⊆ T.originalStepFullCut d := by
  obtain ⟨hrootb,hr⟩ := T.originalCanonicalTail_root hH d y
  obtain ⟨_hx,_hwhole,_heq,_hprice,_htau,_hvalid,hD⟩ :=
    T.originalOwnerTail_canonical_display hH hk hW d y
  obtain ⟨_hsub,he,hbound⟩ := T.rootTailExterior_physical_marker hH hrootb _ hr.1
  have hDActual : T.distance H root W-T.distance H root U≤
      (T.rootTailExterior root U (T.originalOwnerCanonicalTail d y)).card := hD
  have hphysicalActual : (T.rootTailExterior root U (T.originalOwnerCanonicalTail d y)).card≤
      (T.originalCanonicalPhysicalExterior d y).card+1 := hbound
  refine ⟨he,hDActual.trans hphysicalActual,?_⟩
  intro v hv
  exact ((T.mem_originalCanonicalPhysicalExterior hH d y).mp hv).1

/-- Distinct physical head vertices have distinct actual first-occurrence
positions. No equality between a position and a chain rank is asserted. -/
theorem originalCanonicalPhysicalExterior_order_injective {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    {v w : V} (hv : v ∈ T.originalCanonicalPhysicalExterior d y)
    (hw : w ∈ T.originalCanonicalPhysicalExterior d y)
    (he : T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) v=
      T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) w) : v=w := by
  exact T.rootTailHeadPosition_injective _
    (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).1).1
    (Finset.mem_sdiff.mp (Finset.mem_inter.mp hw).1).1 he

theorem originalCanonicalPhysicalExterior_order {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    {v w : V} (hv : v ∈ T.originalCanonicalPhysicalExterior d y)
    (hw : w ∈ T.originalCanonicalPhysicalExterior d y)
    (horder : T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) v≤
      T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) w) :
    Reachable T.G v w := by
  obtain ⟨hrootb,hr⟩ := T.originalCanonicalTail_root hH d y
  exact T.rootTailHeads_order hH hrootb _ hr.1
    (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).1).1
    (Finset.mem_sdiff.mp (Finset.mem_inter.mp hw).1).1 horder

/-- W remains a real physical exterior head of the canonical display.
Only the old literal proof's SAME-child nonmembership is reused, not its
head set. Removing W costs one more head after the possible marker debit. -/
theorem originalCanonicalPhysicalExterior_W_debit {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    let C := T.originalCanonicalPhysicalExterior d y
    W ∈ C ∧ (C \ {W}).card+1=C.card ∧
      T.distance H root W-T.distance H root U≤(C \ {W}).card+2 := by
  classical
  have hWE := (T.originalOwnerTail_endpoint_and_exclusion hH hk hW d y).1
  have hWNotU := (Finset.mem_sdiff.mp hWE).2
  have hWP := T.rootTailHeads_endpoint (T.originalOwnerCanonicalTail d y)
    (T.mem_rootHeadCone_iff.mp hW.1).1
  have hWC : W ∈ T.originalCanonicalPhysicalExterior d y :=
    Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hWP,hWNotU⟩,
      List.mem_toFinset.mpr (T.originalOwnerCanonicalTail d y).end_mem_support⟩
  have hc := Finset.card_sdiff_add_card_inter (T.originalCanonicalPhysicalExterior d y) {W}
  have hsub : ({W} : Finset V) ⊆ T.originalCanonicalPhysicalExterior d y := by
    intro z hz
    simpa only [Finset.mem_singleton.mp hz] using hWC
  rw [Finset.inter_eq_right.mpr hsub,Finset.card_singleton] at hc
  have hD := (T.originalCanonicalPhysicalExterior_drop hH hk hW d y).2.1
  exact ⟨hWC,hc,by omega⟩

end GreedyShortcuts.ChainDistance.Context
