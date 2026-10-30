import GreedyShortcuts.ChainRootTailHeadOrder
import GreedyShortcuts.ChainOriginalTraceRemoval

/-! SOURCE ONLY, UNCOMPILED. Actual old-owner LAST-tail exterior relative
to the SAME selected child. Initial covered marker is counted once; no
row/source reuse, E, objective bank or insertion payment is asserted. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def rootTailExterior (root U : V) {b W : V} (q : DWalk b W) : Finset V :=
  T.rootTailHeads root q \ T.rootHeadCone root U

private theorem tailHead_max_inside_suffix {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W U v : V}
    (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q)
    (hv : v ∈ T.rootTailHeads root q ∩ T.rootHeadCone root U)
    (hmax : ∀ y ∈ T.rootTailHeads root q ∩ T.rootHeadCone root U,
      T.rootTailHeadPosition root q y≤T.rootTailHeadPosition root q v) :
    let i := T.rootTailHeadPosition root q v
    T.rootTailHeads root (q.drop i) ⊆ T.rootTailHeads root q ∧
      T.rootTailHeads root (q.drop i) ∩ T.rootHeadCone root U ⊆ {v} := by
  classical
  let i := T.rootTailHeadPosition root q v
  have hvi := T.rootTailHeadPosition_spec q (Finset.mem_inter.mp hv).1
  have hfirstAt : first T.chains root (q.getVert i)=v := hvi.2.2
  have hsub : T.rootTailHeads root (q.drop i) ⊆ T.rootTailHeads root q := by
    intro y hy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨c,T.chainSet_subwalk (q.isSubwalk_drop i) hc,rfl⟩
  refine ⟨hsub,?_⟩
  intro y hy
  obtain ⟨hyS,hyU⟩ := Finset.mem_inter.mp hy
  have hyP := hsub hyS
  have hypos := T.rootTailHeadPosition_spec q hyP
  have hle : T.rootTailHeadPosition root q y ≤ i := hmax y (Finset.mem_inter.mpr ⟨hyP,hyU⟩)
  obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hyS
  have hcP := T.chainSet_subwalk (q.isSubwalk_drop i) hc
  have hyLabel : label T.chains y=some c := by
    rw [← he]
    exact (T.root_projection_entry_on_walk hH hrootb q
      (T.allowed_rebase hH hrootb q hq) hcP).1
  have hphysicalLabel : label T.chains (q.getVert (T.rootTailHeadPosition root q y))=some c :=
    (T.rootTailHeadPosition_label hH hrootb q hq hyP).trans hyLabel
  have hcPrefix : c ∈ T.chainSet (q.take i) :=
    T.chainSet_subwalk (q.take_isSubwalk_take hle)
      ((T.mem_chainSet (q.take (T.rootTailHeadPosition root q y)) c).mpr
        ⟨q.getVert _,(q.take _).end_mem_support,hphysicalLabel⟩)
  have hjoin : Allowed (T.graph H b) ((q.take i).append (q.drop i)) := by
    simpa only [Walk.append_take_drop_eq] using T.allowed_rebase hH hrootb q hq
  have hinter := T.chainSet_append_inter hH (q.take i) (q.drop i) hjoin
  have hci : c ∈ T.chainSet (q.take i) ∩ T.chainSet (q.drop i) :=
    Finset.mem_inter.mpr ⟨hcPrefix,hc⟩
  rw [hinter] at hci
  have hic : label T.chains (q.getVert i)=some c := by
    simpa only [Option.mem_toFinset,Option.mem_def] using hci
  have hyv : y=v := by
    rw [← he]
    simpa only [first,hic] using hfirstAt
  exact Finset.mem_singleton.mpr hyv

/-- A real last inside head, selected from the ACTUAL finite head set,
gives a ROOT route whose remaining count is paid by exterior heads once.
The initial projected head may be before the literal tail start. -/
private theorem tailHead_last_inside_rank {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W U v : V}
    (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) (hU : T.RootConeMaximizer H root U U)
    (hv : v ∈ T.rootTailHeads root q ∩ T.rootHeadCone root U)
    (hmax : ∀ y ∈ T.rootTailHeads root q ∩ T.rootHeadCone root U,
      T.rootTailHeadPosition root q y≤T.rootTailHeadPosition root q v) :
    T.distance H root W-T.distance H root U≤(T.rootTailExterior root U q).card := by
  classical
  let i := T.rootTailHeadPosition root q v
  let u := q.getVert i
  let s := q.drop i
  let S := T.rootTailHeads root s
  have hvi := T.rootTailHeadPosition_spec q (Finset.mem_inter.mp hv).1
  have hfirstAt : first T.chains root (q.getVert i)=v := hvi.2.2
  have hrootu : Reachable T.G root u :=
    reachable_trans hrootb ((reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨q.take i,allowed_mono (fun _ _ h => h.1)
        (allowed_subwalk hq (q.isSubwalk_take i))⟩)
  have hs : Allowed (T.graph H root) s := allowed_subwalk hq (q.isSubwalk_drop i)
  obtain ⟨hsub,honly⟩ := tailHead_max_inside_suffix T hH hrootb q hq hv hmax
  have hvS : v ∈ S := by
    have hm := (T.rootTailHeads_marker (root := root) s hvi.2.1).1
    change first T.chains root (q.getVert i) ∈ S at hm
    simpa only [hfirstAt] using hm
  have hSE : S \ {v} ⊆ T.rootTailExterior root U q := by
    intro y hy
    obtain ⟨hyS,hyv⟩ := Finset.mem_sdiff.mp hy
    refine Finset.mem_sdiff.mpr ⟨hsub hyS,?_⟩
    intro hyU
    exact hyv (honly (Finset.mem_inter.mpr ⟨hyS,hyU⟩))
  have hsingleton : ({v} : Finset V) ⊆ S := by
    intro y hy
    simpa only [Finset.mem_singleton.mp hy] using hvS
  have hcS := Finset.card_sdiff_add_card_inter S {v}
  rw [Finset.inter_eq_right.mpr hsingleton,Finset.card_singleton] at hcS
  have hScount : S.card=T.count s := T.rootTailHeads_card hH hrootu s hs
  have hcard := Finset.card_le_card hSE
  obtain ⟨c,_hc,_he,hvc,hrootv,_hfirst,hip,_hvW,_hentry⟩ :=
    T.rootTailHeads_spec hH hrootb q hq (Finset.mem_inter.mp hv).1
  have huc : label T.chains u=some c :=
    (T.rootTailHeadPosition_label hH hrootb q hq (Finset.mem_inter.mp hv).1).trans hvc
  have hvu : Reachable T.G v u := by
    have hf := (first_spec T.chains T.disjoint root u hrootu hvi.2.1).2.1
    change Reachable T.G (first T.chains root (q.getVert i)) u at hf
    simpa only [hfirstAt] using hf
  obtain ⟨internal,hi,_hlen,hicolor⟩ := GreedyShortcuts.ChainCover.internal_short T hH hvu hvc huc
  have hir : Allowed (T.graph H root) internal := T.allowed_internal internal hi hicolor
  obtain ⟨p,hp,hpc⟩ := T.distance_spec H hrootv
  have hall : Allowed (T.graph H root) ((p.append internal).append s) :=
    (allowed_append _ _ _).mpr ⟨(allowed_append _ _ _).mpr ⟨hp,hir⟩,hs⟩
  have hrootW : Reachable T.G root W :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨(p.append internal).append s,allowed_mono (fun _ _ h => h.1) hall⟩
  have hd := T.distance_le_walk H hrootW ((p.append internal).append s) hall
  have hj := T.count_append_covered (p.append internal) s huc
  rw [T.count_append_internal p internal hicolor,hpc] at hj
  have hbound := hU.2 v (Finset.mem_inter.mp hv).2
  omega

/-- Honest actual disjunction: either NO head is inside and all chain
heads are exterior, or the real last-inside rank route supplies Delta.
No large interval, canonical retie or inherited suffix optimum is needed. -/
theorem rootTailExterior_alternative {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W U : V}
    (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) (hU : T.RootConeMaximizer H root U U) :
    (T.rootTailExterior root U q).card=T.count q ∨
      T.distance H root W-T.distance H root U≤(T.rootTailExterior root U q).card := by
  classical
  by_cases hex : (T.rootTailHeads root q ∩ T.rootHeadCone root U).Nonempty
  · obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image
      (T.rootTailHeads root q ∩ T.rootHeadCone root U) (T.rootTailHeadPosition root q) hex
    exact Or.inr (tailHead_last_inside_rank T hH hrootb q hq hU hv hmax)
  · have he : T.rootTailExterior root U q=T.rootTailHeads root q := by
      apply Finset.Subset.antisymm
      · exact Finset.sdiff_subset
      · intro v hv
        refine Finset.mem_sdiff.mpr ⟨hv,?_⟩
        intro hvU
        exact hex ⟨v,Finset.mem_inter.mpr ⟨hv,hvU⟩⟩
    exact Or.inl (he.symm ▸ T.rootTailHeads_card hH hrootb q hq)

theorem rootTailExterior_min_bound {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root b W U : V}
    (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) (hU : T.RootConeMaximizer H root U U) :
    min (T.count q-1) (T.distance H root W-T.distance H root U)≤
      (T.rootTailExterior root U q).card := by
  rcases T.rootTailExterior_alternative hH hrootb q hq hU with he|hd
  · exact (Nat.min_le_left _ _).trans (by omega)
  · exact (Nat.min_le_right _ _).trans hd

theorem rootTailHeads_subset_parent {H : Finset (V × V)} (hH : H ⊆ candidates T.G)
    {root b W : V} (hrootb : Reachable T.G root b) (q : DWalk b W)
    (hq : Allowed (T.graph H root) q) : T.rootTailHeads root q ⊆ T.rootHeadCone root W := by
  intro v hv
  obtain ⟨c,_hc,_he,hl,_hr,_hf,hip,hvW,_he'⟩ := T.rootTailHeads_spec hH hrootb q hq hv
  exact T.mem_rootHeadCone_iff.mpr ⟨hip,hvW,c,hl⟩

/-- This is EACH actual fixed old-owner walk/LAST tail, not an arbitrary
new row or whole-own-distance substitute. Its exact tau supplies the cap
on the genuine SAME-child drop from the existing original step theorem. -/
theorem originalOwnerTail_exterior {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    let F := d.tails y
    let E := T.rootTailExterior root U F.tail
    (T.rootTailHeads root F.tail).card=F.tau+1 ∧
      min F.tau (T.distance H root W-T.distance H root U)≤E.card ∧
      T.distance H root W-T.distance H root U≤E.card ∧
      E ⊆ T.originalStepFullCut d := by
  let F := d.tails y
  have hy := (T.mem_rootHeadCone_iff.mp y.property).1
  have hyb : Reachable T.G y.val F.entry :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨F.prefix,allowed_mono (fun _ _ h => h.1) F.ownPrefix⟩
  have hrootb := reachable_trans (T.important_spec hy).1 hyb
  obtain ⟨htau,_hp,_hwhole⟩ := T.ownerLastRootTail_prices hH F (d.owners y).property.2
  have hf := (T.originalSelectorStepData_facts hH hk hW d).1
  have hU := hf.2.2.1
  obtain ⟨_hip,_hUW,_hU,_hsub,_hproper,_hc,_hl,_hu,_hD,_ht,hrows,_hs⟩ := hf
  have hDrop := hrows y
  have hmin := T.rootTailExterior_min_bound hH hrootb F.tail F.rootTail hU
  have hcount := T.rootTailHeads_card hH hrootb F.tail F.rootTail
  have hmin' : min F.tau (T.distance H root W-T.distance H root U)≤
      (T.rootTailExterior root U F.tail).card := by
    have he : T.count F.tail-1=F.tau := by omega
    simpa only [he] using hmin
  have hD : T.distance H root W-T.distance H root U≤
      (T.rootTailExterior root U F.tail).card := by
    rw [Nat.min_eq_right hDrop] at hmin'
    exact hmin'
  refine ⟨hcount.trans htau.symm,hmin',hD,?_⟩
  intro v hv
  obtain ⟨hhead,hnot⟩ := Finset.mem_sdiff.mp hv
  exact Finset.mem_sdiff.mpr ⟨T.rootTailHeads_subset_parent hH hrootb F.tail F.rootTail hhead,hnot⟩

/-- Genuine root-to-physical-entry availability and the FIXED-ROOT suffix
minimum of the literal original row. No own-entry suffix optimum claimed. -/
theorem originalOwnerTail_entry_and_fixed_minimum {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    Reachable T.G root (d.tails y).entry ∧
      T.FixedRootSuffixMinimum H root (d.tails y).tail := by
  have hy := (T.mem_rootHeadCone_iff.mp y.property).1
  have hyb : Reachable T.G y.val (d.tails y).entry :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨(d.tails y).prefix,allowed_mono (fun _ _ h => h.1) (d.tails y).ownPrefix⟩
  exact ⟨reachable_trans (T.important_spec hy).1 hyb,
    T.ownerLastRootTail_fixed_root_minimum hH hy (d.tails y) (d.owners y).property.2⟩

/-- Exactly tau transition heads after removing ONE initial covered ROOT
projection. That projection need not equal the physical LAST entry. -/
theorem originalOwnerTail_marker_count {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    let F := d.tails y
    let m := first T.chains root F.entry
    m ∈ T.rootTailHeads root F.tail ∧ T.rootTailHeadPosition root F.tail m=0 ∧
      (T.rootTailHeads root F.tail \ {m}).card=F.tau := by
  classical
  let F := d.tails y
  let m := first T.chains root F.entry
  obtain ⟨hm,hpos⟩ := T.rootTailHeads_marker (root := root) F.tail F.covered
  have hc : (T.rootTailHeads root F.tail).card=F.tau+1 :=
    (T.originalOwnerTail_exterior hH hk hW d y).1
  have hsingle : ({m} : Finset V) ⊆ T.rootTailHeads root F.tail := by
    intro z hz
    simpa only [Finset.mem_singleton.mp hz] using hm
  have he := Finset.card_sdiff_add_card_inter (T.rootTailHeads root F.tail) {m}
  rw [Finset.inter_eq_right.mpr hsingle,Finset.card_singleton] at he
  refine ⟨hm,hpos,?_⟩
  change (T.rootTailHeads root F.tail \ {m}).card=F.tau
  omega

/-- W is actually INCLUDED in the exterior. If a later application removes
it, that costs exactly ONE head and the guaranteed bound becomes Delta-1. -/
theorem originalOwnerTail_endpoint_and_exclusion {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    let E := T.rootTailExterior root U (d.tails y).tail
    W ∈ E ∧ (E \ {W}).card+1=E.card ∧
      T.distance H root W-T.distance H root U-1≤(E \ {W}).card := by
  classical
  let E := T.rootTailExterior root U (d.tails y).tail
  have hIPW := (T.mem_rootHeadCone_iff.mp hW.1).1
  have hmem := T.rootTailHeads_endpoint (d.tails y).tail hIPW
  obtain ⟨_hip,hUW,_hU,_hsub,_hp,hcard,_hl,_hu,_hD,_ht,_hr,_hs⟩ :=
    (T.originalSelectorStepData_facts hH hk hW d).1
  have hnot : W ∉ T.rootHeadCone root U := by
    intro hWU
    have he : W=U := (GreedyShortcuts.CanonicalSegments.acyclic_iff_reachable_antisymm T.G).mp T.acyclic _ _
      (T.mem_rootHeadCone_iff.mp hWU).2.1 hUW
    rw [he] at hcard
    omega
  have hWE : W ∈ E := Finset.mem_sdiff.mpr ⟨hmem,hnot⟩
  have hsingle : ({W} : Finset V) ⊆ E := by
    intro z hz
    simpa only [Finset.mem_singleton.mp hz] using hWE
  have he := Finset.card_sdiff_add_card_inter E {W}
  rw [Finset.inter_eq_right.mpr hsingle,Finset.card_singleton] at he
  have hD : T.distance H root W-T.distance H root U≤E.card :=
    (T.originalOwnerTail_exterior hH hk hW d y).2.2.1
  refine ⟨hWE,he,?_⟩
  change T.distance H root W-T.distance H root U-1≤(E \ {W}).card
  omega

/-- OPTIONAL canonical display. The unchanged Q, physical LAST entry and
old prefix stay arguments. The existing explicit SAME-owner equal-price
splice discharges all changed-walk admission and marker prices; the row
family/selector is never silently replaced. -/
theorem originalOwnerTail_canonical_display {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    let F := d.tails y
    let r := T.rootCanonicalSuffix H root F.entry W ⟨F.tail,F.rootTail⟩
    Allowed (T.graph H y.val) r ∧ Allowed (T.graph H y.val) (F.prefix.append r) ∧
      T.count r=T.count F.tail ∧ T.count (F.prefix.append r)=T.distance H y.val W ∧
      F.tau+1=T.count r ∧
      (Allowed (T.graph H root) (F.prefix.append r) ↔ Allowed (T.graph H root) (d.owners y).val) ∧
      T.distance H root W-T.distance H root U≤(T.rootTailExterior root U r).card := by
  let F := d.tails y
  let r := T.rootCanonicalSuffix H root F.entry W ⟨F.tail,F.rootTail⟩
  have hy := (T.mem_rootHeadCone_iff.mp y.property).1
  obtain ⟨hrx,hsplice,heq,hprice,htau,hvalid⟩ :=
    T.ownerLastRootTail_coalescing_replacement hH hy F (d.owners y).property.2
  have hrootb := (T.originalOwnerTail_entry_and_fixed_minimum hH d y).1
  have hr : Allowed (T.graph H root) r :=
    (T.rootCanonicalSuffix_optimal H root F.entry W ⟨F.tail,F.rootTail⟩).1
  have hf := (T.originalSelectorStepData_facts hH hk hW d).1
  have hU := hf.2.2.1
  obtain ⟨_hip,_hUW,_hU,_hsub,_hp,_hc,_hl,_hu,_hD,_ht,hrows,_hs⟩ := hf
  have hdrop : T.distance H root W-T.distance H root U≤F.tau := hrows y
  have htauActual : F.tau+1=T.count r := htau
  have hE : T.distance H root W-T.distance H root U≤(T.rootTailExterior root U r).card := by
    rcases T.rootTailExterior_alternative hH hrootb r hr hU with he|hd
    · omega
    · exact hd
  exact ⟨hrx,hsplice,heq,hprice,htau,hvalid,hE⟩

end GreedyShortcuts.ChainDistance.Context
