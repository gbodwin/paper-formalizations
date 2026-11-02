import GreedyShortcuts.ChainCanonicalExteriorIncidence
import GreedyShortcuts.ChainCanonicalMidpointPressure

/-! SOURCE ONLY, UNCOMPILED. Actual row/head incidence, literal coalescing
remaining suffixes and finite weighted reindexing. A per-center cap is
conditional on the SAME current FULL cap; no alternative gains are summed. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- An actual available member supplies the path. The zero value outside
that domain does not assert a route, a row or a favorable shared family. -/
noncomputable def originalCanonicalRemainingCount {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U)
    (v : V) : ℕ := by
  classical
  exact if h : ∃ y : T.RootOwner root (d.corridor.getVert d.index),
      v ∈ (T.originalOwnerCanonicalTail d y).support then
    T.count (T.originalOwnerSharedSuffix d (Classical.choose h) (Classical.choose_spec h)) else 0

/-- Independence is a consequence of literal global coalescence at the
actual physical v, not equal labels, prices or a desired invariant field. -/
theorem originalCanonicalRemainingCount_eq {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U v : V} (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    (hv : v ∈ (T.originalOwnerCanonicalTail d y).support) :
    T.originalCanonicalRemainingCount d v=T.count (T.originalOwnerSharedSuffix d y hv) := by
  classical
  have h : ∃ z : T.RootOwner root (d.corridor.getVert d.index),
      v ∈ (T.originalOwnerCanonicalTail d z).support := ⟨y,hv⟩
  simp only [originalCanonicalRemainingCount,dif_pos h]
  exact congrArg (fun q : DWalk v W => T.count q)
    (T.originalOwnerCanonicalGroup_coalesces d y hv (Classical.choose h)
      ((T.mem_originalOwnerCanonicalGroup d (Classical.choose h)).mpr (Classical.choose_spec h)))

/-- At a PHYSICAL exterior center every remaining ROOT head is still
exterior and physical. The exact remaining count is the cardinal of these
actual later row incidences, including W once; positions are not ranks. -/
theorem originalCanonicalPhysicalExterior_remaining {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U v : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    (hv : v ∈ T.originalCanonicalPhysicalExterior d y) :
    let hvQ := (T.mem_originalOwnerCanonicalGroup d y).mp
      ((T.mem_originalCanonicalPhysicalExterior hH d y).mp hv).2
    let q := T.originalOwnerSharedSuffix d y hvQ
    T.originalCanonicalPhysicalExterior d y ∩ q.support.toFinset=T.rootTailHeads root q ∧
      (T.originalCanonicalPhysicalExterior d y ∩ q.support.toFinset).card=
        T.originalCanonicalRemainingCount d v := by
  classical
  obtain ⟨hvCut,hy⟩ := (T.mem_originalCanonicalPhysicalExterior hH d y).mp hv
  let hvQ := (T.mem_originalOwnerCanonicalGroup d y).mp hy
  let r := T.originalOwnerCanonicalTail d y
  let p := r.takeUntil v hvQ
  let q := T.originalOwnerSharedSuffix d y hvQ
  have he : p.append q=r := r.take_spec hvQ
  obtain ⟨hrootb,hr⟩ := T.originalCanonicalTail_root hH d y
  obtain ⟨hq,hrootv,_hmin⟩ := T.originalOwnerSharedSuffix_root hH d y hvQ
  obtain ⟨hvParent,hvU⟩ := Finset.mem_sdiff.mp hvCut
  have hvIP := (T.mem_rootHeadCone_iff.mp hvParent).1
  have hsplit : Allowed (T.graph H root) (p.append q) := by simpa only [he] using hr.1
  have htEq : T.rootTailHeads root r ∩ q.support.toFinset=T.rootTailHeads root q := by
    simpa only [he] using T.rootTailHeads_suffix_targets hH hrootb p q hsplit hvIP
  have hset : T.originalCanonicalPhysicalExterior d y ∩ q.support.toFinset=
      T.rootTailHeads root q := by
    ext t
    constructor
    · intro ht
      obtain ⟨htC,htQ⟩ := Finset.mem_inter.mp ht
      have htR := (Finset.mem_sdiff.mp (Finset.mem_inter.mp htC).1).1
      rw [← htEq]
      exact Finset.mem_inter.mpr ⟨htR,htQ⟩
    · intro ht
      have htQ := T.rootTailHeads_physical hH q hq hvIP ht
      have htPhys := List.mem_toFinset.mp htQ
      have htR := (Finset.mem_inter.mp (htEq.symm ▸ ht)).1
      have htRPhys : t ∈ r.support :=
        (Walk.isSubwalk_iff_support_isInfix.mp (r.isSubwalk_dropUntil hvQ)).subset htPhys
      have hvt : Reachable T.G v t :=
        (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
          ⟨q.takeUntil t htPhys,allowed_mono (fun _ _ h => h.1)
            (allowed_subwalk hq (q.isSubwalk_takeUntil htPhys))⟩
      have htU : t ∉ T.rootHeadCone root U := by
        intro htIn
        obtain ⟨cv,hvc⟩ := T.important_covered hvIP
        exact hvU (T.mem_rootHeadCone_iff.mpr
          ⟨hvIP,reachable_trans hvt (T.mem_rootHeadCone_iff.mp htIn).2.1,cv,hvc⟩)
      exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨htR,htU⟩,List.mem_toFinset.mpr htRPhys⟩,htQ⟩
  refine ⟨hset,?_⟩
  rw [hset,T.rootTailHeads_card hH hrootv q hq]
  exact (T.originalCanonicalRemainingCount_eq d y hvQ).symm

def canonicalMidpointWeight (N : ℕ) : ℕ := ((N-1)/2)*(N-1-(N-1)/2)

noncomputable def originalCanonicalRowWeight {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) (v : V) : ℕ := by
  classical
  exact if hv : v ∈ (T.originalOwnerCanonicalTail d y).support then
    canonicalMidpointWeight (T.count (T.originalOwnerSharedSuffix d y hv)) else 0

theorem originalCanonicalRowWeight_eq {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U v : V} (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    (hv : v ∈ (T.originalOwnerCanonicalTail d y).support) :
    T.originalCanonicalRowWeight d y v=canonicalMidpointWeight (T.originalCanonicalRemainingCount d v) := by
  classical
  simp only [originalCanonicalRowWeight,dif_pos hv,T.originalCanonicalRemainingCount_eq d y hv]

/-- Finite EXACT incidence, for arbitrary natural weights. It is a
reindexing of old physical records, NOT a sum of candidate scores or an
injection into new physical heads/owners. Repeated centers have their full
actual group factor; no population, degree or Hall premise is introduced. -/
theorem originalCanonicalPhysicalExterior_sum {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U) (f : V → ℕ) :
    (∑ y,∑ v ∈ T.originalCanonicalPhysicalExterior d y,f v)=
      ∑ v ∈ T.originalStepFullCut d,(T.originalOwnerCanonicalGroup d v).card*f v := by
  classical
  have hrow : ∀ y : T.RootOwner root (d.corridor.getVert d.index),
      T.originalCanonicalPhysicalExterior d y=
        (T.originalStepFullCut d).filter (fun v => y ∈ T.originalOwnerCanonicalGroup d v) := by
    intro y
    ext v
    simp only [Finset.mem_filter,T.mem_originalCanonicalPhysicalExterior hH d y]
  simp_rw [hrow,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  calc
    (∑ y,if y ∈ T.originalOwnerCanonicalGroup d v then f v else 0)=
        ∑ y ∈ T.originalOwnerCanonicalGroup d v,f v := by
      rw [← Finset.sum_filter]
      congr 1
      ext y
      simp
    _ =(T.originalOwnerCanonicalGroup d v).card*f v := by simp

theorem originalCanonicalPhysicalExterior_card_sum {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U) :
    (∑ y,(T.originalCanonicalPhysicalExterior d y).card)=
      ∑ v ∈ T.originalStepFullCut d,(T.originalOwnerCanonicalGroup d v).card := by
  simpa using T.originalCanonicalPhysicalExterior_sum hH d (fun _ => 1)

/-- Projected exterior incidences equal physical incidences PLUS each
row's exact actual nonphysical marker debit. This is old-stock incidence
accounting, not disjointness between different rows or a weighted payment. -/
theorem originalCanonicalExterior_marker_sum {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U) :
    (∑ y,(T.rootTailExterior root U (T.originalOwnerCanonicalTail d y)).card)=
      (∑ v ∈ T.originalStepFullCut d,(T.originalOwnerCanonicalGroup d v).card)+
      ∑ y,if first T.chains root (d.tails y).entry ∈
          T.rootTailExterior root U (T.originalOwnerCanonicalTail d y) ∧
        first T.chains root (d.tails y).entry ∉ (T.originalOwnerCanonicalTail d y).support
        then 1 else 0 := by
  classical
  calc
    _ =∑ y,((T.originalCanonicalPhysicalExterior d y).card+
        (if first T.chains root (d.tails y).entry ∈
            T.rootTailExterior root U (T.originalOwnerCanonicalTail d y) ∧
          first T.chains root (d.tails y).entry ∉ (T.originalOwnerCanonicalTail d y).support
          then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      obtain ⟨hrootb,hr⟩ := T.originalCanonicalTail_root hH d y
      exact (T.rootTailExterior_physical_marker hH hrootb _ hr.1).2.1
    _ =_ := by rw [Finset.sum_add_distrib,T.originalCanonicalPhysicalExterior_card_sum hH d]

/-- Row weights are evaluated on EACH actual unchanged canonical drop,
then reindexed by the proved literal common suffix/count. -/
theorem originalCanonicalPhysicalExterior_weighted_sum {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U) :
    (∑ y,∑ v ∈ T.originalCanonicalPhysicalExterior d y,T.originalCanonicalRowWeight d y v)=
      ∑ v ∈ T.originalStepFullCut d,(T.originalOwnerCanonicalGroup d v).card*
        canonicalMidpointWeight (T.originalCanonicalRemainingCount d v) := by
  classical
  calc
    _ =∑ y,∑ v ∈ T.originalCanonicalPhysicalExterior d y,
        canonicalMidpointWeight (T.originalCanonicalRemainingCount d v) := by
      apply Finset.sum_congr rfl
      intro y _hy
      apply Finset.sum_congr rfl
      intro v hv
      exact T.originalCanonicalRowWeight_eq d y (List.mem_toFinset.mp (Finset.mem_inter.mp hv).2)
    _ =_ := T.originalCanonicalPhysicalExterior_sum hH d _

/-- The terminal center has no weight, even if every owner meets it.
Nil covered/uncovered endpoints are handled without a free second target. -/
theorem originalCanonicalRemainingCount_W_weight {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U) :
    canonicalMidpointWeight (T.originalCanonicalRemainingCount d W)=0 := by
  classical
  by_cases h : ∃ y : T.RootOwner root (d.corridor.getVert d.index),
      W ∈ (T.originalOwnerCanonicalTail d y).support
  · rw [T.originalCanonicalRemainingCount_eq d (Classical.choose h) (Classical.choose_spec h),
      T.originalOwnerSharedSuffix_terminal d (Classical.choose h) (Classical.choose_spec h)]
    have hn := T.count_le_vertices (.nil : DWalk W W)
    change T.count (.nil : DWalk W W)≤1 at hn
    have hz : T.count (.nil : DWalk W W)-1=0 := by omega
    simp only [canonicalMidpointWeight,hz,Nat.zero_div,Nat.zero_sub,Nat.zero_mul]
  · rw [originalCanonicalRemainingCount,dif_neg h]
    simp [canonicalMidpointWeight]

/-- ONE center under a genuine SAME-current FULL legal-edge cap. The
statement does not sum alternative candidate gains or cap the incidence
sum by M. M=K-1 is a separate instantiation only where that cap is proved. -/
theorem originalCanonical_center_cap {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U v : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U)
    (hv : v ∈ T.originalStepFullCut d) (M : ℕ)
    (hcap : ∀ e ∈ candidates T.G,T.potential H-T.potential (insert e H)≤M) :
    (T.originalOwnerCanonicalGroup d v).card*
      canonicalMidpointWeight (T.originalCanonicalRemainingCount d v)≤M := by
  classical
  by_cases hg : (T.originalOwnerCanonicalGroup d v).Nonempty
  · obtain ⟨y,hy⟩ := hg
    have hvQ := (T.mem_originalOwnerCanonicalGroup d y).mp hy
    have hcount := T.originalCanonicalRemainingCount_eq d y hvQ
    have hvIP := (T.mem_rootHeadCone_iff.mp (Finset.mem_sdiff.mp hv).1).1
    have hWIP := (T.mem_rootHeadCone_iff.mp hW.1).1
    by_cases hn : 3≤T.count (T.originalOwnerSharedSuffix d y hvQ)
    · obtain ⟨w,_hw,_hipw,hlegal,_hfresh,_hWt,_hwt,_hr,_htc,_hc,hbank,_hsquare⟩ :=
        T.originalCanonicalGroup_midpoint_pressure hH d y hvQ hvIP hWIP hn
      have he : (T.originalOwnerCanonicalGroup d v).card*
          canonicalMidpointWeight (T.originalCanonicalRemainingCount d v)=
          (T.originalOwnerCanonicalGroup d v).card*
            (T.count (T.originalOwnerSharedSuffix d y hvQ)-1-
              (T.count (T.originalOwnerSharedSuffix d y hvQ)-1)/2)*
            ((T.count (T.originalOwnerSharedSuffix d y hvQ)-1)/2) := by
        rw [hcount]
        simp only [canonicalMidpointWeight]
        ac_rfl
      rw [he]
      exact hbank.trans (hcap (v,w) hlegal)
    · have hz : (T.count (T.originalOwnerSharedSuffix d y hvQ)-1)/2=0 := by omega
      simp only [hcount,canonicalMidpointWeight,hz,Nat.zero_mul,Nat.mul_zero]
      exact Nat.zero_le M
  · have he : T.originalOwnerCanonicalGroup d v=∅ := by
      ext y
      constructor
      · intro hy
        exact False.elim (hg ⟨y,hy⟩)
      · simp
    simp only [he,Finset.card_empty,Nat.zero_mul]
    exact Nat.zero_le M

end GreedyShortcuts.ChainDistance.Context
