import GreedyShortcuts.ChainOriginalCutCandidate

/-! SOURCE ONLY, UNCOMPILED. Actual physical-membership groups of the
separately displayed fixed canonical suffixes. Original Q/F and selector
records remain unchanged; no desired saving/coalescence field is supplied. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def originalOwnerCanonicalTail {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) : DWalk (d.tails y).entry W :=
  T.rootCanonicalSuffix H root (d.tails y).entry W ⟨(d.tails y).tail,(d.tails y).rootTail⟩

noncomputable def originalOwnerCanonicalGroup {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U)
    (v : V) : Finset (T.RootOwner root (d.corridor.getVert d.index)) := by
  classical
  exact Finset.univ.filter (fun y => v ∈ (T.originalOwnerCanonicalTail d y).support)

theorem mem_originalOwnerCanonicalGroup {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U v : V} (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    y ∈ T.originalOwnerCanonicalGroup d v ↔ v ∈ (T.originalOwnerCanonicalTail d y).support := by
  classical
  simp only [originalOwnerCanonicalGroup,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Actual suffix witness, not a fresh favorable route to W. Its type is
available only at a real physical vertex of the displayed canonical path. -/
noncomputable def originalOwnerSharedSuffix {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U v : V} (d : T.OriginalSelectorStepData H root k W U)
    (y₀ : T.RootOwner root (d.corridor.getVert d.index))
    (hv₀ : v ∈ (T.originalOwnerCanonicalTail d y₀).support) : DWalk v W :=
  (T.originalOwnerCanonicalTail d y₀).dropUntil v hv₀

noncomputable def originalOwnerCanonicalPrefix {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U v : V} (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    (hv : v ∈ (T.originalOwnerCanonicalTail d y).support) : DWalk y.val v :=
  (d.tails y).prefix.append ((T.originalOwnerCanonicalTail d y).takeUntil v hv)

/-- Real global coalescence at a LATER physical vertex, not equal labels,
equal prices or same-start proof irrelevance alone. -/
theorem originalOwnerCanonicalGroup_coalesces {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U v : V} (d : T.OriginalSelectorStepData H root k W U)
    (y₀ : T.RootOwner root (d.corridor.getVert d.index))
    (hv₀ : v ∈ (T.originalOwnerCanonicalTail d y₀).support)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    (hy : y ∈ T.originalOwnerCanonicalGroup d v) :
    (T.originalOwnerCanonicalTail d y).dropUntil v
      ((T.mem_originalOwnerCanonicalGroup d y).mp hy)=T.originalOwnerSharedSuffix d y₀ hv₀ := by
  exact T.rootCanonicalSuffix_shared_vertex H root
    ⟨(d.tails y).tail,(d.tails y).rootTail⟩
    ⟨(d.tails y₀).tail,(d.tails y₀).rootTail⟩
    ((T.mem_originalOwnerCanonicalGroup d y).mp hy) hv₀

/-- Display the admitted equal-price SAME-owner splice separately. The
original walk, physical LAST entry/prefix and ROOT validity stay evidence. -/
theorem originalOwnerCanonicalTail_display {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    Allowed (T.graph H y.val) (T.originalOwnerCanonicalTail d y) ∧
      Allowed (T.graph H y.val) ((d.tails y).prefix.append (T.originalOwnerCanonicalTail d y)) ∧
      T.count (T.originalOwnerCanonicalTail d y)=T.count (d.tails y).tail ∧
      T.count ((d.tails y).prefix.append (T.originalOwnerCanonicalTail d y))=T.distance H y.val W ∧
      (d.tails y).tau+1=T.count (T.originalOwnerCanonicalTail d y) ∧
      (Allowed (T.graph H root) ((d.tails y).prefix.append (T.originalOwnerCanonicalTail d y)) ↔
        Allowed (T.graph H root) (d.owners y).val) := by
  exact T.ownerLastRootTail_coalescing_replacement hH
    (T.mem_rootHeadCone_iff.mp y.property).1 (d.tails y) (d.owners y).property.2

theorem originalOwnerSharedSuffix_root {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U v : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y₀ : T.RootOwner root (d.corridor.getVert d.index))
    (hv₀ : v ∈ (T.originalOwnerCanonicalTail d y₀).support) :
    Allowed (T.graph H root) (T.originalOwnerSharedSuffix d y₀ hv₀) ∧
      Reachable T.G root v ∧ T.FixedRootSuffixMinimum H root (T.originalOwnerSharedSuffix d y₀ hv₀) := by
  have hentry := (T.originalOwnerTail_entry_and_fixed_minimum hH d y₀).1
  obtain ⟨hvW,hr,he,hmin⟩ := T.rootCanonicalSuffix_later_minimum hH hentry
    ⟨(d.tails y₀).tail,(d.tails y₀).rootTail⟩ hv₀
  have hmin' : T.FixedRootSuffixMinimum H root (T.originalOwnerSharedSuffix d y₀ hv₀) := by
    change T.FixedRootSuffixMinimum H root ((T.originalOwnerCanonicalTail d y₀).dropUntil v hv₀)
    change T.FixedRootSuffixMinimum H root
      ((T.rootCanonicalSuffix H root (d.tails y₀).entry W
        ⟨(d.tails y₀).tail,(d.tails y₀).rootTail⟩).dropUntil v hv₀)
    exact he.symm ▸ hmin
  exact ⟨hmin'.1,hr,hmin'⟩

/-- Each ACTUAL member owns its original-source prefix price and shares
the SAME literal q. The marker is exact even for an uncovered shared v. -/
theorem originalOwnerCanonicalGroup_row {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U v : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y₀ : T.RootOwner root (d.corridor.getVert d.index))
    (hv₀ : v ∈ (T.originalOwnerCanonicalTail d y₀).support)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    (hy : y ∈ T.originalOwnerCanonicalGroup d v) :
    let p := T.originalOwnerCanonicalPrefix d y ((T.mem_originalOwnerCanonicalGroup d y).mp hy)
    let q := T.originalOwnerSharedSuffix d y₀ hv₀
    p.append q=(d.tails y).prefix.append (T.originalOwnerCanonicalTail d y) ∧
      Allowed (T.graph H y.val) (p.append q) ∧ Allowed (T.graph H y.val) q ∧
      T.count (p.append q)=T.distance H y.val W ∧ T.count p=T.distance H y.val v ∧
      T.distance H y.val W+(label T.chains v).toFinset.card=
        T.distance H y.val v+T.count q := by
  let hv := (T.mem_originalOwnerCanonicalGroup d y).mp hy
  let p := T.originalOwnerCanonicalPrefix d y hv
  let q := T.originalOwnerSharedSuffix d y₀ hv₀
  have hco := T.originalOwnerCanonicalGroup_coalesces d y₀ hv₀ y hy
  obtain ⟨_hr,hwhole,_heq,hprice,_htau,_hvalid⟩ := T.originalOwnerCanonicalTail_display hH d y
  have he : p.append q=(d.tails y).prefix.append (T.originalOwnerCanonicalTail d y) := by
    change ((d.tails y).prefix.append ((T.originalOwnerCanonicalTail d y).takeUntil v hv)).append q=_
    calc
      ((d.tails y).prefix.append ((T.originalOwnerCanonicalTail d y).takeUntil v hv)).append q =
          ((d.tails y).prefix.append ((T.originalOwnerCanonicalTail d y).takeUntil v hv)).append
            ((T.originalOwnerCanonicalTail d y).dropUntil v hv) :=
        congrArg (fun z => ((d.tails y).prefix.append
          ((T.originalOwnerCanonicalTail d y).takeUntil v hv)).append z) hco.symm
      _ = (d.tails y).prefix.append
          (((T.originalOwnerCanonicalTail d y).takeUntil v hv).append
            ((T.originalOwnerCanonicalTail d y).dropUntil v hv)) :=
        (Walk.append_assoc _ _ _).symm
      _ = (d.tails y).prefix.append (T.originalOwnerCanonicalTail d y) :=
        congrArg (fun z => (d.tails y).prefix.append z)
          ((T.originalOwnerCanonicalTail d y).take_spec hv)
  have hall : Allowed (T.graph H y.val) (p.append q) := by simpa only [he] using hwhole
  have hmin : T.count (p.append q)=T.distance H y.val W := by simpa only [he] using hprice
  have hp := T.minimum_prefix hH p q hall hmin
  have hj := T.count_append_exact hH p q hall
  have hpriceJoin : T.distance H y.val W+(label T.chains v).toFinset.card=
      T.distance H y.val v+T.count q := by
    calc
      _ = T.count (p.append q)+(label T.chains v).toFinset.card :=
        congrArg (fun n => n+(label T.chains v).toFinset.card) hmin.symm
      _ = T.count p+T.count q := hj
      _ = _ := congrArg (fun n => n+T.count q) hp
  exact ⟨he,hall,((allowed_append _ _ _).mp hall).2,hmin,hp,hpriceJoin⟩

theorem originalOwnerCanonicalGroup_witness {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U v : V} (d : T.OriginalSelectorStepData H root k W U)
    (y₀ : T.RootOwner root (d.corridor.getVert d.index))
    (hv₀ : v ∈ (T.originalOwnerCanonicalTail d y₀).support) :
    y₀ ∈ T.originalOwnerCanonicalGroup d v :=
  (T.mem_originalOwnerCanonicalGroup d y₀).mpr hv₀

/-- At W the genuine shared suffix is nil, regardless of group size.
An endpoint group cannot manufacture a positive interval or another band. -/
theorem originalOwnerSharedSuffix_terminal {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U)
    (y₀ : T.RootOwner root (d.corridor.getVert d.index))
    (hv₀ : W ∈ (T.originalOwnerCanonicalTail d y₀).support) :
    T.originalOwnerSharedSuffix d y₀ hv₀=(.nil : DWalk W W) := by
  obtain ⟨hW,he⟩ := T.rootCanonicalSuffix_dropUntil H root
    ⟨(d.tails y₀).tail,(d.tails y₀).rootTail⟩ hv₀
  exact he.trans (T.rootCanonicalSuffix_self H root W hW)

theorem originalOwnerCanonicalGroup_terminal {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U) :
    T.originalOwnerCanonicalGroup d W=Finset.univ := by
  classical
  ext y
  constructor
  · intro _
    exact Finset.mem_univ _
  · intro _
    exact (T.mem_originalOwnerCanonicalGroup d y).mpr (T.originalOwnerCanonicalTail d y).end_mem_support

end GreedyShortcuts.ChainDistance.Context
