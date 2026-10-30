import GreedyShortcuts.ChainFiniteOriginalSelectorHistory

/-! SOURCE ONLY, UNCOMPILED. Actual rank-k..16k band of the unchanged
step corridor, preserving its literal anchor. All membership/cardinality/
order and child-retirement properties are PROVED, not constructor fields. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

private theorem originalBandLevelExists {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) (j : Fin (15*k+1)) :
    ∃ i,i≤d.corridor.length ∧ T.count (d.corridor.take i)=k+j.val ∧
      (root,d.corridor.getVert i) ∈ T.important ∧
      T.distance H root (d.corridor.getVert i)=k+j.val ∧
      Reachable T.G (d.corridor.getVert i) W ∧
      (k+j.val=T.distance H root W → i=d.corridor.length ∧ d.corridor.getVert i=W) := by
  have hj := j.isLt
  have hactive := d.active
  obtain ⟨i,hi,hc,hip,hrank,hreach,hend,_hstrict,_hinit,_hpos⟩ :=
    T.normalized_root_corridor_anchor hH hW d.corridor d.corridorAllowed
      d.corridorMinimum (k+j.val) (by omega) (by omega)
  exact ⟨i,hi,hc,hip,hrank,hreach,hend⟩

/-- Rank k uses the EXACT recorded literal index, never a replacement
anchor. Other ranks use real native entries of this SAME corridor. -/
noncomputable def originalStepBandPosition {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) (j : Fin (15*k+1)) : ℕ :=
  if j.val=0 then d.index else Classical.choose (originalBandLevelExists T hH hk hW d j)

theorem originalStepBandPosition_spec {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) (j : Fin (15*k+1)) :
    let i := T.originalStepBandPosition hH hk hW d j
    i≤d.corridor.length ∧ T.count (d.corridor.take i)=k+j.val ∧
      (root,d.corridor.getVert i) ∈ T.important ∧
      T.distance H root (d.corridor.getVert i)=k+j.val ∧
      Reachable T.G (d.corridor.getVert i) W ∧
      (k+j.val=T.distance H root W → i=d.corridor.length ∧ d.corridor.getVert i=W) := by
  classical
  dsimp only
  by_cases h0 : j.val=0
  · have hpos : T.originalStepBandPosition hH hk hW d j=d.index := by
      simp only [originalStepBandPosition,if_pos h0]
    rw [hpos]
    have hrank := (T.minimum_take hH d.corridor d.corridorAllowed
      d.corridorMinimum d.index).symm.trans d.entryCount
    have hreach : Reachable T.G (d.corridor.getVert d.index) W :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨d.corridor.drop d.index,allowed_mono (fun _ _ h => h.1)
          (allowed_subwalk d.corridorAllowed (d.corridor.isSubwalk_drop d.index))⟩
    refine ⟨d.indexLe,?_,d.entryImportant,?_,hreach,?_⟩
    · simpa only [h0,Nat.add_zero] using d.entryCount
    · simpa only [h0,Nat.add_zero] using hrank
    · intro he
      have hactive := d.active
      omega
  · have hpos : T.originalStepBandPosition hH hk hW d j=
        Classical.choose (originalBandLevelExists T hH hk hW d j) := by
      simp only [originalStepBandPosition,if_neg h0]
    rw [hpos]
    exact Classical.choose_spec (originalBandLevelExists T hH hk hW d j)

noncomputable def originalStepBandHead {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) (j : Fin (15*k+1)) : V :=
  d.corridor.getVert (T.originalStepBandPosition hH hk hW d j)

theorem originalStepBandHead_spec {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) (j : Fin (15*k+1)) :
    let b := T.originalStepBandHead hH hk hW d j
    (root,b) ∈ T.important ∧ T.distance H root b=k+j.val ∧
      Reachable T.G b W ∧ Reachable T.G root b ∧ first T.chains root b=b ∧
      (∃ c,label T.chains b=some c) ∧ b ∈ d.corridor.support := by
  obtain ⟨_hi,_hc,hip,hrank,hreach,_hend⟩ := T.originalStepBandPosition_spec hH hk hW d j
  exact ⟨hip,hrank,hreach,(T.important_spec hip).1,(T.important_spec hip).2,
    T.important_covered hip,d.corridor.getVert_mem_support _⟩

theorem originalStepBandHead_anchor {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    T.originalStepBandPosition hH hk hW d ⟨0,by omega⟩=d.index ∧
      T.originalStepBandHead hH hk hW d ⟨0,by omega⟩=d.corridor.getVert d.index := by
  simp [originalStepBandPosition,originalStepBandHead]

/-- Terminal parent rank uses the genuine corridor endpoint, not an
invented next-band vertex. -/
theorem originalStepBandHead_at_parent_rank {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) (j : Fin (15*k+1))
    (hj : k+j.val=T.distance H root W) : T.originalStepBandHead hH hk hW d j=W := by
  obtain ⟨_hi,_hc,_hip,_hr,_hreach,hend⟩ := T.originalStepBandPosition_spec hH hk hW d j
  exact (hend hj).2

theorem originalStepBandPosition_strictMono {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    StrictMono (T.originalStepBandPosition hH hk hW d) := by
  intro i j hij
  have hi := (T.originalStepBandPosition_spec hH hk hW d i).2.1
  have hj := (T.originalStepBandPosition_spec hH hk hW d j).2.1
  by_contra hn
  have hc := T.count_take_mono d.corridor
    (show T.originalStepBandPosition hH hk hW d j≤T.originalStepBandPosition hH hk hW d i by omega)
  rw [hi,hj] at hc
  change i.val<j.val at hij
  omega

theorem originalStepBandHead_injective {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    Function.Injective (T.originalStepBandHead hH hk hW d) := by
  intro i j he
  have hi := (T.originalStepBandHead_spec hH hk hW d i).2.1
  have hj := (T.originalStepBandHead_spec hH hk hW d j).2.1
  have hr := congrArg (T.distance H root) he
  apply Fin.ext
  omega

/-- Distinct rank entries are distinct ORIGINAL ROOT chains as well as
physical heads. Repeated chain occurrences cannot create extra members. -/
theorem originalStepBandHead_label_injective {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) {i j : Fin (15*k+1)}
    (he : label T.chains (T.originalStepBandHead hH hk hW d i)=
      label T.chains (T.originalStepBandHead hH hk hW d j)) : i=j := by
  have hi := (T.originalStepBandHead_spec hH hk hW d i).1
  have hj := (T.originalStepBandHead_spec hH hk hW d j).1
  have hf := first_constant T.chains root _ _ he
  have hv : T.originalStepBandHead hH hk hW d i=T.originalStepBandHead hH hk hW d j :=
    (T.important_spec hi).2.symm.trans (hf.trans (T.important_spec hj).2)
  exact T.originalStepBandHead_injective hH hk hW d hv

theorem originalStepBandHead_order {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) {i j : Fin (15*k+1)} (hij : i≤j) :
    Reachable T.G (T.originalStepBandHead hH hk hW d i) (T.originalStepBandHead hH hk hW d j) := by
  have hpos := (T.originalStepBandPosition_strictMono hH hk hW d).monotone hij
  exact (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
    (reachable_segment (allowed_mono (fun _ _ h => h.1) d.corridorAllowed) hpos)

noncomputable def originalStepBand {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) : Finset V :=
  Finset.univ.image (T.originalStepBandHead hH hk hW d)

theorem originalStepBand_card {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    (T.originalStepBand hH hk hW d).card=15*k+1 := by
  classical
  simp only [originalStepBand,Finset.card_image_of_injective _
    (T.originalStepBandHead_injective hH hk hW d),Finset.card_univ,Fintype.card_fin]

theorem originalStepBand_anchor_mem {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    d.corridor.getVert d.index ∈ T.originalStepBand hH hk hW d := by
  classical
  exact Finset.mem_image.mpr ⟨⟨0,by omega⟩,Finset.mem_univ _,
    (T.originalStepBandHead_anchor hH hk hW d).2⟩

theorem originalStepBand_parent_and_descendant {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    T.originalStepBand hH hk hW d ⊆ T.rootHeadCone root W ∧
      ∀ b ∈ T.originalStepBand hH hk hW d,Reachable T.G (d.corridor.getVert d.index) b := by
  classical
  constructor
  · intro b hb
    obtain ⟨j,_hj,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hip,_hr,hreach,_hroot,_hf,hcovered,_hmem⟩ := T.originalStepBandHead_spec hH hk hW d j
    exact T.mem_rootHeadCone_iff.mpr ⟨hip,hreach,hcovered⟩
  · intro b hb
    obtain ⟨j,_hj,rfl⟩ := Finset.mem_image.mp hb
    have hzero : (⟨0,by omega⟩ : Fin (15*k+1))≤j := by change 0≤j.val;omega
    have hr := T.originalStepBandHead_order hH hk hW d hzero
    simpa only [(T.originalStepBandHead_anchor hH hk hW d).2] using hr

/-- EXACT retained membership of this real band. The terminal anchor is
kept; a nonglobal guard or projection is not automatically declared removed. -/
theorem originalStepBand_retained_iff {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) {b : V}
    (hb : b ∈ T.originalStepBand hH hk hW d) :
    b ∈ T.rootHeadCone root U ↔ U=d.corridor.getVert d.index ∧ b=d.corridor.getVert d.index := by
  have hdesc := (T.originalStepBand_parent_and_descendant hH hk hW d).2 b hb
  obtain ⟨_hf,hbranch⟩ := T.originalSelectorStepData_facts hH hk hW d
  rcases hbranch with ⟨_he,_hcompare,_hUa,_hremoved,hretain,_hterminal⟩ |
    ⟨g,_hc,_hg,_hbad,_hip,_hgW,_hxg,_hUg,_hmax,_hsig,_hp,_hfloor,_hxremoved,hno⟩
  · constructor
    · intro hchild
      obtain ⟨hb',hu'⟩ := (hretain b hdesc).mp hchild
      exact ⟨hu',hb'⟩
    · rintro ⟨hu',hb'⟩
      exact (hretain b hdesc).mpr ⟨hb',hu'⟩
  · constructor
    · intro hchild
      exact (hno b hdesc hchild).elim
    · rintro ⟨hu',_hb'⟩
      have haChild : d.corridor.getVert d.index ∈ T.rootHeadCone root U := by
        simpa only [hu'] using T.rootCone_self_mem d.entryImportant
      exact (hno _ (reachable_refl T.G _) haChild).elim

noncomputable def originalStepRetiredBand {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) : Finset V :=
  T.originalStepBand hH hk hW d \ T.rootHeadCone root U

noncomputable def originalStepBandAnchorLoss {H : Finset (V × V)} {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U) : ℕ := by
  classical
  exact if U=d.corridor.getVert d.index then 1 else 0

theorem originalStepBand_retained_set {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    T.originalStepBand hH hk hW d ∩ T.rootHeadCone root U=
      if U=d.corridor.getVert d.index then {d.corridor.getVert d.index} else ∅ := by
  classical
  by_cases he : U=d.corridor.getVert d.index
  · rw [if_pos he]
    ext b
    constructor
    · intro hb
      obtain ⟨hband,hchild⟩ := Finset.mem_inter.mp hb
      exact Finset.mem_singleton.mpr ((T.originalStepBand_retained_iff hH hk hW d hband).mp hchild).2
    · intro hb
      have hb' := Finset.mem_singleton.mp hb
      subst b
      have ha := T.originalStepBand_anchor_mem hH hk hW d
      exact Finset.mem_inter.mpr ⟨ha,(T.originalStepBand_retained_iff hH hk hW d ha).mpr ⟨he,rfl⟩⟩
  · rw [if_neg he]
    ext b
    constructor
    · intro hb
      obtain ⟨hband,hchild⟩ := Finset.mem_inter.mp hb
      exact (he ((T.originalStepBand_retained_iff hH hk hW d hband).mp hchild).1).elim
    · intro hb
      simp at hb

theorem originalStepRetiredBand_exact {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    T.originalStepRetiredBand hH hk hW d=
      if U=d.corridor.getVert d.index then
        (T.originalStepBand hH hk hW d).erase (d.corridor.getVert d.index)
      else T.originalStepBand hH hk hW d := by
  classical
  by_cases he : U=d.corridor.getVert d.index
  · rw [if_pos he]
    ext b
    constructor
    · intro hb
      obtain ⟨hband,hno⟩ := Finset.mem_sdiff.mp hb
      refine Finset.mem_erase.mpr ⟨?_,hband⟩
      intro hb'
      exact hno ((T.originalStepBand_retained_iff hH hk hW d hband).mpr ⟨he,hb'⟩)
    · intro hb
      obtain ⟨hne,hband⟩ := Finset.mem_erase.mp hb
      refine Finset.mem_sdiff.mpr ⟨hband,?_⟩
      intro hchild
      exact hne ((T.originalStepBand_retained_iff hH hk hW d hband).mp hchild).2
  · rw [if_neg he]
    apply Finset.Subset.antisymm
    · exact Finset.sdiff_subset
    · intro b hband
      refine Finset.mem_sdiff.mpr ⟨hband,?_⟩
      intro hchild
      exact he ((T.originalStepBand_retained_iff hH hk hW d hband).mp hchild).1

theorem originalStepRetiredBand_subset {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    T.originalStepRetiredBand hH hk hW d ⊆ T.rootHeadCone root W \ T.rootHeadCone root U := by
  intro b hb
  obtain ⟨hband,hno⟩ := Finset.mem_sdiff.mp hb
  exact Finset.mem_sdiff.mpr ⟨(T.originalStepBand_parent_and_descendant hH hk hW d).1 hband,hno⟩

theorem originalStepRetiredBand_card {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    (T.originalStepRetiredBand hH hk hW d).card+T.originalStepBandAnchorLoss d=15*k+1 := by
  classical
  have hc := Finset.card_sdiff_add_card_inter (T.originalStepBand hH hk hW d) (T.rootHeadCone root U)
  rw [T.originalStepBand_retained_set hH hk hW d,T.originalStepBand_card hH hk hW d] at hc
  by_cases he : U=d.corridor.getVert d.index
  · simpa [originalStepRetiredBand,originalStepBandAnchorLoss,he] using hc
  · simpa [originalStepRetiredBand,originalStepBandAnchorLoss,he] using hc

/-- The sole retained anchor case is genuinely RELAY and terminal. -/
theorem originalStepBand_anchor_terminal {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) (he : U=d.corridor.getVert d.index) :
    U=d.maxOwner ∧ T.distance H root W-T.distance H root d.maxOwner≤(d.tails d.minOwner).tau ∧
      T.distance H root U=k ∧ T.distance H root U<16*k := by
  obtain ⟨_hf,hbranch⟩ := T.originalSelectorStepData_facts hH hk hW d
  rcases hbranch with ⟨hmax,hcompare,_hUa,_hremoved,_hretain,hterminal⟩ |
    ⟨g,_hc,_hg,_hbad,_hip,_hgW,_hxg,_hUg,_hmax,_hsig,_hp,_hfloor,_hxremoved,hno⟩
  · exact ⟨hmax,hcompare,(hterminal he).1,(hterminal he).2⟩
  · have haChild : d.corridor.getVert d.index ∈ T.rootHeadCone root U := by
      simpa only [he] using T.rootCone_self_mem d.entryImportant
    exact (hno _ (reachable_refl T.G _) haChild).elim

end GreedyShortcuts.ChainDistance.Context
