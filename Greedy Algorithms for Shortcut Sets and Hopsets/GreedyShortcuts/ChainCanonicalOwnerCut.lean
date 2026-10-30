import GreedyShortcuts.ChainCanonicalOwnerGroup
import GreedyShortcuts.ChainRectangleCharging

/-! One physical shared-suffix cohort yields one actual multi-source,
retained-target cut. No population, price, saving or coverage field is
assumed for a row. This is a one-state offer, not a phase payment. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def originalCanonicalCutSources {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U)
    (a : V) : Finset V := by
  classical
  exact (T.originalOwnerCanonicalGroup d a).image Subtype.val

theorem originalCanonicalCutSources_card {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U)
    (a : V) :
    (T.originalCanonicalCutSources d a).card=(T.originalOwnerCanonicalGroup d a).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro y _ z _ h
  exact Subtype.ext h

/-- Literal coalescence supplies every original-source minimum needed for
ONE rectangle. The marker at a and the entry at b retain both exact native
joins. A row's own FIRST admission is derived from its actual access. -/
theorem originalCanonicalGroup_cut_bank {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U a b : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y₀ : T.RootOwner root (d.corridor.getVert d.index))
    (ha : a ∈ (T.originalOwnerCanonicalTail d y₀).support)
    (hipa : (root,a) ∈ T.important) (hipb : (root,b) ∈ T.important)
    (hipW : (root,W) ∈ T.important)
    (hb : b ∈ (T.originalOwnerSharedSuffix d y₀ ha).support)
    (hne : a≠b)
    (hlong : 3≤T.count ((T.originalOwnerSharedSuffix d y₀ ha).takeUntil b hb)) :
    let q := T.originalOwnerSharedSuffix d y₀ ha
    let r := q.takeUntil b hb
    let s := q.dropUntil b hb
    let targets := T.rootTailHeads root q ∩ s.support.toFinset
    (a,b) ∈ candidates T.G ∧ (a,b) ∉ H ∧ W ∈ targets ∧
      1≤(T.originalOwnerCanonicalGroup d a).card ∧
      (∀ x ∈ T.originalCanonicalCutSources d a,∀ t ∈ targets,
        (x,t) ∈ T.important ∧ T.graph (insert (a,b) H) x a b ∧
        T.distance (insert (a,b) H) x t+T.count r≤T.distance H x t+2) ∧
      (T.originalOwnerCanonicalGroup d a).card*targets.card*(T.count r-2)≤
        T.potential H-T.potential (insert (a,b) H) := by
  classical
  let q := T.originalOwnerSharedSuffix d y₀ ha
  let r := q.takeUntil b hb
  let s := q.dropUntil b hb
  let targets := T.rootTailHeads root q ∩ s.support.toFinset
  have hroot := T.originalOwnerSharedSuffix_root hH d y₀ ha
  have hrRoot : Allowed (T.graph H root) r :=
    allowed_subwalk hroot.1 (q.isSubwalk_takeUntil hb)
  have hlegal : (a,b) ∈ candidates T.G := T.interior_candidate hH r hrRoot hne
  obtain ⟨ca,hca⟩ := T.important_covered hipa
  have haCov : label T.chains a≠none := by simp [hca]
  have hW : W ∈ targets := Finset.mem_inter.mpr
    ⟨T.rootTailHeads_endpoint q hipW,List.mem_toFinset.mpr s.end_mem_support⟩
  have hy₀ : y₀ ∈ T.originalOwnerCanonicalGroup d a :=
    T.originalOwnerCanonicalGroup_witness d y₀ ha
  have hG : 1≤(T.originalOwnerCanonicalGroup d a).card :=
    Finset.one_le_card.mpr ⟨y₀,hy₀⟩
  have rows : ∀ y ∈ T.originalOwnerCanonicalGroup d a,
      ∀ t ∈ targets,(y.val,t) ∈ T.important ∧
        T.graph (insert (a,b) H) y.val a b ∧
        T.distance (insert (a,b) H) y.val t+T.count r≤T.distance H y.val t+2 := by
    intro y hy
    let p := T.originalOwnerCanonicalPrefix d y ((T.mem_originalOwnerCanonicalGroup d y).mp hy)
    obtain ⟨_hdisplay,hpq,_hq,hprice,_hp,_hj⟩ :=
      T.originalOwnerCanonicalGroup_row hH d y₀ ha y hy
    have he : (p.append r).append s=p.append q := by
      calc
        _ = p.append (r.append s) := (Walk.append_assoc p r s).symm
        _ = p.append q := congrArg (fun z => p.append z) (q.take_spec hb)
    have hall : Allowed (T.graph H y.val) ((p.append r).append s) :=
      he.symm ▸ hpq
    have hmin : T.count ((p.append r).append s)=T.distance H y.val W :=
      (congrArg T.count he).trans hprice
    have hrooty := (T.important_spec (T.mem_rootHeadCone_iff.mp y.property).1).1
    have hpr := ((allowed_append _ _ _).mp hall).1
    have hyb : Reachable T.G y.val b :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨p.append r,allowed_mono (fun _ _ h => h.1) hpr⟩
    have hbOwn := T.important_from_root_and_actual_access hrooty hyb hipb
    intro t ht
    have hts : t ∈ s.support := List.mem_toFinset.mp (Finset.mem_inter.mp ht).2
    have hyt : Reachable T.G y.val t :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨(p.append r).append (s.takeUntil t hts),allowed_mono (fun _ _ h => h.1)
          ((allowed_append _ _ _).mpr ⟨hpr,allowed_subwalk
            ((allowed_append _ _ _).mp hall).2 (s.isSubwalk_takeUntil hts)⟩)⟩
    obtain ⟨_ct,_hct,_he,_hl,_hr,_hf,hipt,_htW,_hedge⟩ :=
      T.rootTailHeads_spec hH hroot.2.1 q hroot.1 (Finset.mem_inter.mp ht).1
    exact ⟨T.important_from_root_and_actual_access hrooty hyt hipt,
      T.important_target_inserted_dart H hbOwn,
      T.interior_insertion_suffix_saving hH p r s hall hmin haCov hbOwn hne hts⟩
  have hrows : ∀ x ∈ T.originalCanonicalCutSources d a,∀ t ∈ targets,
      (x,t) ∈ T.important ∧ T.graph (insert (a,b) H) x a b ∧
        T.distance (insert (a,b) H) x t+T.count r≤T.distance H x t+2 := by
    intro x hx t ht
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact rows y hy t ht
  have hlongActual : 3≤T.count r := hlong
  have hfresh : (a,b) ∉ H := by
    intro he
    have hs := (rows y₀ hy₀ W hW).2.2
    rw [Finset.insert_eq_of_mem he] at hs
    omega
  have hbank := T.rectangle_drop_lower_bound H (a,b)
    (T.originalCanonicalCutSources d a) targets (T.count r-2)
    (fun x hx t ht => (hrows x hx t ht).1)
    (by intro x hx t ht;have hs := (hrows x hx t ht).2.2;omega)
  rw [T.originalCanonicalCutSources_card] at hbank
  exact ⟨hlegal,hfresh,hW,hG,hrows,hbank⟩

noncomputable def originalCanonicalCutHeads {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) : Finset V :=
  T.rootTailExterior root U (T.originalOwnerCanonicalTail d y) \
    {first T.chains root (d.tails y).entry,W}

theorem originalCanonicalCutHeads_bound {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    T.distance H root W-T.distance H root U-2≤(T.originalCanonicalCutHeads d y).card := by
  classical
  have he := T.originalOwnerTail_canonical_display hH hk hW d y
  have hd : T.distance H root W-T.distance H root U≤
      (T.rootTailExterior root U (T.originalOwnerCanonicalTail d y)).card := he.2.2.2.2.2.2
  have hc := Finset.card_sdiff_add_card_inter
    (T.rootTailExterior root U (T.originalOwnerCanonicalTail d y))
    {first T.chains root (d.tails y).entry,W}
  have hb : ({first T.chains root (d.tails y).entry,W} : Finset V).card≤2 := by
    simpa only [Finset.card_singleton] using Finset.card_insert_le
      (first T.chains root (d.tails y).entry) ({W} : Finset V)
  have hi := (Finset.card_le_card
    (Finset.inter_subset_right :
      T.rootTailExterior root U (T.originalOwnerCanonicalTail d y) ∩
        {first T.chains root (d.tails y).entry,W} ⊆
          {first T.chains root (d.tails y).entry,W})).trans hb
  change _≤(T.rootTailExterior root U (T.originalOwnerCanonicalTail d y) \
    {first T.chains root (d.tails y).entry,W}).card
  omega

/-- No favorable segment or cohort is supplied. The first and last actual
eligible heads select ONE cut; its literal coalescing group supplies the
source factor. This gives no lower bound on that factor beyond one. -/
theorem originalCanonicalCut_short_or_cohort_offer {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    ((T.originalCanonicalCutHeads d y).card≤2 ∧
      T.distance H root W-T.distance H root U≤4) ∨
      ∃ a ∈ T.originalCanonicalCutHeads d y,∃ b ∈ T.originalCanonicalCutHeads d y,
        (a,b) ∈ candidates T.G ∧ (a,b) ∉ H ∧
        1≤(T.originalOwnerCanonicalGroup d a).card ∧
        1≤T.potential H-T.potential (insert (a,b) H) ∧
        (T.originalOwnerCanonicalGroup d a).card*
          (T.distance H root W-T.distance H root U-4)≤
            T.potential H-T.potential (insert (a,b) H) := by
  classical
  let C := T.originalCanonicalCutHeads d y
  have hD : T.distance H root W-T.distance H root U-2≤C.card :=
    T.originalCanonicalCutHeads_bound hH hk hW d y
  by_cases hsmall : C.card≤2
  · exact Or.inl ⟨hsmall,by omega⟩
  have hClarge : 3≤C.card := by omega
  let q := T.originalOwnerCanonicalTail d y
  have hr : Allowed (T.graph H root) q :=
    (T.rootCanonicalSuffix_optimal H root (d.tails y).entry W
      ⟨(d.tails y).tail,(d.tails y).rootTail⟩).1
  have hentry := (T.originalOwnerTail_entry_and_fixed_minimum hH d y).1
  have hex : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,ha,hminPos⟩ := Finset.exists_min_image C (T.rootTailHeadPosition root q) hex
  obtain ⟨b,hb,hmaxPos⟩ := Finset.exists_max_image C (T.rootTailHeadPosition root q) hex
  have members : ∀ v ∈ C,v ∈ T.rootTailHeads root q ∧
      v≠first T.chains root (d.tails y).entry := by
    intro v hv
    obtain ⟨hE,hbad⟩ := Finset.mem_sdiff.mp hv
    refine ⟨(Finset.mem_sdiff.mp hE).1,?_⟩
    intro he
    exact hbad (by simp [he])
  have haP := (members a ha).1
  have hbP := (members b hb).1
  have hne : a≠b := by
    intro he
    have hsub : C ⊆ {a} := by
      intro v hv
      have hl := hminPos v hv
      have hu := hmaxPos v hv
      rw [← he] at hu
      exact Finset.mem_singleton.mpr (T.rootTailHeadPosition_injective q
        (members v hv).1 haP (by omega))
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  have haQ := (T.rootTailHead_nonmarker_physical hH hentry q hr haP (members a ha).2).2
  have hbQ := (T.rootTailHead_nonmarker_physical hH hentry q hr hbP (members b hb).2).2
  have hab := T.rootTailHeads_order hH hentry q hr haP hbP (hminPos b hb)
  let qA := q.dropUntil a haQ
  have hqA : Allowed (T.graph H root) qA := allowed_subwalk hr (q.isSubwalk_dropUntil haQ)
  have hbA : b ∈ qA.support := T.actual_forward_mem_dropUntil hH q hr haQ hbQ hab
  let r := qA.takeUntil b hbA
  have hrA : Allowed (T.graph H root) r := allowed_subwalk hqA (qA.isSubwalk_takeUntil hbA)
  obtain ⟨_ca,_hca,_hea,_hl,_hra,_hfa,hipa,_haW,_hae⟩ :=
    T.rootTailHeads_spec hH hentry q hr haP
  obtain ⟨_cb,_hcb,_heb,_hlb,_hrb,_hfb,hipb,_hbW,_hbe⟩ :=
    T.rootTailHeads_spec hH hentry q hr hbP
  have hCsegment : C ⊆ T.rootTailHeads root r := by
    intro v hv
    have hvP := (members v hv).1
    have hvQ := (T.rootTailHead_nonmarker_physical hH hentry q hr hvP (members v hv).2).2
    have hav := T.rootTailHeads_order hH hentry q hr haP hvP (hminPos v hv)
    have hvb := T.rootTailHeads_order hH hentry q hr hvP hbP (hmaxPos v hv)
    have hvA := T.actual_forward_mem_dropUntil hH q hr haQ hvQ hav
    have hvr := T.actual_backward_mem_takeUntil hH qA hqA hbA hvA hvb
    obtain ⟨c,hc,_he,_hl,_hr,_hf,hip,_hW,_he'⟩ :=
      T.rootTailHeads_spec hH hentry q hr hvP
    refine Finset.mem_image.mpr ⟨c,(T.mem_chainSet r c).mpr ⟨v,hvr,_hl⟩,?_⟩
    simpa only [first,_hl] using (T.important_spec hip).2
  have hRcount : C.card≤T.count r := by
    have hc := Finset.card_le_card hCsegment
    rw [T.rootTailHeads_card hH (T.important_spec hipa).1 r hrA] at hc
    exact hc
  have hlong : 3≤T.count r := by omega
  have hbank := T.originalCanonicalGroup_cut_bank hH d y haQ hipa hipb
    (T.mem_rootHeadCone_iff.mp hW.1).1 hbA hne hlong
  obtain ⟨hlegal,hfresh,hWT,hG,_hrows,hpay⟩ := hbank
  let targets := T.rootTailHeads root qA ∩ (qA.dropUntil b hbA).support.toFinset
  have htargets : 1≤targets.card := Finset.one_le_card.mpr ⟨W,hWT⟩
  have hpay' : (T.originalOwnerCanonicalGroup d a).card*targets.card*(T.count r-2)≤
      T.potential H-T.potential (insert (a,b) H) := hpay
  have hlow : T.distance H root W-T.distance H root U-4≤T.count r-2 := by omega
  have hscaled := Nat.mul_le_mul_left (T.originalOwnerCanonicalGroup d a).card hlow
  have hfactor := Nat.mul_le_mul_left (T.originalOwnerCanonicalGroup d a).card htargets
  simp only [Nat.mul_one] at hfactor
  have hscaled' := Nat.mul_le_mul_right (T.count r-2) hfactor
  have hpositive : 1≤(T.originalOwnerCanonicalGroup d a).card*targets.card*(T.count r-2) := by
    have hp := Nat.mul_le_mul (Nat.mul_le_mul hG htargets) (by omega : 1≤T.count r-2)
    simpa only [Nat.one_mul] using hp
  exact Or.inr ⟨a,ha,b,hb,hlegal,hfresh,hG,hpositive.trans hpay',hscaled.trans (hscaled'.trans hpay')⟩

end GreedyShortcuts.ChainDistance.Context

