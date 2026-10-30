import GreedyShortcuts.ChainTailInteriorSavings

/-! SOURCE ONLY, UNCOMPILED. ONE real owner-row/cut candidate and its
literal same-edge demand family. Old physical stock is not fresh E, and
no cross-row rectangle or common-cap summation is assumed. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def originalOwnerCutCandidateHeads {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) : Finset V :=
  T.rootTailExterior root U (d.tails y).tail \ {first T.chains root (d.tails y).entry,W}

/-- Both exclusions are paid as ONE literal intersection, so marker=W
or an already-inside marker never incurs an invented second head. -/
theorem originalOwnerCutCandidateHeads_card {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    let E := T.rootTailExterior root U (d.tails y).tail
    let bad := {first T.chains root (d.tails y).entry,W}
    (T.originalOwnerCutCandidateHeads d y).card+(E ∩ bad).card=E.card ∧
      1≤(E ∩ bad).card ∧ (E ∩ bad).card≤2 ∧
      T.distance H root W-T.distance H root U-2≤(T.originalOwnerCutCandidateHeads d y).card := by
  classical
  let E := T.rootTailExterior root U (d.tails y).tail
  let m := first T.chains root (d.tails y).entry
  have hc := Finset.card_sdiff_add_card_inter E {m,W}
  have hWmem := (T.originalOwnerTail_endpoint_and_exclusion hH hk hW d y).1
  have hWbad : W ∈ ({m,W} : Finset V) := by simp
  have hlow : 1≤(E ∩ {m,W}).card :=
    Finset.one_le_card.mpr ⟨W,Finset.mem_inter.mpr ⟨hWmem,hWbad⟩⟩
  have hpair : ({m,W} : Finset V).card≤2 := by
    simpa only [Finset.card_singleton] using Finset.card_insert_le m ({W} : Finset V)
  have hupp := (Finset.card_le_card (Finset.inter_subset_right : E ∩ {m,W} ⊆ {m,W})).trans hpair
  have hD : T.distance H root W-T.distance H root U≤E.card :=
    (T.originalOwnerTail_exterior hH hk hW d y).2.2.1
  exact ⟨hc,hlow,hupp,by change _≤(E \ {m,W}).card;omega⟩

private theorem rootImportant_mem_tailHeads {root a b v : V} (r : DWalk a b)
    (hip : (root,v) ∈ T.important) (hv : v ∈ r.support) : v ∈ T.rootTailHeads root r := by
  classical
  obtain ⟨c,hc⟩ := T.important_covered hip
  refine Finset.mem_image.mpr ⟨c,(T.mem_chainSet r c).mpr ⟨v,hv,hc⟩,?_⟩
  simpa only [first,hc] using (T.important_spec hip).2

/-- A positive actual candidate-head branch constructs the edge, exact
original-source prices and literal important demands. NONE are callbacks
or desired saving fields. Only one actual owner and one edge are counted. -/
theorem exists_originalOwnerCut_bank {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    (hlarge : 3≤(T.originalOwnerCutCandidateHeads d y).card) :
    ∃ a ∈ T.originalOwnerCutCandidateHeads d y,∃ b ∈ T.originalOwnerCutCandidateHeads d y,
      a≠b ∧ ∃ p : DWalk y.val a,∃ r : DWalk a b,∃ s : DWalk b W,
      (p.append r).append s=(d.owners y).val ∧
      T.count p=T.distance H y.val a ∧ T.count (p.append r)=T.distance H y.val b ∧
      T.distance H y.val b+1=T.distance H y.val a+T.count r ∧
      (T.originalOwnerCutCandidateHeads d y).card≤T.count r ∧
      (a,b) ∈ candidates T.G ∧ T.graph (insert (a,b) H) y.val a b ∧ (a,b) ∉ H ∧
      let targets := T.rootTailHeads root (d.tails y).tail ∩ s.support.toFinset
      W ∈ targets ∧ targets ⊆ T.originalStepFullCut d ∧
      (targets.image (fun t => (y.val,t))).card=targets.card ∧
      targets.image (fun t => (y.val,t)) ⊆ T.important ∧
      (∀ t ∈ targets,T.distance (insert (a,b) H) y.val t+T.count r≤T.distance H y.val t+2 ∧
        T.distance (insert (a,b) H) y.val t+T.distance H y.val b≤
          T.distance H y.val t+T.distance H y.val a+1) ∧
      targets.card*((T.originalOwnerCutCandidateHeads d y).card-2)≤
        T.potential H-T.potential (insert (a,b) H) := by
  classical
  let F := d.tails y
  let q := F.tail
  let C := T.originalOwnerCutCandidateHeads d y
  have hClarge : 3≤C.card := hlarge
  have hex : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,ha,hminPos⟩ := Finset.exists_min_image C (T.rootTailHeadPosition root q) hex
  obtain ⟨b,hb,hmaxPos⟩ := Finset.exists_max_image C (T.rootTailHeadPosition root q) hex
  have members : ∀ v ∈ C,v ∈ T.rootTailHeads root q ∧
      v ∉ T.rootHeadCone root U ∧ v≠first T.chains root F.entry ∧ v≠W := by
    intro v hv
    obtain ⟨hE,hbad⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hP,hU⟩ := Finset.mem_sdiff.mp hE
    refine ⟨hP,hU,?_,?_⟩
    · intro he
      exact hbad (by simp [F,he])
    · intro he
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
      have hpos : T.rootTailHeadPosition root q v=T.rootTailHeadPosition root q a := by omega
      exact Finset.mem_singleton.mpr (T.rootTailHeadPosition_injective q (members v hv).1 haP hpos)
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega
  have hrootEntry := (T.originalOwnerTail_entry_and_fixed_minimum hH d y).1
  have haQ := (T.rootTailHead_nonmarker_physical hH hrootEntry q F.rootTail haP (members a ha).2.2.1).2
  have hbQ := (T.rootTailHead_nonmarker_physical hH hrootEntry q F.rootTail hbP (members b hb).2.2.1).2
  have hab := T.rootTailHeads_order hH hrootEntry q F.rootTail haP hbP (hminPos b hb)
  let tailA := q.dropUntil a haQ
  have htailA : Allowed (T.graph H root) tailA := allowed_subwalk F.rootTail (q.isSubwalk_dropUntil haQ)
  have hbA : b ∈ tailA.support := T.actual_forward_mem_dropUntil hH q F.rootTail haQ hbQ hab
  let p : DWalk y.val a := F.prefix.append (q.takeUntil a haQ)
  let r : DWalk a b := tailA.takeUntil b hbA
  let s : DWalk b W := tailA.dropUntil b hbA
  have heq : (p.append r).append s=(d.owners y).val := by
    calc
      (p.append r).append s = p.append (r.append s) :=
        (Walk.append_assoc p r s).symm
      _ = p.append tailA :=
        congrArg (fun z => p.append z) (tailA.take_spec hbA)
      _ = F.prefix.append q :=
        (Walk.append_assoc F.prefix (q.takeUntil a haQ) (q.dropUntil a haQ)).symm.trans
          (congrArg (fun z => F.prefix.append z) (q.take_spec haQ))
      _ = (d.owners y).val := F.split.symm
  have hall : Allowed (T.graph H y.val) ((p.append r).append s) := by
    simpa only [heq] using (d.owners y).property.1
  have hwhole : T.count ((p.append r).append s)=T.distance H y.val W := by
    simpa only [heq] using (d.owners y).property.2
  obtain ⟨hpr,hsOwn⟩ := (allowed_append _ _ _).mp hall
  have hyB : Reachable T.G y.val b :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨p.append r,allowed_mono (fun _ _ h => h.1) hpr⟩
  have hrootY := (T.important_spec (T.mem_rootHeadCone_iff.mp y.property).1).1
  obtain ⟨ca,_hca,_hea,hac,_hra,_hfa,hipa,_haW,_hae⟩ :=
    T.rootTailHeads_spec hH hrootEntry q F.rootTail haP
  obtain ⟨cb,_hcb,_heb,_hbc,_hrb,_hfb,hipb,_hbW,_hbe⟩ :=
    T.rootTailHeads_spec hH hrootEntry q F.rootTail hbP
  have haCov : label T.chains a≠none := by simp [hac]
  have hbOwn := T.important_from_root_and_actual_access hrootY hyB hipb
  have hrRoot : Allowed (T.graph H root) r := allowed_subwalk htailA (tailA.isSubwalk_takeUntil hbA)
  have hCsegment : C ⊆ T.rootTailHeads root r := by
    intro v hv
    have hvP := (members v hv).1
    have hvQ := (T.rootTailHead_nonmarker_physical hH hrootEntry q F.rootTail hvP (members v hv).2.2.1).2
    have hav := T.rootTailHeads_order hH hrootEntry q F.rootTail haP hvP (hminPos v hv)
    have hvb := T.rootTailHeads_order hH hrootEntry q F.rootTail hvP hbP (hmaxPos v hv)
    have hvA := T.actual_forward_mem_dropUntil hH q F.rootTail haQ hvQ hav
    have hvr := T.actual_backward_mem_takeUntil hH tailA htailA hbA hvA hvb
    obtain ⟨_c,_hc,_he,_hl,_hr,_hf,hip,_hW,_he'⟩ := T.rootTailHeads_spec hH hrootEntry q F.rootTail hvP
    exact rootImportant_mem_tailHeads T r hip hvr
  have hRcount : C.card≤T.count r := by
    have hc := Finset.card_le_card hCsegment
    rw [T.rootTailHeads_card hH (T.important_spec hipa).1 r hrRoot] at hc
    exact hc
  have hpriceB := T.minimum_prefix hH (p.append r) s hall hwhole
  have hallA : Allowed (T.graph H y.val) (p.append (r.append s)) := by
    simpa only [Walk.append_assoc] using hall
  have hwholeA : T.count (p.append (r.append s))=T.distance H y.val W := by
    simpa only [Walk.append_assoc] using hwhole
  have hpriceA := T.minimum_prefix hH p (r.append s) hallA hwholeA
  have hjoin := T.count_append_exact hH p r hpr
  simp only [hac,Option.toFinset_some,Finset.card_singleton] at hjoin
  have hprices : T.distance H y.val b+1=T.distance H y.val a+T.count r := by omega
  obtain ⟨hlegal,hdart,_hsaveW⟩ := T.tail_interior_insertion_saving hH p r s hall hwhole haCov hbOwn hne
  let targets := T.rootTailHeads root q ∩ s.support.toFinset
  have hWhead := T.rootTailHeads_endpoint q (T.mem_rootHeadCone_iff.mp hW.1).1
  have hWT : W ∈ targets := Finset.mem_inter.mpr ⟨hWhead,List.mem_toFinset.mpr s.end_mem_support⟩
  have htargetImportant : ∀ t ∈ targets,(y.val,t) ∈ T.important := by
    intro t ht
    obtain ⟨htP,htS⟩ := Finset.mem_inter.mp ht
    have ht := List.mem_toFinset.mp htS
    have hyt : Reachable T.G y.val t :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨(p.append r).append (s.takeUntil t ht),allowed_mono (fun _ _ h => h.1)
          ((allowed_append _ _ _).mpr ⟨hpr,allowed_subwalk hsOwn (s.isSubwalk_takeUntil ht)⟩)⟩
    obtain ⟨_c,_hc,_he,_hl,_hr,_hf,hip,_hW,_he'⟩ := T.rootTailHeads_spec hH hrootEntry q F.rootTail htP
    exact T.important_from_root_and_actual_access hrootY hyt hip
  have htargetCut : targets ⊆ T.originalStepFullCut d := by
    intro t ht
    obtain ⟨htP,htS⟩ := Finset.mem_inter.mp ht
    obtain ⟨c,_hc,_he,hl,_hr,_hf,hip,htW,_he'⟩ := T.rootTailHeads_spec hH hrootEntry q F.rootTail htP
    have hbt : Reachable T.G b t :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨s.takeUntil t (List.mem_toFinset.mp htS),allowed_mono (fun _ _ h => h.1)
          (allowed_subwalk hsOwn (s.isSubwalk_takeUntil (List.mem_toFinset.mp htS)))⟩
    have hnot : t ∉ T.rootHeadCone root U := by
      intro htU
      obtain ⟨cB,hBc⟩ := T.important_covered hipb
      exact (members b hb).2.1 (T.mem_rootHeadCone_iff.mpr
        ⟨hipb,reachable_trans hbt (T.mem_rootHeadCone_iff.mp htU).2.1,cB,hBc⟩)
    exact Finset.mem_sdiff.mpr ⟨T.mem_rootHeadCone_iff.mpr ⟨hip,htW,c,hl⟩,hnot⟩
  have hsave : ∀ t ∈ targets,T.distance (insert (a,b) H) y.val t+T.count r≤T.distance H y.val t+2 := by
    intro t ht
    exact T.interior_insertion_suffix_saving hH p r s hall hwhole haCov hbOwn hne
      (List.mem_toFinset.mp (Finset.mem_inter.mp ht).2)
  have hfresh : (a,b) ∉ H := by
    intro he
    have hs := hsave W hWT
    rw [Finset.insert_eq_of_mem he] at hs
    omega
  have hpairCard : (targets.image (fun t => (y.val,t))).card=targets.card := by
    apply Finset.card_image_iff.mpr
    intro t _ u _ he
    exact (Prod.mk.inj he).2
  have hpairSub : targets.image (fun t => (y.val,t)) ⊆ T.important := by
    intro st hst
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hst
    exact htargetImportant t ht
  have hbank : targets.card*(C.card-2)≤T.potential H-T.potential (insert (a,b) H) := by
    apply T.source_drop_lower_bound H (a,b) y.val targets (C.card-2) htargetImportant
    intro t ht
    have hs := hsave t ht
    omega
  refine ⟨a,ha,b,hb,hne,p,r,s,heq,hpriceA,hpriceB,hprices,hRcount,hlegal,hdart,hfresh,
    hWT,htargetCut,hpairCard,hpairSub,?_,hbank⟩
  intro t ht
  have hs := hsave t ht
  exact ⟨hs,by omega⟩

/-- Actual finite branch, not an assumed long/favorable family: few
eligible heads force Delta<=4; otherwise the SAME row has the proved bank. -/
theorem originalOwnerCut_short_or_positive_bank {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    ((T.originalOwnerCutCandidateHeads d y).card≤2 ∧ T.distance H root W-T.distance H root U≤4) ∨
      ∃ e ∈ candidates T.G,e ∉ H ∧ 1≤T.potential H-T.potential (insert e H) ∧
        T.distance H root W-T.distance H root U-4≤T.potential H-T.potential (insert e H) := by
  classical
  obtain ⟨_hcardExact,_hdebitPositive,_hdebitUpper,hdropBound⟩ :=
    T.originalOwnerCutCandidateHeads_card hH hk hW d y
  by_cases hs : (T.originalOwnerCutCandidateHeads d y).card≤2
  · exact Or.inl ⟨hs,by omega⟩
  · have hl : 3≤(T.originalOwnerCutCandidateHeads d y).card := by omega
    obtain ⟨a,_ha,b,_hb,_hne,p,r,s,_heq,_hpa,_hpb,_hp,_hR,hlegal,_hdart,hfresh,
      hWT,_hcut,_hpairCard,_hpairSub,_hsaving,hbank⟩ := T.exists_originalOwnerCut_bank hH hk hW d y hl
    have hcount : 1≤(T.rootTailHeads root (d.tails y).tail ∩ s.support.toFinset).card :=
      Finset.one_le_card.mpr ⟨W,hWT⟩
    have hmul := Nat.mul_le_mul_right ((T.originalOwnerCutCandidateHeads d y).card-2) hcount
    have hone : 1≤T.potential H-T.potential (insert (a,b) H) := by
      simp only [Nat.one_mul] at hmul
      omega
    have hD : T.distance H root W-T.distance H root U-4≤
        T.potential H-T.potential (insert (a,b) H) := by
      simp only [Nat.one_mul] at hmul
      omega
    exact Or.inr ⟨(a,b),hlegal,hfresh,hone,hD⟩

end GreedyShortcuts.ChainDistance.Context
