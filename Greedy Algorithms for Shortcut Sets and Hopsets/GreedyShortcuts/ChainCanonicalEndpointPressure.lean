import GreedyShortcuts.ChainCanonicalProfitableEndpoints

/-! A one-state suffix-length refinement of the profitable-endpoint bridge.
Actual ordered heads give triangular row savings. Averaging still pays the
literal LongCenters cardinality; alternative endpoint scores are not progress. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

private theorem twice_sum_later {A : Type*} [DecidableEq A] (S : Finset A)
    (f : A → ℕ) (hf : Set.InjOn f S) :
    S.card*(S.card-1)=2*∑ v ∈ S,(S.filter (fun w => f v<f w)).card := by
  classical
  have hsplit : ∀ v ∈ S,
      (S.filter (fun w => f v<f w)).card+
        (S.filter (fun w => f w<f v)).card=S.card-1 := by
    intro v hv
    have hdis : Disjoint (S.filter (fun w => f v<f w))
        (S.filter (fun w => f w<f v)) := by
      apply Finset.disjoint_left.mpr
      intro w hw hw'
      exact Nat.lt_asymm (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp hw').2
    have he : (S.filter (fun w => f v<f w)) ∪
        (S.filter (fun w => f w<f v))=S.erase v := by
      ext w
      simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_erase]
      constructor
      · rintro (⟨hw,hh⟩|⟨hw,hh⟩)
        · exact ⟨by intro h;subst w;omega,hw⟩
        · exact ⟨by intro h;subst w;omega,hw⟩
      · rintro ⟨hne,hw⟩
        have hn : f v≠f w := by intro h;exact hne (hf hv hw h).symm
        rcases lt_or_gt_of_ne hn with hh|hh
        · exact Or.inl ⟨hw,hh⟩
        · exact Or.inr ⟨hw,hh⟩
    rw [← Finset.card_union_of_disjoint hdis,he,Finset.card_erase_of_mem hv]
  have hswap : (∑ v ∈ S,(S.filter (fun w => f w<f v)).card)=
      ∑ v ∈ S,(S.filter (fun w => f v<f w)).card := by
    simp_rw [Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  calc
    _ = ∑ _v ∈ S,(S.card-1) := by simp
    _ = ∑ v ∈ S,((S.filter (fun w => f v<f w)).card+
          (S.filter (fun w => f w<f v)).card) := Finset.sum_congr rfl (fun v hv => (hsplit v hv).symm)
    _ = (∑ v ∈ S,(S.filter (fun w => f v<f w)).card)+
        (∑ v ∈ S,(S.filter (fun w => f w<f v)).card) := Finset.sum_add_distrib
    _ = _ := by rw [hswap];omega

theorem originalCanonical_owner_target_important {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) : (y.val,W) ∈ T.important := by
  have hall := (T.originalOwnerCanonicalTail_display hH d y).2.1
  have hyW : Reachable T.G y.val W :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨(d.tails y).prefix.append (T.originalOwnerCanonicalTail d y),
        allowed_mono (fun _ _ h => h.1) hall⟩
  exact T.important_from_root_and_actual_access
    (T.important_spec (T.mem_rootHeadCone_iff.mp y.property).1).1 hyW
    (T.mem_rootHeadCone_iff.mp hW.1).1

/-- Later distinct physical heads, v and W all occur in the literal suffix.
The two covered joins are paid by the existing interior-insertion theorem. -/
theorem originalCanonical_later_heads_saving {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U v : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    (hv : v ∈ T.originalCanonicalPhysicalExterior d y \ {W}) :
    (((T.originalCanonicalPhysicalExterior d y \ {W}).filter (fun w =>
      T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) v<
        T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) w)).card)≤
      T.distance H y.val W-T.distance (insert (v,W) H) y.val W := by
  classical
  let C := T.originalCanonicalPhysicalExterior d y \ {W}
  let L := C.filter (fun w =>
    T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) v<
      T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) w)
  have hvP := (Finset.mem_sdiff.mp hv).1
  have hvW : v≠W := by simpa only [Finset.mem_singleton] using (Finset.mem_sdiff.mp hv).2
  have hvCut := ((T.mem_originalCanonicalPhysicalExterior hH d y).mp hvP).1
  have hvIP := (T.mem_rootHeadCone_iff.mp (Finset.mem_sdiff.mp hvCut).1).1
  have hvQ : v ∈ (T.originalOwnerCanonicalTail d y).support :=
    List.mem_toFinset.mp (Finset.mem_inter.mp hvP).2
  let q := T.originalOwnerSharedSuffix d y hvQ
  have hq := T.originalOwnerSharedSuffix_root hH d y hvQ
  have hL : L ⊆ T.rootTailHeads root q := by
    intro w hw
    obtain ⟨hwC,horder⟩ := Finset.mem_filter.mp hw
    have hwP := (Finset.mem_sdiff.mp hwC).1
    have hwCut := ((T.mem_originalCanonicalPhysicalExterior hH d y).mp hwP).1
    have hwIP := (T.mem_rootHeadCone_iff.mp (Finset.mem_sdiff.mp hwCut).1).1
    have hwQ : w ∈ (T.originalOwnerCanonicalTail d y).support :=
      List.mem_toFinset.mp (Finset.mem_inter.mp hwP).2
    have hvw := T.originalCanonicalPhysicalExterior_order hH d y hvP hwP (Nat.le_of_lt horder)
    have hwAfter : w ∈ q.support := T.actual_forward_mem_dropUntil hH
      (T.originalOwnerCanonicalTail d y) (T.originalCanonicalTail_root hH d y).2.1 hvQ hwQ hvw
    obtain ⟨c,hc⟩ := T.important_covered hwIP
    exact Finset.mem_image.mpr ⟨c,(T.mem_chainSet q c).mpr ⟨w,hwAfter,hc⟩,
      by simpa only [first,hc] using (T.important_spec hwIP).2⟩
  have hvHead : v ∈ T.rootTailHeads root q := by
    obtain ⟨c,hc⟩ := T.important_covered hvIP
    exact Finset.mem_image.mpr ⟨c,(T.mem_chainSet q c).mpr ⟨v,q.start_mem_support,hc⟩,
      by simpa only [first,hc] using (T.important_spec hvIP).2⟩
  have hWHead := T.rootTailHeads_endpoint q (T.mem_rootHeadCone_iff.mp hW.1).1
  have hvNot : v ∉ L := by simp [L]
  have hWNot : W ∉ L := by simp [L,C]
  have hsub : insert v (insert W L) ⊆ T.rootTailHeads root q := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact hvHead
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact hWHead
    · exact hL hz
  have hc : (insert v (insert W L)).card=L.card+2 := by simp [hvNot,hWNot,hvW]
  have hN : L.card+2≤T.count q := by
    calc
      _ = (insert v (insert W L)).card := hc.symm
      _ ≤ (T.rootTailHeads root q).card := Finset.card_le_card hsub
      _ = _ := T.rootTailHeads_card hH hq.2.1 q hq.1
  let p := T.originalOwnerCanonicalPrefix d y hvQ
  have hy := T.originalOwnerCanonicalGroup_witness d y hvQ
  obtain ⟨_he,hall,_hq,hmin,_hp,_hj⟩ := T.originalOwnerCanonicalGroup_row hH d y hvQ y hy
  have hall' : Allowed (T.graph H y.val) ((p.append q).append (.nil : DWalk W W)) := by simpa using hall
  have hmin' : T.count ((p.append q).append (.nil : DWalk W W))=T.distance H y.val W := by simpa using hmin
  have hsave := T.interior_insertion_drop hH p q .nil hall' hmin'
    (T.originalCanonical_owner_target_important hH hW d y) hvW
  exact (by omega : L.card≤T.count q-2).trans hsave

/-- Triangular physical row pressure, restricted to the ACTUAL long centers.
The gain is the original (y,W) cell at the same H and the same edge (v,W). -/
theorem originalCanonical_row_triangular_pressure {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    (T.distance H root W-T.distance H root U-2)*
        (T.distance H root W-T.distance H root U-3)≤
      2*∑ v ∈ T.originalCanonicalLongCenters d,
        (T.distance H y.val W-T.distance (insert (v,W) H) y.val W) := by
  classical
  let C := T.originalCanonicalPhysicalExterior d y \ {W}
  let f := T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y)
  let L := T.originalCanonicalLongCenters d
  have hinj : Set.InjOn f C := by
    intro v hv w hw he
    exact T.originalCanonicalPhysicalExterior_order_injective d y
      (Finset.mem_sdiff.mp hv).1 (Finset.mem_sdiff.mp hw).1 he
  have hzero : ∀ v ∈ C,v ∉ L → (C.filter (fun w => f v<f w)).card=0 := by
    intro v hv hn
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hwC,hlt⟩ := Finset.mem_filter.mp hw
    have hne : v≠w := by intro he;subst w;omega
    exact hn (T.originalCanonical_earlier_is_long hH hW d y hv hwC hne (Nat.le_of_lt hlt))
  have hrestrict : (∑ v ∈ C,(C.filter (fun w => f v<f w)).card)=
      ∑ v ∈ C ∩ L,(C.filter (fun w => f v<f w)).card := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro v hv hvnot
    exact hzero v hv (by intro hl;exact hvnot (Finset.mem_inter.mpr ⟨hv,hl⟩))
  have hsum : (∑ v ∈ C,(C.filter (fun w => f v<f w)).card)≤
      ∑ v ∈ L,(T.distance H y.val W-T.distance (insert (v,W) H) y.val W) := by
    rw [hrestrict]
    calc
      _ ≤ ∑ v ∈ C ∩ L,(T.distance H y.val W-T.distance (insert (v,W) H) y.val W) :=
        Finset.sum_le_sum (fun v hv => T.originalCanonical_later_heads_saving hH hW d y (Finset.mem_inter.mp hv).1)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => Nat.zero_le _)
  have hcard : T.distance H root W-T.distance H root U≤C.card+2 :=
    (T.originalCanonicalPhysicalExterior_W_debit hH hk hW d y).2.2
  have hleft : (T.distance H root W-T.distance H root U-2)*
      (T.distance H root W-T.distance H root U-3)≤C.card*(C.card-1) :=
    Nat.mul_le_mul (by omega) (by omega)
  exact hleft.trans ((twice_sum_later C f hinj).le.trans (Nat.mul_le_mul_left 2 hsum))

/-- Original owner subtypes are distinct physical sources. Keeping W once
per source embeds their ACTUAL cell drops into the full objective decrease. -/
theorem originalCanonical_endpoint_owner_sum {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U v : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U) :
    (∑ y : T.RootOwner root (d.corridor.getVert d.index),
      (T.distance H y.val W-T.distance (insert (v,W) H) y.val W))≤
      T.potential H-T.potential (insert (v,W) H) := by
  classical
  let S : Finset (V×V) := Finset.univ.image
    (fun y : T.RootOwner root (d.corridor.getVert d.index) => (y.val,W))
  have hsub : S ⊆ T.important := by
    intro st hst
    obtain ⟨y,_hy,rfl⟩ := Finset.mem_image.mp hst
    exact T.originalCanonical_owner_target_important hH hW d y
  have he : (∑ st ∈ S,(T.distance H st.1 st.2-T.distance (insert (v,W) H) st.1 st.2))=
      ∑ y : T.RootOwner root (d.corridor.getVert d.index),
        (T.distance H y.val W-T.distance (insert (v,W) H) y.val W) := by
    apply Finset.sum_image
    intro y _ z _ he
    exact Subtype.ext (Prod.mk.inj he).1
  rw [T.potential_drop_sum,← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- The additional suffix-length factor is derived from actual physical
order, not favorable cohort coverage. Scores of distinct edges are used
only in the averaging inequality, never added as selected progress. -/
theorem originalCanonical_triangular_endpoint_inventory {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U) :
    Fintype.card (T.RootOwner root (d.corridor.getVert d.index))*
        (T.distance H root W-T.distance H root U-2)*
        (T.distance H root W-T.distance H root U-3)≤
      2*∑ v ∈ T.originalCanonicalLongCenters d,
        (T.potential H-T.potential (insert (v,W) H)) := by
  classical
  calc
    _ = ∑ _y : T.RootOwner root (d.corridor.getVert d.index),
        (T.distance H root W-T.distance H root U-2)*
        (T.distance H root W-T.distance H root U-3) := by simp [Nat.mul_assoc]
    _ ≤ ∑ y : T.RootOwner root (d.corridor.getVert d.index),
        2*∑ v ∈ T.originalCanonicalLongCenters d,
          (T.distance H y.val W-T.distance (insert (v,W) H) y.val W) :=
      Finset.sum_le_sum (fun y _ => T.originalCanonical_row_triangular_pressure hH hk hW d y)
    _ = 2*∑ v ∈ T.originalCanonicalLongCenters d,
        ∑ y : T.RootOwner root (d.corridor.getVert d.index),
          (T.distance H y.val W-T.distance (insert (v,W) H) y.val W) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ _ := Nat.mul_le_mul_left 2
      (Finset.sum_le_sum (fun _ _ => T.originalCanonical_endpoint_owner_sum hH hW d))

/-- ONE actual maximum endpoint earns the quadratic-gap numerator divided
by the explicit 2*LongCenters.card multiplicity. No denominator cancellation,
cumulative payment or original-scale cubic/phase conclusion is asserted. -/
theorem exists_originalCanonical_triangular_endpoint_pressure {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y₀ : T.RootOwner root (d.corridor.getVert d.index))
    (hgap : 4≤T.distance H root W-T.distance H root U) :
    ∃ v ∈ T.originalCanonicalLongCenters d,
      (v,W) ∈ candidates T.G ∧ (v,W) ∉ H ∧
      1≤T.potential H-T.potential (insert (v,W) H) ∧
      (∀ z ∈ T.originalCanonicalLongCenters d,
        T.potential H-T.potential (insert (z,W) H)≤
          T.potential H-T.potential (insert (v,W) H)) ∧
      Fintype.card (T.RootOwner root (d.corridor.getVert d.index))*
          (T.distance H root W-T.distance H root U-2)*
          (T.distance H root W-T.distance H root U-3)≤
        2*(T.originalCanonicalLongCenters d).card*
          (T.potential H-T.potential (insert (v,W) H)) := by
  classical
  obtain ⟨u,hu,_⟩ := T.exists_originalCanonical_profitable_endpoint_pressure hH hk hW d y₀ hgap
  obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image (T.originalCanonicalLongCenters d)
    (fun z => T.potential H-T.potential (insert (z,W) H)) ⟨u,hu⟩
  obtain ⟨hlegal,hfresh,hpositive,_⟩ := T.originalCanonical_long_endpoint_bank hH hW d hv
  have hsum : (∑ z ∈ T.originalCanonicalLongCenters d,
      (T.potential H-T.potential (insert (z,W) H)))≤
      (T.originalCanonicalLongCenters d).card*(T.potential H-T.potential (insert (v,W) H)) := by
    calc
      _ ≤ ∑ _z ∈ T.originalCanonicalLongCenters d,
          (T.potential H-T.potential (insert (v,W) H)) := Finset.sum_le_sum (fun z hz => hmax z hz)
      _ = _ := by simp
  refine ⟨v,hv,hlegal,hfresh,hpositive,hmax,?_⟩
  exact (T.originalCanonical_triangular_endpoint_inventory hH hk hW d).trans
    (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hsum)

end GreedyShortcuts.ChainDistance.Context
