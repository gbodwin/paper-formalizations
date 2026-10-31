import GreedyShortcuts.ChainCanonicalCohortCoverage

/-! Filter literal centers by an actual long canonical suffix. At most one
nonterminal physical head per original row fails this filter. Every retained
center supplies a genuine profitable endpoint edge. Averaging selects ONE
actual candidate; the sum of alternative scores is never spent as progress. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def originalCanonicalLongCenters {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U) : Finset V := by
  classical
  exact (T.originalStepFullCut d \ {W}).filter (fun v =>
    ∃ y : T.RootOwner root (d.corridor.getVert d.index),
      ∃ hv : v ∈ (T.originalOwnerCanonicalTail d y).support,
        3≤T.count (T.originalOwnerSharedSuffix d y hv))

/-- Distinct retained centers index distinct endpoint candidates. -/
theorem originalCanonical_long_endpoint_card {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U) :
    ((T.originalCanonicalLongCenters d).image (fun v => (v,W))).card=
      (T.originalCanonicalLongCenters d).card := by
  classical
  apply Finset.card_image_iff.mpr
  intro v _ w _ he
  exact (Prod.mk.inj he).1

private theorem endpoint_important_head {root a z t : V} (q : DWalk a z)
    (hip : (root,t) ∈ T.important) (ht : t ∈ q.support) : t ∈ T.rootTailHeads root q := by
  classical
  obtain ⟨c,hc⟩ := T.important_covered hip
  refine Finset.mem_image.mpr ⟨c,(T.mem_chainSet q c).mpr ⟨t,ht,hc⟩,?_⟩
  simpa only [first,hc] using (T.important_spec hip).2

/-- An earlier distinct nonterminal physical head sees itself, the later
head and W in its SAME ROOT suffix. It therefore passes the long filter. -/
theorem originalCanonical_earlier_is_long {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U v w : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index))
    (hv : v ∈ T.originalCanonicalPhysicalExterior d y \ {W})
    (hw : w ∈ T.originalCanonicalPhysicalExterior d y \ {W}) (hne : v≠w)
    (horder : T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) v≤
      T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) w) :
    v ∈ T.originalCanonicalLongCenters d := by
  classical
  obtain ⟨hvP,hvNotW⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨hwP,hwNotW⟩ := Finset.mem_sdiff.mp hw
  have hvW : v≠W := by simpa only [Finset.mem_singleton] using hvNotW
  have hwW : w≠W := by simpa only [Finset.mem_singleton] using hwNotW
  have hvCut := ((T.mem_originalCanonicalPhysicalExterior hH d y).mp hvP).1
  have hwCut := ((T.mem_originalCanonicalPhysicalExterior hH d y).mp hwP).1
  have hvIP := (T.mem_rootHeadCone_iff.mp (Finset.mem_sdiff.mp hvCut).1).1
  have hwIP := (T.mem_rootHeadCone_iff.mp (Finset.mem_sdiff.mp hwCut).1).1
  have hvQ : v ∈ (T.originalOwnerCanonicalTail d y).support :=
    List.mem_toFinset.mp (Finset.mem_inter.mp hvP).2
  have hwQ : w ∈ (T.originalOwnerCanonicalTail d y).support :=
    List.mem_toFinset.mp (Finset.mem_inter.mp hwP).2
  let q := T.originalOwnerSharedSuffix d y hvQ
  have hfull := T.originalCanonicalTail_root hH d y
  have hvw := T.originalCanonicalPhysicalExterior_order hH d y hvP hwP horder
  have hwAfter : w ∈ q.support :=
    T.actual_forward_mem_dropUntil hH (T.originalOwnerCanonicalTail d y) hfull.2.1 hvQ hwQ hvw
  have hq := T.originalOwnerSharedSuffix_root hH d y hvQ
  have hvHead := endpoint_important_head T q hvIP q.start_mem_support
  have hwHead := endpoint_important_head T q hwIP hwAfter
  have hWHead := T.rootTailHeads_endpoint q (T.mem_rootHeadCone_iff.mp hW.1).1
  have hsub : ({v,w,W} : Finset V) ⊆ T.rootTailHeads root q := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl|rfl
    · exact hvHead
    · exact hwHead
    · exact hWHead
  have hthree : ({v,w,W} : Finset V).card=3 := by simp [hne,hvW,hwW]
  have hN : 3≤T.count q := by
    calc
      3 = ({v,w,W} : Finset V).card := hthree.symm
      _ ≤ (T.rootTailHeads root q).card := Finset.card_le_card hsub
      _ = T.count q := T.rootTailHeads_card hH hq.2.1 q hq.1
  exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hvCut,hvNotW⟩,⟨y,hvQ,hN⟩⟩

theorem originalCanonical_short_centers_card {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    ((T.originalCanonicalPhysicalExterior d y \ {W}) \ T.originalCanonicalLongCenters d).card≤1 := by
  classical
  apply Finset.card_le_one.mpr
  intro v hv w hw
  by_contra hne
  obtain ⟨hvRow,hvShort⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨hwRow,hwShort⟩ := Finset.mem_sdiff.mp hw
  rcases le_total (T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) v)
      (T.rootTailHeadPosition root (T.originalOwnerCanonicalTail d y) w) with h|h
  · exact hvShort (T.originalCanonical_earlier_is_long hH hW d y hvRow hwRow hne h)
  · exact hwShort (T.originalCanonical_earlier_is_long hH hW d y hwRow hvRow (Ne.symm hne) h)

theorem originalCanonical_long_row_coverage {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y : T.RootOwner root (d.corridor.getVert d.index)) :
    T.distance H root W-T.distance H root U-3≤
      ((T.originalCanonicalPhysicalExterior d y \ {W}) ∩ T.originalCanonicalLongCenters d).card := by
  classical
  have hrow := (T.originalCanonicalPhysicalExterior_W_debit hH hk hW d y).2.2
  have hshort := T.originalCanonical_short_centers_card hH hW d y
  have hc := Finset.card_sdiff_add_card_inter
    (T.originalCanonicalPhysicalExterior d y \ {W}) (T.originalCanonicalLongCenters d)
  omega

/-- Exact incidence followed by a derived per-row loss of at most one
short center. This sums physical owner/head incidences, not edge gains. -/
theorem originalCanonical_long_incidence_coverage {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U) :
    Fintype.card (T.RootOwner root (d.corridor.getVert d.index))*
        (T.distance H root W-T.distance H root U-3)≤
      ∑ v ∈ T.originalCanonicalLongCenters d,(T.originalOwnerCanonicalGroup d v).card := by
  classical
  have hrow : ∀ y : T.RootOwner root (d.corridor.getVert d.index),
      (T.originalCanonicalPhysicalExterior d y \ {W}) ∩ T.originalCanonicalLongCenters d=
        (T.originalCanonicalLongCenters d).filter (fun v => y ∈ T.originalOwnerCanonicalGroup d v) := by
    intro y
    ext v
    constructor
    · intro hv
      obtain ⟨hvR,hvL⟩ := Finset.mem_inter.mp hv
      exact Finset.mem_filter.mpr ⟨hvL,
        ((T.mem_originalCanonicalPhysicalExterior hH d y).mp (Finset.mem_sdiff.mp hvR).1).2⟩
    · intro hv
      obtain ⟨hvL,hy⟩ := Finset.mem_filter.mp hv
      obtain ⟨hvCut,hvNotW⟩ := Finset.mem_sdiff.mp (Finset.mem_filter.mp hvL).1
      exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr
        ⟨(T.mem_originalCanonicalPhysicalExterior hH d y).mpr ⟨hvCut,hy⟩,hvNotW⟩,hvL⟩
  have hsum : (∑ y : T.RootOwner root (d.corridor.getVert d.index),
      ((T.originalCanonicalPhysicalExterior d y \ {W}) ∩ T.originalCanonicalLongCenters d).card)=
      ∑ v ∈ T.originalCanonicalLongCenters d,(T.originalOwnerCanonicalGroup d v).card := by
    simp_rw [hrow,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _hv
    calc
      (∑ y : T.RootOwner root (d.corridor.getVert d.index),
          if y ∈ T.originalOwnerCanonicalGroup d v then 1 else 0)=
        ∑ y ∈ T.originalOwnerCanonicalGroup d v,(1 : ℕ) := by
          rw [← Finset.sum_filter]
          congr 1
          ext y
          simp
      _ = _ := by simp
  calc
    _ = ∑ _y : T.RootOwner root (d.corridor.getVert d.index),
        (T.distance H root W-T.distance H root U-3) := by simp
    _ ≤ _ := (Finset.sum_le_sum (fun y _ => T.originalCanonical_long_row_coverage hH hk hW d y)).trans hsum.le

/-- Each retained center has ONE profitable legal endpoint edge. Every
original-source OLD minimum and entry is derived from literal coalescence. -/
theorem originalCanonical_long_endpoint_bank {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U v : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (hv : v ∈ T.originalCanonicalLongCenters d) :
    (v,W) ∈ candidates T.G ∧ (v,W) ∉ H ∧
      1≤T.potential H-T.potential (insert (v,W) H) ∧
      (T.originalOwnerCanonicalGroup d v).card≤T.potential H-T.potential (insert (v,W) H) := by
  classical
  obtain ⟨hvCutW,y₀,hv₀,hN⟩ := Finset.mem_filter.mp hv
  have hvW : v≠W := by simpa only [Finset.mem_singleton] using (Finset.mem_sdiff.mp hvCutW).2
  let q := T.originalOwnerSharedSuffix d y₀ hv₀
  have hlong : 3≤T.count q := hN
  have hq := T.originalOwnerSharedSuffix_root hH d y₀ hv₀
  have hlegal := T.interior_candidate hH q hq.1 hvW
  have hG : 1≤(T.originalOwnerCanonicalGroup d v).card :=
    Finset.one_le_card.mpr ⟨y₀,T.originalOwnerCanonicalGroup_witness d y₀ hv₀⟩
  have rows : ∀ y ∈ T.originalOwnerCanonicalGroup d v,
      (y.val,W) ∈ T.important ∧
      T.count q-2≤T.distance H y.val W-T.distance (insert (v,W) H) y.val W := by
    intro y hy
    let p := T.originalOwnerCanonicalPrefix d y ((T.mem_originalOwnerCanonicalGroup d y).mp hy)
    obtain ⟨_he,hall,_hq,hmin,_hp,_hj⟩ := T.originalOwnerCanonicalGroup_row hH d y₀ hv₀ y hy
    have hyW : Reachable T.G y.val W :=
      (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
        ⟨p.append q,allowed_mono (fun _ _ h => h.1) hall⟩
    have hrooty := (T.important_spec (T.mem_rootHeadCone_iff.mp y.property).1).1
    have hentry := T.important_from_root_and_actual_access hrooty hyW (T.mem_rootHeadCone_iff.mp hW.1).1
    have hall' : Allowed (T.graph H y.val) ((p.append q).append (.nil : DWalk W W)) := by simpa using hall
    have hmin' : T.count ((p.append q).append (.nil : DWalk W W))=T.distance H y.val W := by simpa using hmin
    exact ⟨hentry,T.interior_insertion_drop hH p q .nil hall' hmin' hentry hvW⟩
  have hbank := T.rectangle_drop_lower_bound H (v,W)
    (T.originalCanonicalCutSources d v) {W} (T.count q-2)
    (by intro x hx t ht;obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx;simpa only [Finset.mem_singleton.mp ht] using (rows y hy).1)
    (by intro x hx t ht;obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx;simpa only [Finset.mem_singleton.mp ht] using (rows y hy).2)
  rw [T.originalCanonicalCutSources_card] at hbank
  simp only [Finset.card_singleton,Nat.mul_one] at hbank
  have hmul := Nat.mul_le_mul_left (T.originalOwnerCanonicalGroup d v).card (by omega : 1≤T.count q-2)
  simp only [Nat.mul_one] at hmul
  have hpay := hmul.trans hbank
  have hpositive := hG.trans hpay
  have hfresh : (v,W) ∉ H := by
    intro he
    rw [Finset.insert_eq_of_mem he] at hpositive
    omega
  exact ⟨hlegal,hfresh,hpositive,hpay⟩

/-- Averaging bounds actual cohort incidence by the maximum of an actual
profitable candidate family at THIS H. Different scores are not added as
selected progress. No new cohort-size or phase-payment premise is used. -/
theorem exists_originalCanonical_profitable_endpoint_pressure {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (y₀ : T.RootOwner root (d.corridor.getVert d.index))
    (hgap : 4≤T.distance H root W-T.distance H root U) :
    ∃ v ∈ T.originalCanonicalLongCenters d,
      (v,W) ∈ candidates T.G ∧ (v,W) ∉ H ∧
      1≤T.potential H-T.potential (insert (v,W) H) ∧
      Fintype.card (T.RootOwner root (d.corridor.getVert d.index))*
          (T.distance H root W-T.distance H root U-3)≤
        (T.originalCanonicalLongCenters d).card*(T.potential H-T.potential (insert (v,W) H)) := by
  classical
  have hrow := T.originalCanonical_long_row_coverage hH hk hW d y₀
  have hp : 0<((T.originalCanonicalPhysicalExterior d y₀ \ {W}) ∩ T.originalCanonicalLongCenters d).card := by omega
  obtain ⟨u,hu⟩ := Finset.card_pos.mp hp
  have huL := (Finset.mem_inter.mp hu).2
  obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image (T.originalCanonicalLongCenters d)
    (fun z => T.potential H-T.potential (insert (z,W) H)) ⟨u,huL⟩
  obtain ⟨hlegal,hfresh,hpositive,_hpay⟩ := T.originalCanonical_long_endpoint_bank hH hW d hv
  have htotal := T.originalCanonical_long_incidence_coverage hH hk hW d
  have hcap : (∑ z ∈ T.originalCanonicalLongCenters d,(T.originalOwnerCanonicalGroup d z).card)≤
      (T.originalCanonicalLongCenters d).card*(T.potential H-T.potential (insert (v,W) H)) := by
    calc
      _ ≤ ∑ z ∈ T.originalCanonicalLongCenters d,
          (T.potential H-T.potential (insert (z,W) H)) :=
        Finset.sum_le_sum (fun z hz => (T.originalCanonical_long_endpoint_bank hH hW d hz).2.2.2)
      _ ≤ ∑ _z ∈ T.originalCanonicalLongCenters d,
          (T.potential H-T.potential (insert (v,W) H)) :=
        Finset.sum_le_sum (fun z hz => hmax z hz)
      _ = _ := by simp
  exact ⟨v,hv,hlegal,hfresh,hpositive,htotal.trans hcap⟩

end GreedyShortcuts.ChainDistance.Context
