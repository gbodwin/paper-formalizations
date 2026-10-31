import GreedyShortcuts.ChainCanonicalSuffixCounts

/-! Quantitative downstream-target amplification for ONE actual canonical
cohort, at ONE H and original ROOT. All original sources keep their own OLD
minimum and FIRST filter through the accepted cut bank. This is a local
candidate offer, not useful cohort coverage or cumulative selected payment. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Every attained noninitial count level supplies its exact downstream
target count. The witnesses are the actual physical subwalks of q; no
source-rebased minimum, target-population premise or alternate score sum. -/
theorem originalCanonicalGroup_exact_level_pressure {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U a : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y₀ : T.RootOwner root (d.corridor.getVert d.index))
    (ha : a ∈ (T.originalOwnerCanonicalTail d y₀).support)
    (hipa : (root,a) ∈ T.important) (hipW : (root,W) ∈ T.important)
    (ell : ℕ) (hell : 3 ≤ ell)
    (hellq : ell ≤ T.count (T.originalOwnerSharedSuffix d y₀ ha)) :
    let q := T.originalOwnerSharedSuffix d y₀ ha
    ∃ (b : V) (hb : b ∈ q.support),
      let r := q.takeUntil b hb
      let s := q.dropUntil b hb
      let targets := T.rootTailHeads root q ∩ s.support.toFinset
      (root,b) ∈ T.important ∧ (a,b) ∈ candidates T.G ∧ (a,b) ∉ H ∧
      W ∈ targets ∧ b ∈ targets ∧ T.count r = ell ∧
      targets.card + ell = T.count q + 1 ∧
      1 ≤ (T.originalOwnerCanonicalGroup d a).card ∧
      (∀ x ∈ T.originalCanonicalCutSources d a, ∀ t ∈ targets,
        (x,t) ∈ T.important ∧ T.graph (insert (a,b) H) x a b ∧
        T.distance (insert (a,b) H) x t + ell ≤ T.distance H x t + 2) ∧
      (T.originalOwnerCanonicalGroup d a).card *
        (T.count q + 1 - ell) * (ell - 2) ≤
          T.potential H - T.potential (insert (a,b) H) := by
  classical
  let q := T.originalOwnerSharedSuffix d y₀ ha
  obtain ⟨hq,_hroota,hmin⟩ := T.originalOwnerSharedSuffix_root hH d y₀ ha
  obtain ⟨b,hb,hipb,hba,hr,htc⟩ :=
    T.fixedRootSuffix_level_split hH q hipa hmin ell (by omega) hellq
  dsimp only [q] at hr htc
  obtain ⟨hlegal,hfresh,hWT,hcohort,hrows,hbank⟩ :=
    T.originalCanonicalGroup_cut_bank hH d y₀ ha hipa hipb hipW hb
      (Ne.symm hba) (by omega)
  have hbT : b ∈ T.rootTailHeads root q ∩ (q.dropUntil b hb).support.toFinset :=
    Finset.mem_inter.mpr ⟨T.rootTailHeads_of_important_mem q hipb hb,
      List.mem_toFinset.mpr (q.dropUntil b hb).start_mem_support⟩
  have hcard : (T.rootTailHeads root q ∩ (q.dropUntil b hb).support.toFinset).card =
      T.count q + 1 - ell := by
    dsimp only [q]
    omega
  dsimp only [q] at hcard
  refine ⟨b,hb,hipb,hlegal,hfresh,hWT,hbT,hr,htc,hcohort,?_,?_⟩
  · simpa only [hr] using hrows
  · simpa only [hr,hcard] using hbank

/-- A real midpoint balances attained prefix saving against the actual
remaining distinct target heads. The literal cohort factor is retained;
only its inherited cardinality >= 1 is claimed. -/
theorem originalCanonicalGroup_midpoint_pressure {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} {W U a : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (y₀ : T.RootOwner root (d.corridor.getVert d.index))
    (ha : a ∈ (T.originalOwnerCanonicalTail d y₀).support)
    (hipa : (root,a) ∈ T.important) (hipW : (root,W) ∈ T.important)
    (hN : 3 ≤ T.count (T.originalOwnerSharedSuffix d y₀ ha)) :
    let q := T.originalOwnerSharedSuffix d y₀ ha
    let m := (T.count q - 1) / 2
    ∃ (b : V) (hb : b ∈ q.support),
      let targets := T.rootTailHeads root q ∩ (q.dropUntil b hb).support.toFinset
      (root,b) ∈ T.important ∧ (a,b) ∈ candidates T.G ∧ (a,b) ∉ H ∧
      W ∈ targets ∧ b ∈ targets ∧
      T.count (q.takeUntil b hb) = m + 2 ∧
      targets.card = T.count q - 1 - m ∧
      1 ≤ (T.originalOwnerCanonicalGroup d a).card ∧
      (T.originalOwnerCanonicalGroup d a).card *
        (T.count q - 1 - m) * m ≤ T.potential H - T.potential (insert (a,b) H) ∧
      (T.originalOwnerCanonicalGroup d a).card * (T.count q - 2) * (T.count q - 2) ≤
        4 * (T.potential H - T.potential (insert (a,b) H)) := by
  classical
  let q := T.originalOwnerSharedSuffix d y₀ ha
  let m := (T.count q - 1) / 2
  have hNq : 3 ≤ T.count q := hN
  have hm : 3 ≤ m + 2 := by dsimp only [m]; omega
  have hmq : m + 2 ≤ T.count q := by dsimp only [m]; omega
  obtain ⟨b,hb,hipb,hlegal,hfresh,hWT,hbT,hr,htc,hcohort,_hrows,hbank⟩ :=
    T.originalCanonicalGroup_exact_level_pressure hH d y₀ ha hipa hipW (m+2) hm hmq
  have hcard : (T.rootTailHeads root q ∩ (q.dropUntil b hb).support.toFinset).card =
      T.count q - 1 - m := by
    dsimp only [q]
    omega
  have hsub : T.count q + 1 - (m+2) = T.count q - 1 - m := by omega
  dsimp only [q] at hsub
  have hprod : (T.originalOwnerCanonicalGroup d a).card * (T.count q - 1 - m) * m ≤
      T.potential H - T.potential (insert (a,b) H) := by
    simpa only [hsub,Nat.add_sub_cancel] using hbank
  refine ⟨b,hb,hipb,hlegal,hfresh,hWT,hbT,hr,hcard,hcohort,hprod,?_⟩
  have hx : T.count q - 2 ≤ 2*m := by dsimp only [m]; omega
  have hy : T.count q - 2 ≤ 2*(T.count q - 1 - m) := by dsimp only [m]; omega
  have hsquare : (T.count q - 2)*(T.count q - 2) ≤
      (2*m)*(2*(T.count q - 1 - m)) := Nat.mul_le_mul hx hy
  have hscaled := Nat.mul_le_mul_left (T.originalOwnerCanonicalGroup d a).card hsquare
  nlinarith [hscaled,hprod]

end GreedyShortcuts.ChainDistance.Context
