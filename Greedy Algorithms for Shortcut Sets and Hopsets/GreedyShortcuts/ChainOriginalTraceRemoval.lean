import GreedyShortcuts.ChainOriginalRetiredBands

/-! SOURCE ONLY, UNCOMPILED. Full physical cone cuts and their actual
trace occurrences. No partition/owner/cone-nesting conclusions are stored
as choice inputs. This is ONE fixed-H normalized trace, not insertion time. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def originalStepFullCut {H : Finset (V × V)} {root : V} {k : ℕ} {W U : V}
    (_d : T.OriginalSelectorStepData H root k W U) : Finset V :=
  T.rootHeadCone root W \ T.rootHeadCone root U

/-- Literal OLD endpoint, child endpoint and complete original choice
record; no desired invariant or owner field is added. -/
def OriginalTraceStepRecord (H : Finset (V × V)) (root : V) (k : ℕ) :=
  Σ W : V,Σ U : V,T.OriginalSelectorStepData H root k W U

/-- Zero-based actual occurrence lookup. Out-of-range indices have no
record. Present records retain literal old-row/minimum/guard/relay data. -/
def originalTraceStepAt {H : Finset (V × V)} {root : V} {k : ℕ} {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) (i : ℕ) :
    Option (T.OriginalTraceStepRecord H root k) :=
  match tr,i with
  | .nil _,_ => none
  | .cons d _,0 => some ⟨W,T.originalStepChild d,d⟩
  | .cons _ tail,i+1 => originalTraceStepAt tail i

noncomputable def originalTraceCutAt {H : Finset (V × V)} {root : V} {k : ℕ} {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) (i : ℕ) : Finset V :=
  match tr,i with
  | .nil _,_ => ∅
  | .cons d _,0 => T.originalStepFullCut d
  | .cons _ tail,i+1 => originalTraceCutAt tail i

noncomputable def originalTraceFullRemoved {H : Finset (V × V)} {root : V} {k : ℕ}
    {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) : Finset V :=
  match tr with
  | .nil _ => ∅
  | .cons d tail => T.originalStepFullCut d ∪ originalTraceFullRemoved tail

noncomputable def originalTraceFullCutCardSum {H : Finset (V × V)} {root : V} {k : ℕ}
    {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) : ℕ :=
  match tr with
  | .nil _ => 0
  | .cons d tail => (T.originalStepFullCut d).card+originalTraceFullCutCardSum tail

theorem originalTraceStepAt_exists_iff {H : Finset (V × V)} {root : V} {k : ℕ}
    {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) (i : ℕ) :
    (∃ r,T.originalTraceStepAt tr i=some r) ↔ i<T.originalTraceLength tr := by
  induction tr generalizing i with
  | nil W => simp [originalTraceStepAt,originalTraceLength]
  | @cons W U Z d tail ih =>
    cases i with
    | zero =>
      simp [originalTraceStepAt,originalTraceLength]
      exact ⟨_,rfl⟩
    | succ i => simpa [originalTraceStepAt,originalTraceLength] using ih i

theorem originalTraceCutAt_record {H : Finset (V × V)} {root : V} {k : ℕ}
    {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) (i : ℕ) :
    T.originalTraceCutAt tr i=
      match T.originalTraceStepAt tr i with
      | none => ∅
      | some r => T.rootHeadCone root r.1 \ T.rootHeadCone root r.2.1 := by
  induction tr generalizing i with
  | nil W => rfl
  | @cons W U Z d tail ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem originalTraceCutAt_empty_of_outside {H : Finset (V × V)} {root : V} {k : ℕ}
    {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) (i : ℕ)
    (hi : T.originalTraceLength tr ≤ i) : T.originalTraceCutAt tr i=∅ := by
  rw [T.originalTraceCutAt_record]
  cases he : T.originalTraceStepAt tr i with
  | none => rfl
  | some r =>
    have hlt := (T.originalTraceStepAt_exists_iff tr i).mp ⟨r,he⟩
    omega

/-- Every present lookup has its actual normalization, endpoint nesting
and OLD-row branch witnesses rederived from the unchanged selected data. -/
theorem originalTraceStepAt_geometry {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    ∀ hW : T.RootConeMaximizer H root W W,∀ i r,
      T.originalTraceStepAt tr i=some r →
      T.RootConeMaximizer H root r.1 r.1 ∧
      T.RootConeMaximizer H root r.2.1 r.2.1 ∧
      T.rootHeadCone root r.1 ⊆ T.rootHeadCone root W ∧
      T.rootHeadCone root Z ⊆ T.rootHeadCone root r.2.1 ∧
      T.OriginalMinimumTailStepFacts k (16*k) r.2.2.owners r.2.2.tails
        r.2.2.minOwner r.2.2.maxOwner r.2.1 ∧
      T.OriginalMinimumTailBranchFacts k (16*k) r.2.2.owners r.2.2.tails
        r.2.2.minOwner r.2.2.maxOwner r.2.1 := by
  induction tr with
  | nil W => intro hW i r he;cases he
  | @cons W U Z d tail ih =>
    intro hW i r he
    obtain ⟨hf,hb⟩ := T.originalSelectorStepData_facts hH hk hW d
    have hU := hf.2.2.1
    have hUW := hf.2.2.2.1
    cases i with
    | zero =>
      have hr : (⟨W,U,d⟩ : T.OriginalTraceStepRecord H root k)=r := Option.some.inj he
      subst r
      exact ⟨hW,hU,Finset.Subset.refl _,
        (T.originalTrace_bounds hH hk tail hU).2.2.1,hf,hb⟩
    | succ i =>
      obtain ⟨hA,hB,hAW,hZB,hf',hb'⟩ := ih hU i r he
      exact ⟨hA,hB,Finset.Subset.trans hAW hUW,hZB,hf',hb'⟩

/-- The exact cut union is the whole initial-minus-final cone. Its
cardinality is the sum of the actual full cuts, not event-name counts. -/
theorem originalTraceFullRemoved_partition {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    ∀ hW : T.RootConeMaximizer H root W W,
      T.originalTraceFullRemoved tr=T.rootHeadCone root W \ T.rootHeadCone root Z ∧
      Disjoint (T.originalTraceFullRemoved tr) (T.rootHeadCone root Z) ∧
      T.originalTraceFullRemoved tr ∪ T.rootHeadCone root Z=T.rootHeadCone root W ∧
      (T.originalTraceFullRemoved tr).card+(T.rootHeadCone root Z).card=
        (T.rootHeadCone root W).card ∧
      (T.originalTraceFullRemoved tr).card=T.originalTraceFullCutCardSum tr := by
  classical
  induction tr with
  | nil W =>
    intro hW
    simp [originalTraceFullRemoved,originalTraceFullCutCardSum]
  | @cons W U Z d tail ih =>
    intro hW
    have hf := (T.originalSelectorStepData_facts hH hk hW d).1
    have hU := hf.2.2.1
    have hUW := hf.2.2.2.1
    have hZU := (T.originalTrace_bounds hH hk tail hU).2.2.1
    obtain ⟨heTail,_hdTail,_huTail,_hcTail,hSumTail⟩ := ih hU
    let D := T.originalStepFullCut d
    let F := T.originalTraceFullRemoved tail
    have hF : F=T.rootHeadCone root U \ T.rootHeadCone root Z := heTail
    have hDF : Disjoint D F := by
      apply Finset.disjoint_left.mpr
      intro b hd hb
      exact (Finset.mem_sdiff.mp hd).2 (Finset.mem_sdiff.mp (hF ▸ hb)).1
    have he : D ∪ F=T.rootHeadCone root W \ T.rootHeadCone root Z := by
      ext b
      constructor
      · intro hb
        rcases Finset.mem_union.mp hb with hb|hb
        · obtain ⟨hw,hnu⟩ := Finset.mem_sdiff.mp hb
          exact Finset.mem_sdiff.mpr ⟨hw,fun hz => hnu (hZU hz)⟩
        · obtain ⟨hu,hnz⟩ := Finset.mem_sdiff.mp (hF ▸ hb)
          exact Finset.mem_sdiff.mpr ⟨hUW hu,hnz⟩
      · intro hb
        obtain ⟨hw,hnz⟩ := Finset.mem_sdiff.mp hb
        by_cases hu : b ∈ T.rootHeadCone root U
        · exact Finset.mem_union_right _ (hF.symm ▸ Finset.mem_sdiff.mpr ⟨hu,hnz⟩)
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hw,hu⟩)
    have hd : Disjoint (D ∪ F) (T.rootHeadCone root Z) := by
      apply Finset.disjoint_left.mpr
      intro b hb hz
      exact (Finset.mem_sdiff.mp (he ▸ hb)).2 hz
    have hu : (D ∪ F) ∪ T.rootHeadCone root Z=T.rootHeadCone root W := by
      ext b
      constructor
      · intro hb
        rcases Finset.mem_union.mp hb with hb|hb
        · exact (Finset.mem_sdiff.mp (he ▸ hb)).1
        · exact hUW (hZU hb)
      · intro hw
        by_cases hz : b ∈ T.rootHeadCone root Z
        · exact Finset.mem_union_right _ hz
        · exact Finset.mem_union_left _ (he.symm ▸ Finset.mem_sdiff.mpr ⟨hw,hz⟩)
    have hc : (D ∪ F).card+(T.rootHeadCone root Z).card=(T.rootHeadCone root W).card := by
      rw [← Finset.card_union_of_disjoint hd,hu]
    have hs : (D ∪ F).card=D.card+T.originalTraceFullCutCardSum tail := by
      rw [Finset.card_union_of_disjoint hDF]
      exact congrArg (D.card+·) hSumTail
    exact ⟨he,hd,hu,hc,hs⟩

theorem mem_originalTraceFullRemoved_iff {H : Finset (V × V)} {root : V} {k : ℕ}
    {W Z b : V} (tr : T.OriginalSelectorTrace H root k W Z) :
    b ∈ T.originalTraceFullRemoved tr ↔ ∃ i,b ∈ T.originalTraceCutAt tr i := by
  classical
  induction tr with
  | nil W => simp [originalTraceFullRemoved,originalTraceCutAt]
  | @cons W U Z d tail ih =>
    constructor
    · intro hb
      rcases Finset.mem_union.mp hb with hb|hb
      · exact ⟨0,hb⟩
      · obtain ⟨i,hi⟩ := ih.mp hb
        exact ⟨i+1,hi⟩
    · rintro ⟨i,hi⟩
      cases i with
      | zero => exact Finset.mem_union_left _ hi
      | succ i => exact Finset.mem_union_right _ (ih.mpr ⟨i,hi⟩)

/-- Actual later OLD endpoints lie in an earlier child cone, including
rank-neutral stages. This is original cone nesting, not filter transport. -/
theorem originalTraceStepAt_chronology {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    ∀ hW : T.RootConeMaximizer H root W W,∀ i j a b,
      T.originalTraceStepAt tr i=some a → T.originalTraceStepAt tr j=some b → i<j →
      T.rootHeadCone root b.1 ⊆ T.rootHeadCone root a.2.1 := by
  induction tr with
  | nil W => intro hW i j a b hi;cases hi
  | @cons W U Z d tail ih =>
    intro hW i j a b hi hj hij
    have hU := (T.originalSelectorStepData_facts hH hk hW d).1.2.2.1
    cases i with
    | zero =>
      have ha : (⟨W,U,d⟩ : T.OriginalTraceStepRecord H root k)=a := Option.some.inj hi
      subst a
      cases j with
      | zero => omega
      | succ j => exact (T.originalTraceStepAt_geometry hH hk tail hU j b hj).2.2.1
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact ih hU i j a b hi hj (by omega)

theorem originalTraceCuts_pairwise_disjoint {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z)
    (hW : T.RootConeMaximizer H root W W) :
    Pairwise (fun i j : ℕ => Disjoint (T.originalTraceCutAt tr i) (T.originalTraceCutAt tr j)) := by
  classical
  intro i j hne
  apply Finset.disjoint_left.mpr
  intro v hi hj
  have actual : ∀ n,v ∈ T.originalTraceCutAt tr n →
      ∃ r,T.originalTraceStepAt tr n=some r ∧
        v ∈ T.rootHeadCone root r.1 ∧ v ∉ T.rootHeadCone root r.2.1 := by
    intro n hn
    rw [T.originalTraceCutAt_record] at hn
    cases he : T.originalTraceStepAt tr n with
    | none => simp [he] at hn
    | some r =>
      rw [he] at hn
      exact ⟨r,rfl,(Finset.mem_sdiff.mp hn).1,(Finset.mem_sdiff.mp hn).2⟩
  obtain ⟨a,ha,hpa,hna⟩ := actual i hi
  obtain ⟨b,hb,hpb,hnb⟩ := actual j hj
  rcases lt_or_gt_of_ne hne with hij|hji
  · exact hna (T.originalTraceStepAt_chronology hH hk tr hW i j a b ha hb hij hpb)
  · exact hnb (T.originalTraceStepAt_chronology hH hk tr hW j i b a hb ha hji hpa)

/-- Every initial physical head has a unique actual cut occurrence unless
it survives in the final cone. No renewed owner-pool exit is a cut test. -/
theorem originalTrace_removed_unique {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z)
    (hW : T.RootConeMaximizer H root W W) {b : V}
    (hb : b ∈ T.rootHeadCone root W) (hn : b ∉ T.rootHeadCone root Z) :
    ∃! i,b ∈ T.originalTraceCutAt tr i := by
  have he := (T.originalTraceFullRemoved_partition hH hk tr hW).1
  have hremoved : b ∈ T.originalTraceFullRemoved tr :=
    he.symm ▸ Finset.mem_sdiff.mpr ⟨hb,hn⟩
  obtain ⟨i,hi⟩ := (T.mem_originalTraceFullRemoved_iff tr).mp hremoved
  refine ⟨i,hi,?_⟩
  intro j hj
  by_contra hne
  exact Finset.disjoint_left.mp (T.originalTraceCuts_pairwise_disjoint hH hk tr hW hne) hj hi

theorem originalTrace_survivor_iff_no_cut {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z)
    (hW : T.RootConeMaximizer H root W W) {b : V}
    (hb : b ∈ T.rootHeadCone root W) :
    b ∈ T.rootHeadCone root Z ↔ ∀ i,b ∉ T.originalTraceCutAt tr i := by
  constructor
  · intro hz i hi
    have hd := (T.originalTraceFullRemoved_partition hH hk tr hW).2.1
    exact Finset.disjoint_left.mp hd
      ((T.mem_originalTraceFullRemoved_iff tr).mpr ⟨i,hi⟩) hz
  · intro hn
    by_contra hz
    obtain ⟨i,hi,_hu⟩ := T.originalTrace_removed_unique hH hk tr hW hb hz
    exact hn i hi

theorem originalTrace_head_disposition {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z)
    (hW : T.RootConeMaximizer H root W W) {b : V}
    (hb : b ∈ T.rootHeadCone root W) :
    (b ∈ T.rootHeadCone root Z ∧ ∀ i,b ∉ T.originalTraceCutAt tr i) ∨
      (b ∉ T.rootHeadCone root Z ∧ ∃! i,b ∈ T.originalTraceCutAt tr i) := by
  classical
  by_cases hz : b ∈ T.rootHeadCone root Z
  · exact Or.inl ⟨hz,(T.originalTrace_survivor_iff_no_cut hH hk tr hW hb).mp hz⟩
  · exact Or.inr ⟨hz,T.originalTrace_removed_unique hH hk tr hW hb hz⟩

/-- A genuine assignment, constructed AFTER the partition proof. None
means final survival; some i is the unique actual physical removal cut. -/
noncomputable def originalTraceRemovalIndex {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z)
    (hW : T.RootConeMaximizer H root W W) (b : V)
    (hb : b ∈ T.rootHeadCone root W) : Option ℕ := by
  classical
  exact if hz : b ∈ T.rootHeadCone root Z then none else
    some (Classical.choose (T.originalTrace_removed_unique hH hk tr hW hb hz))

theorem originalTraceRemovalIndex_spec {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z)
    (hW : T.RootConeMaximizer H root W W) (b : V)
    (hb : b ∈ T.rootHeadCone root W) :
    (T.originalTraceRemovalIndex hH hk tr hW b hb=none ↔ b ∈ T.rootHeadCone root Z) ∧
      ∀ i,T.originalTraceRemovalIndex hH hk tr hW b hb=some i ↔
        b ∈ T.originalTraceCutAt tr i := by
  classical
  by_cases hz : b ∈ T.rootHeadCone root Z
  · have hn := (T.originalTrace_survivor_iff_no_cut hH hk tr hW hb).mp hz
    constructor
    · simp [originalTraceRemovalIndex,hz]
    · intro i
      simp [originalTraceRemovalIndex,hz,hn i]
  · have hspec := Classical.choose_spec (T.originalTrace_removed_unique hH hk tr hW hb hz)
    constructor
    · simp [originalTraceRemovalIndex,hz]
    · intro i
      simp only [originalTraceRemovalIndex,dif_neg hz,Option.some.injEq]
      constructor
      · intro he
        exact he ▸ hspec.1
      · intro hi
        exact (hspec.2 i hi).symm

/-- A physical removal INDEX always has a real original step record inside
the finite trace. Earlier actual child cones contain the head; later OLD
parent cones exclude it. This is not actual greedy insertion payment. -/
theorem originalTrace_removal_occurrence {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z b : V}
    (tr : T.OriginalSelectorTrace H root k W Z)
    (hW : T.RootConeMaximizer H root W W) {i : ℕ}
    (hi : b ∈ T.originalTraceCutAt tr i) :
    ∃ r,T.originalTraceStepAt tr i=some r ∧ i<T.originalTraceLength tr ∧
      b ∈ T.rootHeadCone root r.1 ∧ b ∉ T.rootHeadCone root r.2.1 ∧
      ∀ j q,T.originalTraceStepAt tr j=some q →
        (j < i → b ∈ T.rootHeadCone root q.2.1) ∧
        (i<j → b ∉ T.rootHeadCone root q.1) := by
  rw [T.originalTraceCutAt_record] at hi
  cases he : T.originalTraceStepAt tr i with
  | none => simp [he] at hi
  | some r =>
    rw [he] at hi
    obtain ⟨hp,hn⟩ := Finset.mem_sdiff.mp hi
    refine ⟨r,rfl,(T.originalTraceStepAt_exists_iff tr i).mp ⟨r,he⟩,hp,hn,?_⟩
    intro j q hq
    constructor
    · intro hji
      exact T.originalTraceStepAt_chronology hH hk tr hW j i q r hq he hji hp
    · intro hij hqp
      exact hn (T.originalTraceStepAt_chronology hH hk tr hW i j r q he hq hij hqp)

theorem originalStep_child_member_not_removed {H : Finset (V × V)} {root : V} {k : ℕ}
    {W U b : V} (d : T.OriginalSelectorStepData H root k W U)
    (hb : b ∈ T.rootHeadCone root U) : b ∉ T.originalStepFullCut d := by
  intro hd
  exact (Finset.mem_sdiff.mp hd).2 hb

/-- The former retired-band union is an INSIDE portion of the full
removed union, with a disjoint remainder, never an additional budget. -/
theorem originalTrace_retired_band_inside_full_cut {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z)
    (hW : T.RootConeMaximizer H root W W) :
    let B := T.originalTraceRetiredBands hH hk tr hW
    let D := T.originalTraceFullRemoved tr
    B ⊆ D ∧ B ∪ (D \ B)=D ∧ Disjoint B (D \ B) ∧
      D.card=B.card+(D \ B).card := by
  classical
  let B := T.originalTraceRetiredBands hH hk tr hW
  let D := T.originalTraceFullRemoved tr
  have he : D=T.rootHeadCone root W \ T.rootHeadCone root Z :=
    (T.originalTraceFullRemoved_partition hH hk tr hW).1
  have hsub : B ⊆ D := by
    rw [he]
    exact (T.originalTraceRetiredBands_facts hH hk tr hW).1
  have hu : B ∪ (D \ B)=D := by
    ext b
    constructor
    · intro hb
      rcases Finset.mem_union.mp hb with hb|hb
      · exact hsub hb
      · exact (Finset.mem_sdiff.mp hb).1
    · intro hb
      by_cases hB : b ∈ B
      · exact Finset.mem_union_left _ hB
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hb,hB⟩)
  have hd : Disjoint B (D \ B) := by
    apply Finset.disjoint_left.mpr
    intro b hb hx
    exact (Finset.mem_sdiff.mp hx).2 hb
  have hc := Finset.card_union_of_disjoint hd
  rw [hu] at hc
  exact ⟨hsub,hu,hd,hc⟩

theorem originalTrace_terminal_anchor_survives {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U Z : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U)
    (he : U=d.corridor.getVert d.index) (tail : T.OriginalSelectorTrace H root k U Z) :
    d.corridor.getVert d.index ∈ T.rootHeadCone root Z ∧
      d.corridor.getVert d.index ∉ T.originalTraceFullRemoved (.cons d tail) := by
  have hUZ := (T.originalTrace_after_anchor_child hH hk d he tail).1
  have haU : d.corridor.getVert d.index ∈ T.rootHeadCone root U := by
    simpa only [he] using T.rootCone_self_mem d.entryImportant
  have haZ : d.corridor.getVert d.index ∈ T.rootHeadCone root Z := by
    simpa only [hUZ] using haU
  refine ⟨haZ,?_⟩
  intro hd
  exact Finset.disjoint_left.mp
    (T.originalTraceFullRemoved_partition hH hk (.cons d tail) hW).2.1 hd haZ

end GreedyShortcuts.ChainDistance.Context
