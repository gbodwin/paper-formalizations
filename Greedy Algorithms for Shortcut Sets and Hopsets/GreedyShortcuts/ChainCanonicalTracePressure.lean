import GreedyShortcuts.ChainCanonicalEndpointPressure

/-! One H and one original ROOT only. Qualifying steps retain Delta >= 4.
Their actual endpoint family has physically distinct tails across the trace.
The cumulative quadratic mass is bounded by ONE actual candidate maximum
times the literal pooled LongCenters cardinality. This is a same-state
pressure inventory, not selected progress, stock, or cross-event payment. -/
namespace GreedyShortcuts.ChainDistance.Context
open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

noncomputable def originalQualifiedStepCenters {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U) : Finset V := by
  classical
  exact if 4 ≤ T.distance H root W-T.distance H root U then
    T.originalCanonicalLongCenters d else ∅

noncomputable def originalStepEndpointMass {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U) : ℕ :=
  Fintype.card (T.RootOwner root (d.corridor.getVert d.index))*
    (T.distance H root W-T.distance H root U-2)*
    (T.distance H root W-T.distance H root U-3)

noncomputable def originalTraceEndpointFamily {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) : Finset (V × V) :=
  match tr with
  | .nil _ => ∅
  | .cons d tail => (T.originalQualifiedStepCenters d).image (fun v => (v,W)) ∪
      originalTraceEndpointFamily tail

noncomputable def originalTraceEndpointCenterCount {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) : ℕ :=
  match tr with
  | .nil _ => 0
  | .cons d tail => (T.originalQualifiedStepCenters d).card+
      originalTraceEndpointCenterCount tail

noncomputable def originalTraceEndpointMass {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) : ℕ :=
  match tr with
  | .nil _ => 0
  | .cons d tail => T.originalStepEndpointMass d+originalTraceEndpointMass tail

theorem originalQualifiedStepCenters_subset {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U) :
    T.originalQualifiedStepCenters d ⊆ T.originalCanonicalLongCenters d ∧
      T.originalQualifiedStepCenters d ⊆ T.originalStepFullCut d \ {W} := by
  classical
  by_cases h : 4 ≤ T.distance H root W-T.distance H root U
  · simp only [originalQualifiedStepCenters,if_pos h]
    refine ⟨Finset.Subset.refl _,?_⟩
    intro v hv
    exact (Finset.mem_filter.mp hv).1
  · simp only [originalQualifiedStepCenters,if_neg h]
    exact ⟨Finset.empty_subset _,Finset.empty_subset _⟩

theorem originalTraceEndpointFamily_removed {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) :
    ∀ e ∈ T.originalTraceEndpointFamily tr,e.1 ∈ T.originalTraceFullRemoved tr := by
  classical
  induction tr with
  | nil W => simp [originalTraceEndpointFamily]
  | @cons W U Z d tail ih =>
    intro e he
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mp ((T.originalQualifiedStepCenters_subset d).2 hv)).1
    · exact Finset.mem_union_right _ (ih e he)

private theorem trace_endpoint_separated {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1 ≤ k) {W U Z : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U)
    (tail : T.OriginalSelectorTrace H root k U Z) :
    ∀ e ∈ (T.originalQualifiedStepCenters d).image (fun v => (v,W)),
      ∀ f ∈ T.originalTraceEndpointFamily tail,e.1 ≠ f.1 := by
  classical
  have hU := (T.originalSelectorStepData_facts hH hk hW d).1.2.2.1
  have hp := (T.originalTraceFullRemoved_partition hH hk tail hU).1
  intro e he f hf heq
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
  have hvCut := (Finset.mem_sdiff.mp ((T.originalQualifiedStepCenters_subset d).2 hv)).1
  have hfCut := T.originalTraceEndpointFamily_removed tail f hf
  rw [hp] at hfCut
  have heq' : v=f.1 := heq
  exact (Finset.mem_sdiff.mp hvCut).2 (heq'.symm ▸ (Finset.mem_sdiff.mp hfCut).1)

/-- Both candidate and physical-tail identities are once-owned in this trace.
No assertion is made about another branch or another greedy state. -/
theorem originalTraceEndpointFamily_injective_card {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1 ≤ k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    ∀ hW : T.RootConeMaximizer H root W W,
      Set.InjOn (fun e : V × V => e.1) (T.originalTraceEndpointFamily tr : Set (V × V)) ∧
      (T.originalTraceEndpointFamily tr).card=T.originalTraceEndpointCenterCount tr := by
  classical
  induction tr with
  | nil W => intro _;simp [originalTraceEndpointFamily,originalTraceEndpointCenterCount,Set.InjOn]
  | @cons W U Z d tail ih =>
    intro hW
    have hU := (T.originalSelectorStepData_facts hH hk hW d).1.2.2.1
    obtain ⟨hi,hc⟩ := ih hU
    let F := (T.originalQualifiedStepCenters d).image (fun v => (v,W))
    let G := T.originalTraceEndpointFamily tail
    have hsep := trace_endpoint_separated T hH hk hW d tail
    have hdis : Disjoint F G := Finset.disjoint_left.mpr (fun e he hg => hsep e he e hg rfl)
    have hF : Set.InjOn (fun e : V × V => e.1) (F : Set (V × V)) := by
      intro e he f hf heq
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hf
      exact Prod.ext heq rfl
    refine ⟨?_,?_⟩
    · intro e he f hf heq
      rcases Finset.mem_union.mp he with he|he <;>
        rcases Finset.mem_union.mp hf with hf|hf
      · exact hF he hf heq
      · exact (hsep e he f hf heq).elim
      · exact (hsep f hf e he heq.symm).elim
      · exact hi he hf heq
    · have hcF : F.card=(T.originalQualifiedStepCenters d).card := by
        apply Finset.card_image_iff.mpr
        intro v _ w _ heq
        exact (Prod.mk.inj heq).1
      change (F ∪ G).card=(T.originalQualifiedStepCenters d).card+T.originalTraceEndpointCenterCount tail
      rw [Finset.card_union_of_disjoint hdis,hcF,hc]

theorem originalQualifiedStepCenters_target_debit {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1 ≤ k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U) :
    (T.originalQualifiedStepCenters d).card+1 ≤ (T.originalStepFullCut d).card := by
  classical
  have hWC := (T.originalCanonicalPhysicalExterior_W_debit hH hk hW d d.minOwner).1
  have hWCut := ((T.mem_originalCanonicalPhysicalExterior hH d d.minOwner).mp hWC).1
  have hsub := (T.originalQualifiedStepCenters_subset d).2
  have hc := Finset.card_le_card hsub
  have he := Finset.card_sdiff_add_card_inter (T.originalStepFullCut d) {W}
  have hw : ({W} : Finset V) ⊆ T.originalStepFullCut d := by
    intro v hv;simpa only [Finset.mem_singleton.mp hv] using hWCut
  rw [Finset.inter_eq_right.mpr hw,Finset.card_singleton] at he
  omega

/-- Each step's excluded target is charged once alongside its actual long
centers, inside the disjoint FULL cuts. This is static capacity, not progress. -/
theorem originalTraceEndpoint_pool_capacity {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1 ≤ k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z)
    (hW : T.RootConeMaximizer H root W W) :
    (T.originalTraceEndpointFamily tr).card+T.originalTraceLength tr+
        (T.rootHeadCone root Z).card ≤ (T.rootHeadCone root W).card := by
  classical
  have aux : ∀ {A B : V} (q : T.OriginalSelectorTrace H root k A B),
      T.RootConeMaximizer H root A A →
      T.originalTraceEndpointCenterCount q+T.originalTraceLength q ≤ T.originalTraceFullCutCardSum q := by
    intro A B q
    induction q with
    | nil A => intro _;simp [originalTraceEndpointCenterCount,originalTraceLength,originalTraceFullCutCardSum]
    | @cons A U B d tail ih =>
      intro hA
      have hU := (T.originalSelectorStepData_facts hH hk hA d).1.2.2.1
      have ht := ih hU
      have hc := T.originalQualifiedStepCenters_target_debit hH hk hA d
      change (T.originalQualifiedStepCenters d).card+T.originalTraceEndpointCenterCount tail+
        (T.originalTraceLength tail+1) ≤ (T.originalStepFullCut d).card+T.originalTraceFullCutCardSum tail
      omega
  have hcount := (T.originalTraceEndpointFamily_injective_card hH hk tr hW).2
  have hc := aux tr hW
  obtain ⟨_he,_hd,_hu,hcard,hsum⟩ := T.originalTraceFullRemoved_partition hH hk tr hW
  omega

theorem originalTraceEndpointFamily_bank {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1 ≤ k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    ∀ hW : T.RootConeMaximizer H root W W,∀ e ∈ T.originalTraceEndpointFamily tr,
      e ∈ candidates T.G ∧ e ∉ H ∧ 1 ≤ T.potential H-T.potential (insert e H) := by
  classical
  induction tr with
  | nil W => intro hW e he;simp [originalTraceEndpointFamily] at he
  | @cons W U Z d tail ih =>
    intro hW e he
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hl,hf,hp,_⟩ := T.originalCanonical_long_endpoint_bank hH hW d
        ((T.originalQualifiedStepCenters_subset d).1 hv)
      exact ⟨hl,hf,hp⟩
    · exact ih (T.originalSelectorStepData_facts hH hk hW d).1.2.2.1 e he

private theorem step_endpoint_inventory {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1 ≤ k) {W U : V}
    (hW : T.RootConeMaximizer H root W W) (d : T.OriginalSelectorStepData H root k W U) :
    T.originalStepEndpointMass d ≤ 2*∑ e ∈
      (T.originalQualifiedStepCenters d).image (fun v => (v,W)),
        (T.potential H-T.potential (insert e H)) := by
  classical
  by_cases h : 4 ≤ T.distance H root W-T.distance H root U
  · simp only [originalQualifiedStepCenters,if_pos h]
    have he : (∑ e ∈ (T.originalCanonicalLongCenters d).image (fun v => (v,W)),
        (T.potential H-T.potential (insert e H)))=
        ∑ v ∈ T.originalCanonicalLongCenters d,(T.potential H-T.potential (insert (v,W) H)) := by
      apply Finset.sum_image
      intro v _ w _ heq
      exact (Prod.mk.inj heq).1
    rw [he]
    exact T.originalCanonical_triangular_endpoint_inventory hH hk hW d
  · have hz : T.distance H root W-T.distance H root U-3=0 := by omega
    simp [originalQualifiedStepCenters,h,originalStepEndpointMass,hz]

/-- Actual same-state alternatives are inventoried with their exact disjoint
family membership. Their sum is used ONLY to select one actual maximum. -/
theorem originalTraceEndpoint_mass_inventory {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1 ≤ k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    ∀ hW : T.RootConeMaximizer H root W W,
      T.originalTraceEndpointMass tr ≤ 2*∑ e ∈ T.originalTraceEndpointFamily tr,
        (T.potential H-T.potential (insert e H)) := by
  classical
  induction tr with
  | nil W => intro _;simp [originalTraceEndpointMass,originalTraceEndpointFamily]
  | @cons W U Z d tail ih =>
    intro hW
    have ht := ih (T.originalSelectorStepData_facts hH hk hW d).1.2.2.1
    have hs := step_endpoint_inventory T hH hk hW d
    have hsep := trace_endpoint_separated T hH hk hW d tail
    have hdis : Disjoint ((T.originalQualifiedStepCenters d).image (fun v => (v,W)))
        (T.originalTraceEndpointFamily tail) :=
      Finset.disjoint_left.mpr (fun e he hf => hsep e he e hf rfl)
    change T.originalStepEndpointMass d+T.originalTraceEndpointMass tail ≤
      2*∑ e ∈ (T.originalQualifiedStepCenters d).image (fun v => (v,W)) ∪
        T.originalTraceEndpointFamily tail,(T.potential H-T.potential (insert e H))
    rw [Finset.sum_union hdis,Nat.mul_add]
    exact Nat.add_le_add hs ht

private theorem step_endpoint_rank_debit {H : Finset (V × V)}
    {root : V} {k : ℕ} {W U : V} (d : T.OriginalSelectorStepData H root k W U) :
    2*(T.distance H root W-T.distance H root U) ≤ 6+T.originalStepEndpointMass d := by
  have hc : 1 ≤ Fintype.card (T.RootOwner root (d.corridor.getVert d.index)) := by
    letI : Nonempty (T.RootOwner root (d.corridor.getVert d.index)) := ⟨d.minOwner⟩
    exact Nat.succ_le_of_lt Fintype.card_pos
  by_cases h : 4 ≤ T.distance H root W-T.distance H root U
  · have hb : 2*(T.distance H root W-T.distance H root U-3) ≤
        (T.distance H root W-T.distance H root U-2)*
        (T.distance H root W-T.distance H root U-3) :=
      Nat.mul_le_mul_right _ (by omega)
    have hm := Nat.mul_le_mul_right
      ((T.distance H root W-T.distance H root U-2)*
        (T.distance H root W-T.distance H root U-3)) hc
    simp only [Nat.one_mul,← Nat.mul_assoc] at hm
    change _ ≤ T.originalStepEndpointMass d at hm
    omega
  · omega

theorem originalTraceEndpoint_rank_debit {H : Finset (V × V)}
    {root : V} {k : ℕ} {W Z : V} (tr : T.OriginalSelectorTrace H root k W Z) :
    2*T.originalTraceDrop tr ≤ 6*T.originalTraceLength tr+T.originalTraceEndpointMass tr := by
  induction tr with
  | nil W => simp [originalTraceDrop,originalTraceLength,originalTraceEndpointMass]
  | @cons W U Z d tail ih =>
    have hs := step_endpoint_rank_debit T d
    change 2*((T.distance H root W-T.distance H root U)+T.originalTraceDrop tail) ≤
      6*(T.originalTraceLength tail+1)+(T.originalStepEndpointMass d+T.originalTraceEndpointMass tail)
    omega

/-- Unconditional alternative: zero mass leaves its explicit small-drop debit;
otherwise ONE fresh legal maximum controls the cumulative mass, with the
literal once-owned union-cardinality denominator and terminal cone retained.
All quantities refer to one H/ROOT trace, never greedy insertion time. -/
theorem originalTraceEndpoint_pressure_alternative {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1 ≤ k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z)
    (hW : T.RootConeMaximizer H root W W) :
    (T.originalTraceEndpointMass tr=0 ∧ T.originalTraceDrop tr ≤ 3*T.originalTraceLength tr) ∨
    ∃ e ∈ T.originalTraceEndpointFamily tr,
      e ∈ candidates T.G ∧ e ∉ H ∧ 1 ≤ T.potential H-T.potential (insert e H) ∧
      (∀ f ∈ T.originalTraceEndpointFamily tr,
        T.potential H-T.potential (insert f H) ≤ T.potential H-T.potential (insert e H)) ∧
      T.originalTraceEndpointMass tr ≤ 2*(T.originalTraceEndpointFamily tr).card*
        (T.potential H-T.potential (insert e H)) ∧
      T.originalTraceDrop tr ≤ 3*T.originalTraceLength tr+
        (T.originalTraceEndpointFamily tr).card*(T.potential H-T.potential (insert e H)) ∧
      (T.originalTraceEndpointFamily tr).card=T.originalTraceEndpointCenterCount tr ∧
      (T.originalTraceEndpointFamily tr).card+T.originalTraceLength tr+
        (T.rootHeadCone root Z).card ≤ (T.rootHeadCone root W).card := by
  classical
  have hr := T.originalTraceEndpoint_rank_debit tr
  by_cases hz : T.originalTraceEndpointMass tr=0
  · exact Or.inl ⟨hz,by omega⟩
  · have hi := T.originalTraceEndpoint_mass_inventory hH hk tr hW
    have hn : (T.originalTraceEndpointFamily tr).Nonempty := by
      by_contra he
      have hempty := Finset.not_nonempty_iff_eq_empty.mp he
      rw [hempty,Finset.sum_empty,Nat.mul_zero] at hi
      omega
    obtain ⟨e,he,hmax⟩ := Finset.exists_max_image (T.originalTraceEndpointFamily tr)
      (fun f => T.potential H-T.potential (insert f H)) hn
    obtain ⟨hl,hf,hp⟩ := T.originalTraceEndpointFamily_bank hH hk tr hW e he
    have hs : (∑ f ∈ T.originalTraceEndpointFamily tr,
        (T.potential H-T.potential (insert f H))) ≤
        (T.originalTraceEndpointFamily tr).card*(T.potential H-T.potential (insert e H)) := by
      calc
        _ ≤ ∑ _f ∈ T.originalTraceEndpointFamily tr,
            (T.potential H-T.potential (insert e H)) := Finset.sum_le_sum (fun f hf => hmax f hf)
        _ = _ := by simp
    have hmass := hi.trans (Nat.mul_le_mul_left 2 hs)
    have hmass' : T.originalTraceEndpointMass tr ≤ 2*(T.originalTraceEndpointFamily tr).card*
        (T.potential H-T.potential (insert e H)) := by simpa only [Nat.mul_assoc] using hmass
    exact Or.inr ⟨e,he,hl,hf,hp,hmax,hmass',by omega,
      (T.originalTraceEndpointFamily_injective_card hH hk tr hW).2,
      T.originalTraceEndpoint_pool_capacity hH hk tr hW⟩

end GreedyShortcuts.ChainDistance.Context
