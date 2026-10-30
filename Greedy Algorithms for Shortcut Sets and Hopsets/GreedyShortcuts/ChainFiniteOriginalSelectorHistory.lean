import GreedyShortcuts.ChainOriginalMinimumTailStep

/-! SOURCE ONLY, UNCOMPILED. Actual finite H-fixed normalized selector
histories. Raw records store permitted ORIGINAL choices and the governing
active test, NOT child invariants, cone decrease, owners or forcing. All
geometry, termination and telescoping below are derived from native steps. -/
namespace GreedyShortcuts.ChainDistance.Context

open Finset SimpleGraph DirectedPaths ChainFirst ShortcutWalk
open LinearDistancePreservers.ConsistentTiebreaking
universe u v
variable {V : Type u} {I : Type v} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable (T : ChainDistance.Context V I)

/-- Only actual choice INPUTS: active test, fixed ROOT minimum/corridor
entry, original own-minimum/LAST families and permitted min/max/mode ties.
No normalization, child cone/rank/decrease, stopping-output or owner field. -/
structure OriginalSelectorStepData (H : Finset (V × V)) (root : V) (k : ℕ)
    (W U : V) where
  active : 16*k≤T.distance H root W
  corridor : DWalk root W
  corridorAllowed : Allowed (T.graph H root) corridor
  corridorMinimum : T.count corridor=T.distance H root W
  index : ℕ
  indexLe : index≤corridor.length
  entryCount : T.count (corridor.take index)=k
  entryImportant : (root,corridor.getVert index) ∈ T.important
  owners : T.OwnerMinimumFamily H root (corridor.getVert index) W
  tails : ∀ x : T.RootOwner root (corridor.getVert index),
    T.OwnerLastRootTail H root x.val W (owners x).val
  minOwner : T.RootOwner root (corridor.getVert index)
  minTail : ∀ y : T.RootOwner root (corridor.getVert index),
    (tails minOwner).tau≤(tails y).tau
  maxOwner : V
  ownerMaximum : T.RootConeMaximizer H root (corridor.getVert index) maxOwner
  childChoice : T.OriginalMinimumTailChoice owners tails minOwner maxOwner U

/-- Raw permitted choice data yield all previous one-step outputs; none
of those outputs was assumed in the record. SAME-source prices remain ROOT. -/
theorem originalSelectorStepData_facts {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    (d : T.OriginalSelectorStepData H root k W U) :
    T.OriginalMinimumTailStepFacts k (16*k) d.owners d.tails d.minOwner d.maxOwner U ∧
      T.OriginalMinimumTailBranchFacts k (16*k) d.owners d.tails d.minOwner d.maxOwner U := by
  have hrank : T.distance H root (d.corridor.getVert d.index)=k :=
    (T.root_minimum_prefix_price hH d.corridor d.corridorAllowed
      d.corridorMinimum d.index).symm.trans d.entryCount
  have hreach : Reachable T.G (d.corridor.getVert d.index) W :=
    (reachable_augment_iff T.G _ (T.augmentation_legal hH) _ _).mp
      ⟨d.corridor.drop d.index,allowed_mono (fun _ _ h => h.1)
        (allowed_subwalk d.corridorAllowed (d.corridor.isSubwalk_drop d.index))⟩
  have hactive := d.active
  have hne : d.corridor.getVert d.index≠W := by
    intro he
    rw [he] at hrank
    omega
  exact T.originalMinimumTailChoice_facts hH hW d.entryImportant hreach hne
    hrank (by omega) d.owners d.tails d.minOwner d.maxOwner U
    d.minTail d.ownerMaximum d.childChoice

/-- Real attainment constructs the actual records. Existing records can
be used directly; this theorem is not a favorable retie instruction. -/
theorem exists_originalSelectorStepData {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W : V}
    (hW : T.RootConeMaximizer H root W W) (hactive : 16*k≤T.distance H root W) :
    Nonempty (Σ U : V,T.OriginalSelectorStepData H root k W U) := by
  classical
  have hip := (T.mem_rootHeadCone_iff.mp hW.1).1
  obtain ⟨P,hP,hPmin⟩ := T.distance_spec H (T.important_spec hip).1
  obtain ⟨i,hilt,hcount,ha,_harank,_haW,_hne,hfamilies,hselect⟩ :=
    T.actual_root_corridor_minimum_tail_step hH hW P hP hPmin hk (by omega) hactive
  obtain ⟨⟨Q,F⟩⟩ := hfamilies
  obtain ⟨x,Vmax,U,hmin,hmax,hchoice,_hfacts,_hbranch⟩ := hselect Q F
  exact ⟨⟨U,{
    active := hactive, corridor := P, corridorAllowed := hP, corridorMinimum := hPmin,
    index := i, indexLe := Nat.le_of_lt hilt, entryCount := hcount, entryImportant := ha,
    owners := Q, tails := F, minOwner := x, minTail := hmin,
    maxOwner := Vmax, ownerMaximum := hmax, childChoice := hchoice }⟩⟩

/-- Finite actual step prefixes. Only raw permitted choice data link
successive endpoints. A COMPLETED history additionally has stopped final
rank, proved below; nil also represents an already fixed partial prefix. -/
inductive OriginalSelectorTrace (C : ChainDistance.Context V I)
    (H : Finset (V × V)) (root : V) (k : ℕ) : V → V → Type (max u v)
  | nil (W : V) : OriginalSelectorTrace C H root k W W
  | cons {W U Z : V} (d : C.OriginalSelectorStepData H root k W U)
      (tail : OriginalSelectorTrace C H root k U Z) : OriginalSelectorTrace C H root k W Z

def originalTraceLength {H : Finset (V × V)} {root : V} {k : ℕ} {W Z : V} :
    T.OriginalSelectorTrace H root k W Z → ℕ
  | .nil _ => 0
  | .cons _ tail => originalTraceLength tail+1

def originalStepChild {H : Finset (V × V)} {root : V} {k : ℕ} {W U : V}
    (_d : T.OriginalSelectorStepData H root k W U) : V := U

/-- Sum of the ACTUAL consecutive native rank drops, not paid progress. -/
noncomputable def originalTraceDrop {H : Finset (V × V)} {root : V} {k : ℕ} {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) : ℕ :=
  match tr with
  | .nil _ => 0
  | .cons d tail =>
      (T.distance H root W-T.distance H root (T.originalStepChild d))+originalTraceDrop tail

/-- Derived output predicate over ALL actual steps, never constructor
premises. It retains the precise old-row drop/guard/relay/terminal witnesses. -/
def originalTraceLinked {H : Finset (V × V)} {root : V} {k : ℕ} {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) : Prop :=
  match tr with
  | .nil _ => True
  | .cons d tail =>
      T.RootConeMaximizer H root W W ∧
      T.OriginalMinimumTailStepFacts k (16*k) d.owners d.tails d.minOwner d.maxOwner
        (T.originalStepChild d) ∧
      T.OriginalMinimumTailBranchFacts k (16*k) d.owners d.tails d.minOwner d.maxOwner
        (T.originalStepChild d) ∧
      originalTraceLinked tail

theorem originalTrace_linked {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    T.RootConeMaximizer H root W W → T.originalTraceLinked tr := by
  induction tr with
  | nil W => intro _;trivial
  | @cons W U Z d tail ih =>
    intro hW
    obtain ⟨hf,hb⟩ := T.originalSelectorStepData_facts hH hk hW d
    exact ⟨hW,hf,hb,ih hf.2.2.1⟩

/-- Final endpoint bounds and exact finite folds, valid for EVERY permitted
trace. The floor at an inactive start is conditional, not invented. -/
theorem originalTrace_bounds {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) :
    T.RootConeMaximizer H root W W →
      T.RootConeMaximizer H root Z Z ∧ Reachable T.G Z W ∧
      T.rootHeadCone root Z ⊆ T.rootHeadCone root W ∧
      T.distance H root Z≤T.distance H root W ∧
      (k≤T.distance H root W → k≤T.distance H root Z) ∧
      (0<T.originalTraceLength tr → k≤T.distance H root Z) ∧
      (T.rootHeadCone root Z).card+T.originalTraceLength tr≤(T.rootHeadCone root W).card ∧
      T.originalTraceDrop tr+T.distance H root Z=T.distance H root W := by
  induction tr with
  | nil W =>
    intro hW
    refine ⟨hW,reachable_refl T.G W,Finset.Subset.refl _,le_rfl,fun h => h,?_,?_,?_⟩
    · intro hn
      simp [originalTraceLength] at hn
    · simp [originalTraceLength]
    · simp [originalTraceDrop]
  | @cons W U Z d tail ih =>
    intro hW
    obtain ⟨hf,_hb⟩ := T.originalSelectorStepData_facts hH hk hW d
    obtain ⟨_hip,hUW,hU,hsub,_hproper,hcard,hfloor,hupper,_hD,_htau,_hrows,_hstop⟩ := hf
    obtain ⟨hZ,hZU,hsubZ,hupperZ,hfloorZ,_hposZ,hcardZ,hsumZ⟩ := ih hU
    have hfinal : k≤T.distance H root Z := hfloorZ hfloor
    have hlength : (T.rootHeadCone root Z).card+
        T.originalTraceLength (.cons d tail)≤(T.rootHeadCone root W).card := by
      change (T.rootHeadCone root Z).card+(T.originalTraceLength tail+1)≤
        (T.rootHeadCone root W).card
      omega
    have hsum : T.originalTraceDrop (.cons d tail)+T.distance H root Z=
        T.distance H root W := by
      change (T.distance H root W-T.distance H root U)+T.originalTraceDrop tail+
        T.distance H root Z=T.distance H root W
      omega
    exact ⟨hZ,reachable_trans hZU hUW,Finset.Subset.trans hsubZ hsub,
      hupperZ.trans hupper,fun _ => hfinal,fun _ => hfinal,hlength,hsum⟩

theorem originalTrace_zero_length {H : Finset (V × V)} {root : V} {k : ℕ} {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) (hz : T.originalTraceLength tr=0) : W=Z := by
  cases tr with
  | nil => rfl
  | cons d tail => simp [originalTraceLength] at hz

/-- The real q-test forbids continuation from ANY already stopped endpoint,
including a relay child equal to its old anchor. No next band is postulated. -/
theorem originalTrace_from_stopped {H : Finset (V × V)} {root : V} {k : ℕ} {W Z : V}
    (hstop : T.distance H root W<16*k) (tr : T.OriginalSelectorTrace H root k W Z) :
    W=Z ∧ T.originalTraceLength tr=0 := by
  cases tr with
  | nil => exact ⟨rfl,rfl⟩
  | cons d tail => have ha := d.active;omega

/-- Any actual child equal to its literal corridor anchor is below q; the
tail is empty. Relay's U=a exception is retained, not silently retired. -/
theorem originalTrace_after_anchor_child {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U Z : V}
    (d : T.OriginalSelectorStepData H root k W U)
    (he : U=d.corridor.getVert d.index) (tail : T.OriginalSelectorTrace H root k U Z) :
    U=Z ∧ T.originalTraceLength tail=0 := by
  have hrank : T.distance H root (d.corridor.getVert d.index)=k :=
    (T.root_minimum_prefix_price hH d.corridor d.corridorAllowed
      d.corridorMinimum d.index).symm.trans d.entryCount
  have hstop : T.distance H root U<16*k := by rw [he,hrank];omega
  exact T.originalTrace_from_stopped hstop tail

/-- A policy fixes only genuine permitted choice data at normalized active
endpoints. Existence is constructed, not a progress/decrease axiom. -/
def OriginalSelectorPolicy (H : Finset (V × V)) (root : V) (k : ℕ) :=
  ∀ W : V,T.RootConeMaximizer H root W W → 16*k≤T.distance H root W →
    Σ U : V,T.OriginalSelectorStepData H root k W U

noncomputable def originalSelectorPolicy {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) (root : V) {k : ℕ} (hk : 1≤k) :
    T.OriginalSelectorPolicy H root k :=
  fun _ hW hactive => Classical.choice (T.exists_originalSelectorStepData hH hk hW hactive)

def originalStepPackage {H : Finset (V × V)} {root : V} {k : ℕ} {W U : V}
    (d : T.OriginalSelectorStepData H root k W U) :
    Σ u : V,T.OriginalSelectorStepData H root k W u := ⟨U,d⟩

/-- Literal adherence to any already fixed permitted policy is a PROVED
output. No normalization/decrease conclusions enter history constructors. -/
def originalTraceFollows {H : Finset (V × V)} {root : V} {k : ℕ}
    (policy : T.OriginalSelectorPolicy H root k) {W Z : V}
    (tr : T.OriginalSelectorTrace H root k W Z) : Prop :=
  match tr with
  | .nil _ => True
  | .cons d tail =>
      (∃ hW hactive,policy W hW hactive=T.originalStepPackage d) ∧
      originalTraceFollows policy tail

/-- Termination for EVERY genuine fixed policy: induction measure is actual
cone cardinality. No rank-drop positivity, owner mass or gain is assumed. -/
theorem exists_finite_original_history_with_policy {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k)
    (policy : T.OriginalSelectorPolicy H root k) {W : V}
    (hW : T.RootConeMaximizer H root W W) :
    ∃ Z,∃ tr : T.OriginalSelectorTrace H root k W Z,
      T.distance H root Z<16*k ∧ T.originalTraceFollows policy tr := by
  classical
  have aux : ∀ n,∀ W : V,(T.rootHeadCone root W).card=n →
      T.RootConeMaximizer H root W W →
      ∃ Z,∃ tr : T.OriginalSelectorTrace H root k W Z,
        T.distance H root Z<16*k ∧ T.originalTraceFollows policy tr := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W hn hW
      by_cases hactive : 16*k≤T.distance H root W
      · cases hpolicy : policy W hW hactive with
        | mk U d =>
          obtain ⟨hf,_hb⟩ := T.originalSelectorStepData_facts hH hk hW d
          have hU := hf.2.2.1
          have hcard := hf.2.2.2.2.2.1
          obtain ⟨Z,tail,hstop,hfollow⟩ := ih (T.rootHeadCone root U).card (by omega) U rfl hU
          refine ⟨Z,.cons d tail,hstop,?_,hfollow⟩
          exact ⟨hW,hactive,hpolicy⟩
      · exact ⟨W,.nil W,by omega,trivial⟩
  exact aux (T.rootHeadCone root W).card W rfl hW

theorem exists_finite_original_history {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W : V}
    (hW : T.RootConeMaximizer H root W W) :
    ∃ Z,∃ tr : T.OriginalSelectorTrace H root k W Z,T.distance H root Z<16*k := by
  obtain ⟨Z,tr,hstop,_hfollows⟩ := T.exists_finite_original_history_with_policy hH hk
    (T.originalSelectorPolicy hH root hk) hW
  exact ⟨Z,tr,hstop⟩

/-- Append preserves EVERY already fixed prefix record literally. -/
def originalTraceAppend {H : Finset (V × V)} {root : V} {k : ℕ} {W U Z : V}
    («prefix» : T.OriginalSelectorTrace H root k W U)
    (tail : T.OriginalSelectorTrace H root k U Z) : T.OriginalSelectorTrace H root k W Z :=
  match «prefix» with
  | .nil _ => tail
  | .cons d rest => .cons d (originalTraceAppend rest tail)

theorem complete_fixed_original_prefix {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W U : V}
    (hW : T.RootConeMaximizer H root W W)
    («prefix» : T.OriginalSelectorTrace H root k W U) :
    ∃ Z,∃ tail : T.OriginalSelectorTrace H root k U Z,
      T.distance H root Z<16*k ∧ T.originalTraceLinked (T.originalTraceAppend «prefix» tail) := by
  have hU := (T.originalTrace_bounds hH hk «prefix» hW).1
  obtain ⟨Z,tail,hstop⟩ := T.exists_finite_original_history hH hk hU
  exact ⟨Z,tail,hstop,T.originalTrace_linked hH hk (T.originalTraceAppend «prefix» tail) hW⟩

/-- Exact completed ACTIVE-start range and aggregate rank telescope. An
inactive start instead has the literal empty trace and its original rank. -/
theorem original_active_history_terminal_bounds {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k) {W Z : V}
    (hW : T.RootConeMaximizer H root W W) (hactive : 16*k≤T.distance H root W)
    (tr : T.OriginalSelectorTrace H root k W Z) (hstop : T.distance H root Z<16*k) :
    0<T.originalTraceLength tr ∧ k≤T.distance H root Z ∧ T.distance H root Z<16*k ∧
      T.originalTraceDrop tr=T.distance H root W-T.distance H root Z ∧
      T.distance H root W-16*k+1≤T.originalTraceDrop tr := by
  obtain ⟨_hZ,_hZW,_hsub,_hupper,_hfloor,hpos,_hcard,hsum⟩ :=
    T.originalTrace_bounds hH hk tr hW
  have hlength : 0<T.originalTraceLength tr := by
    by_contra hn
    have hz : T.originalTraceLength tr=0 := by omega
    have he := T.originalTrace_zero_length tr hz
    rw [← he] at hstop
    omega
  exact ⟨hlength,hpos hlength,hstop,by omega,by omega⟩

/-- Integrated actual ACTIVE-start history for ANY already fixed permitted
policy. Every claimed final/history bound belongs to THIS constructed
trace; no favorable policy, scalar profile or supplied history is assumed. -/
theorem exists_active_original_history_bounds {H : Finset (V × V)}
    (hH : H ⊆ candidates T.G) {root : V} {k : ℕ} (hk : 1≤k)
    (policy : T.OriginalSelectorPolicy H root k) {W : V}
    (hW : T.RootConeMaximizer H root W W) (hactive : 16*k≤T.distance H root W) :
    ∃ Z,∃ tr : T.OriginalSelectorTrace H root k W Z,
      T.originalTraceFollows policy tr ∧ T.originalTraceLinked tr ∧
      T.RootConeMaximizer H root Z Z ∧ Reachable T.G Z W ∧
      T.rootHeadCone root Z ⊆ T.rootHeadCone root W ∧
      k≤T.distance H root Z ∧ T.distance H root Z<16*k ∧
      T.distance H root Z≤T.distance H root W ∧ 0<T.originalTraceLength tr ∧
      (T.rootHeadCone root Z).card+T.originalTraceLength tr≤(T.rootHeadCone root W).card ∧
      T.originalTraceDrop tr+T.distance H root Z=T.distance H root W ∧
      T.originalTraceDrop tr=T.distance H root W-T.distance H root Z ∧
      T.distance H root W-16*k+1≤T.originalTraceDrop tr := by
  obtain ⟨Z,tr,hstop,hfollow⟩ := T.exists_finite_original_history_with_policy hH hk policy hW
  obtain ⟨hZ,hZW,hsub,hupper,_hfloor,_hpos,hcard,hsum⟩ := T.originalTrace_bounds hH hk tr hW
  obtain ⟨hlen,hfloor,hstop',hdrop,hlower⟩ :=
    T.original_active_history_terminal_bounds hH hk hW hactive tr hstop
  exact ⟨Z,tr,hfollow,T.originalTrace_linked hH hk tr hW,hZ,hZW,hsub,
    hfloor,hstop',hupper,hlen,hcard,hsum,hdrop,hlower⟩

end GreedyShortcuts.ChainDistance.Context
