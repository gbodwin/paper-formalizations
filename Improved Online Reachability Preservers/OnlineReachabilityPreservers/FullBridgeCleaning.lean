import OnlineReachabilityPreservers.ComponentSplitCleaning
import OnlineReachabilityPreservers.LocalFrozenLowMass
import OnlineReachabilityPreservers.OfflineBridgeConverse

/-! Frozen cleaning at all bridge sizes after the common-order deletion. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

variable {n p : ℕ}

/-- A common order forbids returns in the precedence graph. -/
theorem noShortPrecedenceCycle_of_increasing_order (paths : Fin p → List (Fin n))
    (rank : Fin n → Fin n) (ordered : ∀ i, ((paths i).map rank).Pairwise (· < ·)) (cutoff : ℕ) :
    NoShortPrecedenceCycle paths cutoff := by
  classical
  have increases {x y : Fin n} (edge : Edge (pathPrecedenceGraph paths) x y) : rank x < rank y := by
    obtain ⟨i,step⟩ := (mem_filter.mp edge).2
    have raw := List.pairwise_map.mp (ordered i)
    have early := List.idxOf_lt_length_of_mem step.1
    have late := List.idxOf_lt_length_of_mem step.2.1
    have comparison := List.pairwise_iff_getElem.mp raw _ _ early late step.2.2
    rwa [List.getElem_idxOf early,List.getElem_idxOf late] at comparison
  have nondecreasing {x y : Fin n} (path : Reach (pathPrecedenceGraph paths) x y) : rank x ≤ rank y := by
    induction path with
    | refl => exact le_rfl
    | tail _ edge previous => exact previous.trans (increases edge).le
  intro x y forward backward
  exact (increases forward).not_ge (nondecreasing (reachIn_sound backward))

/-- For input excluding every full bridge, the original four average caps
can be attained while still excluding bridges of every size. The larger
mass branch needs at least twenty-four incidences per original vertex. -/
theorem regularization_list_frozen_full_all_of_mass (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : ∀ d, IsEmpty (Bridge (Before paths) d))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (range : let M := ∑ i, (paths i).length; M ≤ 8*max n p ∨ 24*n ≤ M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before clean) d)) ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let cutoff := max 2 p
  obtain ⟨rank,kept,sub,ordered,_,_,lost⟩ := fullBridgeFree_increasing_subsequences paths simple free
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have keptFree : BridgeFree (Before kept) cutoff := by
    intro d _
    exact ⟨fun b => (free d).false (b.mapPaths id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (simple i) (sub i) step))⟩
  have permitted : BridgeFree (Before (listRegularizedPaths kept (4*M/n) (4*M/p))) cutoff :=
    listRegularizedPaths_fullFree_of_noShortPrecedenceCycle kept keptSimple keptFree
      (noShortPrecedenceCycle_of_increasing_order kept rank ordered (cutoff-2)) _ _
  have inputHalf : HalfBridgeFree (Before paths) cutoff := fun d _ b _ => (free d).false b
  have enough (above : 8*max n p < M) : 7*M ≤ 8*(∑ i, (kept i).length) := by
    have mass : 24*n ≤ M := range.resolve_left above.not_ge
    change M ≤ _ at lost
    omega
  obtain ⟨n',vBudget,p',pBudget,clean,cleanSimple,cleanFree,retained,upper,caps⟩ :=
    regularization_list_frozen_of_seven_eighths_mass (half := false) paths kept simple keptSimple inputHalf
      (le_max_left _ _) hn hp dense long (sum_le_sum fun i _ => (sub i).length_le) enough permitted
  refine ⟨n',vBudget,p',pBudget,clean,cleanSimple,?_,retained,upper,caps⟩
  intro d
  refine ⟨fun b => (cleanFree ?_).false b⟩
  have count : d+2 ≤ p' := by simpa only [Fintype.card_fin] using SourceAudit.bridge_path_count_le b
  exact count.trans (pBudget.trans (le_max_right _ _))

private theorem expanded_support_ratio {M q K : ℕ} (positive : 0 < q) (large : 8*q ≤ M) :
    (31*M)*(q+K/(4*M/q)) ≤ (31*M+8*K)*q := by
  let width := 4*M/q
  have floor := Nat.lt_mul_div_succ (4*M) positive
  change 4*M < q*(width+1) at floor
  rw [Nat.mul_succ] at floor
  have covers : 31*M ≤ 8*(q*width) := by omega
  have extra : (31*M)*(K/width) ≤ 8*K*q := calc
    _ ≤ (8*(q*width))*(K/width) := Nat.mul_le_mul_right _ covers
    _ = (8*q)*((K/width)*width) := by ring
    _ ≤ (8*q)*K := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    _ = _ := by ring
  change (31*M)*(q+K/width) ≤ _
  rw [Nat.mul_add,Nat.add_mul]
  exact Nat.add_le_add_left extra _

private theorem three_quarters_frozen_ratio {M K : ℕ} (upper : K ≤ M) (lower : 3*M ≤ 4*K) :
    ((31*M+8*K)*(31*M+8*K))*(40+2)*M ≤ 2*((31*M)*(31*M))*40*K := by
  have compare : 3*M*(31*M+8*K)^2 ≤ 4*K*(37*M)^2 := by
    have first : 0 ≤ (4*(K:ℤ)-3*(M:ℤ)) := sub_nonneg.mpr (by exact_mod_cast lower)
    have last : 0 ≤ (961*(M:ℤ)-48*(K:ℤ)) := by
      have small : 48*K ≤ 961*M := (Nat.mul_le_mul_left _ upper).trans (Nat.mul_le_mul_right _ (by decide))
      exact sub_nonneg.mpr (by exact_mod_cast small)
    have difference : (4*(K:ℤ)*(37*(M:ℤ))^2)-(3*(M:ℤ)*(31*(M:ℤ)+8*(K:ℤ))^2) =
        (M:ℤ)*(4*(K:ℤ)-3*(M:ℤ))*(961*(M:ℤ)-48*(K:ℤ)) := by ring
    have nonnegative : 0 ≤ (4*(K:ℤ)*(37*(M:ℤ))^2)-(3*(M:ℤ)*(31*(M:ℤ)+8*(K:ℤ))^2) := by
      rw [difference]
      exact mul_nonneg (mul_nonneg (Int.natCast_nonneg _) first) last
    exact_mod_cast sub_nonneg.mp nonnegative
  calc
    _ = 14*(3*M*(31*M+8*K)^2) := by ring
    _ ≤ 14*(4*K*(37*M)^2) := Nat.mul_le_mul_left _ compare
    _ = 76664*(K*M^2) := by ring
    _ ≤ 76880*(K*M^2) := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring

private theorem five_sevenths_frozen_ratio {M K : ℕ} (upper : K ≤ M) (lower : 5*M ≤ 7*K) :
    ((31*M+8*K)*(31*M+8*K))*(128+2)*M ≤ 2*((31*M)*(31*M))*128*K := by
  -- Compare the retained mass per pair of expanded support sizes at K = 5M/7.
  have compare : 5*M*(217*M+56*K)^2 ≤ 7*K*(257*M)^2 := by
    have first : 0 ≤ (7*(K:ℤ)-5*(M:ℤ)) := sub_nonneg.mpr (by exact_mod_cast lower)
    have last : 0 ≤ (47089*(M:ℤ)-2240*(K:ℤ)) := by
      have small : 2240*K ≤ 47089*M :=
        (Nat.mul_le_mul_left _ upper).trans (Nat.mul_le_mul_right _ (by decide))
      exact sub_nonneg.mpr (by exact_mod_cast small)
    have difference : (7*(K:ℤ)*(257*(M:ℤ))^2)-(5*(M:ℤ)*(217*(M:ℤ)+56*(K:ℤ))^2) =
        (M:ℤ)*(7*(K:ℤ)-5*(M:ℤ))*(47089*(M:ℤ)-2240*(K:ℤ)) := by ring
    have nonnegative : 0 ≤ (7*(K:ℤ)*(257*(M:ℤ))^2)-(5*(M:ℤ)*(217*(M:ℤ)+56*(K:ℤ))^2) := by
      rw [difference]
      exact mul_nonneg (mul_nonneg (Int.natCast_nonneg _) first) last
    exact_mod_cast sub_nonneg.mp nonnegative
  refine Nat.le_of_mul_le_mul_left (c := 49) ?_ (by decide)
  calc
    _ = 26*(5*M*(217*M+56*K)^2) := by ring
    _ ≤ 26*(7*K*(257*M)^2) := Nat.mul_le_mul_left 26 compare
    _ = 12020918*(K*M^2) := by ring
    _ ≤ 12054784*(K*M^2) := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring

private theorem frozen_full_dense_of_increasing {k retention : ℕ} (paths kept : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (sub : ∀ i, (kept i).Sublist (paths i))
    (free : BridgeFree (Before paths) k) (rank : Fin n → Fin n)
    (ordered : ∀ i, ((kept i).map rank).Pairwise (· < ·))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (massN : 8*n ≤ ∑ i, (paths i).length) (massP : 8*p ≤ ∑ i, (paths i).length)
    (enough : let M := ∑ i, (paths i).length; let K := ∑ i, (kept i).length
      ((31*M+8*K)*(31*M+8*K))*(retention+2)*M ≤ 2*((31*M)*(31*M))*retention*K) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let K := ∑ i, (kept i).length
  let D := 4*M/n
  let L := 4*M/p
  let num := 31*M
  let den := 31*M+8*K
  let pieces := listRegularizedPaths kept D L
  have upper : K ≤ M := sum_le_sum fun i _ => (sub i).length_le
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have keptFree : BridgeFree (Before kept) k := by
    intro d limit
    exact ⟨fun b => (free limit).false (b.mapPaths id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (simple i) (sub i) step))⟩
  have allowed : BridgeFree (Before pieces) k :=
    listRegularizedPaths_fullFree_of_noShortPrecedenceCycle kept keptSimple keptFree
      (noShortPrecedenceCycle_of_increasing_order kept rank ordered (k-2)) D L
  obtain ⟨dPos,_,_⟩ := four_average_width hn dense
  obtain ⟨lPos,_,_⟩ := four_average_width hp long
  obtain ⟨countV,countI⟩ := regularization_list_counts kept keptSimple (D := D) (L := L) dPos lPos
  simp only [Fintype.card_fin] at countV countI
  change Fintype.card (ListVertexBlockIndex kept D) ≤ n+K/D at countV
  change Fintype.card (ListBlockIndex (splitListVertices kept D) L) ≤ p+K/L at countI
  have vRoom : num*Fintype.card (ListVertexBlockIndex kept D) ≤ den*n :=
    (Nat.mul_le_mul_left _ countV).trans (expanded_support_ratio hn massN)
  have iRoom : num*Fintype.card (ListBlockIndex (splitListVertices kept D) L) ≤ den*p :=
    (Nat.mul_le_mul_left _ countI).trans (expanded_support_ratio hp massP)
  obtain ⟨mass,length,degree⟩ := regularization_list_mass_caps kept keptSimple D L dPos lPos
  have denPositive : 0 < den := by unfold den M; omega
  have ratio : num ≤ den := Nat.le_add_right _ _
  refine regularization_list_frozen_after_caps_with_ratios_of_mass pieces
    (listRegularizedPaths_simple kept keptSimple D L) (half := false) (k := k) (retention := retention)
    allowed hn hp dense long denPositive denPositive ratio ratio vRoom iRoom length degree (mass.trans_le upper) ?_
  have sameMass : (∑ i, (pieces i).length) = K := mass
  rw [sameMass]
  exact enough

/-- For exclusion at a finite cutoff, it suffices that each original
precedence component already excludes full bridges at every size. -/
theorem regularization_list_frozen_full_of_component_fullFree {k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k)
    (localFree : ∀ c d, IsEmpty (Bridge (Before (pathsInPrecedenceComponent paths c)) d)) (cutoff : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 40*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n',v,p',q,clean,cleanSimple,cleanFree,keeps,within,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free.halfFree cutoff hn hp dense long low
    exact ⟨n',v,p',q,clean,cleanSimple,cleanFree,by omega,within,caps⟩
  have massN : 8*n ≤ M := (Nat.mul_le_mul_left _ (le_max_left _ _)).trans (lt_of_not_ge low).le
  have massP : 8*p ≤ M := (Nat.mul_le_mul_left _ (le_max_right _ _)).trans (lt_of_not_ge low).le
  obtain ⟨rank,kept,sub,ordered,_,_,removed⟩ :=
    fullBridgeFree_increasing_subsequences_two_of_components paths simple localFree
  have retained : 3*M ≤ 4*(∑ i, (kept i).length) := by change M ≤ _ at removed; omega
  have upper := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin p))) => (sub i).length_le)
  exact frozen_full_dense_of_increasing paths kept simple sub free rank ordered hn hp dense long massN massP
    (three_quarters_frozen_ratio upper retained)

/-- At a finite full-bridge cutoff, cleaning succeeds if every precedence
component has at most that many rows containing strict internal steps. -/
theorem regularization_list_frozen_full_of_component_rows {k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k)
    (few : ∀ c, (precedenceComponentNontrivialRows paths c).card ≤ k) (cutoff : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 40*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_full_of_component_fullFree paths simple free
    (precedenceComponents_fullFree_of_nontrivialRows_le paths simple free few) cutoff hn hp dense long

set_option maxHeartbeats 1200000 in
/-- Delete at most M/28 incidences, leaving precedence components
with all-size full exclusion. The cleaned family keeps the original
finite cutoff, both budgets, and all four original-average caps. -/
theorem regularization_list_frozen_full_of_component_fullFree_after_deletions {k : ℕ}
    (paths kept : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (sub : ∀ i, (kept i).Sublist (paths i)) (free : BridgeFree (Before paths) k)
    (localFree : ∀ c d, IsEmpty (Bridge (Before (pathsInPrecedenceComponent kept c)) d)) (cutoff : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retained : 27*(∑ i, (paths i).length) ≤ 28*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 128*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n',v,p',q,clean,cleanSimple,cleanFree,keeps,within,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free.halfFree cutoff hn hp dense long low
    exact ⟨n',v,p',q,clean,cleanSimple,cleanFree,by omega,within,caps⟩
  have massN : 8*n ≤ M := (Nat.mul_le_mul_left _ (le_max_left _ _)).trans (lt_of_not_ge low).le
  have massP : 8*p ≤ M := (Nat.mul_le_mul_left _ (le_max_right _ _)).trans (lt_of_not_ge low).le
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  obtain ⟨rank,orderedRows,keptSub,ordered,_,_,removed⟩ :=
    fullBridgeFree_increasing_subsequences_two_of_components kept keptSimple localFree
  have composed (i : Fin p) : (orderedRows i).Sublist (paths i) := (keptSub i).trans (sub i)
  have upper : (∑ i, (orderedRows i).length) ≤ M := sum_le_sum (fun i _ => (composed i).length_le)
  have enough : 5*M ≤ 7*(∑ i, (orderedRows i).length) := by
    change 27*M ≤ 28*(∑ i, (kept i).length) at retained
    omega
  exact frozen_full_dense_of_increasing paths orderedRows simple composed free rank ordered hn hp dense long massN massP
    (five_sevenths_frozen_ratio upper enough)

set_option maxHeartbeats 1200000 in
/-- Delete at most M/28 incidences to bring the surviving precedence
components within the full-bridge cutoff on their nontrivial rows.
The cleaned family has all four original-average caps and both budgets. -/
theorem regularization_list_frozen_full_of_component_rows_after_deletions {k : ℕ}
    (paths kept : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (sub : ∀ i, (kept i).Sublist (paths i)) (free : BridgeFree (Before paths) k)
    (few : ∀ c, (precedenceComponentNontrivialRows kept c).card ≤ k) (cutoff : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retained : 27*(∑ i, (paths i).length) ≤ 28*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 128*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have keptSimple (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have keptFree : BridgeFree (Before kept) k := by
    intro d limit
    exact ⟨fun b => (free limit).false (b.mapPaths id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (simple i) (sub i) step))⟩
  exact regularization_list_frozen_full_of_component_fullFree_after_deletions paths kept simple sub free
    (precedenceComponents_fullFree_of_nontrivialRows_le kept keptSimple keptFree few) cutoff hn hp dense long retained

/-- Every fully bridge-free simple family of mass at least both positive
budgets admits cleaning that keeps every full bridge excluded, both
budgets, all four original-average caps, and one fortieth of the mass. -/
theorem regularization_list_frozen_full_all (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : ∀ d, IsEmpty (Bridge (Before paths) d))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ (∀ d, IsEmpty (Bridge (Before clean) d)) ∧
      M ≤ 40*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let cutoff := max 2 p
  have full : BridgeFree (Before paths) cutoff := fun d _ => free d
  obtain ⟨n',vBudget,p',pBudget,clean,cleanSimple,cleanFree,keeps,within,caps⟩ :=
    regularization_list_frozen_full_of_component_fullFree paths simple full (precedenceComponent_fullFree simple free)
      (le_max_left _ _) hn hp dense long
  refine ⟨n',vBudget,p',pBudget,clean,cleanSimple,?_,keeps,within,caps⟩
  intro d
  refine ⟨fun b => (cleanFree ?_).false b⟩
  have count : d+2 ≤ p' := by simpa only [Fintype.card_fin] using SourceAudit.bridge_path_count_le b
  exact count.trans (pBudget.trans (le_max_right _ _))

end OnlineReachabilityPreservers
