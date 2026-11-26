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

end OnlineReachabilityPreservers
