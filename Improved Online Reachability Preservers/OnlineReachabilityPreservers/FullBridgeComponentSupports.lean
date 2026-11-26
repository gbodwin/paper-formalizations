import OnlineReachabilityPreservers.FullBridgeCleaning

/-! Bound local bridges by the corners where two nontrivial rows meet. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

variable {n p : ℕ}

/-- Vertices common to two distinct rows having strict steps in a component. -/
noncomputable def precedenceComponentMeetingVertices (paths : Fin p → List (Fin n)) (c : Fin n) :
    Finset (Fin n) :=
  univ.filter fun v =>
    2 ≤ ((precedenceComponentNontrivialRows paths c).filter
      fun i => v ∈ pathsInPrecedenceComponent paths c i).card

private theorem mem_meetingVertices_of_two_rows {paths : Fin p → List (Fin n)} {c x : Fin n} {i j : Fin p}
    (different : i ≠ j) (validI : i ∈ precedenceComponentNontrivialRows paths c)
    (validJ : j ∈ precedenceComponentNontrivialRows paths c)
    (first : x ∈ pathsInPrecedenceComponent paths c i) (second : x ∈ pathsInPrecedenceComponent paths c j) :
    x ∈ precedenceComponentMeetingVertices paths c := by
  refine mem_filter.mpr ⟨mem_univ _,?_⟩
  let both := (precedenceComponentNontrivialRows paths c).filter
    (fun k => x ∈ pathsInPrecedenceComponent paths c k)
  have inside : ({i,j} : Finset (Fin p)) ⊆ both := by
    intro k present
    rcases mem_insert.mp present with rfl | onLast
    · exact mem_filter.mpr ⟨validI,first⟩
    · rw [mem_singleton] at onLast
      subst k
      exact mem_filter.mpr ⟨validJ,second⟩
  have count := card_le_card inside
  simpa only [card_insert_of_notMem (notMem_singleton.mpr different),card_singleton] using count

/-- Each corner of a bridge meets two different nontrivial rows. -/
theorem precedenceComponent_bridge_size_le_meetingVertices {paths : Fin p → List (Fin n)} {c : Fin n} {d : ℕ}
    (bridge : Bridge (Before (pathsInPrecedenceComponent paths c)) d) :
    d+2 ≤ (precedenceComponentMeetingVertices paths c).card := by
  have inside (j : Fin (d+2)) : bridge.vertex j ∈ precedenceComponentMeetingVertices paths c := by
    refine Fin.lastCases ?_ (fun q => ?_) j
    · let i := Fin.last d
      have last : i.succ = Fin.last (d+1) := Fin.succ_last _
      have onLast := (bridge.arcStep i).2.1
      rw [last] at onLast
      exact mem_meetingVertices_of_two_rows (bridge.river_ne_arc i)
        (precedenceComponent_row_mem_of_step bridge.riverStep)
        (precedenceComponent_row_mem_of_step (bridge.arcStep i)) bridge.riverStep.2.1 onLast
    · rcases Fin.eq_zero_or_eq_succ q with rfl | ⟨r,rfl⟩
      · exact mem_meetingVertices_of_two_rows (bridge.river_ne_arc 0)
          (precedenceComponent_row_mem_of_step bridge.riverStep)
          (precedenceComponent_row_mem_of_step (bridge.arcStep 0)) bridge.riverStep.1 (bridge.arcStep 0).1
      · let previous := r.castSucc
        let next := r.succ
        have adjacent : previous.succ = next.castSucc := Fin.ext rfl
        have distinct : bridge.arc previous ≠ bridge.arc next := by
          intro equal
          have values := congrArg Fin.val (bridge.distinctArcs equal)
          change r.val = r.val+1 at values
          omega
        have onPrevious := (bridge.arcStep previous).2.1
        rw [adjacent] at onPrevious
        exact mem_meetingVertices_of_two_rows distinct
          (precedenceComponent_row_mem_of_step (bridge.arcStep previous))
          (precedenceComponent_row_mem_of_step (bridge.arcStep next)) onPrevious (bridge.arcStep next).1
  let inject (j : Fin (d+2)) : precedenceComponentMeetingVertices paths c := ⟨bridge.vertex j,inside j⟩
  have injective : Function.Injective inject := fun _ _ eq => bridge.distinctVertices (congrArg Subtype.val eq)
  simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective inject injective

/-- Either the row support or the support of meeting vertices can certify
that a component contains no full bridge beyond the global cutoff. -/
theorem precedenceComponents_fullFree_of_small_support {k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k)
    (small : ∀ c, (precedenceComponentNontrivialRows paths c).card ≤ k ∨
      (precedenceComponentMeetingVertices paths c).card ≤ k) :
    ∀ c d, IsEmpty (Bridge (Before (pathsInPrecedenceComponent paths c)) d) := by
  intro c d
  refine ⟨fun b => ?_⟩
  have limit : d+2 ≤ k := (small c).elim
    (fun rows => (precedenceComponent_bridge_size_le_rows b).trans rows)
    (fun vertices => (precedenceComponent_bridge_size_le_meetingVertices b).trans vertices)
  exact (free limit).false (b.mapPaths id Function.injective_id (fun i _ _ step =>
    listBefore_of_sublist (simple i) List.filter_sublist step))

/-- The finite-cutoff cleaning conclusion holds if, in each component,
either support has size at most the cutoff. -/
theorem regularization_list_frozen_full_of_component_small_support {k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k)
    (small : ∀ c, (precedenceComponentNontrivialRows paths c).card ≤ k ∨
      (precedenceComponentMeetingVertices paths c).card ≤ k) (cutoff : 2 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 40*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_full_of_component_fullFree paths simple free
    (precedenceComponents_fullFree_of_small_support paths simple free small) cutoff hn hp dense long

end OnlineReachabilityPreservers
