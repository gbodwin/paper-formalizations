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

/-- The two support bounds suffice separately in each component. -/
private theorem precedenceComponent_fullFree_of_small_support {k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k) {c : Fin n}
    (small : (precedenceComponentNontrivialRows paths c).card ≤ k ∨
      (precedenceComponentMeetingVertices paths c).card ≤ k) (d : ℕ) :
    IsEmpty (Bridge (Before (pathsInPrecedenceComponent paths c)) d) := by
  refine ⟨fun b => ?_⟩
  have limit : d+2 ≤ k := small.elim
    (fun rows => (precedenceComponent_bridge_size_le_rows b).trans rows)
    (fun vertices => (precedenceComponent_bridge_size_le_meetingVertices b).trans vertices)
  exact (free limit).false (b.mapPaths id Function.injective_id (fun i _ _ step =>
    listBefore_of_sublist (simple i) List.filter_sublist step))

/-- Either the row support or the support of meeting vertices can certify
that a component contains no full bridge beyond the global cutoff. -/
theorem precedenceComponents_fullFree_of_small_support {k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k)
    (small : ∀ c, (precedenceComponentNontrivialRows paths c).card ≤ k ∨
      (precedenceComponentMeetingVertices paths c).card ≤ k) :
    ∀ c d, IsEmpty (Bridge (Before (pathsInPrecedenceComponent paths c)) d) :=
  fun c => precedenceComponent_fullFree_of_small_support paths simple free (small c)

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

/-- Mark the components where neither internal support fits the cutoff. -/
noncomputable def oversizedPrecedenceComponentSupports (paths : Fin p → List (Fin n)) (cutoff : ℕ) :
    Finset (Fin n) :=
  univ.filter fun c => cutoff < (precedenceComponentNontrivialRows paths c).card ∧
    cutoff < (precedenceComponentMeetingVertices paths c).card

/-- In each marked component, keep the first vertex of each row. All
other component visits are retained in their original row order. -/
noncomputable def trimOversizedPrecedenceComponentVisits (paths : Fin p → List (Fin n))
    (cutoff : ℕ) (i : Fin p) : List (Fin n) :=
  (paths i).filter fun x =>
    let c := componentLabel (pathPrecedenceGraph paths) x
    decide (c ∉ oversizedPrecedenceComponentSupports paths cutoff ∨
      (pathsInPrecedenceComponent paths c i).head? = some x)

/-- Charge only the extra incidences after the first vertex of each
marked visit. -/
noncomputable def oversizedPrecedenceComponentVisitExcess (paths : Fin p → List (Fin n))
    (cutoff : ℕ) : ℕ :=
  ∑ i, ∑ c ∈ oversizedPrecedenceComponentSupports paths cutoff,
    ((pathsInPrecedenceComponent paths c i).length - 1)

private theorem trimOversizedPrecedenceComponentVisits_filter_old
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (cutoff : ℕ)
    (i : Fin p) (c : Fin n) :
    ((trimOversizedPrecedenceComponentVisits paths cutoff i).filter
      fun x => decide (componentLabel (pathPrecedenceGraph paths) x = c)) =
      if c ∈ oversizedPrecedenceComponentSupports paths cutoff then
        (pathsInPrecedenceComponent paths c i).take 1
      else pathsInPrecedenceComponent paths c i := by
  classical
  let label := componentLabel (pathPrecedenceGraph paths)
  let visit := pathsInPrecedenceComponent paths c i
  let marked := oversizedPrecedenceComponentSupports paths cutoff
  let choose (x : Fin n) := decide (label x ∉ marked ∨
    (pathsInPrecedenceComponent paths (label x) i).head? = some x)
  change ((paths i).filter choose).filter (fun x => decide (label x = c)) =
    if c ∈ marked then visit.take 1 else visit
  rw [List.filter_comm]
  change visit.filter choose = _
  have inComponent {v : Fin n} (present : v ∈ visit) : label v = c :=
    of_decide_eq_true (List.mem_filter.mp present).2
  by_cases mark : c ∈ marked
  · rw [ite_eq_left mark]
    have same : visit.filter choose = visit.filter (fun x => decide (visit.head? = some x)) := by
      apply List.filter_congr
      intro x hx
      simp [choose,inComponent hx,mark,visit]
    rw [same]
    have distinct : visit.Nodup :=
      List.filter_sublist.nodup (simple i)
    cases shape : visit with
    | nil => simp
    | cons first tail =>
      have fresh := (List.nodup_cons.mp (shape ▸ distinct)).1
      have tailEmpty : (tail.filter fun x => decide (first = x)) = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro x present
        obtain ⟨inTail,equal⟩ := List.mem_filter.mp present
        exact fresh ((of_decide_eq_true equal).symm ▸ inTail)
      simp [tailEmpty]
  · rw [ite_eq_right mark]
    exact List.filter_eq_self.mpr (fun x hx => by
      dsimp only [choose]
      rw [inComponent hx]
      exact decide_eq_true (Or.inl mark))

/-- The selected rows lose exactly their summed excess over one vertex
in each oversized original component. -/
theorem trimOversizedPrecedenceComponentVisits_mass_add_excess (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (cutoff : ℕ) :
    (∑ i, (trimOversizedPrecedenceComponentVisits paths cutoff i).length) +
      oversizedPrecedenceComponentVisitExcess paths cutoff = ∑ i, (paths i).length := by
  classical
  unfold oversizedPrecedenceComponentVisitExcess
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  let kept := trimOversizedPrecedenceComponentVisits paths cutoff i
  have keptSimple : kept.Nodup := List.filter_sublist.nodup (simple i)
  rw [precedenceComponent_sum_filtered_lengths (pathPrecedenceGraph paths) kept keptSimple,
    precedenceComponent_sum_filtered_lengths (pathPrecedenceGraph paths) (paths i) (simple i)]
  have extra :
      (∑ c ∈ oversizedPrecedenceComponentSupports paths cutoff, ((pathsInPrecedenceComponent paths c i).length-1)) =
        ∑ c : Fin n, if c ∈ oversizedPrecedenceComponentSupports paths cutoff then
          (pathsInPrecedenceComponent paths c i).length-1 else 0 := by
    rw [← sum_filter]
    simp
  rw [extra,← sum_add_distrib]
  apply sum_congr rfl
  intro c _
  change ((trimOversizedPrecedenceComponentVisits paths cutoff i).filter _).length + _ = _
  rw [trimOversizedPrecedenceComponentVisits_filter_old paths simple cutoff i c]
  let visit := pathsInPrecedenceComponent paths c i
  let marked := oversizedPrecedenceComponentSupports paths cutoff
  change (if c ∈ marked then visit.take 1 else visit).length +
    (if c ∈ marked then visit.length-1 else 0) = visit.length
  split_ifs
  · rw [List.length_take]
    omega
  · omega

private theorem trimOversizedPrecedenceComponentVisits_local_fullFree {k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k) :
    let kept := trimOversizedPrecedenceComponentVisits paths k
    ∀ c d, IsEmpty (Bridge (Before (pathsInPrecedenceComponent kept c)) d) := by
  classical
  intro kept c d
  let old := pathPrecedenceGraph paths
  let after := pathPrecedenceGraph kept
  let originalLabel := componentLabel old
  let parent := originalLabel c
  let oldVisit (i : Fin p) := pathsInPrecedenceComponent paths parent i
  let newVisit (i : Fin p) := pathsInPrecedenceComponent kept c i
  have sub (i : Fin p) : (kept i).Sublist (paths i) := List.filter_sublist
  have edges : after ⊆ old := by
    intro e
    simp only [after,old,pathPrecedenceGraph,mem_filter,mem_univ,true_and]
    rintro ⟨i,step⟩
    exact ⟨i,listBefore_of_sublist (simple i) (sub i) step⟩
  have labelOn {i : Fin p} {x : Fin n} (on : x ∈ newVisit i) : originalLabel x = parent := by
    have newLabel : componentLabel after x = c := of_decide_eq_true (List.mem_filter.mp on).2
    have same : SameComponent after x c := newLabel ▸ componentLabel_same x
    exact componentLabel_eq.mpr ⟨reach_mono edges same.1,reach_mono edges same.2⟩
  let fromParent (x : Fin n) := decide (originalLabel x = parent)
  have under (i : Fin p) : (newVisit i).Sublist ((kept i).filter fromParent) := by
    have same : (newVisit i).filter fromParent = newVisit i :=
      List.filter_eq_self.mpr (fun _ on => decide_eq_true (labelOn on))
    rw [← same]
    exact List.filter_sublist.filter fromParent
  let marked := oversizedPrecedenceComponentSupports paths k
  by_cases exceptional : parent ∈ marked
  · have few (i : Fin p) : (newVisit i).length ≤ 1 := by
      have shorter := (under i).length_le
      change _ ≤ ((trimOversizedPrecedenceComponentVisits paths k i).filter
        fun x => decide (componentLabel (pathPrecedenceGraph paths) x = parent)).length at shorter
      rw [trimOversizedPrecedenceComponentVisits_filter_old paths simple k i parent,ite_eq_left exceptional,
        List.length_take] at shorter
      exact shorter.trans (min_le_left _ _)
    refine ⟨fun b => ?_⟩
    have limit := List.idxOf_lt_length_of_mem b.riverStep.2.1
    have strictly := b.riverStep.2.2
    have one := few b.river
    change (pathsInPrecedenceComponent kept c b.river).length ≤ 1 at one
    omega
  · have small : (precedenceComponentNontrivialRows paths parent).card ≤ k ∨
        (precedenceComponentMeetingVertices paths parent).card ≤ k := by
      by_cases rows : (precedenceComponentNontrivialRows paths parent).card ≤ k
      · exact Or.inl rows
      right
      by_contra! vertices
      exact exceptional (mem_filter.mpr ⟨mem_univ _,lt_of_not_ge rows,vertices⟩)
    have oldFree := precedenceComponent_fullFree_of_small_support paths simple free small d
    have visits (i : Fin p) : (newVisit i).Sublist (oldVisit i) :=
      (under i).trans ((sub i).filter fromParent)
    refine ⟨fun b => oldFree.false (b.mapPaths id Function.injective_id (fun i _ _ step => ?_))⟩
    exact listBefore_of_sublist (List.filter_sublist.nodup (simple i)) (visits i) step

/-- If the total excess over one incidence per row in oversized original
components is at most M/28, finite full-bridge cleaning keeps M/128,
both original budgets, and all four original-average caps. -/
theorem regularization_list_frozen_full_of_small_oversizedComponentVisitExcess {k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) k)
    (cutoff : 2 ≤ k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (excess : 28*oversizedPrecedenceComponentVisitExcess paths k ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      M ≤ 128*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have mass := trimOversizedPrecedenceComponentVisits_mass_add_excess paths simple k
  exact regularization_list_frozen_full_of_component_fullFree_after_deletions paths
    (trimOversizedPrecedenceComponentVisits paths k) simple (fun _ => List.filter_sublist) free
    (trimOversizedPrecedenceComponentVisits_local_fullFree paths simple free) cutoff hn hp dense long (by omega)

end OnlineReachabilityPreservers
