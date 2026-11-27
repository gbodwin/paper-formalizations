import OnlineReachabilityPreservers.HalfBridgeArrivalOrder
import OnlineReachabilityPreservers.FrozenHalfFourConflicts
import OnlineReachabilityPreservers.LocalSourceCounting

/-! Which incidence deletions remove the arrival constraints of a bridge. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- The row occurrences needed by the river and each arc of a bridge. -/
def Bridge.cornerIncidences {I V : Type*} [DecidableEq I] [DecidableEq V]
    {before : I → V → V → Prop} {d : ℕ} (b : Bridge before d) : Finset (I × V) :=
  insert (b.river,b.vertex 0) (insert (b.river,b.vertex (Fin.last (d+1)))
    (univ.biUnion fun i : Fin (d+1) => {(b.arc i,b.vertex i.castSucc),(b.arc i,b.vertex i.succ)}))

private theorem Bridge.disjoint_cornerIncidences_iff {I V : Type*} [DecidableEq I] [DecidableEq V]
    {before : I → V → V → Prop} {d : ℕ} (b : Bridge before d) (deleted : Finset (I × V)) :
    Disjoint b.cornerIncidences deleted ↔ (b.river,b.vertex 0) ∉ deleted ∧
      (b.river,b.vertex (Fin.last (d+1))) ∉ deleted ∧
      ∀ i, (b.arc i,b.vertex i.castSucc) ∉ deleted ∧ (b.arc i,b.vertex i.succ) ∉ deleted := by
  simp only [Bridge.cornerIncidences,disjoint_insert_left]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  simp only [Finset.disjoint_left,mem_biUnion,mem_univ,true_and,mem_insert,mem_singleton]
  constructor
  · intro apart i
    exact ⟨apart ⟨i,Or.inl rfl⟩,apart ⟨i,Or.inr rfl⟩⟩
  · rintro apart _ ⟨i,h | h⟩
    · exact h ▸ (apart i).1
    · exact h ▸ (apart i).2

/-- An arrival constraint survives deletion exactly when one of its
original bridge witnesses keeps all its required incidences. -/
theorem halfBridgeArrivalGraph_edge_erase_iff {I V : Type*} [DecidableEq I] [Fintype I] [LinearOrder V]
    {rows : I → List V} (simple : ∀ i, (rows i).Nodup) (deleted : Finset (I × V))
    {k : ℕ} {r a : I} :
    Edge (halfBridgeArrivalGraph (erasePieceIncidences rows deleted) k) r a ↔
      ∃ d, d+2 ≤ k ∧ ∃ b : Bridge (Before rows) d,
        b.river = r ∧ b.arc (Fin.last d) = a ∧ Disjoint b.cornerIncidences deleted := by
  rw [halfBridgeArrivalGraph_edge]
  constructor
  · rintro ⟨d,small,b,river,lastStep⟩
    let original : Bridge (Before rows) d := b.mapPaths id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (simple i) (erasePieceIncidences_sublist rows deleted i) step)
    refine ⟨d,small,original,river,lastStep,(original.disjoint_cornerIncidences_iff deleted).mpr ?_⟩
    exact ⟨(mem_erasePieceIncidences.mp b.riverStep.1).2,(mem_erasePieceIncidences.mp b.riverStep.2.1).2,
      fun i => ⟨(mem_erasePieceIncidences.mp (b.arcStep i).1).2,(mem_erasePieceIncidences.mp (b.arcStep i).2.1).2⟩⟩
  · rintro ⟨d,small,b,river,lastStep,disjoint⟩
    obtain ⟨start,finish,arcs⟩ := (b.disjoint_cornerIncidences_iff deleted).mp disjoint
    have keep {i x y} (step : Before rows i x y) (left : (i,x) ∉ deleted) (right : (i,y) ∉ deleted) :
        Before (erasePieceIncidences rows deleted) i x y :=
      (listBefore_sublist_iff (simple i) (erasePieceIncidences_sublist rows deleted i)
        (mem_erasePieceIncidences.mpr ⟨step.1,left⟩) (mem_erasePieceIncidences.mpr ⟨step.2.1,right⟩)).mpr step
    let survives : Bridge (Before (erasePieceIncidences rows deleted)) d :=
      ⟨b.vertex,b.arc,b.river,b.distinctVertices,b.distinctArcs,b.river_ne_arc,
        keep b.riverStep start finish,fun i => keep (b.arcStep i) (arcs i).1 (arcs i).2⟩
    exact ⟨d,small,survives,river,lastStep⟩

/-- For a proposed order, the erased incidences must hit every bridge
whose river and final arc disagree with that order. -/
theorem halfBridgeArrivalGraph_erase_increases_iff {I V : Type*} [DecidableEq I] [Fintype I] [LinearOrder V]
    {rows : I → List V} (simple : ∀ i, (rows i).Nodup) (deleted : Finset (I × V))
    {k : ℕ} {α : Type*} [LinearOrder α] (rank : I → α) (distinct : Function.Injective rank) :
    (∀ ⦃r a⦄, Edge (halfBridgeArrivalGraph (erasePieceIncidences rows deleted) k) r a → rank r < rank a) ↔
      ∀ ⦃d⦄, d+2 ≤ k → ∀ b : Bridge (Before rows) d,
        rank (b.arc (Fin.last d)) < rank b.river → (b.cornerIncidences ∩ deleted).Nonempty := by
  constructor
  · intro increases d small b opposite
    apply Finset.not_disjoint_iff_nonempty_inter.mp
    intro disjoint
    have on := (halfBridgeArrivalGraph_edge_erase_iff simple deleted).mpr ⟨d,small,b,rfl,rfl,disjoint⟩
    exact opposite.asymm (increases on)
  · intro covers r a on
    obtain ⟨d,small,b,rfl,rfl,disjoint⟩ := (halfBridgeArrivalGraph_edge_erase_iff simple deleted).mp on
    have unequal : rank b.river ≠ rank (b.arc (Fin.last d)) := fun eq => b.river_ne_arc _ (distinct eq)
    refine (le_of_not_gt ?_).lt_of_ne unequal
    intro opposite
    exact (Finset.not_disjoint_iff_nonempty_inter.mpr (covers small b opposite)) disjoint

/-- A set of incidences covering all violations of a proposed arrival
order gives frozen half cleaning if its actual cost is at most `M/18`. -/
theorem regularization_list_frozen_half_of_arrival_incidence_cover {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    let D := 4*M/n
    let L := 4*M/p
    let I := ListBlockIndex (splitListVertices paths D) L
    let V := ListVertexBlockIndex paths D
    let pieces : I → List V := listRegularizedPaths paths D L
    ∀ (rank : I → ℕ) (deleted : Finset (I × V)), Function.Injective rank →
      (∀ ⦃d⦄, d+2 ≤ k → ∀ b : Bridge (Before pieces) d,
        rank (b.arc (Fin.last d)) < rank b.river → (b.cornerIncidences ∩ deleted).Nonempty) →
      18*(pieceIncidences pieces univ ∩ deleted).card ≤ M →
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
        M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  dsimp only
  intro rank deleted distinct covers smallLoss
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let pieces := listRegularizedPaths paths D L
  let kept := erasePieceIncidences pieces deleted
  let G := halfBridgeArrivalGraph kept k
  have pieceSimple := listRegularizedPaths_simple paths simple D L
  have increases : ∀ ⦃r a⦄, Edge G r a → rank r < rank a :=
    (halfBridgeArrivalGraph_erase_increases_iff pieceSimple deleted rank distinct).mpr
      (fun {_} small b opposite => covers small b opposite)
  have dag : IsDAG G := by
    intro r a edge back
    have weak {u v} (route : Reach G u v) : rank u ≤ rank v := by
      induction route with
      | refl => exact le_rfl
      | tail _ step prev => exact prev.trans (increases step).le
    exact (increases edge).not_ge (weak back)
  obtain ⟨mass,_,_⟩ := regularization_list_mass_caps paths simple D L
    (four_average_width hn dense).1 (four_average_width hp long).1
  have measured := (erasePieceIncidences_mass_add_loss pieceSimple univ deleted).trans mass
  change (∑ i, (kept i).length)+(pieceIncidences pieces univ ∩ deleted).card = M at measured
  apply regularization_list_frozen_half_after_arrival_deletions paths simple kept
    (erasePieceIncidences_sublist pieces deleted) dag ?_ hn hp dense long
  change 18*(M-∑ i, (kept i).length) ≤ M
  change 18*(pieceIncidences pieces univ ∩ deleted).card ≤ M at smallLoss
  omega

/-- For each designated constraint, erase the occurrences on its final
arc piece of all vertices shared with its river piece. -/
def arrivalFeedbackIncidences {I V : Type*} [DecidableEq I] [DecidableEq V]
    (rows : I → List V) (feedback : Arcs I) : Finset (I × V) :=
  feedback.biUnion fun e =>
    ((rows e.1).toFinset ∩ (rows e.2).toFinset).image (fun v => (e.2,v))

/-- The union of erased incidences costs at most the sum of river and final-piece
intersection sizes, with shared erasures counted only once in the union. -/
theorem arrivalFeedbackIncidences_card_le {I V : Type*} [DecidableEq I] [DecidableEq V]
    (rows : I → List V) (feedback : Arcs I) :
    (arrivalFeedbackIncidences rows feedback).card ≤
      ∑ e ∈ feedback, ((rows e.1).toFinset ∩ (rows e.2).toFinset).card := by
  apply card_biUnion_le.trans
  exact sum_le_sum fun e _ => card_image_le

/-- Every surviving constraint was an original constraint outside the
designated feedback edge set. Each erased edge may have many bridge witnesses. -/
theorem halfBridgeArrivalGraph_erase_feedback_subset {I V : Type*}
    [DecidableEq I] [Fintype I] [LinearOrder V] {rows : I → List V}
    (simple : ∀ i, (rows i).Nodup) (feedback : Arcs I) (k : ℕ) :
    halfBridgeArrivalGraph (erasePieceIncidences rows (arrivalFeedbackIncidences rows feedback)) k ⊆
      halfBridgeArrivalGraph rows k \ feedback := by
  intro e edge
  obtain ⟨d,small,b,river,lastArc,disjoint⟩ :=
    (halfBridgeArrivalGraph_edge_erase_iff simple (arrivalFeedbackIncidences rows feedback)).mp
      (show Edge _ e.1 e.2 from edge)
  refine mem_sdiff.mpr ⟨halfBridgeArrivalGraph_edge.mpr ⟨d,small,b,river,lastArc⟩,?_⟩
  intro picked
  let x := b.vertex (Fin.last (d+1))
  have riverEnd : x ∈ rows e.1 := by rw [← river]; exact b.riverStep.2.1
  have finalEnd : x ∈ rows e.2 := by rw [← lastArc]; exact (b.arcStep (Fin.last d)).2.1
  have erased : (e.2,x) ∈ arrivalFeedbackIncidences rows feedback :=
    mem_biUnion.mpr ⟨e,picked,mem_image.mpr ⟨x,mem_inter.mpr
      ⟨List.mem_toFinset.mpr riverEnd,List.mem_toFinset.mpr finalEnd⟩,rfl⟩⟩
  have intact := ((b.disjoint_cornerIncidences_iff (arrivalFeedbackIncidences rows feedback)).mp
    disjoint).2.2 (Fin.last d)
  exact intact.2 (lastArc.symm ▸ erased)

/-- Break the arrival cycles by erasing the final incidences of a feedback
edge set. The summed intersection sizes give a sufficient deletion budget. -/
theorem regularization_list_frozen_half_of_feedback_intersections {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    let D := 4*M/n
    let L := 4*M/p
    let I := ListBlockIndex (splitListVertices paths D) L
    let pieces := listRegularizedPaths paths D L
    ∀ feedback : Arcs I, IsDAG (halfBridgeArrivalGraph pieces k \ feedback) →
      18*(∑ e ∈ feedback, ((pieces e.1).toFinset ∩ (pieces e.2).toFinset).card) ≤ M →
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
        M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  dsimp only
  intro feedback acyclic smallLoss
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let pieces := listRegularizedPaths paths D L
  let deleted := arrivalFeedbackIncidences pieces feedback
  let kept := erasePieceIncidences pieces deleted
  have pieceSimple := listRegularizedPaths_simple paths simple D L
  have sub := halfBridgeArrivalGraph_erase_feedback_subset pieceSimple feedback k
  have dag : IsDAG (halfBridgeArrivalGraph kept k) :=
    fun _ _ e reverse => acyclic (sub e) (reach_mono sub reverse)
  obtain ⟨mass,_,_⟩ := regularization_list_mass_caps paths simple D L
    (four_average_width hn dense).1 (four_average_width hp long).1
  have loss : (pieceIncidences pieces univ ∩ deleted).card ≤
      ∑ e ∈ feedback, ((pieces e.1).toFinset ∩ (pieces e.2).toFinset).card :=
    (card_le_card inter_subset_right).trans (arrivalFeedbackIncidences_card_le pieces feedback)
  have cost := (Nat.mul_le_mul_left 18 loss).trans smallLoss
  have measured := (erasePieceIncidences_mass_add_loss pieceSimple univ deleted).trans mass
  change (∑ i, (kept i).length)+(pieceIncidences pieces univ ∩ deleted).card = M at measured
  apply regularization_list_frozen_half_after_arrival_deletions paths simple kept
    (erasePieceIncidences_sublist pieces deleted) dag ?_ hn hp dense long
  change 18*(M-∑ i, (kept i).length) ≤ M
  omega

end OnlineReachabilityPreservers
