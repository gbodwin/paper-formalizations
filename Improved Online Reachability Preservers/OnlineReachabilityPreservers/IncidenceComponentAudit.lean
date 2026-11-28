import OnlineReachabilityPreservers.IncidenceComponentCleaning
import OnlineReachabilityPreservers.RainbowListSearch

/-! Keeping deleted-row incidence components together can repair an unsafe width split. -/

namespace OnlineReachabilityPreservers.SourceAudit
open SimpleGraph Finset
local notation "Before" => SourceAudit.BeforeIn
open scoped Sigma.Lex

/-- One long row, two disjoint reverse rows, and six empty indexed rows. -/
def incidenceDeletionRows : Fin 9 → List (Fin 9) := ![[0,1,2,3,4,5],[5,0],[4,1],[],[],[],[],[],[]]
/-- Pack the two reverse components together and put the private
interior vertices in a second piece of the long row. -/
def incidenceDeletionPieces : Fin 10 → List (Fin 9) := ![[0,1,4,5],[2,3],[5,0],[4,1],[],[],[],[],[],[]]
private def parent (i : Fin 10) : Fin 9 := ⟨i.val-1,by omega⟩
private abbrev OriginalNode := Fin 9 ⊕ Fin 9
private abbrev SplitNode := Fin 10 ⊕ Fin 9
private abbrev originalGraph := pathIncidenceGraph incidenceDeletionRows
private abbrev splitGraph := pathIncidenceGraph incidenceDeletionPieces
private def root : OriginalNode := .inl 0

private theorem parent_monotone : Monotone parent := by
  intro i j ordered
  exact Nat.sub_le_sub_right ordered 1

private theorem members : ∀ i x, x ∈ incidenceDeletionPieces i → x ∈ incidenceDeletionRows (parent i) := by decide
private theorem steps : ∀ i x y, Before incidenceDeletionPieces i x y → Before incidenceDeletionRows (parent i) x y := by
  unfold SourceAudit.BeforeIn
  decide

private def hom : splitGraph →g originalGraph := pathIncidenceGraph_hom parent id
  (fun {_ _} => members _ _)

private instance originalAdjDecidable : DecidableRel originalGraph.Adj
  | .inl i, .inr x => inferInstanceAs (Decidable (x ∈ incidenceDeletionRows i))
  | .inr x, .inl i => inferInstanceAs (Decidable (x ∈ incidenceDeletionRows i))
  | .inl _, .inl _ => isFalse id
  | .inr _, .inr _ => isFalse id

private def colour : OriginalNode → Bool
  | .inl _ => true
  | .inr x => decide (x ≠ 2 ∧ x ≠ 3)

private theorem colour_edge : ∀ u v, u ≠ root → v ≠ root → originalGraph.Adj u v → colour u = colour v := by decide

private theorem colour_walk {x y : OriginalNode} (w : originalGraph.Walk x y) (avoid : root ∉ w.support) :
    colour x = colour y := by
  induction w with
  | nil => rfl
  | @cons u v z edge tail ih =>
    have rootU : u ≠ root := fun equal => avoid (equal ▸ (SimpleGraph.Walk.cons edge tail).start_mem_support)
    have remaining : root ∉ tail.support := by
      intro on
      apply avoid
      simp only [Walk.support_cons,List.mem_cons]
      exact Or.inr on
    have rootV : v ≠ root := fun equal => remaining (equal ▸ tail.start_mem_support)
    exact (colour_edge u v rootU rootV edge).trans (ih remaining)

private theorem duplicate_parent : ∀ i j, i ≠ j → parent i = parent j →
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by decide
private theorem colour_first : ∀ u, u ∈ incidenceDeletionPieces 0 → colour (.inr u) = true := by decide
private theorem colour_second : ∀ u, u ∈ incidenceDeletionPieces 1 → colour (.inr u) = false := by decide

private theorem coherence (a : OriginalNode) : RespectsDeletionComponentsAt hom a := by
  intro x y u v fx fy xu yv w avoid
  have eq := fx.trans fy.symm
  cases x with
  | inr x =>
    cases y with
    | inr y => exact congrArg Sum.inr (Sum.inr.inj eq)
    | inl _ => cases eq
  | inl i =>
    cases y with
    | inr _ => cases eq
    | inl j =>
      by_cases same : i = j
      · exact congrArg Sum.inl same
      have sameParent : parent i = parent j := Sum.inl.inj eq
      cases u with
      | inl _ => exact xu.elim
      | inr u =>
        cases v with
        | inl _ => exact yv.elim
        | inr v =>
          have anchored : a = root := by
            rcases duplicate_parent i j same sameParent with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
            · exact fx.symm
            · exact fx.symm
          rw [anchored] at avoid
          have matching : colour (.inr u) = colour (.inr v) := colour_walk w avoid
          rcases duplicate_parent i j same sameParent with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          · rw [colour_first u xu,colour_second v yv] at matching
            contradiction
          · rw [colour_second u xu,colour_first v yv] at matching
            contradiction

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
private theorem no_rainbow : ∀ (fuel river : Fin 9) (x y : Fin 9), Before incidenceDeletionRows river x y →
    rainbowSearch incidenceDeletionRows fuel.val ((List.finRange 9).filter (fun i => decide (i ≠ river))) x y = false := by
  unfold SourceAudit.BeforeIn
  decide

/-- The original rows exclude every full bridge, hence every half bridge. -/
theorem incidenceDeletionRows_admissible (half : Bool) (k : ℕ) : localOrderAdmissible half k incidenceDeletionRows := by
  have full : BridgeFree (Before incidenceDeletionRows) k := fun {d} _ => isEmpty_bridge_of_rainbowSearch incidenceDeletionRows no_rainbow d
  cases half
  · exact full
  · exact full.halfFree

/-- Explicit whole-component pieces retain both exclusions at all cutoffs. -/
theorem incidenceDeletionPieces_admissible (half : Bool) (k : ℕ) : localOrderAdmissible half k incidenceDeletionPieces := by
  exact localOrderAdmissible_of_incidence_components (incidenceDeletionRows_admissible half k) parent id parent_monotone
    (fun {_ _} => members _ _) (fun {_ _ _} => steps _ _ _) coherence

theorem incidenceDeletionRows_widths : let M := ∑ i, (incidenceDeletionRows i).length
    M = 10 ∧ 4*M/9 = 4 ∧ (∀ i, (incidenceDeletionRows i).Nodup) ∧
    (∀ i, (incidenceDeletionPieces i).length ≤ 4) ∧
    ∀ v, (occurrences (fun i => (incidenceDeletionRows i).toFinset) v).card ≤ 2 := by decide

private def leftCycle : originalGraph.Walk root root :=
  Walk.ofSupport [root,.inr 0,.inl 1,.inr 5,root] (by decide) (by decide)
private def rightCycle : originalGraph.Walk root root :=
  Walk.ofSupport [root,.inr 1,.inl 2,.inr 4,root] (by decide) (by decide)

/-- The overlong original row shares two edge-disjoint four-cycles. -/
theorem incidenceDeletionRows_cycle_pair :
    ¬ NoShortCyclePairAt (pathIncidenceGraph incidenceDeletionRows) 4 (Sum.inl 0) := by
  have first : leftCycle.IsCycle := by
    rw [Walk.isCycle_def,Walk.isTrail_def]
    refine ⟨by decide,?_,by decide⟩
    intro nil
    have length : leftCycle.length = 4 := by decide
    simp only [nil,Walk.length_nil] at length
    omega
  have last : rightCycle.IsCycle := by
    rw [Walk.isCycle_def,Walk.isTrail_def]
    refine ⟨by decide,?_,by decide⟩
    intro nil
    have length : rightCycle.length = 4 := by decide
    simp only [nil,Walk.length_nil] at length
    omega
  have checked : Disjoint leftCycle.edges.toFinset rightCycle.edges.toFinset := by decide
  have separate : Disjoint leftCycle.edgeSet rightCycle.edgeSet := by
    rw [Set.disjoint_left]
    intro e left right
    exact Finset.disjoint_left.mp checked (List.mem_toFinset.mpr left) (List.mem_toFinset.mpr right)
  intro condition
  have total := condition _ _ first last separate
  have lengths : leftCycle.length+rightCycle.length = 8 := by decide
  have impossible : ¬ 8 < leftCycle.length+rightCycle.length := by rw [lengths]; decide
  exact impossible total

set_option synthInstance.maxSize 1024 in
/-- Consecutive blocks at the exact original widths create a full bridge
with river `4 → 1` and detour `4 → 5 → 0 → 1`. -/
theorem incidenceDeletionRows_contiguous_split_creates_full_four : ¬ BridgeFree (Before (listRegularizedPaths incidenceDeletionRows 4 4)) 4 := by
  let W := ListVertexBlockIndex incidenceDeletionRows 4
  let I := ListBlockIndex (splitListVertices incidenceDeletionRows 4) 4
  let vertex : Fin 4 → W := ![⟨4,⟨0,by decide⟩⟩,⟨5,⟨0,by decide⟩⟩,
    ⟨0,⟨0,by decide⟩⟩,⟨1,⟨0,by decide⟩⟩]
  let arc : Fin 3 → I := ![⟨0,⟨1,by decide⟩⟩,⟨1,⟨0,by decide⟩⟩,⟨0,⟨0,by decide⟩⟩]
  let river : I := ⟨2,⟨0,by decide⟩⟩
  have injectiveV : ∀ i j, vertex i = vertex j → i = j := by decide
  have injectiveI : ∀ i j, arc i = arc j → i = j := by decide
  have parentApart : ∀ i, river.fst ≠ (arc i).fst := by decide
  have riverApart (i) : river ≠ arc i := fun same => parentApart i (congrArg Sigma.fst same)
  have riverStep : Before (listRegularizedPaths incidenceDeletionRows 4 4) river (vertex 0) (vertex (Fin.last 3)) := by
    unfold SourceAudit.BeforeIn
    decide
  have arcStep : ∀ i, Before (listRegularizedPaths incidenceDeletionRows 4 4) (arc i) (vertex i.castSucc) (vertex i.succ) := by
    unfold SourceAudit.BeforeIn
    decide
  intro free
  exact (free (k := 2) (by decide)).false
    ⟨vertex,arc,river,fun {_ _} => injectiveV _ _,fun {_ _} => injectiveI _ _,riverApart,riverStep,arcStep⟩

private abbrev Copy := ListVertexBlockIndex incidenceDeletionRows 4

private def firstCopy (v : Fin 9) : Copy := ⟨v,⟨0,Nat.zero_lt_succ _⟩⟩

private theorem firstCopy_on_row : ∀ (i v : Fin 9), v ∈ incidenceDeletionRows i →
    firstCopy v ∈ splitListVertices incidenceDeletionRows 4 i := by decide

/-- The cycle-pair test also fails at the overlong row of the actual
degree-copied graph. All used vertices stay in the first degree block. -/
theorem incidenceDeletionRows_copied_cycle_pair :
    4 < (splitListVertices incidenceDeletionRows 4 (0 : Fin 9)).length ∧
      ¬ NoShortCyclePairAt (pathIncidenceGraph (splitListVertices incidenceDeletionRows 4)) 4 (Sum.inl 0) := by
  refine ⟨by decide,?_⟩
  let f := pathIncidenceGraph_hom (id : Fin 9 → Fin 9) firstCopy (fun {i v} => firstCopy_on_row i v)
  have injective : Function.Injective f := by
    apply Sum.map_injective.mpr
    exact ⟨Function.injective_id,fun {_ _} equal => congrArg Sigma.fst equal⟩
  intro condition
  exact incidenceDeletionRows_cycle_pair
    (NoShortCyclePairAt.of_edge_injective_hom f condition (fun {_ _} _ _ eq => Sym2.map.injective injective eq))

private theorem colour_class_size : ∀ (x : Fin 9),
    ((incidenceDeletionRows 0).toFinset.filter fun y => colour (.inr y) = colour (.inr x)).card ≤ 4 := by decide

private theorem other_rows_short : ∀ (i : Fin 9), i ≠ 0 → (incidenceDeletionRows i).length ≤ 4 := by decide

/-- All original deleted-row groups fit width four, including the one
row where a consecutive split can create a bridge. -/
theorem incidenceDeletionRows_group_room (i : Fin 9) (x : Fin 9) :
    (incidenceRowDeletionGroup incidenceDeletionRows i x).card ≤ 4 := by
  by_cases long : i = 0
  · subst i
    refine (card_le_card (t := (incidenceDeletionRows 0).toFinset.filter
      (fun y => colour (.inr y) = colour (.inr x))) ?_).trans (colour_class_size x)
    intro y member
    obtain ⟨on,w,avoids⟩ := mem_incidenceRowDeletionGroup.mp member
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr on,(colour_walk w avoids).symm⟩
  · have subset : incidenceRowDeletionGroup incidenceDeletionRows i x ⊆ (incidenceDeletionRows i).toFinset :=
      fun y member => List.mem_toFinset.mpr (mem_incidenceRowDeletionGroup.mp member).1
    exact (card_le_card subset).trans ((List.toFinset_card_le _).trans (other_rows_short i long))

/-- The original component bound supplies an indexed full witness with
both original budgets and all four original-average caps. -/
theorem incidenceDeletionRows_frozen (k : ℕ) :
    ∃ n' ≤ 9, ∃ p' ≤ 9, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) k ∧
      10 ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 10 ∧ frozenListCaps 9 9 10 clean := by
  have mass := incidenceDeletionRows_widths.1
  have dense : 9 ≤ ∑ i, (incidenceDeletionRows i).length := by rw [mass]; decide
  have result := regularization_list_frozen_full_of_original_incidence_row_deletion_group_room incidenceDeletionRows
    incidenceDeletionRows_widths.2.2.1 (incidenceDeletionRows_admissible false k) (by decide) (by decide) dense dense
    (by dsimp only; rw [mass]; intro i x _; exact incidenceDeletionRows_group_room i x)
  simpa only [mass] using result

end OnlineReachabilityPreservers.SourceAudit
