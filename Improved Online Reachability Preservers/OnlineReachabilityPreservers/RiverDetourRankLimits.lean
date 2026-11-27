import OnlineReachabilityPreservers.RiverDetourComponents
import Mathlib.Data.Fin.VecNotation

/-! A valid split can have two pieces of one parent in one rank component. -/

namespace OnlineReachabilityPreservers

open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- The long first row contains the two opposite sides of a directed
eight-cycle. At width two its two pieces complete the cycle. -/
def rankCriterionCycleRows : Fin 7 → List (Fin 8) :=
  ![[0,1,4,5],[1,2],[2,3],[3,4],[5,6],[6,7],[7,0]]

theorem rankCriterionCycleRows_simple : ∀ i, (rankCriterionCycleRows i).Nodup := by decide

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem rankCriterionCycle_no_short_detour :
    ∀ (i : Fin 7) (x y : Fin 8), Before rankCriterionCycleRows i x y →
      x ∉ reachIn (listPiecePrecedenceGraph (fun j => if j = i then [] else rankCriterionCycleRows j)) y 2 := by
  unfold SourceAudit.BeforeIn
  decide +kernel

/-- The input excludes full bridges of size at most three. -/
theorem rankCriterionCycle_original_full_free : BridgeFree (Before rankCriterionCycleRows) 3 := by
  intro d small
  refine ⟨fun b => ?_⟩
  let G := listPiecePrecedenceGraph (fun j => if j = b.river then [] else rankCriterionCycleRows j)
  have edges (j : Fin (d+1)) : Edge G (b.vertex j.castSucc) (b.vertex j.succ) := by
    apply listPiecePrecedenceGraph_edge.mpr
    exact ⟨b.arc j,by simpa only [SourceAudit.BeforeIn,ite_eq_right (b.river_ne_arc j).symm] using b.arcStep j⟩
  have path : b.vertex 0 ∈ reachIn G (b.vertex (Fin.last (d+1))) (d+1) := reachIn_of_fin_steps b.vertex edges
  exact rankCriterionCycle_no_short_detour b.river _ _ b.riverStep
    (monotone_nat_of_le_succ (reachIn_subset_succ G _) (show d+1 ≤ 2 by omega) path)

abbrev RankCriterionCyclePiece := ListBlockIndex rankCriterionCycleRows 2

/-- The standard width-two path blocks of the example. -/
def rankCriterionCyclePieces := splitListPaths rankCriterionCycleRows 2

private def firstPiece (i : Fin 7) : RankCriterionCyclePiece := ⟨i,⟨0,Nat.succ_pos _⟩⟩
private def secondPiece : RankCriterionCyclePiece := ⟨0,⟨1,by decide⟩⟩

private def cyclePieceOwner (x : Fin 8) : RankCriterionCyclePiece :=
  ![firstPiece 0,firstPiece 1,firstPiece 2,firstPiece 3,secondPiece,firstPiece 4,firstPiece 5,firstPiece 6] x

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
private theorem cyclePieceOwner_of_step :
    ∀ (i : RankCriterionCyclePiece) (x y : Fin 8), Before rankCriterionCyclePieces i x y →
      i = cyclePieceOwner x := by
  unfold SourceAudit.BeforeIn
  decide +kernel

private theorem cyclePieceOwner_step :
    ∀ x : Fin 8, Before rankCriterionCyclePieces (cyclePieceOwner x) x (x+1) := by
  unfold SourceAudit.BeforeIn
  decide +kernel

/-- Each vertex starts a strict comparison in only one piece. The first
arc and the river of a bridge would need different pieces. -/
theorem rankCriterionCycle_pieces_full_free (k : ℕ) : BridgeFree (Before rankCriterionCyclePieces) k := by
  intro d _
  refine ⟨fun b => ?_⟩
  exact b.river_ne_arc 0 ((cyclePieceOwner_of_step _ _ _ b.riverStep).trans
    (cyclePieceOwner_of_step _ _ _ (b.arcStep 0)).symm)

/-- The two pieces of row zero share a component, so the rank condition
fails on these pieces for every cutoff. -/
theorem rankCriterionCycle_component_test_fails (k : ℕ) :
    ¬ (∀ ⦃i j : RankCriterionCyclePiece⦄ ⦃x y : Fin 8⦄, i ≠ j → i.fst = j.fst →
      x ∈ rankCriterionCyclePieces i → y ∈ rankCriterionCyclePieces j →
      ¬ SameComponent (riverDetourConstraintGraph rankCriterionCyclePieces k) x y) := by
  let G := riverDetourConstraintGraph rankCriterionCyclePieces k
  have step (x : Fin 8) : Edge G x (x+1) := riverDetourConstraintGraph_edge.mpr (Or.inl ⟨_,cyclePieceOwner_step x⟩)
  have forward : Reach G (0 : Fin 8) 4 := (((Relation.ReflTransGen.single (step 0)).tail (step 1)).tail (step 2)).tail (step 3)
  have backward : Reach G (4 : Fin 8) 0 := (((Relation.ReflTransGen.single (step 4)).tail (step 5)).tail (step 6)).tail (step 7)
  have left : (0 : Fin 8) ∈ rankCriterionCyclePieces (firstPiece 0) := by decide
  have right : (4 : Fin 8) ∈ rankCriterionCyclePieces secondPiece := by decide
  have different : firstPiece 0 ≠ secondPiece := by
    intro same
    have slots := congrArg (fun i : RankCriterionCyclePiece => i.snd.val) same
    change (0 : ℕ) = 1 at slots
    omega
  intro apart
  exact apart different rfl left right ⟨forward,backward⟩

end OnlineReachabilityPreservers
