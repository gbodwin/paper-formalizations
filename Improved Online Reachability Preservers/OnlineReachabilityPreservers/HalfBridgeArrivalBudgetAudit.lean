import OnlineReachabilityPreservers.HalfBridgeArrivalOrderAudit

/-! The small-loss criterion need not hold even at cutoff four. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset
open scoped Sigma.Lex

/-- The four midpoint rows with eight additional empty labels. -/
def arrivalBudgetRows (i : Fin 12) : List (Fin 7) :=
  if h : i.val < 4 then splitOrderExample ⟨i.val,h⟩ else []

theorem arrivalBudgetRows_parameters :
    (∀ i, (arrivalBudgetRows i).Nodup) ∧ (∑ i, (arrivalBudgetRows i).length) = 14 := by
  decide +kernel

/-- The extra labels leave the original half-four exclusion unchanged. -/
theorem arrivalBudgetRows_halfFree : HalfBridgeFree (BeforeIn arrivalBudgetRows) 4 := by
  intro d atMost b earlier
  have active {i u v} (step : BeforeIn arrivalBudgetRows i u v) : i.val < 4 := by
    by_contra above
    simpa [arrivalBudgetRows,above] using step.1
  let row (i : Fin 12) (h : i.val < 4) : Fin 4 := ⟨i.val,h⟩
  have project {i u v} (step : BeforeIn arrivalBudgetRows i u v) :
      BeforeIn splitOrderExample (row i (active step)) u v := by
    simpa only [BeforeIn,arrivalBudgetRows,dite_eq_left (active step)] using step
  let old : Bridge (BeforeIn splitOrderExample) d := {
    vertex := b.vertex
    arc := fun i => row (b.arc i) (active (b.arcStep i))
    river := row b.river (active b.riverStep)
    distinctVertices := b.distinctVertices
    distinctArcs := fun {_ _} eq => b.distinctArcs (Fin.ext (congrArg (fun x : Fin 4 => x.val) eq))
    river_ne_arc := fun i eq => b.river_ne_arc i (Fin.ext (congrArg (fun x : Fin 4 => x.val) eq))
    riverStep := project b.riverStep
    arcStep := fun i => project (b.arcStep i) }
  exact splitOrderExample_halfFree atMost old earlier

abbrev ArrivalBudgetVertex := ListVertexBlockIndex arrivalBudgetRows 8
abbrev ArrivalBudgetPiece := ListBlockIndex (splitListVertices arrivalBudgetRows 8) 4

/-- The original widths are eight for degree and four for length. -/
def arrivalBudgetPieces : ArrivalBudgetPiece → List ArrivalBudgetVertex :=
  listRegularizedPaths arrivalBudgetRows 8 4

private def budgetFirst (i : Fin 12) : ArrivalBudgetPiece := ⟨i,⟨0,Nat.succ_pos _⟩⟩
private def budgetSecond : ArrivalBudgetPiece := ⟨(2 : Fin 12),⟨1,by decide +kernel⟩⟩
private def budgetCopy (v : Fin 7) : ArrivalBudgetVertex := ⟨v,⟨0,Nat.succ_pos _⟩⟩

local instance budgetBeforeDecidable (i : ArrivalBudgetPiece) (u v : ArrivalBudgetVertex) :
    Decidable (BeforeIn arrivalBudgetPieces i u v) := by
  unfold BeforeIn
  infer_instance

private def budgetBridgeThree : Bridge (BeforeIn arrivalBudgetPieces) 1 := by
  let vertex : Fin 3 → ArrivalBudgetVertex := ![budgetCopy 2,budgetCopy 5,budgetCopy 4]
  let arc : Fin 2 → ArrivalBudgetPiece := ![budgetFirst 1,budgetFirst 3]
  have vertexDistinct : ∀ i j, vertex i = vertex j → i = j := by decide +kernel
  have arcDistinct : ∀ i j, arc i = arc j → i = j := by decide +kernel
  have fresh : ∀ i, budgetFirst 2 ≠ arc i := by decide +kernel
  have river : BeforeIn arrivalBudgetPieces (budgetFirst 2) (vertex 0) (vertex (Fin.last 2)) := by decide +kernel
  have links : ∀ i, BeforeIn arrivalBudgetPieces (arc i) (vertex i.castSucc) (vertex i.succ) := by decide +kernel
  exact ⟨vertex,arc,budgetFirst 2,fun {_ _} => vertexDistinct _ _,fun {_ _} => arcDistinct _ _,fresh,river,links⟩

private def budgetBridgeFour : Bridge (BeforeIn arrivalBudgetPieces) 2 := by
  let vertex : Fin 4 → ArrivalBudgetVertex := ![budgetCopy 3,budgetCopy 1,budgetCopy 0,budgetCopy 4]
  let arc : Fin 3 → ArrivalBudgetPiece := ![budgetSecond,budgetFirst 0,budgetFirst 2]
  have vertexDistinct : ∀ i j, vertex i = vertex j → i = j := by decide +kernel
  have arcDistinct : ∀ i j, arc i = arc j → i = j := by decide +kernel
  have fresh : ∀ i, budgetFirst 3 ≠ arc i := by decide +kernel
  have river : BeforeIn arrivalBudgetPieces (budgetFirst 3) (vertex 0) (vertex (Fin.last 3)) := by decide +kernel
  have links : ∀ i, BeforeIn arrivalBudgetPieces (arc i) (vertex i.castSucc) (vertex i.succ) := by decide +kernel
  exact ⟨vertex,arc,budgetFirst 3,fun {_ _} => vertexDistinct _ _,fun {_ _} => arcDistinct _ _,fresh,river,links⟩

private theorem arrivalBudgetPieces_not_acyclic {k : ℕ} (includesFour : 4 ≤ k) :
    ¬ IsDAG (halfBridgeArrivalGraph arrivalBudgetPieces k) := by
  intro acyclic
  have first : Edge (halfBridgeArrivalGraph arrivalBudgetPieces k) (budgetFirst 2) (budgetFirst 3) :=
    halfBridgeArrivalGraph_edge.mpr ⟨1,by omega,budgetBridgeThree,rfl,rfl⟩
  have reverse : Edge (halfBridgeArrivalGraph arrivalBudgetPieces k) (budgetFirst 3) (budgetFirst 2) :=
    halfBridgeArrivalGraph_edge.mpr ⟨2,includesFour,budgetBridgeFour,rfl,rfl⟩
  exact acyclic first (.single reverse)

/-- The original-width pieces in this indexed example cannot be repaired
by deleting at most one eighteenth of the input mass, even with reordering. -/
theorem arrivalBudgetRows_no_small_deletion_repair {k : ℕ} (includesFour : 4 ≤ k) :
    let M := ∑ i, (arrivalBudgetRows i).length
    let D := 4*M/7
    let L := 4*M/12
    let pieces := listRegularizedPaths arrivalBudgetRows D L
    ∀ kept : ListBlockIndex (splitListVertices arrivalBudgetRows D) L →
        List (ListVertexBlockIndex arrivalBudgetRows D),
      (∀ i, (kept i).Sublist (pieces i)) →
      18*(M-(∑ i, (kept i).length)) ≤ M → ¬ IsDAG (halfBridgeArrivalGraph kept k) := by
  dsimp only
  rw [arrivalBudgetRows_parameters.2]
  change ∀ kept : ArrivalBudgetPiece → List ArrivalBudgetVertex,
    (∀ i, (kept i).Sublist (arrivalBudgetPieces i)) →
    18*(14-(∑ i, (kept i).length)) ≤ 14 → ¬ IsDAG (halfBridgeArrivalGraph kept k)
  intro kept sub loss
  have mass : (∑ i, (arrivalBudgetPieces i).length) = 14 := by decide +kernel
  have same : kept = arrivalBudgetPieces := by
    funext i
    apply (sub i).eq_of_length_le
    by_contra! less
    have strictly : (∑ j, (kept j).length) < ∑ j, (arrivalBudgetPieces j).length :=
      sum_lt_sum (fun j _ => (sub j).length_le) ⟨i,mem_univ _,less⟩
    omega
  subst kept
  exact arrivalBudgetPieces_not_acyclic includesFour

end OnlineReachabilityPreservers.SourceAudit
