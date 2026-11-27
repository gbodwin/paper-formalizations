import OnlineReachabilityPreservers.HalfBridgeArrivalOrder
import OnlineReachabilityPreservers.HalfFourSplitOrderAudit

/-! Test arrival constraints on repairable and unrepairable width splits. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset
open scoped Sigma.Lex

private def reorderActiveRows : Fin 3 → List (Fin 6) :=
  ![[0,4,5,1,2,3],[3,0],[2,1]]

/-- The usual nested split example with two extra vertices and seven
empty row labels, so its original factor-four path width is four. -/
def widthReorderRows (i : Fin 10) : List (Fin 6) :=
  if h : i.val < 3 then reorderActiveRows ⟨i.val,h⟩ else []

theorem widthReorderRows_parameters :
    (∀ i, (widthReorderRows i).Nodup) ∧ (∑ i, (widthReorderRows i).length) = 10 := by
  decide +kernel

private theorem activeRows_noTwo :
    ∀ (r a : Fin 3) (x y : Fin 6), r ≠ a →
      BeforeIn reorderActiveRows r x y → BeforeIn reorderActiveRows a x y → False := by
  unfold BeforeIn
  decide +kernel

set_option maxRecDepth 16384 in
set_option synthInstance.maxSize 1024 in
private theorem activeRows_noThree :
    ∀ (r a b : Fin 3) (x y z : Fin 6), r ≠ a → r ≠ b → a ≠ b →
      BeforeIn reorderActiveRows r x z → BeforeIn reorderActiveRows a x y →
      BeforeIn reorderActiveRows b y z → False := by
  unfold BeforeIn
  decide +kernel

/-- The original simple family excludes full bridges at every cutoff. -/
theorem widthReorderRows_full_free (k : ℕ) : BridgeFree (BeforeIn widthReorderRows) k := by
  intro d small
  refine ⟨fun b => ?_⟩
  have active {i x y} (step : BeforeIn widthReorderRows i x y) : i.val < 3 := by
    by_contra large
    simpa [widthReorderRows,large] using step.1
  have compare {i x y} (step : BeforeIn widthReorderRows i x y) :
      BeforeIn reorderActiveRows ⟨i.val,active step⟩ x y := by
    have inside := active step
    simpa only [BeforeIn,widthReorderRows,dite_eq_left inside] using step
  let beforeSplit : Bridge (BeforeIn reorderActiveRows) d := {
    vertex := b.vertex
    arc := fun i => ⟨(b.arc i).val,active (b.arcStep i)⟩
    river := ⟨b.river.val,active b.riverStep⟩
    distinctVertices := b.distinctVertices
    distinctArcs := by
      intro i j same
      exact b.distinctArcs (Fin.ext (congrArg (fun x : Fin 3 => x.val) same))
    river_ne_arc := by
      intro i same
      exact b.river_ne_arc i (Fin.ext (congrArg (fun x : Fin 3 => x.val) same))
    riverStep := compare b.riverStep
    arcStep := fun i => compare (b.arcStep i) }
  have count := bridge_path_count_le beforeSplit
  rw [Fintype.card_fin] at count
  have fits : d ≤ 1 := by omega
  interval_cases d
  · exact activeRows_noTwo _ _ _ _ (beforeSplit.river_ne_arc 0)
      beforeSplit.riverStep (beforeSplit.arcStep 0)
  · exact activeRows_noThree _ _ _ _ _ _ (beforeSplit.river_ne_arc 0) (beforeSplit.river_ne_arc 1)
      (fun same => (by decide : (0 : Fin 2) ≠ 1) (beforeSplit.distinctArcs same))
      beforeSplit.riverStep (beforeSplit.arcStep 0) (beforeSplit.arcStep 1)

abbrev WidthReorderVertex := ListVertexBlockIndex widthReorderRows 6
abbrev WidthReorderPiece := ListBlockIndex (splitListVertices widthReorderRows 6) 4

/-- The mass is ten, so the original degree and length widths are six and four. -/
def widthReorderPieces : WidthReorderPiece → List WidthReorderVertex :=
  listRegularizedPaths widthReorderRows 6 4

private def pieceAtStart (i : Fin 10) : WidthReorderPiece := ⟨i,⟨0,Nat.succ_pos _⟩⟩

def widthReorderEarlyPiece : WidthReorderPiece := pieceAtStart 0
def widthReorderRiver : WidthReorderPiece := pieceAtStart 2

private def widthReorderLatePiece : WidthReorderPiece := ⟨(0 : Fin 10),⟨1,by decide +kernel⟩⟩
private def widthReorderMiddlePiece : WidthReorderPiece := pieceAtStart 1
private def widthReorderCorner (v : Fin 6) : WidthReorderVertex := ⟨v,⟨0,Nat.succ_pos _⟩⟩

local instance widthReorderBeforeDecidable (i : WidthReorderPiece) (x y : WidthReorderVertex) :
    Decidable (BeforeIn widthReorderPieces i x y) := by
  unfold BeforeIn
  infer_instance

private def outgoingPieces (v : WidthReorderVertex) : Finset WidthReorderPiece :=
  univ.filter (fun i => ∃ w : WidthReorderVertex, BeforeIn widthReorderPieces i v w)

private def incomingPieces (v : WidthReorderVertex) : Finset WidthReorderPiece :=
  univ.filter (fun i => ∃ w : WidthReorderVertex, BeforeIn widthReorderPieces i w v)

set_option maxRecDepth 16384 in
private theorem outbound_unique :
    ∀ v : WidthReorderVertex, v.fst ≠ 2 → (outgoingPieces v).card ≤ 1 := by
  decide +kernel

set_option maxRecDepth 16384 in
private theorem inbound_three :
    ∀ v : WidthReorderVertex, v.fst = 3 → (incomingPieces v).card ≤ 1 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
set_option synthInstance.maxSize 1024 in
private theorem possible_river_from_two :
    ∀ (r : WidthReorderPiece) (u v : WidthReorderVertex), u.fst = 2 →
      BeforeIn widthReorderPieces r u v → (r = widthReorderRiver ∧ v.fst = 1) ∨ v.fst = 3 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1200000 in
set_option synthInstance.maxSize 1024 in
private theorem possible_final_arc_to_one :
    ∀ (a : WidthReorderPiece) (u v : WidthReorderVertex), v.fst = 1 →
      BeforeIn widthReorderPieces a u v → a = widthReorderRiver ∨ a = widthReorderEarlyPiece := by
  decide +kernel


private theorem pair_not_in_one_piece {a b : WidthReorderPiece} {s : Finset WidthReorderPiece}
    (different : a ≠ b) (first : a ∈ s) (last : b ∈ s) (single : s.card ≤ 1) : False := by
  have both : ({a,b} : Finset WidthReorderPiece) ⊆ s := by
    intro i on
    simp only [mem_insert,mem_singleton] at on
    exact on.elim (fun eq => eq.symm ▸ first) (fun eq => eq.symm ▸ last)
  have size := card_le_card both
  simp [different] at size
  omega

private theorem widthReorder_bridge_labels {d : ℕ} (b : Bridge (BeforeIn widthReorderPieces) d) :
    b.river = widthReorderRiver ∧ b.arc (Fin.last d) = widthReorderEarlyPiece := by
  have first : (b.vertex 0).fst = 2 := by
    by_contra other
    have river : b.river ∈ outgoingPieces (b.vertex 0) :=
      mem_filter.mpr ⟨mem_univ _,b.vertex (Fin.last (d+1)),b.riverStep⟩
    have arc : b.arc 0 ∈ outgoingPieces (b.vertex 0) :=
      mem_filter.mpr ⟨mem_univ _,b.vertex (Fin.succ 0),b.arcStep 0⟩
    exact pair_not_in_one_piece (b.river_ne_arc 0) river arc (outbound_unique _ other)
  rcases possible_river_from_two b.river (b.vertex 0) (b.vertex (Fin.last (d+1))) first b.riverStep with
    ⟨owner,finish⟩ | finish
  · refine ⟨owner,?_⟩
    rcases possible_final_arc_to_one (b.arc (Fin.last d)) (b.vertex (Fin.last d).castSucc)
      (b.vertex (Fin.last (d+1))) finish (b.arcStep (Fin.last d)) with same | head
    · exact (b.river_ne_arc (Fin.last d) (owner.trans same.symm)).elim
    · exact head
  · have river : b.river ∈ incomingPieces (b.vertex (Fin.last (d+1))) :=
      mem_filter.mpr ⟨mem_univ _,b.vertex 0,b.riverStep⟩
    have arc : b.arc (Fin.last d) ∈ incomingPieces (b.vertex (Fin.last (d+1))) :=
      mem_filter.mpr ⟨mem_univ _,b.vertex (Fin.last d).castSucc,b.arcStep (Fin.last d)⟩
    exact (pair_not_in_one_piece (b.river_ne_arc (Fin.last d)) river arc (inbound_three _ finish)).elim

private def widthReorderBridge : Bridge (BeforeIn widthReorderPieces) 2 := by
  let vertex : Fin 4 → WidthReorderVertex := ![widthReorderCorner 2,widthReorderCorner 3,
    widthReorderCorner 0,widthReorderCorner 1]
  let arc : Fin 3 → WidthReorderPiece := ![widthReorderLatePiece,widthReorderMiddlePiece,widthReorderEarlyPiece]
  have simple : ∀ i j, vertex i = vertex j → i = j := by decide +kernel
  have distinct : ∀ i j, arc i = arc j → i = j := by decide +kernel
  have river : ∀ i, widthReorderRiver ≠ arc i := by decide +kernel
  have compare : BeforeIn widthReorderPieces widthReorderRiver (vertex 0) (vertex (Fin.last 3)) := by
    decide +kernel
  have steps : ∀ i, BeforeIn widthReorderPieces (arc i) (vertex i.castSucc) (vertex i.succ) := by
    decide +kernel
  exact ⟨vertex,arc,widthReorderRiver,fun {_ _} => simple _ _,fun {_ _} => distinct _ _,river,compare,steps⟩

/-- The pieces in the prescribed order include a half-bridge of size four. -/
theorem widthReorderPieces_not_halfFree_four : ¬ HalfBridgeFree (BeforeIn widthReorderPieces) 4 := by
  intro free
  have earlier : widthReorderEarlyPiece < widthReorderRiver := by decide +kernel
  exact free (k := 2) (by decide) widthReorderBridge earlier

/-- At cutoff four or more, there is exactly one required arrival comparison. -/
theorem widthReorderArrival_exact {k : ℕ} (includesFour : 4 ≤ k) :
    halfBridgeArrivalGraph widthReorderPieces k = {(widthReorderRiver,widthReorderEarlyPiece)} := by
  ext edge
  obtain ⟨r,a⟩ := edge
  change Edge (halfBridgeArrivalGraph widthReorderPieces k) r a ↔ (r,a) ∈ _
  rw [halfBridgeArrivalGraph_edge]
  constructor
  · rintro ⟨d,_,b,rfl,rfl⟩
    obtain ⟨river,last⟩ := widthReorder_bridge_labels b
    simp [river,last]
  · intro found
    have equal := mem_singleton.mp found
    injection equal with river last
    subst r
    subst a
    exact ⟨2,includesFour,widthReorderBridge,rfl,rfl⟩

/-- The arrival constraints are acyclic at every cutoff. -/
theorem widthReorderArrival_acyclic (k : ℕ) : IsDAG (halfBridgeArrivalGraph widthReorderPieces k) := by
  let G := halfBridgeArrivalGraph widthReorderPieces k
  have only {r a} (edge : Edge G r a) : r = widthReorderRiver ∧ a = widthReorderEarlyPiece := by
    obtain ⟨d,_,b,rfl,rfl⟩ := halfBridgeArrivalGraph_edge.mp edge
    exact widthReorder_bridge_labels b
  have apart : widthReorderEarlyPiece ≠ widthReorderRiver := by decide +kernel
  have noLeave {a} (route : Reach G widthReorderEarlyPiece a) : a = widthReorderEarlyPiece := by
    induction route with
    | refl => rfl
    | tail _ edge previous => exact (apart (previous.symm.trans (only edge).1)).elim
  intro r a edge back
  obtain ⟨rfl,rfl⟩ := only edge
  exact apart (noLeave back).symm

/-- Reordering the actual two-width pieces gives a frozen witness for
every cutoff of the padded example, with both budgets and all four caps. -/
theorem widthReorder_frozen_witness (k : ℕ) :
    ∃ n' ≤ 6, ∃ p' ≤ 10, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (BeforeIn clean) k ∧
      10 ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 10 ∧ frozenListCaps 6 10 10 clean := by
  have mass := widthReorderRows_parameters.2
  have enough : 6 ≤ ∑ i, (widthReorderRows i).length := by rw [mass]; decide
  have long : 10 ≤ ∑ i, (widthReorderRows i).length := mass.ge
  have acyclic :
      let M := ∑ i, (widthReorderRows i).length
      IsDAG (halfBridgeArrivalGraph (listRegularizedPaths widthReorderRows (4*M/6) (4*M/10)) k) := by
    dsimp only
    rw [mass]
    exact widthReorderArrival_acyclic k
  have witness := regularization_list_frozen_half_of_acyclic_arrival_constraints (k := k)
    widthReorderRows widthReorderRows_parameters.1 acyclic (by decide) (by decide) enough long
  simpa only [mass] using witness

/-- The earlier midpoint counterexample has cyclic arrival constraints. -/
theorem splitOrderExampleArrival_not_acyclic : ¬ IsDAG (halfBridgeArrivalGraph splitOrderExampleAfter 4) := by
  intro acyclic
  obtain ⟨arrival,free⟩ := (exists_halfBridgeFree_reordering_iff splitOrderExampleAfter 4).mpr acyclic
  exact splitOrderExample_no_reordering arrival.symm free

end OnlineReachabilityPreservers.SourceAudit
