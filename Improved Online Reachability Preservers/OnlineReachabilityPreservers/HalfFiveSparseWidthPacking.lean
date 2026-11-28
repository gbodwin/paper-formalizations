import OnlineReachabilityPreservers.DegreeTwoBlockOrder
import OnlineReachabilityPreservers.HalfFiveSparseOppositeIncidences
import OnlineReachabilityPreservers.IncidenceWidthOrders

/-! Use the sparse local partner graphs to preserve half-five under both width splits. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

private def packingIndex {A : Type*} [DecidableEq A] (list : List A) (x : A) : ℕ := list.idxOf x

private theorem index_map_of_injective {A B : Type*} [DecidableEq A] [BEq B] [LawfulBEq B] (f : A → B)
    (injective : Function.Injective f) (list : List A) (x : A) :
    (list.map f).idxOf (f x) = packingIndex list x := by
  unfold packingIndex
  induction list with
  | nil => rfl
  | cons a list ih =>
    by_cases same : a = x
    · subst a
      simp
    · simp [same,injective.ne same,ih]

private structure HalfFivePackingPlan {n p : ℕ} (paths : Fin p → List (Fin n)) (D L : ℕ) where
  rowOrder : (x : Fin n) → List (commonVertexRows paths x)
  vertexOrder : (i : Fin p) → List (paths i).toFinset
  rowOrderSimple : ∀ x, (rowOrder x).Nodup
  vertexOrderSimple : ∀ i, (vertexOrder i).Nodup
  allRows : ∀ x (i : commonVertexRows paths x), i ∈ rowOrder x
  allVertices : ∀ i (x : (paths i).toFinset), x ∈ vertexOrder i
  rowCuts : (x : Fin n) → Finset (commonVertexRows paths x)
  vertexCuts : (i : Fin p) → Finset (paths i).toFinset
  rowCharge : ∀ x, (rowCuts x).card ≤ 2*(((commonVertexRows paths x).card-1)/D)
  vertexCharge : ∀ i, (vertexCuts i).card ≤ 2*(((paths i).toFinset.card-1)/L)
  sameRowBlock : ∀ x ⦃i j⦄, (commonRowPartnerGraph paths x).Adj i j →
    i ∉ rowCuts x → j ∉ rowCuts x → packingIndex (rowOrder x) i/D = packingIndex (rowOrder x) j/D
  sameVertexBlock : ∀ i ⦃x y⦄, (commonColumnPartnerGraph paths i).Adj x y →
    x ∉ vertexCuts i → y ∉ vertexCuts i → packingIndex (vertexOrder i) x/L = packingIndex (vertexOrder i) y/L

open scoped Classical in
private theorem exists_halfFivePackingPlan {n p D L : ℕ} (paths : Fin p → List (Fin n))
    (degreeRows : ∀ x (i : commonVertexRows paths x), (commonRowPartnerGraph paths x).degree i ≤ 2)
    (degreeVertices : ∀ i (x : (paths i).toFinset), (commonColumnPartnerGraph paths i).degree x ≤ 2)
    (Dpos : 0 < D) (Lpos : 0 < L) : Nonempty (HalfFivePackingPlan paths D L) := by
  classical
  have chooseRows (x : Fin n) := degreeTwo_block_order (commonRowPartnerGraph paths x) (degreeRows x) D Dpos
  have chooseVertices (i : Fin p) := degreeTwo_block_order (commonColumnPartnerGraph paths i) (degreeVertices i) L Lpos
  choose rowOrder rowSimple allRows rowCuts rowCharge rowBlocks using chooseRows
  choose vertexOrder vertexSimple allVertices vertexCuts vertexCharge vertexBlocks using chooseVertices
  exact ⟨⟨rowOrder,vertexOrder,rowSimple,vertexSimple,allRows,allVertices,rowCuts,vertexCuts,
    fun x => by simpa only [Fintype.card_coe] using rowCharge x,
    fun i => by simpa only [Fintype.card_coe] using vertexCharge i,
    fun x _ _ adjacent left right => rowBlocks x adjacent left right,
    fun i _ _ adjacent left right => vertexBlocks i adjacent left right⟩⟩

namespace HalfFivePackingPlan

variable {n p D L : ℕ} {paths : Fin p → List (Fin n)} (plan : HalfFivePackingPlan paths D L)

private def orders : IncidenceWidthOrders paths where
  rowsAt x := (plan.rowOrder x).map Subtype.val
  verticesOn i := (plan.vertexOrder i).map Subtype.val
  rowsSimple x := (plan.rowOrderSimple x).map Subtype.val_injective
  verticesSimple i := (plan.vertexOrderSimple i).map Subtype.val_injective
  rowsMem x i := by
    constructor
    · intro on
      obtain ⟨label,_,rfl⟩ := List.mem_map.mp on
      exact mem_commonVertexRows.mp label.property
    · intro on
      let label : commonVertexRows paths x := ⟨i,mem_commonVertexRows.mpr on⟩
      exact List.mem_map.mpr ⟨label,plan.allRows x label,rfl⟩
  verticesMem i x := by
    constructor
    · intro on
      obtain ⟨label,_,rfl⟩ := List.mem_map.mp on
      exact List.mem_toFinset.mp label.property
    · intro on
      let label : (paths i).toFinset := ⟨x,List.mem_toFinset.mpr on⟩
      exact List.mem_map.mpr ⟨label,plan.allVertices i label,rfl⟩

private def vertexMark (x : Fin n) : commonVertexRows paths x ↪ Fin p × Fin n :=
  ⟨fun i => (i.val,x),fun _ _ equal => Subtype.ext (congrArg Prod.fst equal)⟩

private def rowMark (i : Fin p) : (paths i).toFinset ↪ Fin p × Fin n :=
  ⟨fun x => (i,x.val),fun _ _ equal => Subtype.ext (congrArg Prod.snd equal)⟩

private def marks : Finset (Fin p × Fin n) :=
  (univ.biUnion fun x => (plan.rowCuts x).map (vertexMark x)) ∪
    (univ.biUnion fun i => (plan.vertexCuts i).map (rowMark i))

private theorem marked_at_vertex {x : Fin n} {i : commonVertexRows paths x} (cut : i ∈ plan.rowCuts x) :
    (i.val,x) ∈ plan.marks :=
  mem_union_left _ (mem_biUnion.mpr ⟨x,mem_univ _,mem_map.mpr ⟨i,cut,rfl⟩⟩)

private theorem marked_on_row {i : Fin p} {x : (paths i).toFinset} (cut : x ∈ plan.vertexCuts i) :
    (i,x.val) ∈ plan.marks :=
  mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,mem_map.mpr ⟨x,cut,rfl⟩⟩)

private theorem sum_width_fees {A : Type*} [Fintype A] (weights fees : A → ℕ) {w : ℕ} (positive : 0 < w)
    (fee : ∀ a, fees a ≤ 2*((weights a-1)/w)) :
    (∑ a, fees a) ≤ 2*((∑ a, weights a)/w) := by
  have quotients : (∑ a, weights a/w) ≤ (∑ a, weights a)/w := by
    apply (Nat.le_div_iff_mul_le positive).mpr
    rw [sum_mul]
    exact sum_le_sum fun a _ => Nat.div_mul_le_self (weights a) w
  calc
    _ ≤ ∑ a, 2*(weights a/w) := sum_le_sum fun a _ =>
      (fee a).trans (Nat.mul_le_mul_left _ (Nat.div_le_div_right (Nat.sub_le _ _)))
    _ = 2*(∑ a, weights a/w) := (mul_sum _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ quotients

private theorem marks_card (simple : ∀ i, (paths i).Nodup) (Dpos : 0 < D) (Lpos : 0 < L) :
    plan.marks.card ≤ 2*((∑ i, (paths i).length)/D)+2*((∑ i, (paths i).length)/L) := by
  let fromVertices := univ.biUnion fun x => (plan.rowCuts x).map (vertexMark x)
  let fromRows := univ.biUnion fun i => (plan.vertexCuts i).map (rowMark i)
  have left : fromVertices.card ≤ ∑ x, (plan.rowCuts x).card := by
    apply card_biUnion_le.trans
    simp only [card_map,le_rfl]
  have right : fromRows.card ≤ ∑ i, (plan.vertexCuts i).card := by
    apply card_biUnion_le.trans
    simp only [card_map,le_rfl]
  have rowMass : (∑ i, (paths i).toFinset.card) = ∑ i, (paths i).length :=
    sum_congr rfl fun i _ => List.toFinset_card_of_nodup (simple i)
  have vertexMass : (∑ x, (commonVertexRows paths x).card) = ∑ i, (paths i).length := by
    have same (x : Fin n) : commonVertexRows paths x = occurrences (fun i => (paths i).toFinset) x := by
      ext i
      rw [mem_commonVertexRows,mem_occurrences,List.mem_toFinset]
    simp only [same,sum_occurrences,rowMass]
  have vCharge := sum_width_fees (fun x => (commonVertexRows paths x).card) (fun x => (plan.rowCuts x).card)
    Dpos plan.rowCharge
  have iCharge := sum_width_fees (fun i => (paths i).toFinset.card) (fun i => (plan.vertexCuts i).card)
    Lpos plan.vertexCharge
  rw [vertexMass] at vCharge
  rw [rowMass] at iCharge
  exact (card_union_le fromVertices fromRows).trans (add_le_add (left.trans vCharge) (right.trans iCharge))

private theorem row_blocks_of_survivors {x : Fin n} {i j : commonVertexRows paths x}
    (adjacent : (commonRowPartnerGraph paths x).Adj i j) (keptI : (i.val,x) ∉ plan.marks) (keptJ : (j.val,x) ∉ plan.marks) :
    (plan.orders.rowsAt x).idxOf i.val/D = (plan.orders.rowsAt x).idxOf j.val/D := by
  change ((plan.rowOrder x).map Subtype.val).idxOf i.val/D = ((plan.rowOrder x).map Subtype.val).idxOf j.val/D
  simp only [index_map_of_injective Subtype.val Subtype.val_injective]
  exact plan.sameRowBlock x adjacent (fun cut => keptI (plan.marked_at_vertex cut))
    (fun cut => keptJ (plan.marked_at_vertex cut))

private theorem vertex_blocks_of_survivors {i : Fin p} {x y : (paths i).toFinset}
    (adjacent : (commonColumnPartnerGraph paths i).Adj x y) (keptX : (i,x.val) ∉ plan.marks) (keptY : (i,y.val) ∉ plan.marks) :
    (plan.orders.verticesOn i).idxOf x.val/L = (plan.orders.verticesOn i).idxOf y.val/L := by
  change ((plan.vertexOrder i).map Subtype.val).idxOf x.val/L = ((plan.vertexOrder i).map Subtype.val).idxOf y.val/L
  simp only [index_map_of_injective Subtype.val Subtype.val_injective]
  exact plan.sameVertexBlock i adjacent (fun cut => keptX (plan.marked_on_row cut)) (fun cut => keptY (plan.marked_on_row cut))

private theorem packingBlock_eq {A B : Type*} [LinearOrder B] (order : A → List B) {w : ℕ}
    {a b : ListBlockIndex order w} (same : a.fst = b.fst) (block : a.snd.val = b.snd.val) : a = b := by
  rcases a with ⟨a,k⟩
  rcases b with ⟨b,l⟩
  change a = b at same
  subst b
  exact congrArg (Sigma.mk a) (Fin.ext block)

private def keptCopies (i : Fin p) : List (plan.orders.VertexCopy D) :=
  (plan.orders.copiedRows D i).filter fun x => decide ((i,x.fst) ∉ plan.marks)

private theorem mem_keptCopies {i : Fin p} {x : plan.orders.VertexCopy D} :
    x ∈ plan.keptCopies i ↔ x ∈ plan.orders.copiedRows D i ∧ (i,x.fst) ∉ plan.marks := by
  simp only [keptCopies,List.mem_filter,decide_eq_true_eq]

private theorem keptCopies_simple (simple : ∀ i, (paths i).Nodup) (i : Fin p) : (plan.keptCopies i).Nodup :=
  List.filter_sublist.nodup (plan.orders.copiedRows_simple D i (simple i))

private theorem keptCopies_step (simple : ∀ i, (paths i).Nodup) {i : Fin p} {x y : plan.orders.VertexCopy D}
    (step : Before plan.keptCopies i x y) : Before paths i x.fst y.fst :=
  plan.orders.copiedRows_step (simple i) (listBefore_of_sublist (plan.orders.copiedRows_simple D i (simple i))
    List.filter_sublist step)

private theorem keptCopies_halfFree (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5) :
    HalfBridgeFree (Before plan.keptCopies) 5 := by
  refine free.split_list_vertices_five_of_no_split_return (fun x => x.fst)
    (fun {_ _ _} => plan.keptCopies_step simple) ?_
  intro i j x y z first second same
  have forward := plan.keptCopies_step simple first
  have backward := plan.keptCopies_step simple second
  by_cases rows : i = j
  · subst j
    rw [← same] at backward
    exact (lt_asymm forward.2.2 backward.2.2).elim
  let u := x.fst
  have uj : u ∈ paths j := by
    change x.fst ∈ paths j
    exact same.symm ▸ backward.2.1
  let start : commonVertexRows paths u := ⟨i,mem_commonVertexRows.mpr forward.1⟩
  let finish : commonVertexRows paths u := ⟨j,mem_commonVertexRows.mpr uj⟩
  have adjacent : (commonRowPartnerGraph paths u).Adj start finish :=
    ⟨fun equal => rows (congrArg Subtype.val equal),y.fst,(listBefore_ne forward).symm,forward.2.1,backward.1⟩
  have keptFirst := plan.mem_keptCopies.mp first.1
  have keptLast := plan.mem_keptCopies.mp second.2.1
  have keptHere : (j,u) ∉ plan.marks := by
    change (j,x.fst) ∉ plan.marks
    exact same.symm ▸ keptLast.2
  have together := plan.row_blocks_of_survivors adjacent keptFirst.2 keptHere
  have firstRank := (mem_localPathBlock.mp (plan.orders.mem_copiedRows.mp keptFirst.1)).2
  have lastRank := (mem_localPathBlock.mp (plan.orders.mem_copiedRows.mp keptLast.1)).2
  change (plan.orders.rowsAt u).idxOf i/D = (plan.orders.rowsAt u).idxOf j/D at together
  change (plan.orders.rowsAt u).idxOf i/D = x.snd.val at firstRank
  change (plan.orders.rowsAt z.fst).idxOf j/D = z.snd.val at lastRank
  have sameRank := congrArg (fun v : Fin n => (plan.orders.rowsAt v).idxOf j/D) same
  exact packingBlock_eq plan.orders.rowsAt same (firstRank.symm.trans (together.trans (sameRank.trans lastRank)))

private def keptPieces (j : plan.orders.PathPiece L) : List (plan.orders.VertexCopy D) :=
  (plan.orders.pieceRows D L j).filter fun x => decide ((j.fst,x.fst) ∉ plan.marks)

private theorem keptPieces_sublist (j : plan.orders.PathPiece L) :
    (plan.keptPieces j).Sublist (plan.orders.pieceRows D L j) := List.filter_sublist

private theorem keptPieces_sublist_copies (j : plan.orders.PathPiece L) :
    (plan.keptPieces j).Sublist (plan.keptCopies j.fst) :=
  (plan.orders.pieceRows_sublist D L j).filter _

private theorem keptPieces_step (simple : ∀ i, (paths i).Nodup)
    {j : plan.orders.PathPiece L} {x y : plan.orders.VertexCopy D}
    (step : Before plan.keptPieces j x y) : Before plan.keptCopies j.fst x y :=
  listBefore_of_sublist (paths := fun j : plan.orders.PathPiece L => plan.keptCopies j.fst)
    (plan.keptCopies_simple simple j.fst) (plan.keptPieces_sublist_copies j) step

private theorem reversed_endpoints_same_piece (simple : ∀ i, (paths i).Nodup)
    {i j river : plan.orders.PathPiece L} {x y : plan.orders.VertexCopy D}
    (parent : i.fst = j.fst) (different : i.fst ≠ river.fst) (forward : Before plan.keptCopies i.fst x y)
    (backward : Before plan.keptPieces river y x) (inI : x ∈ plan.keptPieces i) (inJ : y ∈ plan.keptPieces j) : i = j := by
  have left := plan.keptCopies_step simple forward
  have right := plan.keptCopies_step simple (plan.keptPieces_step simple backward)
  let source : (paths i.fst).toFinset := ⟨x.fst,List.mem_toFinset.mpr left.1⟩
  let target : (paths i.fst).toFinset := ⟨y.fst,List.mem_toFinset.mpr left.2.1⟩
  have edge : (commonColumnPartnerGraph paths i.fst).Adj source target :=
    ⟨fun eq => listBefore_ne left (congrArg Subtype.val eq),river.fst,different.symm,right.2.1,right.1⟩
  have first : x ∈ plan.orders.pieceRows D L i ∧ (i.fst,x.fst) ∉ plan.marks := by
    simpa only [keptPieces,List.mem_filter,decide_eq_true_eq] using inI
  have last : y ∈ plan.orders.pieceRows D L j ∧ (j.fst,y.fst) ∉ plan.marks := by
    simpa only [keptPieces,List.mem_filter,decide_eq_true_eq] using inJ
  have lastHere : (i.fst,y.fst) ∉ plan.marks := parent.symm ▸ last.2
  have together := plan.vertex_blocks_of_survivors edge first.2 lastHere
  have firstRank := (plan.orders.mem_pieceRows.mp first.1).2
  have lastRank := (plan.orders.mem_pieceRows.mp last.1).2
  change (plan.orders.verticesOn i.fst).idxOf x.fst/L = (plan.orders.verticesOn i.fst).idxOf y.fst/L at together
  have sameRank := congrArg (fun k : Fin p => (plan.orders.verticesOn k).idxOf y.fst/L) parent
  exact packingBlock_eq plan.orders.verticesOn parent (firstRank.symm.trans (together.trans (sameRank.trans lastRank)))

private theorem keptPieces_halfFree (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5) :
    HalfBridgeFree (Before plan.keptPieces) 5 := by
  have copiesFree := plan.keptCopies_halfFree simple free
  intro size cutoff bridge earlier
  let old := listBridge_after_opposite_safe_split_through_five Sigma.fst
    (fun {_ _ _} => plan.keptPieces_step simple)
    (fun {i j _} apart same first second => plan.orders.pieceRows_disjoint apart same
      ((plan.keptPieces_sublist i).subset first) ((plan.keptPieces_sublist j).subset second))
    (fun _ {_ _ _ _} different first second => no_parallel_list_steps copiesFree (by decide) different first second)
    (fun _ {_ _ _ _ _} => plan.reversed_endpoints_same_piece simple) (by omega) bridge
  apply copiesFree cutoff old
  exact lt_of_le_of_ne (block_parent_mono (fun i => (plan.orders.verticesOn i).toFinset) L earlier.le) (old.river_ne_arc _).symm

private theorem keptPieces_loss (simple : ∀ i, (paths i).Nodup) :
    (∑ i, (paths i).length) ≤ (∑ j, (plan.keptPieces j).length)+plan.marks.card := by
  classical
  let raw := plan.orders.pieceRows D L
  let original := pieceIncidences raw univ
  let erase := original.filter fun cell => (cell.1.fst,cell.2.fst) ∈ plan.marks
  have subset : erase ⊆ original := filter_subset _ _
  have repair : erasePieceIncidences raw erase = plan.keptPieces := by
    funext j
    unfold erasePieceIncidences keptPieces
    apply List.filter_congr
    intro x on
    have onOriginal : (j,x) ∈ original := mem_pieceIncidences.mpr ⟨mem_univ _,on⟩
    simp only [erase,mem_filter,onOriginal,true_and]
  have charged : erase.card ≤ plan.marks.card := by
    apply card_le_card_of_injOn (fun cell : plan.orders.PathPiece L × plan.orders.VertexCopy D => (cell.1.fst,cell.2.fst))
    · intro cell on
      exact (mem_filter.mp on).2
    · intro a onA b onB same
      apply plan.orders.pieceRows_incidence_injective D L simple
      · exact (mem_pieceIncidences.mp (subset onA)).2
      · exact (mem_pieceIncidences.mp (subset onB)).2
      · exact same
  have exactMass := erasePieceIncidences_mass_add_loss (pieces := raw)
    (fun j => plan.orders.pieceRows_simple (simple j.fst)) univ erase
  rw [repair,inter_eq_right.mpr subset] at exactMass
  change (∑ j, (plan.keptPieces j).length)+erase.card = ∑ j, (raw j).length at exactMass
  have rawMass : (∑ j, (raw j).length) = ∑ i, (paths i).length := plan.orders.pieceRows_mass D L simple
  omega

end HalfFivePackingPlan

open scoped Classical in
/-- With maximum degree two in both local partner graphs, independent
width splits preserve half-five after discarding at most two incidences
per boundary on the two sides. -/
theorem half_five_width_packing_of_local_degree_two {n p D L : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (degreeRows : ∀ x (i : commonVertexRows paths x), (commonRowPartnerGraph paths x).degree i ≤ 2)
    (degreeVertices : ∀ i (x : (paths i).toFinset), (commonColumnPartnerGraph paths i).degree x ≤ 2)
    (Dpos : 0 < D) (Lpos : 0 < L) :
    let M := ∑ i, (paths i).length
    ∃ orders : IncidenceWidthOrders paths, ∃ pieces : orders.PathPiece L → List (orders.VertexCopy D),
      (∀ j, (pieces j).Sublist (orders.pieceRows D L j)) ∧ HalfBridgeFree (Before pieces) 5 ∧
      M ≤ (∑ j, (pieces j).length)+2*(M/D)+2*(M/L) := by
  obtain ⟨plan⟩ := exists_halfFivePackingPlan paths degreeRows degreeVertices Dpos Lpos
  refine ⟨plan.orders,plan.keptPieces,plan.keptPieces_sublist,plan.keptPieces_halfFree simple free,?_⟩
  have cost := plan.marks_card simple Dpos Lpos
  have mass := plan.keptPieces_loss simple
  omega

/-- Apply the degree-two packing after the common-pair deletion. The
intermediate rows retain mass K with `3M ≤ 3K+E`, and the width cuts
lose at most `2*(K/D)+2*(K/L)` more incidences. -/
theorem half_five_width_packing_after_sparse_overlap {n p D L : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (Dpos : 0 < D) (Lpos : 0 < L) :
    let M := ∑ i, (paths i).length
    let E := commonVertexPairCount paths
    ∃ kept : Fin p → List (Fin n), (∀ i, (kept i).Sublist (paths i)) ∧
      let K := ∑ i, (kept i).length
      3*M ≤ 3*K+E ∧ ∃ orders : IncidenceWidthOrders kept,
        ∃ pieces : orders.PathPiece L → List (orders.VertexCopy D),
          (∀ j, (pieces j).Sublist (orders.pieceRows D L j)) ∧ HalfBridgeFree (Before pieces) 5 ∧
          K ≤ (∑ j, (pieces j).length)+2*(K/D)+2*(K/L) := by
  obtain ⟨kept,sub,mass,degreeRows,degreeVertices⟩ := common_vertex_pairs_local_degree_two paths simple
  have keptSimple (i : Fin p) := (sub i).nodup (simple i)
  have keptLegal : HalfBridgeFree (Before kept) 5 := by
    intro k cutoff bridge earlier
    let original := bridge.mapVertices id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (simple i) (sub i) step)
    exact free cutoff original earlier
  exact ⟨kept,sub,mass,half_five_width_packing_of_local_degree_two kept keptSimple keptLegal
    degreeRows degreeVertices Dpos Lpos⟩

end OnlineReachabilityPreservers
