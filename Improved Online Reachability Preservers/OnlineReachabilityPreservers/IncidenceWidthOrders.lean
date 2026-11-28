import OnlineReachabilityPreservers.WidthBlockProfiles

/-! Split incidences using independent orders at the two endpoints. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- The order of incident rows at each vertex, and the order of the
vertices on each row, may be chosen independently for width packing. -/
structure IncidenceWidthOrders {I V : Type*} (paths : I → List V) where
  rowsAt : V → List I
  verticesOn : I → List V
  rowsSimple : ∀ v, (rowsAt v).Nodup
  verticesSimple : ∀ i, (verticesOn i).Nodup
  rowsMem : ∀ v i, i ∈ rowsAt v ↔ v ∈ paths i
  verticesMem : ∀ i v, v ∈ verticesOn i ↔ v ∈ paths i

namespace IncidenceWidthOrders

private def widthBlockOf {A B : Type*} [LinearOrder B] (rows : A → List B)
    (simple : ∀ a, (rows a).Nodup) (width : ℕ) (a : A) (b : B) (member : b ∈ rows a) : ListBlockIndex rows width :=
  ⟨a,⟨(rows a).idxOf b/width,by
    unfold blockCount
    rw [List.toFinset_card_of_nodup (simple a)]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (List.idxOf_lt_length_of_mem member).le)⟩⟩

variable {I V : Type*} [LinearOrder I] [LinearOrder V]
variable {paths : I → List V} (orders : IncidenceWidthOrders paths)

/-- A copy of a vertex is a width block of its incident row order. -/
abbrev VertexCopy (D : ℕ) := ListBlockIndex orders.rowsAt D

/-- A piece of a path is a width block of its vertex packing order. -/
abbrev PathPiece (L : ℕ) := ListBlockIndex orders.verticesOn L

private def copyVertex (D : ℕ) (i : I) (v : {v // v ∈ paths i}) : orders.VertexCopy D :=
  widthBlockOf orders.rowsAt orders.rowsSimple D v.val i ((orders.rowsMem v.val i).mpr v.property)

/-- Assign a copy to each incidence in the original row order. -/
def copiedRows (D : ℕ) (i : I) : List (orders.VertexCopy D) :=
  (paths i).attach.map (orders.copyVertex D i)

omit [LinearOrder V] in
@[simp]
theorem copiedRows_project (D : ℕ) (i : I) :
    (orders.copiedRows D i).map (fun v : orders.VertexCopy D => v.fst) = paths i := by
  unfold copiedRows
  rw [List.map_map]
  exact List.attach_map_subtype_val _

omit [LinearOrder V] in
theorem copiedRows_simple (D : ℕ) (i : I) (simple : (paths i).Nodup) :
    (orders.copiedRows D i).Nodup :=
  List.Nodup.of_map (fun v : orders.VertexCopy D => v.fst) ((orders.copiedRows_project D i).symm ▸ simple)

theorem copiedRows_step {D : ℕ} {i : I} {x y : orders.VertexCopy D} (simple : (paths i).Nodup)
    (step : Before (orders.copiedRows D) i x y) : Before paths i x.fst y.fst := by
  have mapped := listBefore_map (fun v : orders.VertexCopy D => v.fst) ((orders.copiedRows_project D i).symm ▸ simple) step
  simpa only [copiedRows_project] using mapped

omit [LinearOrder V] in
/-- A copied vertex occurs precisely on the rows in its packing block. -/
theorem mem_copiedRows {D : ℕ} {i : I} {x : orders.VertexCopy D} :
    x ∈ orders.copiedRows D i ↔ i ∈ splitListPaths orders.rowsAt D x := by
  constructor
  · intro present
    obtain ⟨old,_,rfl⟩ := List.mem_map.mp present
    exact mem_localPathBlock.mpr ⟨(orders.rowsMem old.val i).mpr old.property,rfl⟩
  · rintro present
    rcases x with ⟨v,b⟩
    obtain ⟨occupied,rank⟩ := mem_localPathBlock.mp present
    let original : {x // x ∈ paths i} := ⟨v,(orders.rowsMem v i).mp occupied⟩
    refine List.mem_map.mpr ⟨original,List.mem_attach _ _,?_⟩
    exact congrArg (Sigma.mk v) (Fin.ext rank)

/-- Select each piece by the packing order while keeping comparisons
from the original copied row. -/
def pieceRows (D L : ℕ) (j : orders.PathPiece L) : List (orders.VertexCopy D) :=
  (orders.copiedRows D j.fst).filter fun x => decide ((orders.verticesOn j.fst).idxOf x.fst/L = j.snd.val)

theorem pieceRows_sublist (D L : ℕ) (j : orders.PathPiece L) :
    (orders.pieceRows D L j).Sublist (orders.copiedRows D j.fst) := List.filter_sublist

theorem pieceRows_simple {D L : ℕ} {j : orders.PathPiece L} (simple : (paths j.fst).Nodup) :
    (orders.pieceRows D L j).Nodup := (orders.pieceRows_sublist D L j).nodup (orders.copiedRows_simple D j.fst simple)

theorem mem_pieceRows {D L : ℕ} {j : orders.PathPiece L} {x : orders.VertexCopy D} :
    x ∈ orders.pieceRows D L j ↔
      x ∈ orders.copiedRows D j.fst ∧ (orders.verticesOn j.fst).idxOf x.fst/L = j.snd.val := by
  simp only [pieceRows,List.mem_filter,decide_eq_true_eq]

theorem pieceRows_disjoint {D L : ℕ} {j k : orders.PathPiece L} {x : orders.VertexCopy D}
    (different : j ≠ k) (parent : j.fst = k.fst) (first : x ∈ orders.pieceRows D L j)
    (second : x ∈ orders.pieceRows D L k) : False := by
  rcases j with ⟨i,a⟩
  rcases k with ⟨j,b⟩
  change i = j at parent
  subst j
  have qa := (orders.mem_pieceRows.mp first).2
  have qb := (orders.mem_pieceRows.mp second).2
  obtain rfl := Fin.ext (qa.symm.trans qb)
  exact different rfl

/-- Every original incidence is placed in a piece of its original row. -/
theorem exists_pieceRows_of_incidence (D L : ℕ) {i : I} {v : V} (present : v ∈ paths i) :
    ∃ j : orders.PathPiece L, ∃ x : orders.VertexCopy D,
      j.fst = i ∧ x.fst = v ∧ x ∈ orders.pieceRows D L j := by
  let j := widthBlockOf orders.verticesOn orders.verticesSimple L i v ((orders.verticesMem i v).mpr present)
  let x := orders.copyVertex D i ⟨v,present⟩
  have copied : x ∈ orders.copiedRows D i := List.mem_map.mpr ⟨⟨v,present⟩,List.mem_attach _ _,rfl⟩
  exact ⟨j,x,rfl,rfl,orders.mem_pieceRows.mpr ⟨copied,rfl⟩⟩

/-- An original incidence identifies at most one copied piece incidence. -/
theorem pieceRows_incidence_injective (D L : ℕ) (simple : ∀ i, (paths i).Nodup) :
    Set.InjOn (fun cell : orders.PathPiece L × orders.VertexCopy D => (cell.1.fst,cell.2.fst))
      {cell | cell.2 ∈ orders.pieceRows D L cell.1} := by
  intro a aOn b bOn equal
  obtain ⟨aRow,aVertex⟩ := a
  obtain ⟨bRow,bVertex⟩ := b
  have parents : aRow.fst = bRow.fst := congrArg Prod.fst equal
  have vertices : aVertex.fst = bVertex.fst := congrArg Prod.snd equal
  have copiedA := (orders.mem_pieceRows.mp aOn).1
  have copiedB : bVertex ∈ orders.copiedRows D aRow.fst := parents.symm ▸ (orders.mem_pieceRows.mp bOn).1
  have priorSimple : ((orders.copiedRows D aRow.fst).map (fun x : orders.VertexCopy D => x.fst)).Nodup := by
    rw [orders.copiedRows_project]
    exact simple aRow.fst
  have sameVertex := List.inj_on_of_nodup_map priorSimple copiedA copiedB vertices
  have sameRow : aRow = bRow := by
    by_contra different
    exact orders.pieceRows_disjoint different parents aOn (sameVertex.symm ▸ bOn)
  exact Prod.ext sameRow sameVertex

/-- The projection of each piece has the same vertex set as its width
block in the row's auxiliary packing order. -/
theorem pieceRows_project_set (D L : ℕ) (j : orders.PathPiece L) :
    ((orders.pieceRows D L j).map (fun v : orders.VertexCopy D => v.fst)).toFinset = (splitListPaths orders.verticesOn L j).toFinset := by
  ext v
  simp only [List.mem_toFinset]
  constructor
  · rintro listed
    obtain ⟨x,on,rfl⟩ := List.mem_map.mp listed
    have copied := orders.mem_pieceRows.mp on
    have original : x.fst ∈ paths j.fst := by
      rw [← orders.copiedRows_project D j.fst]
      exact List.mem_map_of_mem copied.1
    exact mem_localPathBlock.mpr ⟨(orders.verticesMem j.fst x.fst).mpr original,copied.2⟩
  · intro listed
    obtain ⟨auxiliary,rank⟩ := mem_localPathBlock.mp listed
    have original := (orders.verticesMem j.fst v).mp auxiliary
    rw [← orders.copiedRows_project D j.fst] at original
    obtain ⟨x,copied,rfl⟩ := List.mem_map.mp original
    exact List.mem_map.mpr ⟨x,orders.mem_pieceRows.mpr ⟨copied,rank⟩,rfl⟩

/-- The piece has the same size as the block chosen by the auxiliary order. -/
theorem pieceRows_length_eq (D L : ℕ) (j : orders.PathPiece L) (simple : (paths j.fst).Nodup) :
    (orders.pieceRows D L j).length = (splitListPaths orders.verticesOn L j).length := by
  have retained : ((orders.pieceRows D L j).map (fun v : orders.VertexCopy D => v.fst)).Sublist (paths j.fst) := by
    rw [← orders.copiedRows_project D j.fst]
    exact (orders.pieceRows_sublist D L j).map _
  have original := retained.nodup simple
  have auxiliary : (splitListPaths orders.verticesOn L j).Nodup := List.filter_sublist.nodup (orders.verticesSimple j.fst)
  have same := congrArg Finset.card (orders.pieceRows_project_set D L j)
  rw [List.toFinset_card_of_nodup original,List.length_map,List.toFinset_card_of_nodup auxiliary] at same
  exact same

variable [Fintype I] [Fintype V]

omit [Fintype V] in
/-- The occurrence set of a degree copy is exactly its transposed block. -/
theorem copiedRows_occurrences (D : ℕ) (x : orders.VertexCopy D) :
    occurrences (fun i => (orders.copiedRows D i).toFinset) x = (splitListPaths orders.rowsAt D x).toFinset := by
  ext i
  rw [mem_occurrences,List.mem_toFinset,List.mem_toFinset,orders.mem_copiedRows]

omit [Fintype V] in
/-- Dividing each row into pieces leaves the degree of every copy unchanged. -/
theorem pieceRows_degree_eq (D L : ℕ) (x : orders.VertexCopy D) :
    (occurrences (fun j => (orders.pieceRows D L j).toFinset) x).card =
      (occurrences (fun i => (orders.copiedRows D i).toFinset) x).card := by
  let whole := occurrences (fun i => (orders.copiedRows D i).toFinset) x
  let pieces := occurrences (fun j => (orders.pieceRows D L j).toFinset) x
  have onPiece (j : pieces) : x ∈ orders.pieceRows D L j.val :=
    List.mem_toFinset.mp ((mem_occurrences (marks := fun j => (orders.pieceRows D L j).toFinset)).mp j.property)
  let parent (j : pieces) : whole := ⟨j.val.fst,mem_occurrences.mpr
    (List.mem_toFinset.mpr (orders.mem_pieceRows.mp (onPiece j)).1)⟩
  let locate (i : whole) : pieces := by
    have copied : x ∈ orders.copiedRows D i.val :=
      List.mem_toFinset.mp ((mem_occurrences (marks := fun i => (orders.copiedRows D i).toFinset)).mp i.property)
    have original : x.fst ∈ paths i.val := by
      rw [← orders.copiedRows_project D i.val]
      exact List.mem_map_of_mem copied
    let j := widthBlockOf orders.verticesOn orders.verticesSimple L i.val x.fst
      ((orders.verticesMem i.val x.fst).mpr original)
    exact ⟨j,mem_occurrences.mpr (List.mem_toFinset.mpr (orders.mem_pieceRows.mpr ⟨copied,rfl⟩))⟩
  have inverse (j : pieces) : locate (parent j) = j := by
    apply Subtype.ext
    by_contra different
    exact orders.pieceRows_disjoint different rfl (onPiece (locate (parent j))) (onPiece j)
  let relabel : pieces ≃ whole := ⟨parent,locate,inverse,fun i => Subtype.ext rfl⟩
  simpa only [Fintype.card_coe,pieces,whole] using Fintype.card_congr relabel

/-- Allocating width blocks in the two local orders preserves all
incidences before any boundary marks are deleted. -/
theorem pieceRows_mass (D L : ℕ) (simple : ∀ i, (paths i).Nodup) :
    (∑ j, (orders.pieceRows D L j).length) = ∑ i, (paths i).length := by
  let pieces (j : orders.PathPiece L) := (orders.pieceRows D L j).toFinset
  let copied (i : I) := (orders.copiedRows D i).toFinset
  calc
    _ = ∑ j, (pieces j).card := sum_congr rfl fun j _ =>
      (List.toFinset_card_of_nodup (orders.pieceRows_simple (simple j.fst))).symm
    _ = ∑ x, (occurrences pieces x).card := (sum_occurrences pieces).symm
    _ = ∑ x, (occurrences copied x).card := sum_congr rfl fun x _ => orders.pieceRows_degree_eq D L x
    _ = ∑ i, (copied i).card := sum_occurrences copied
    _ = _ := by
      apply sum_congr rfl
      intro i _
      rw [List.toFinset_card_of_nodup (orders.copiedRows_simple D i (simple i)),copiedRows]
      simp only [List.length_map,List.length_attach]

omit [Fintype V] in
/-- Both caps hold for the two independent packing orders. -/
theorem pieceRows_caps {D L : ℕ} (Dpos : 0 < D) (Lpos : 0 < L) (simple : ∀ i, (paths i).Nodup) :
    (∀ j, (orders.pieceRows D L j).length ≤ L) ∧
      ∀ x, (occurrences (fun j => (orders.pieceRows D L j).toFinset) x).card ≤ D := by
  constructor
  · intro j
    rw [orders.pieceRows_length_eq D L j (simple j.fst)]
    exact localPathBlock_length _ (orders.verticesSimple j.fst) Lpos _
  · intro x
    rw [orders.pieceRows_degree_eq,orders.copiedRows_occurrences]
    exact (List.toFinset_card_le _).trans (localPathBlock_length _ (orders.rowsSimple x.fst) Dpos _)

/-- On either side, all nonfinal blocks are full and there is one
possible remainder slot per original label. -/
theorem pieceRows_full_block_profiles {D L : ℕ} (Dpos : 0 < D) (Lpos : 0 < L)
    (simple : ∀ i, (paths i).Nodup) :
    ∃ (fullV : Finset (orders.VertexCopy D)) (fullI : Finset (orders.PathPiece L)),
      (∀ x ∈ fullV, (occurrences (fun j => (orders.pieceRows D L j).toFinset) x).card = D) ∧
      (univ \ fullV).card = Fintype.card V ∧
      (∀ j ∈ fullI, (orders.pieceRows D L j).length = L) ∧
      (univ \ fullI).card = Fintype.card I := by
  obtain ⟨fullV,filledV,remainderV⟩ := splitListPaths_full_block_profile orders.rowsAt orders.rowsSimple Dpos
  obtain ⟨fullI,filledI,remainderI⟩ := splitListPaths_full_block_profile orders.verticesOn orders.verticesSimple Lpos
  refine ⟨fullV,fullI,?_,remainderV,?_,remainderI⟩
  · intro x member
    rw [orders.pieceRows_degree_eq,orders.copiedRows_occurrences]
    have simpleBlock : (splitListPaths orders.rowsAt D x).Nodup := List.filter_sublist.nodup (orders.rowsSimple x.fst)
    rw [List.toFinset_card_of_nodup simpleBlock]
    exact filledV x member
  · intro j member
    rw [orders.pieceRows_length_eq D L j (simple j.fst)]
    exact filledI j member

end IncidenceWidthOrders

end OnlineReachabilityPreservers
