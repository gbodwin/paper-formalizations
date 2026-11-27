import OnlineReachabilityPreservers.HalfBridgeArrivalOrderAudit

/-! A cyclic arrival constraint survives both prescribed factor-four widths. -/

namespace OnlineReachabilityPreservers.SourceAudit

open Finset
open scoped Sigma.Lex

private def reorderObstructionCore : Fin 4 → List (Fin 8) :=
  ![[1,6,0],[2,5],[0,2,7,4,6,3,1],[5,3,4]]

private def reorderObstructionEmbed : Fin 8 → Fin 49 := Fin.castAdd 41

/-- Pad the midpoint obstruction with distinct singleton rows and
one extra vertex of the split parent. -/
def widthObstructionRows (i : Fin 45) : List (Fin 49) :=
  if h : i.val < 4 then (reorderObstructionCore ⟨i.val,h⟩).map reorderObstructionEmbed
  else [⟨i.val+4,by omega⟩]

set_option maxRecDepth 16384 in
set_option synthInstance.maxSize 1024 in
theorem widthObstructionRows_parameters :
    (∀ i, (widthObstructionRows i).Nodup ∧ (widthObstructionRows i).length ≠ 0) ∧
      (∀ i j, widthObstructionRows i = widthObstructionRows j → i = j) ∧
      (∑ i, (widthObstructionRows i).length) = 56 := by
  decide +kernel

private theorem splitObstruction_coreDummy :
    ∀ i : Fin 4, (7 : Fin 8) ∈ reorderObstructionCore i → i.val = 2 := by
  decide +kernel

private theorem splitObstruction_only_one_row_for_padding {x : Fin 49} (outside : 7 ≤ x.val)
    {i j : Fin 45} (onI : x ∈ widthObstructionRows i) (onJ : x ∈ widthObstructionRows j) : i = j := by
  have core {r : Fin 45} (active : r.val < 4) (on : x ∈ widthObstructionRows r) :
      x.val = 7 ∧ r.val = 2 := by
    obtain ⟨v,member,eq⟩ := List.mem_map.mp (by simpa only [widthObstructionRows,dite_eq_left active] using on)
    have value : v.val = x.val := congrArg Fin.val eq
    have maxValue := v.isLt
    have atSeven : v = 7 := Fin.ext (by omega)
    exact ⟨by omega,splitObstruction_coreDummy ⟨r.val,active⟩ (atSeven ▸ member)⟩
  have single {r : Fin 45} (later : ¬ r.val < 4) (on : x ∈ widthObstructionRows r) :
      x.val = r.val+4 := by
    have equal : x = ⟨r.val+4,by omega⟩ := by
      simpa only [widthObstructionRows,dite_eq_right later,List.mem_singleton] using on
    exact congrArg Fin.val equal
  by_cases first : i.val < 4 <;> by_cases second : j.val < 4
  · exact Fin.ext ((core first onI).2.trans (core second onJ).2.symm)
  · have near := (core first onI).1
    have far := single second onJ
    omega
  · have near := (core second onJ).1
    have far := single first onI
    omega
  · have equal := (single first onI).symm.trans (single second onJ)
    exact Fin.ext (by omega)

private theorem bridge_corner_shared {I V : Type*} [DecidableEq V] {rows : I → List V}
    {d : ℕ} (b : Bridge (BeforeIn rows) d) (i : Fin (d+2)) :
    ∃ r a, r ≠ a ∧ b.vertex i ∈ rows r ∧ b.vertex i ∈ rows a := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j,rfl⟩
  · exact ⟨b.river,b.arc 0,b.river_ne_arc 0,b.riverStep.1,(b.arcStep 0).1⟩
  by_cases final : j = Fin.last d
  · subst j
    exact ⟨b.river,b.arc (Fin.last d),b.river_ne_arc _,b.riverStep.2.1,(b.arcStep _).2.1⟩
  · have before : j.val < d := by
      have bounded := j.isLt
      have unequal : j.val ≠ d := fun eq => final (Fin.ext eq)
      omega
    let next : Fin (d+1) := ⟨j.val+1,by omega⟩
    have same : next.castSucc = j.succ := Fin.ext rfl
    have different : j ≠ next := by
      intro eq
      have number := congrArg Fin.val eq
      change j.val = j.val+1 at number
      omega
    exact ⟨b.arc j,b.arc next,fun eq => different (b.distinctArcs eq),(b.arcStep j).2.1,
      same ▸ (b.arcStep next).1⟩

private theorem splitObstruction_core_projects :
    ∀ (i : Fin 4) (x y : Fin 7),
      BeforeIn reorderObstructionCore i (Fin.castAdd 1 x) (Fin.castAdd 1 y) →
      BeforeIn splitOrderExample i x y := by
  unfold BeforeIn
  decide +kernel

/-- The literal input rows retain the original half-four exclusion. -/
theorem widthObstructionRows_halfFree : HalfBridgeFree (BeforeIn widthObstructionRows) 4 := by
  intro d small b earlier
  have active {i x y} (step : BeforeIn widthObstructionRows i x y) : i.val < 4 := by
    by_contra later
    have first : x = ⟨i.val+4,by omega⟩ := by
      simpa only [widthObstructionRows,dite_eq_right later,List.mem_singleton] using step.1
    have second : y = ⟨i.val+4,by omega⟩ := by
      simpa only [widthObstructionRows,dite_eq_right later,List.mem_singleton] using step.2.1
    exact listBefore_ne step (first.trans second.symm)
  have visible (i : Fin (d+2)) : (b.vertex i).val < 7 := by
    obtain ⟨r,a,distinct,first,second⟩ := bridge_corner_shared b i
    exact lt_of_not_ge (fun larger => distinct (splitObstruction_only_one_row_for_padding larger first second))
  let vertex (i : Fin (d+2)) : Fin 7 := ⟨(b.vertex i).val,visible i⟩
  have project {i j : Fin (d+2)} {r : Fin 45} (step : BeforeIn widthObstructionRows r (b.vertex i) (b.vertex j)) :
      BeforeIn splitOrderExample ⟨r.val,active step⟩ (vertex i) (vertex j) := by
    have owner := active step
    have projection (t : Fin (d+2)) : reorderObstructionEmbed (Fin.castAdd 1 (vertex t)) = b.vertex t :=
      Fin.ext rfl
    have shifted : BeforeIn (fun r : Fin 4 => (reorderObstructionCore r).map reorderObstructionEmbed)
        ⟨r.val,owner⟩ (b.vertex i) (b.vertex j) := by
      simpa only [BeforeIn,widthObstructionRows,dite_eq_left owner] using step
    let shrink (x : Fin 49) : Fin 8 := ⟨x.val%8,Nat.mod_lt _ (by decide)⟩
    have inverse (x : Fin 8) : shrink (reorderObstructionEmbed x) = x :=
      Fin.ext (Nat.mod_eq_of_lt x.isLt)
    have identity : shrink ∘ reorderObstructionEmbed = id := funext inverse
    have shape (p : Fin 4) : ((reorderObstructionCore p).map reorderObstructionEmbed).map shrink =
        reorderObstructionCore p := by rw [List.map_map,identity,List.map_id]
    have simple : ∀ p : Fin 4, (reorderObstructionCore p).Nodup := by decide +kernel
    have mapped := listBefore_map shrink ((shape ⟨r.val,owner⟩).symm ▸ simple ⟨r.val,owner⟩) shifted
    have first : shrink (b.vertex i) = Fin.castAdd 1 (vertex i) := by rw [← projection i,inverse]
    have second : shrink (b.vertex j) = Fin.castAdd 1 (vertex j) := by rw [← projection j,inverse]
    apply splitObstruction_core_projects
    simpa only [BeforeIn,shape,first,second] using mapped
  let old : Bridge (BeforeIn splitOrderExample) d := {
    vertex := vertex
    arc := fun i => ⟨(b.arc i).val,active (b.arcStep i)⟩
    river := ⟨b.river.val,active b.riverStep⟩
    distinctVertices := fun {i j} eq => b.distinctVertices (Fin.ext (congrArg (fun a : Fin 7 => a.val) eq))
    distinctArcs := fun {i j} eq => b.distinctArcs (Fin.ext (congrArg (fun a : Fin 4 => a.val) eq))
    river_ne_arc := fun i eq => b.river_ne_arc i (Fin.ext (congrArg (fun a : Fin 4 => a.val) eq))
    riverStep := project b.riverStep
    arcStep := fun i => project (b.arcStep i) }
  exact splitOrderExample_halfFree small old earlier


abbrev WidthObstructionVertex := ListVertexBlockIndex widthObstructionRows 4
abbrev WidthObstructionPiece := ListBlockIndex (splitListVertices widthObstructionRows 4) 4

/-- Both original factor-four widths equal four. -/
def widthObstructionPieces : WidthObstructionPiece → List WidthObstructionVertex :=
  listRegularizedPaths widthObstructionRows 4 4

private def obstructionFirst (i : Fin 45) : WidthObstructionPiece := ⟨i,⟨0,Nat.succ_pos _⟩⟩

private def obstructionSecond : WidthObstructionPiece := ⟨(2 : Fin 45),⟨1,by decide +kernel⟩⟩

private def obstructionCopy (v : Fin 49) : WidthObstructionVertex := ⟨v,⟨0,Nat.succ_pos _⟩⟩

local instance obstructionBeforeDecidable (i : WidthObstructionPiece) (x y : WidthObstructionVertex) :
    Decidable (BeforeIn widthObstructionPieces i x y) := by
  unfold BeforeIn
  infer_instance

private def obstructionThree : Bridge (BeforeIn widthObstructionPieces) 1 := by
  let vertex : Fin 3 → WidthObstructionVertex := ![obstructionCopy 2,obstructionCopy 5,obstructionCopy 4]
  let arc : Fin 2 → WidthObstructionPiece := ![obstructionFirst 1,obstructionFirst 3]
  have distinct : ∀ i j, vertex i = vertex j → i = j := by decide +kernel
  have labels : ∀ i j, arc i = arc j → i = j := by decide +kernel
  have river : ∀ i, obstructionFirst 2 ≠ arc i := by decide +kernel
  have compared : BeforeIn widthObstructionPieces (obstructionFirst 2) (vertex 0) (vertex (Fin.last 2)) := by
    decide +kernel
  have steps : ∀ i, BeforeIn widthObstructionPieces (arc i) (vertex i.castSucc) (vertex i.succ) := by
    decide +kernel
  exact ⟨vertex,arc,obstructionFirst 2,fun {_ _} => distinct _ _,fun {_ _} => labels _ _,river,compared,steps⟩

private def obstructionFour : Bridge (BeforeIn widthObstructionPieces) 2 := by
  let vertex : Fin 4 → WidthObstructionVertex := ![obstructionCopy 3,obstructionCopy 1,obstructionCopy 0,obstructionCopy 4]
  let arc : Fin 3 → WidthObstructionPiece := ![obstructionSecond,obstructionFirst 0,obstructionFirst 2]
  have distinct : ∀ i j, vertex i = vertex j → i = j := by decide +kernel
  have labels : ∀ i j, arc i = arc j → i = j := by decide +kernel
  have river : ∀ i, obstructionFirst 3 ≠ arc i := by decide +kernel
  have compared : BeforeIn widthObstructionPieces (obstructionFirst 3) (vertex 0) (vertex (Fin.last 3)) := by
    decide +kernel
  have steps : ∀ i, BeforeIn widthObstructionPieces (arc i) (vertex i.castSucc) (vertex i.succ) := by
    decide +kernel
  exact ⟨vertex,arc,obstructionFirst 3,fun {_ _} => distinct _ _,fun {_ _} => labels _ _,river,compared,steps⟩

/-- The two implications between the first piece of the long row and
the last active row forbid every arrival order at the original widths. -/
theorem widthObstruction_original_widths_not_acyclic {k : ℕ} (coversFour : 4 ≤ k) :
    let M := ∑ i, (widthObstructionRows i).length
    ¬ IsDAG (halfBridgeArrivalGraph (listRegularizedPaths widthObstructionRows (4*M/49) (4*M/45)) k) := by
  dsimp only
  rw [widthObstructionRows_parameters.2.2]
  change ¬ IsDAG (halfBridgeArrivalGraph widthObstructionPieces k)
  intro dag
  have first : Edge (halfBridgeArrivalGraph widthObstructionPieces k) (obstructionFirst 2) (obstructionFirst 3) :=
    halfBridgeArrivalGraph_edge.mpr ⟨1,by omega,obstructionThree,rfl,rfl⟩
  have second : Edge (halfBridgeArrivalGraph widthObstructionPieces k) (obstructionFirst 3) (obstructionFirst 2) :=
    halfBridgeArrivalGraph_edge.mpr ⟨2,coversFour,obstructionFour,rfl,rfl⟩
  exact dag first (.single second)

private def obstructionCleanRows : Fin 4 → List (Fin 8) := ![[0,1],[2,3],[4,5],[6,7]]

/-- A separate literal witness fits both budgets and all four frozen caps. -/
theorem widthObstruction_frozen_literal_witness (k : ℕ) :
    ∃ n' ≤ 49, ∃ p' ≤ 45, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup ∧ (clean i).length ≠ 0) ∧ Function.Injective clean ∧
      BridgeFree (BeforeIn clean) k ∧
      56 ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ 56 ∧ frozenListCaps 49 45 56 clean := by
  let clean := obstructionCleanRows
  have simple : ∀ i, (clean i).Nodup ∧ (clean i).length ≠ 0 := by decide +kernel
  have different : ∀ i j, clean i = clean j → i = j := by decide +kernel
  have disjoint : ∀ (r a : Fin 4) (x : Fin 8), x ∈ clean r → x ∈ clean a → r = a := by decide +kernel
  have mass : (∑ i, (clean i).length) = 8 := by decide +kernel
  have degree : ∀ v, (occurrences (fun i => (clean i).toFinset) v).card = 1 := by decide +kernel
  have lengths : ∀ i, (clean i).length = 2 := by decide +kernel
  refine ⟨8,by decide,4,by decide,clean,simple,fun {_ _} => different _ _,?_,?_,?_,?_⟩
  · intro d _
    exact ⟨fun b => b.river_ne_arc 0 (disjoint b.river (b.arc 0) (b.vertex 0) b.riverStep.1 (b.arcStep 0).1)⟩
  · rw [mass]
    decide
  · rw [mass]
    decide
  · constructor
    · intro v
      rw [degree]
      norm_num
    · intro i
      rw [lengths]
      norm_num

end OnlineReachabilityPreservers.SourceAudit
