import OnlineReachabilityPreservers.IncidenceComponentCleaning
import OnlineReachabilityPreservers.ShortReturnVertexPacking

/-! Split degree labels by incidence components and trim both supports. -/

namespace OnlineReachabilityPreservers

open Finset SimpleGraph
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- The incidence transpose, with rows of the input listed in their
arrival order at each vertex. -/
def incidenceTranspose {I V : Type*} [LinearOrder I] [Fintype I] [DecidableEq V]
    (rows : I → List V) (x : V) : List I :=
  (occurrences (fun i => (rows i).toFinset) x).sort (· ≤ ·)

theorem mem_incidenceTranspose {I V : Type*} [LinearOrder I] [Fintype I] [DecidableEq V]
    {rows : I → List V} {i : I} {x : V} : i ∈ incidenceTranspose rows x ↔ x ∈ rows i := by
  rw [incidenceTranspose,mem_sort,mem_occurrences,List.mem_toFinset]

private def incidenceTransposeHom {I V : Type*} [LinearOrder I] [Fintype I] [DecidableEq V]
    (rows : I → List V) : pathIncidenceGraph rows →g pathIncidenceGraph (incidenceTranspose rows) where
  toFun := Sum.swap
  map_rel' := by
    intro a b edge
    cases a <;> cases b
    · exact edge.elim
    · exact mem_incidenceTranspose.mpr edge
    · exact mem_incidenceTranspose.mpr edge
    · exact edge.elim

/-- Incident rows in one component after deleting the original vertex. -/
noncomputable def incidenceVertexDeletionGroup {I V : Type*} [LinearOrder I] [Fintype I] [DecidableEq V]
    (rows : I → List V) (x : V) (i : I) : Finset I :=
  incidenceRowDeletionGroup (incidenceTranspose rows) x i

/-- Allocate degree copies by keeping whole incidence groups together.
The copies preserve every comparison, the length of every row, and
the chosen bridge exclusion at any cutoff. At most one copy per
original vertex has degree at most half the prescribed degree width. -/
theorem copies_of_incidence_vertex_deletion_group_room {n p width k : ℕ} {half : Bool}
    {rows : Fin p → List (Fin n)} (simple : ∀ i, (rows i).Nodup)
    (legal : localOrderAdmissible half k rows)
    (fits : ∀ x i, x ∈ rows i → (incidenceVertexDeletionGroup rows x i).card ≤ width) :
    ∃ (sizes : Fin n → ℕ) (copies : Fin p → List (Σₗ v : Fin n, Fin (sizes v))),
      (∀ i, (copies i).Nodup) ∧ localOrderAdmissible half k copies ∧
      (∀ i, (copies i).map Sigma.fst = rows i) ∧
      (∀ v, (occurrences (fun i => (copies i).toFinset) v).card ≤ width) ∧
      ({v ∈ univ | (occurrences (fun i => (copies i).toFinset) v).card ≤ width/2} :
        Finset (Σₗ v : Fin n, Fin (sizes v))).card ≤ n := by
  let transpose := incidenceTranspose rows
  let linked (x : Fin n) (i j : Fin p) :=
    i ∈ transpose x ∧ j ∈ transpose x ∧ RowDeletionConnected transpose x i j
  have canGroup (x : Fin n) : ∃ groups,
      CappedPathPartition (occurrences (fun i => (rows i).toFinset) x) (linked x) width groups := by
    have incidences : (transpose x).toFinset = occurrences (fun i => (rows i).toFinset) x := by
      ext i
      simp only [List.mem_toFinset,transpose,mem_incidenceTranspose,mem_occurrences]
    rw [← incidences]
    exact incidence_row_deletion_partition transpose x width
      (fun i on => fits x i (mem_incidenceTranspose.mp on))
  refine copies_of_capped_vertex_partitions (half := half) (cutoff := k) simple linked canGroup ?_
  intro sizes copies projects steps together
  let W := Σₗ v : Fin n, Fin (sizes v)
  let project (x : W) := x.fst
  have members {i x} (on : x ∈ copies i) : project x ∈ rows i := by
    rw [← projects i]
    exact List.mem_map_of_mem (f := Sigma.fst) on
  refine localOrderAdmissible_of_incidence_components legal id project monotone_id
    (fun {_ _} on => members on) (fun {_ _ _} on => steps on) ?_
  intro a x y u v atX atY edgeX edgeY w avoids
  cases x with
  | inl i =>
    have equal : Sum.inl i = Sum.map (id : Fin p → Fin p) project y := atX.trans atY.symm
    cases y with
    | inl j => exact congrArg Sum.inl (Sum.inl.inj equal)
    | inr y => cases equal
  | inr x =>
    have equal : Sum.inr (project x) = Sum.map (id : Fin p → Fin p) project y := atX.trans atY.symm
    cases y with
    | inl j => cases equal
    | inr y =>
      have same : x.fst = y.fst := Sum.inr.inj equal
      cases u with
      | inr u => exact edgeX.elim
      | inl i =>
        cases v with
        | inr v => exact edgeY.elim
        | inl j =>
          let f := incidenceTransposeHom rows
          have connected : RowDeletionConnected transpose x.fst i j := by
            refine ⟨w.map f,?_⟩
            change Sum.inl x.fst ∉ (w.map f).support
            simp only [Walk.support_map,List.mem_map]
            rintro ⟨b,on,equal⟩
            have swap : Sum.swap b = Sum.inl x.fst := equal
            have old : b = Sum.inr x.fst := by simpa only [Sum.swap_swap,Sum.swap_inl] using congrArg Sum.swap swap
            have root : Sum.inr x.fst = a := atX
            exact avoids (old.trans root ▸ on)
          have right : x.fst ∈ rows j := by
            have on : y.fst ∈ rows j := members edgeY
            rwa [same]
          have link : linked x.fst i j :=
            ⟨mem_incidenceTranspose.mpr (members edgeX),mem_incidenceTranspose.mpr right,connected⟩
          exact congrArg Sum.inr (together same edgeX edgeY link)

/-- Trim width-bounded vertex groups and row groups. Each profile has at
most one light group per original label, so the two support restrictions
and original lower caps leave at least a quarter of the original mass. -/
theorem regularization_list_frozen_of_incidence_deletion_group_rooms {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (legal : localOrderAdmissible half k rows)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (degreeRoom : let M := ∑ i, (rows i).length
      ∀ x i, x ∈ rows i → (incidenceVertexDeletionGroup rows x i).card ≤ 4*M/n)
    (rowRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ rows i, (incidenceRowDeletionGroup rows i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  let dMin := D/2+1
  let lMin := L/2+1
  obtain ⟨vSizes,copies,copySimple,copyLegal,projects,degree,lightV⟩ :=
    copies_of_incidence_vertex_deletion_group_room simple legal degreeRoom
  have copyRoom (i : Fin p) (x : Σₗ v : Fin n, Fin (vSizes v)) (on : x ∈ copies i) :
      (incidenceRowDeletionGroup copies i x).card ≤ L := by
    have member : x.fst ∈ rows i := by
      rw [← projects i]
      exact List.mem_map_of_mem (f := Sigma.fst) on
    exact (incidenceRowDeletionGroup_card_le_project (fun v => v.fst) simple projects i x).trans
      (rowRoom i x.fst member)
  obtain ⟨iSizes,pieces,pieceSimple,pieceLegal,length,pieceMass,degrees,lightI⟩ :=
    split_of_incidence_row_deletion_group_room copySimple copyLegal copyRoom
  let V := Σₗ v : Fin n, Fin (vSizes v)
  let I := Σₗ i : Fin p, Fin (iSizes i)
  let marks (i : I) := (pieces i).toFinset
  let heavyV := (univ : Finset V).filter fun v => D/2 < (occurrences marks v).card
  let heavyI := (univ : Finset I).filter fun i => L/2 < (pieces i).length
  have massEqual : (∑ i, (pieces i).length) = M := pieceMass.trans (sum_congr rfl fun i _ => by
    exact (List.length_map (as := copies i) (fun v => v.fst)).symm.trans (congrArg List.length (projects i)))
  have dRoom : 2*M ≤ dMin*n := half_average_width_capacity hn
  have lRoom : 2*M ≤ lMin*p := half_average_width_capacity hp
  have restV : (univ \ heavyV).card ≤ n := by
    have rest : (univ : Finset V) \ heavyV =
        (univ.filter fun v => (occurrences (fun i => (copies i).toFinset) v).card ≤ D/2) := by
      ext v
      simp only [heavyV,mem_sdiff,mem_univ,mem_filter,true_and,not_lt,marks]
      exact (congrArg (fun d : ℕ => d ≤ D/2) (degrees v)).to_iff
    rw [rest]
    exact lightV
  have restI : (univ \ heavyI).card ≤ p := by
    have rest : (univ : Finset I) \ heavyI = (univ.filter fun i => (pieces i).length ≤ L/2) := by
      ext i
      simp [heavyI]
    rw [rest]
    exact lightI
  refine regularization_list_frozen_after_threshold_profile_trim_of_loss (retention := 4)
    (degreeThreshold := dMin) (pathThreshold := lMin)
    pieces pieceSimple pieceLegal hn hp dense long length (fun v => (degrees v).trans_le (degree v))
    massEqual.le heavyV heavyI (Nat.succ_pos _) (Nat.succ_pos _)
    (fun v on => (mem_filter.mp on).2) restV (fun i on => (mem_filter.mp on).2) restI
    (massEqual.trans_le ((by omega : M ≤ 2*M).trans dRoom))
    (massEqual.trans_le ((by omega : M ≤ 2*M).trans lRoom)) ?_
  dsimp only
  rw [massEqual]
  intro kept lostV lostI paid boundV boundI
  have mPos : 0 < M := hn.trans_le dense
  have lossBound {capacity loss : ℕ} (room : 2*M ≤ capacity) (bound : 4*capacity*loss ≤ M^2) :
      8*loss ≤ M := by
    apply (Nat.mul_le_mul_left_iff mPos).mp
    calc
      M*(8*loss) = 4*(2*M)*loss := by ring
      _ ≤ 4*capacity*loss := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ room)
      _ ≤ M^2 := bound
      _ = M*M := pow_two _
  have lessV := lossBound dRoom boundV
  have lessI := lossBound lRoom boundI
  omega

/-- Both deletion-component bounds give the literal frozen witness with
distinct nonempty simple paths and at least one eighth of the mass. -/
theorem regularization_literal_frozen_of_incidence_deletion_group_rooms {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows)
    (valid : ∀ i, rows i ≠ [] ∧ (rows i).Nodup) (legal : localOrderAdmissible half k rows)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (degreeRoom : let M := ∑ i, (rows i).length
      ∀ x i, x ∈ rows i → (incidenceVertexDeletionGroup rows x i).card ≤ 4*M/n)
    (rowRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ rows i, (incidenceRowDeletionGroup rows i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨n',vertexBudget,p',rowBudget,clean,injective,nonempty,cleanSimple,cleanLegal,mass,upper,caps⟩ :=
    regularization_list_frozen_distinct_of_indexed (retention := 8) rows distinct (fun i => (valid i).1)
      (fun i => (valid i).2) legal two hn hp dense le_rfl (fun long => by
        obtain ⟨v,vFits,q,qFits,output,outputSimple,allowed,keep,within,bounds⟩ :=
          regularization_list_frozen_of_incidence_deletion_group_rooms rows (fun i => (valid i).2)
            legal hn hp dense long degreeRoom rowRoom
        exact ⟨v,vFits,q,qFits,output,outputSimple,allowed,keep.trans (Nat.mul_le_mul_right _ (by decide)),within,bounds⟩)
  exact ⟨n',vertexBudget,p',rowBudget,clean,injective,fun i => ⟨nonempty i,cleanSimple i⟩,cleanLegal,mass,upper,caps⟩

end OnlineReachabilityPreservers
