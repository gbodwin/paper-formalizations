import OnlineReachabilityPreservers.IncidenceDegreeComponentCleaning
import OnlineReachabilityPreservers.ShortIncidenceRowPacking

/-! Use bounded connections in both incidence orientations. -/

namespace OnlineReachabilityPreservers

open Finset SimpleGraph
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- Incident rows connected by short links after deleting the vertex. -/
noncomputable def shortIncidenceVertexGroup {I V : Type*} [LinearOrder I] [Fintype I] [DecidableEq V]
    (rows : I → List V) (radius : ℕ) (x : V) (i : I) : Finset I :=
  shortIncidenceRowGroup (incidenceTranspose rows) radius x i

/-- Allocate degree copies by keeping whole incidence groups together.
The copies preserve every comparison, the length of every row, and
the chosen bridge exclusion at any cutoff. At most one copy per
original vertex has degree at most half the prescribed degree width. -/
theorem copies_of_short_incidence_vertex_group_room {n p width k : ℕ} {half : Bool}
    {rows : Fin p → List (Fin n)} (simple : ∀ i, (rows i).Nodup)
    (legal : localOrderAdmissible half k rows)
    (fits : ∀ x i, x ∈ rows i → (shortIncidenceVertexGroup rows (k-2) x i).card ≤ width) :
    ∃ (sizes : Fin n → ℕ) (copies : Fin p → List (Σₗ v : Fin n, Fin (sizes v))),
      (∀ i, (copies i).Nodup) ∧ localOrderAdmissible half k copies ∧
      (∀ i, (copies i).map Sigma.fst = rows i) ∧
      (∀ v, (occurrences (fun i => (copies i).toFinset) v).card ≤ width) ∧
      ({v ∈ univ | (occurrences (fun i => (copies i).toFinset) v).card ≤ width/2} :
        Finset (Σₗ v : Fin n, Fin (sizes v))).card ≤ n := by
  let transpose := incidenceTranspose rows
  let linked := shortIncidenceRowLink transpose (k-2)
  have canGroup (x : Fin n) : ∃ groups,
      CappedPathPartition (occurrences (fun i => (rows i).toFinset) x) (linked x) width groups := by
    have incidences : (transpose x).toFinset = occurrences (fun i => (rows i).toFinset) x := by
      ext i
      simp only [List.mem_toFinset,transpose,mem_incidenceTranspose,mem_occurrences]
    rw [← incidences]
    exact short_incidence_row_partition transpose (k-2) x width
      (fun i on => fits x i (mem_incidenceTranspose.mp on))
  refine copies_of_capped_vertex_partitions (half := half) (cutoff := k) simple linked canGroup ?_
  intro sizes copies projects steps together
  let W := Σₗ v : Fin n, Fin (sizes v)
  let project (x : W) := x.fst
  have members {i x} (on : x ∈ copies i) : project x ∈ rows i := by
    rw [← projects i]
    exact List.mem_map_of_mem (f := Sigma.fst) on
  refine localOrderAdmissible_of_short_incidence_links legal id project monotone_id
    (fun {_ _} on => members on) (fun {_ _ _} on => steps on) ?_
  intro a x y u v atX atY edgeX edgeY w near avoids
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
          have right : x.fst ∈ rows j := by
            have on : y.fst ∈ rows j := members edgeY
            rwa [same]
          have link : linked x.fst i j := by
            refine ⟨mem_incidenceTranspose.mpr (members edgeX),mem_incidenceTranspose.mpr right,w.map f,?_,?_⟩
            · change (w.map f).length ≤ k-2
              simpa only [Walk.length_map] using near
            · change Sum.inl x.fst ∉ (w.map f).support
              simp only [Walk.support_map,List.mem_map]
              rintro ⟨b,on,equal⟩
              have swap : Sum.swap b = Sum.inl x.fst := equal
              have old : b = Sum.inr x.fst := by
                simpa only [Sum.swap_swap,Sum.swap_inl] using congrArg Sum.swap swap
              have root : Sum.inr x.fst = a := atX
              exact avoids (old.trans root ▸ on)
          exact congrArg Sum.inr (together same edgeX edgeY link)

/-- Keep the two width tests and lower caps fixed at a supplied starting
mass. The trim reports its two quadratic deletion bounds to the caller. -/
theorem regularization_list_frozen_of_short_incidence_group_rooms_of_mass {n p k M retention : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (legal : localOrderAdmissible half k rows)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (upper : (∑ i, (rows i).length) ≤ M)
    (degreeRoom : ∀ x i, x ∈ rows i → (shortIncidenceVertexGroup rows (k-2) x i).card ≤ 4*M/n)
    (rowRoom : ∀ i, ∀ x ∈ rows i, (shortIncidenceRowGroup rows (k-2) i x).card ≤ 4*M/p)
    (enough : let K := ∑ i, (rows i).length
      ∀ R lostV lostI : ℕ, K ≤ R + (lostV + lostI) →
        4*(((4*M/n)/2 + 1)*n)*lostV ≤ K^2 →
        4*(((4*M/p)/2 + 1)*p)*lostI ≤ K^2 → (retention+2)*M ≤ 2*retention*R) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let D := 4*M/n
  let L := 4*M/p
  obtain ⟨vSizes,copies,copySimple,copyLegal,projects,degree,lightV⟩ :=
    copies_of_short_incidence_vertex_group_room simple legal degreeRoom
  have copyRoom (i : Fin p) (x : Σₗ v : Fin n, Fin (vSizes v)) (on : x ∈ copies i) :
      (shortIncidenceRowGroup copies (k-2) i x).card ≤ L := by
    have member : x.fst ∈ rows i := by
      rw [← projects i]
      exact List.mem_map_of_mem (f := Sigma.fst) on
    exact (shortIncidenceRowGroup_card_le_project (W := Σₗ v : Fin n, Fin (vSizes v))
      (fun v => v.fst) simple projects (k-2) i x).trans
      (rowRoom i x.fst member)
  obtain ⟨iSizes,pieces,pieceSimple,pieceLegal,length,pieceMass,degrees,lightI⟩ :=
    split_of_short_incidence_row_group_room copySimple copyLegal copyRoom
  let V := Σₗ v : Fin n, Fin (vSizes v)
  have massEqual : (∑ i, (pieces i).length) = ∑ i, (rows i).length := pieceMass.trans
    (sum_congr rfl fun i _ =>
      (List.length_map (as := copies i) (fun v => v.fst)).symm.trans (congrArg List.length (projects i)))
  have lightOutput : ({v ∈ univ | (occurrences (fun i => (pieces i).toFinset) v).card ≤ D/2} :
      Finset V).card ≤ n := by
    have present : ({v ∈ univ | (occurrences (fun i => (pieces i).toFinset) v).card ≤ D/2} : Finset V) =
        ({v ∈ univ | (occurrences (fun i => (copies i).toFinset) v).card ≤ D/2} : Finset V) := by
      ext v
      simp only [mem_filter,mem_univ,true_and]
      exact (congrArg (fun d : ℕ => d ≤ D/2) (degrees v)).to_iff
    rw [present]
    exact lightV
  refine regularization_list_frozen_of_half_width_profiles_of_mass pieces pieceSimple pieceLegal hn hp dense long
    (massEqual.trans_le upper) length (fun v => (degrees v).trans_le (degree v)) lightOutput lightI ?_
  dsimp only
  rw [massEqual]
  exact enough

/-- Trim width-bounded vertex groups and row groups. Each profile has at
most one light group per original label, so the two support restrictions
and original lower caps leave at least a quarter of the original mass. -/
theorem regularization_list_frozen_of_short_incidence_group_rooms {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (simple : ∀ i, (rows i).Nodup)
    (legal : localOrderAdmissible half k rows)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length) (long : p ≤ ∑ i, (rows i).length)
    (degreeRoom : let M := ∑ i, (rows i).length
      ∀ x i, x ∈ rows i → (shortIncidenceVertexGroup rows (k-2) x i).card ≤ 4*M/n)
    (rowRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ rows i, (shortIncidenceRowGroup rows (k-2) i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 4*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_of_short_incidence_group_rooms_of_mass rows simple legal hn hp dense long
    le_rfl degreeRoom rowRoom ?_
  exact fun _ _ _ paid boundV boundI => half_width_trim_mass_of_full hn hp (hn.trans_le dense) paid boundV boundI

/-- Both bounded group-size tests give the literal frozen witness with
distinct nonempty simple paths and at least one eighth of the mass. -/
theorem regularization_literal_frozen_of_short_incidence_group_rooms {n p k : ℕ} {half : Bool}
    (rows : Fin p → List (Fin n)) (distinct : Function.Injective rows)
    (valid : ∀ i, rows i ≠ [] ∧ (rows i).Nodup) (legal : localOrderAdmissible half k rows)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (rows i).length)
    (degreeRoom : let M := ∑ i, (rows i).length
      ∀ x i, x ∈ rows i → (shortIncidenceVertexGroup rows (k-2) x i).card ≤ 4*M/n)
    (rowRoom : let M := ∑ i, (rows i).length
      ∀ i, ∀ x ∈ rows i, (shortIncidenceRowGroup rows (k-2) i x).card ≤ 4*M/p) :
    let M := ∑ i, (rows i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ [] ∧ (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨n',vertexBudget,p',rowBudget,clean,injective,nonempty,cleanSimple,cleanLegal,mass,upper,caps⟩ :=
    regularization_list_frozen_distinct_of_indexed (retention := 8) rows distinct (fun i => (valid i).1)
      (fun i => (valid i).2) legal two hn hp dense le_rfl (fun long => by
        obtain ⟨v,vFits,q,qFits,output,outputSimple,allowed,keep,within,bounds⟩ :=
          regularization_list_frozen_of_short_incidence_group_rooms rows (fun i => (valid i).2)
            legal hn hp dense long degreeRoom rowRoom
        exact ⟨v,vFits,q,qFits,output,outputSimple,allowed,keep.trans (Nat.mul_le_mul_right _ (by decide)),within,bounds⟩)
  exact ⟨n',vertexBudget,p',rowBudget,clean,injective,fun i => ⟨nonempty i,cleanSimple i⟩,cleanLegal,mass,upper,caps⟩


end OnlineReachabilityPreservers
