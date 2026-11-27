import OnlineReachabilityPreservers.LocalFrozenCleaning
import Mathlib.Data.Finset.Sort

/-! Exact arrival-order constraints for the half-bridge notion used in the paper. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Prod.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- Each full bridge at the cutoff requires its river to arrive before
its final arc. These constraints depend only on the rows and their labels. -/
noncomputable def halfBridgeArrivalGraph {I V : Type*} [DecidableEq I] [Fintype I] [DecidableEq V]
    (rows : I → List V) (k : ℕ) : Arcs I := by
  classical
  exact univ.filter fun e => ∃ d, d+2 ≤ k ∧ ∃ b : Bridge (Before rows) d,
    b.river = e.1 ∧ b.arc (Fin.last d) = e.2

theorem halfBridgeArrivalGraph_edge {I V : Type*} [DecidableEq I] [Fintype I] [DecidableEq V]
    {rows : I → List V} {k : ℕ} {r a : I} :
    Edge (halfBridgeArrivalGraph rows k) r a ↔
      ∃ d, d+2 ≤ k ∧ ∃ b : Bridge (Before rows) d, b.river = r ∧ b.arc (Fin.last d) = a := by
  classical
  simp only [Edge,halfBridgeArrivalGraph,mem_filter,mem_univ,true_and]

private theorem bridges_arrival_constraints_iff {I V : Type*} [DecidableEq I] [Fintype I] [DecidableEq V]
    (rows : I → List V) (k : ℕ) (arrival : I ≃ Fin (Fintype.card I)) :
    HalfBridgeFree (Before (fun i => rows (arrival.symm i))) k ↔
      ∀ ⦃r a⦄, Edge (halfBridgeArrivalGraph rows k) r a → arrival r < arrival a := by
  constructor
  · intro legal r a e
    obtain ⟨d,small,b,river,last⟩ := halfBridgeArrivalGraph_edge.mp e
    let projected : Bridge (Before (fun i => rows (arrival.symm i))) d :=
      b.mapPaths arrival arrival.injective (fun i _ _ step => by
        simpa only [SourceAudit.BeforeIn,Equiv.symm_apply_apply] using step)
    have parallel : ¬ arrival a < arrival r := by
      have exclude := legal small projected
      simpa only [projected,Bridge.mapPaths,Function.comp_apply,river,last] using exclude
    have different : arrival r ≠ arrival a := by
      intro equal
      exact b.river_ne_arc (Fin.last d) (river.trans ((arrival.injective equal).trans last.symm))
    exact (le_of_not_gt parallel).lt_of_ne different
  · intro constraints d small b earlier
    let old : Bridge (Before rows) d :=
      b.mapPaths arrival.symm arrival.symm.injective (fun _ _ _ step => step)
    have edge : Edge (halfBridgeArrivalGraph rows k) old.river (old.arc (Fin.last d)) :=
      halfBridgeArrivalGraph_edge.mpr ⟨d,small,old,rfl,rfl⟩
    have must := constraints edge
    exact (by simpa only [old,Bridge.mapPaths,Function.comp_apply,Equiv.apply_symm_apply] using must :
      b.river < b.arc (Fin.last d)).not_gt earlier

/-- A reordering of all rows with half-bridge exclusion exists exactly
when the constraints from all full bridges are acyclic. -/
theorem exists_halfBridgeFree_reordering_iff {I V : Type*} [LinearOrder I] [Fintype I] [DecidableEq V]
    (rows : I → List V) (k : ℕ) :
    (∃ arrival : I ≃ Fin (Fintype.card I), HalfBridgeFree
      (Before (fun i => rows (arrival.symm i))) k) ↔
      IsDAG (halfBridgeArrivalGraph rows k) := by
  let G := halfBridgeArrivalGraph rows k
  constructor
  · rintro ⟨arrival,legal⟩ r a e back
    have ordered := (bridges_arrival_constraints_iff rows k arrival).mp legal
    have along {u v : I} (route : Reach G u v) : arrival u ≤ arrival v := by
      induction route with
      | refl => exact le_rfl
      | tail _ step earlier => exact earlier.trans (ordered step).le
    exact (ordered e).not_ge (along back)
  · intro dag
    let R := (Set.range (reverseTopologicalKey G))ᵒᵈ
    let key : I ≃ R := {
      toFun := fun x => OrderDual.toDual (topologicalEquiv G x)
      invFun := fun x => (topologicalEquiv G).symm (OrderDual.ofDual x)
      left_inv := fun x => (topologicalEquiv G).symm_apply_apply x
      right_inv := fun x => (topologicalEquiv G).apply_symm_apply (OrderDual.ofDual x) }
    let : Fintype R := Fintype.ofEquiv I key
    let places := (Fintype.orderIsoFinOfCardEq R (Fintype.card_congr key.symm)).symm
    let arrival := key.trans places.toEquiv
    refine ⟨arrival,(bridges_arrival_constraints_iff rows k arrival).mpr ?_⟩
    intro r a e
    apply places.strictMono
    change (toLex ((reaches G r).card,r)) < toLex ((reaches G a).card,a)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (reaches_card_lt dag e))

/-- Taking sublists can only remove arrival constraints. -/
theorem halfBridgeArrivalGraph_mono_sublist {I V : Type*}
    [DecidableEq I] [Fintype I] [DecidableEq V] {rows kept : I → List V} {k : ℕ}
    (simple : ∀ i, (rows i).Nodup) (sub : ∀ i, (kept i).Sublist (rows i)) :
    halfBridgeArrivalGraph kept k ⊆ halfBridgeArrivalGraph rows k := by
  intro edge on
  obtain ⟨d,small,b,river,last⟩ := halfBridgeArrivalGraph_edge.mp
    (show Edge (halfBridgeArrivalGraph kept k) edge.1 edge.2 from on)
  let projected : Bridge (Before rows) d := b.mapPaths id Function.injective_id
    (fun i _ _ step => listBefore_of_sublist (simple i) (sub i) step)
  exact halfBridgeArrivalGraph_edge.mpr ⟨d,small,projected,river,last⟩

private theorem frozen_half_of_acyclic_prepared_pieces {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V] {n p M k retention : ℕ}
    (pieces : I → List V) (simple : ∀ i, (pieces i).Nodup)
    (acyclic : IsDAG (halfBridgeArrivalGraph pieces k))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertexCap : 3*Fintype.card V ≤ 4*n) (pathCap : 3*Fintype.card I ≤ 4*p)
    (length : ∀ i, (pieces i).length ≤ 4*M/p)
    (degree : ∀ v, (occurrences (fun i => (pieces i).toFinset) v).card ≤ 4*M/n)
    (massCap : (∑ i, (pieces i).length) ≤ M)
    (massFloor : 8*(retention+2)*M ≤ 9*retention*(∑ i, (pieces i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨arrival,free⟩ := (exists_halfBridgeFree_reordering_iff pieces k).mpr acyclic
  let ordered (i : Fin (Fintype.card I)) := pieces (arrival.symm i)
  have orderedMass : (∑ i, (ordered i).length) = ∑ i, (pieces i).length :=
    Equiv.sum_comp arrival.symm (fun i => (pieces i).length)
  have orderedDegree (v : V) : (occurrences (fun i => (ordered i).toFinset) v).card ≤ 4*M/n := by
    let prior := occurrences (fun i => (pieces i).toFinset) v
    have same : occurrences (fun i => (ordered i).toFinset) v = prior.map arrival.toEmbedding := by
      ext j
      constructor
      · intro on
        have present : v ∈ (ordered j).toFinset :=
          (mem_occurrences (marks := fun i => (ordered i).toFinset)).mp on
        have original : arrival.symm j ∈ prior :=
          (mem_occurrences (marks := fun i => (pieces i).toFinset)).mpr present
        exact mem_map.mpr ⟨arrival.symm j,original,arrival.apply_symm_apply j⟩
      · intro on
        obtain ⟨i,found,rfl⟩ := mem_map.mp on
        apply mem_occurrences.mpr
        simpa only [ordered,Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using
          (mem_occurrences.mp found)
    rw [same,card_map]
    exact degree v
  exact regularization_list_frozen_after_caps_with_room_of_mass (half := true) ordered
    (fun i => simple (arrival.symm i)) free hn hp dense long vertexCap
    (by simpa only [Fintype.card_fin] using pathCap)
    (fun i => length (arrival.symm i)) orderedDegree (orderedMass.trans_le massCap)
    (by rw [orderedMass]; exact massFloor)

private theorem frozen_half_of_acyclic_width_sublists {n p k retention : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (kept : let M := ∑ i, (paths i).length
      ListBlockIndex (splitListVertices paths (4*M/n)) (4*M/p) → List (ListVertexBlockIndex paths (4*M/n)))
    (sub : let M := ∑ i, (paths i).length
      ∀ i, (kept i).Sublist (listRegularizedPaths paths (4*M/n) (4*M/p) i))
    (acyclic : IsDAG (halfBridgeArrivalGraph kept k))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (massFloor : 8*(retention+2)*(∑ i, (paths i).length) ≤ 9*retention*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let V := ListVertexBlockIndex paths D
  let I := ListBlockIndex (splitListVertices paths D) L
  let pieces : I → List V := listRegularizedPaths paths D L
  obtain ⟨widthD,trimD,_⟩ := four_average_width hn dense
  obtain ⟨widthL,trimL,_⟩ := four_average_width hp long
  change 0 < D at widthD
  change 0 < L at widthL
  obtain ⟨rawV,rawI⟩ := regularization_list_counts paths simple widthD widthL
  have vertexCap : 3*Fintype.card V ≤ 4*n := by
    simp only [Fintype.card_fin] at rawV
    change 3*(M/D) ≤ n at trimD
    change Fintype.card V ≤ n+M/D at rawV
    omega
  have pathCap : 3*Fintype.card I ≤ 4*p := by
    simp only [Fintype.card_fin] at rawI
    change 3*(M/L) ≤ p at trimL
    change Fintype.card I ≤ p+M/L at rawI
    omega
  obtain ⟨mass,length,degree⟩ := regularization_list_mass_caps paths simple D L widthD widthL
  have shorter (i : I) : (kept i).length ≤ (pieces i).length := (sub i).length_le
  have keptDegree (v : V) : (occurrences (fun i => (kept i).toFinset) v).card ≤ D := by
    apply le_trans (card_le_card ?_) (degree v)
    intro i on
    have found : v ∈ kept i := List.mem_toFinset.mp
      ((mem_occurrences (marks := fun a => (kept a).toFinset)).mp on)
    exact mem_occurrences.mpr (List.mem_toFinset.mpr ((sub i).subset found))
  have massCap : (∑ i, (kept i).length) ≤ M :=
    (sum_le_sum (fun i _ => shorter i)).trans_eq mass
  exact frozen_half_of_acyclic_prepared_pieces (retention := retention) kept
    (fun i => (sub i).nodup (listRegularizedPaths_simple paths simple D L i))
    acyclic hn hp dense long vertexCap pathCap
    (fun i => (shorter i).trans (length i)) keptDegree massCap massFloor

/-- The original-width pieces can be scheduled in any order satisfying
their arrival constraints before restricting the supports and peeling. -/
theorem regularization_list_frozen_half_of_acyclic_arrival_constraints {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (acyclic : let M := ∑ i, (paths i).length
      IsDAG (halfBridgeArrivalGraph (listRegularizedPaths paths (4*M/n) (4*M/p)) k))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  obtain ⟨mass,_,_⟩ := regularization_list_mass_caps paths simple D L
    (four_average_width hn dense).1 (four_average_width hp long).1
  exact frozen_half_of_acyclic_width_sublists (retention := 16) paths simple
    (listRegularizedPaths paths D L) (fun _ => List.Sublist.refl _) acyclic hn hp dense long (by rw [mass])

/-- Keep sublists of the original-width pieces, then choose an arrival
order. A loss of at most one eighteenth of the input mass leaves enough
for both frozen budgets and all four caps. -/
theorem regularization_list_frozen_half_after_arrival_deletions {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (kept : let M := ∑ i, (paths i).length
      ListBlockIndex (splitListVertices paths (4*M/n)) (4*M/p) → List (ListVertexBlockIndex paths (4*M/n)))
    (sub : let M := ∑ i, (paths i).length
      ∀ i, (kept i).Sublist (listRegularizedPaths paths (4*M/n) (4*M/p) i))
    (acyclic : IsDAG (halfBridgeArrivalGraph kept k))
    (smallLoss : let M := ∑ i, (paths i).length
      18*(M-(∑ i, (kept i).length)) ≤ M)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) k ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  apply frozen_half_of_acyclic_width_sublists (retention := 32) paths simple kept sub acyclic hn hp dense long
  dsimp only at smallLoss
  omega

end OnlineReachabilityPreservers
