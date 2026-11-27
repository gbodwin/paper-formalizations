import OnlineReachabilityPreservers.HalfThreeUpstreamMass
import OnlineReachabilityPreservers.LocalAverageCleaning
import OnlineReachabilityPreservers.LocalFrozenCleaning
import OnlineReachabilityPreservers.DistinctPathBudgets

/-! Full-three-free rows from finite incidence relations. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

/-- A pair of distinct vertices belongs to at most one row. -/
def IncidencePairUnique {I V : Type*} (hit : I → V → Prop) : Prop :=
  ∀ {a b x y}, x ≠ y → hit a x → hit a y → hit b x → hit b y → a = b

/-- Three distinct rows cannot meet pairwise at three distinct vertices. -/
def IncidenceNoTriangle {I V : Type*} (hit : I → V → Prop) : Prop :=
  ∀ {a b r x y z}, a ≠ b → r ≠ a → r ≠ b → x ≠ y → y ≠ z → x ≠ z →
    hit a x → hit a y → hit b y → hit b z → hit r x → hit r z → False

theorem IncidencePairUnique.swap {I V : Type*} {hit : I → V → Prop}
    (unique : IncidencePairUnique hit) : IncidencePairUnique (fun v i => hit i v) := by
  intro a b x y apart ax ay bx by_
  by_contra different
  exact apart (unique different ax bx ay by_)

theorem IncidenceNoTriangle.swap {I V : Type*} {hit : I → V → Prop}
    (noTriangle : IncidenceNoTriangle hit) : IncidenceNoTriangle (fun v i => hit i v) := by
  intro a b r x y z ab ra rb xy yz xz ax ay by_ bz rx rz
  exact noTriangle yz xy xz ab rb.symm ra.symm ay by_ bz rz ax rx

private theorem incidenceRowsFullThree {I V : Type*} [DecidableEq V] {hit : I → V → Prop}
    (pairUnique : IncidencePairUnique hit) (noTriangle : IncidenceNoTriangle hit)
    (rows : I → List V) (sound : ∀ i v, v ∈ rows i → hit i v) :
    BridgeFree (Before rows) 3 := by
  intro d size
  refine ⟨fun bridge => ?_⟩
  obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
  · exact bridge.river_ne_arc 0 (pairUnique (listBefore_ne bridge.riverStep)
      (sound _ _ bridge.riverStep.1) (sound _ _ bridge.riverStep.2.1)
      (sound _ _ (bridge.arcStep 0).1) (sound _ _ (bridge.arcStep 0).2.1))
  · exact noTriangle (bridge.distinctArcs.ne (by decide : (0:Fin 2) ≠ 1))
      (bridge.river_ne_arc 0) (bridge.river_ne_arc 1)
      (bridge.distinctVertices.ne (by decide : (0:Fin 3) ≠ 1))
      (bridge.distinctVertices.ne (by decide : (1:Fin 3) ≠ 2))
      (bridge.distinctVertices.ne (by decide : (0:Fin 3) ≠ 2))
      (sound _ _ (bridge.arcStep 0).1) (sound _ _ (bridge.arcStep 0).2.1)
      (sound _ _ (bridge.arcStep 1).1) (sound _ _ (bridge.arcStep 1).2.1)
      (sound _ _ bridge.riverStep.1) (sound _ _ bridge.riverStep.2.1)

/-- Turn regular finite incidence sets into literal rows with full-three
exclusion in any order, preserving both exact budgets and the mass. -/
theorem fullThreeRows_of_finiteIncidence {I V : Type*} [Fintype I] [Fintype V]
    (hit : I → V → Prop) [DecidableRel hit]
    (pairUnique : IncidencePairUnique hit) (noTriangle : IncidenceNoTriangle hit)
    {n p length degree : ℕ} (vCard : Fintype.card V = n) (iCard : Fintype.card I = p)
    (rowSize : ∀ i, (univ.filter (hit i)).card = length)
    (vertexSize : ∀ v, (univ.filter (fun i => hit i v)).card = degree)
    (long : 2 ≤ length) :
    ∃ rows : Fin p → List (Fin n), Function.Injective rows ∧
      (∀ i, (rows i).Nodup ∧ (rows i).length = length) ∧ BridgeFree (Before rows) 3 ∧
      (∑ i, (rows i).length) = p*length ∧
      (∀ v, (occurrences (fun i => (rows i).toFinset) v).card = degree) ∧
      listOutputAverageCaps rows := by
  classical
  let label := Fintype.equivFinOfCardEq iCard
  let vertex := Fintype.equivFinOfCardEq vCard
  let on (i : Fin p) := (univ.filter (hit (label.symm i))).map vertex.toEmbedding
  let rows (i : Fin p) := (on i).toList
  have contains (i v) : v ∈ rows i ↔ hit (label.symm i) (vertex.symm v) := by
    dsimp only [rows,on]
    simp only [Finset.mem_toList,Finset.mem_map,Finset.mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨x,hx,equal⟩
      change vertex x = v at equal
      simpa only [← equal,Equiv.symm_apply_apply] using hx
    · intro hv
      exact ⟨vertex.symm v,hv,vertex.apply_symm_apply v⟩
  have simple (i) : (rows i).Nodup := nodup_toList _
  have lengths (i) : (rows i).length = length := by simp [rows,on,rowSize]
  have injective : Function.Injective rows := by
    intro i j eq
    have enough : 2 ≤ (rows i).length := (lengths i).symm ▸ long
    let x := (rows i)[0]'(by omega)
    let y := (rows i)[1]'(by omega)
    have different : x ≠ y := fun h => by
      have := (simple i).getElem_inj_iff.mp h
      omega
    have xOn : x ∈ rows i := List.getElem_mem _
    have yOn : y ∈ rows i := List.getElem_mem _
    exact label.symm.injective (pairUnique (vertex.symm.injective.ne different)
      ((contains i x).mp xOn) ((contains i y).mp yOn)
      ((contains j x).mp (eq ▸ xOn)) ((contains j y).mp (eq ▸ yOn)))
  have free : BridgeFree (Before rows) 3 := by
    apply incidenceRowsFullThree (hit := fun i v => hit (label.symm i) (vertex.symm v))
    · intro a b x y apart ax ay bx by_
      exact label.symm.injective (pairUnique (vertex.symm.injective.ne apart) ax ay bx by_)
    · intro a b r x y z ab ra rb xy yz xz ax ay by_ bz rx rz
      exact noTriangle (label.symm.injective.ne ab) (label.symm.injective.ne ra) (label.symm.injective.ne rb)
        (vertex.symm.injective.ne xy) (vertex.symm.injective.ne yz) (vertex.symm.injective.ne xz)
        ax ay by_ bz rx rz
    · exact fun i v => (contains i v).mp
  have degrees (v) : (occurrences (fun i => (rows i).toFinset) v).card = degree := by
    have same : occurrences (fun i => (rows i).toFinset) v =
        ((univ : Finset I).filter (fun i => hit i (vertex.symm v))).map label.toEmbedding := by
      ext i
      rw [mem_occurrences,List.mem_toFinset,contains]
      simp only [Finset.mem_map,Finset.mem_filter,mem_univ,true_and]
      constructor
      · intro h
        exact ⟨label.symm i,h,label.apply_symm_apply i⟩
      · rintro ⟨j,h,equal⟩
        change label j = i at equal
        simpa only [← equal,Equiv.symm_apply_apply] using h
    rw [same,card_map,vertexSize]
  have caps : listOutputAverageCaps rows := by
    apply listOutputAverageCaps_of_widths rows simple degree length
    · intro v
      rw [degrees]
      exact ⟨div_le_self (by positivity) (by norm_num),le_rfl⟩
    · intro i
      rw [lengths]
      exact ⟨div_le_self (by positivity) (by norm_num),le_rfl⟩
  exact ⟨rows,injective,fun i => ⟨simple i,lengths i⟩,free,by simp [lengths],degrees,caps⟩

variable {F : Type*} [Field F]

/-- In every finite field, the map `z ↦ z² + z` misses a value. -/
theorem exists_missing_quadratic_value [Finite F] : ∃ ν : F, ∀ z : F, z^2+z ≠ ν := by
  have notInjective : ¬Function.Injective (fun z : F => z^2+z) := by
    intro injective
    have values : (0:F)^2+0 = (-1)^2+(-1) := by ring
    exact neg_ne_zero.mpr (one_ne_zero : (1:F) ≠ 0) (injective values).symm
  have notSurjective : ¬Function.Surjective (fun z : F => z^2+z) := by
    rwa [← Finite.injective_iff_surjective]
  unfold Function.Surjective at notSurjective
  push Not at notSurjective
  exact notSurjective

/-- A mass scale whose cube dominates the square of the budget product
and absorbs the linear charge controls all half-three-free masses. -/
theorem half_three_mass_le_four_of_volume {n p W cutoff : ℕ} (hn : 0 < n) (hp : 0 < p)
    (charge : 4*n+p ≤ W) (volume : (n*p)^2 ≤ W^3)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (half : HalfBridgeFree (Before paths) cutoff) (three : 3 ≤ cutoff) :
    (∑ i, (paths i).length) ≤ 4*W := by
  let M := ∑ i, (paths i).length
  let S := M-M/4-(4*n+p)
  have bound : S^3 ≤ 6*(n*p)^2 :=
    half_three_latest_intersection_shifted_mass_cube_le hn hp paths simple half three 3
  by_contra! excess
  have floor : 4*(M/4) ≤ M := Nat.mul_div_le _ _
  have gap : 2*W < S := by dsimp only [S]; omega
  have cap : S^3 ≤ (2*W)^3 := calc
    _ ≤ 6*(n*p)^2 := bound
    _ ≤ 6*W^3 := Nat.mul_le_mul_left _ volume
    _ ≤ 8*W^3 := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring
  exact (not_lt_of_ge cap) (pow_lt_pow_left₀ gap (Nat.zero_le _) (by decide : 3 ≠ 0))

/-- A regular exact-budget full-three witness certifies literal half
feasibility. An upper bound of four witness masses on every half
family then gives all four starting-average caps at the literal maximum. -/
theorem literal_half_maximum_frozen_full_three_of_regular_rows {n p length degree : ℕ}
    (hn : 0 < n) (hp : 0 < p) (rows : Fin p → List (Fin n))
    (distinct : Function.Injective rows) (valid : ∀ i, rows i ≠ [] ∧ (rows i).Nodup)
    (free : BridgeFree (Before rows) 3)
    (lengths : ∀ i, (rows i).length = length)
    (degrees : ∀ v, (occurrences (fun i => (rows i).toFinset) v).card = degree)
    (balance : n*degree = p*length)
    (upperBound : ∀ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) →
      HalfBridgeFree (Before paths) 3 → (∑ i, (paths i).length) ≤ 4*(p*length)) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ HalfBridgeFree (Before paths) 3 ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → HalfBridgeFree (Before other) 3 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      (∑ i, (rows i).length) ≤ M ∧ M ≤ 4*(∑ i, (rows i).length) ∧ frozenListCaps n p M rows := by
  obtain ⟨paths,injective,well,half,maximal,_,_⟩ := localOrderDistinctExtremal_isDense (k := 3) true hp
    ⟨rows,distinct,valid,free.halfFree⟩
  let M := ∑ i, (paths i).length
  have mass : (∑ i, (rows i).length) = p*length := by simp [lengths]
  have limit : (∑ i, (rows i).length) ≤ M := maximal rows distinct valid free.halfFree
  have lower : p*length ≤ M := mass.symm.trans_le limit
  have upper : M ≤ 4*(p*length) := upperBound paths (fun i => (well i).2) half
  have intervals {budget width : ℕ} (budgetPos : 0 < budget) (same : budget*width = p*length) :
      (M:ℝ)/(4*(budget:ℝ)) ≤ width ∧ (width:ℝ) ≤ 4*(M:ℝ)/budget := by
    have volume : (budget:ℝ)*width = (p:ℝ)*length := by exact_mod_cast same
    have pos : (0:ℝ) < budget := Nat.cast_pos.mpr budgetPos
    have lowerR : (p:ℝ)*length ≤ M := by exact_mod_cast lower
    have upperR : (M:ℝ) ≤ 4*((p:ℝ)*length) := by exact_mod_cast upper
    refine ⟨(div_le_iff₀ (by positivity)).mpr ?_,(le_div_iff₀ pos).mpr ?_⟩
    · calc
        _ ≤ 4*((budget:ℝ)*width) := by rw [volume]; exact upperR
        _ = _ := by ring
    · calc
        _ = (p:ℝ)*length := by rw [mul_comm,volume]
        _ ≤ _ := by linarith only [lowerR,show (0:ℝ) ≤ M by positivity]
  have caps : frozenListCaps n p M rows := by
    simp only [frozenListCaps,degrees,lengths]
    exact ⟨fun _ => intervals hn balance,fun _ => intervals hp rfl⟩
  exact ⟨paths,injective,well,half,maximal,limit,by rw [mass]; exact upper,caps⟩

end OnlineReachabilityPreservers
