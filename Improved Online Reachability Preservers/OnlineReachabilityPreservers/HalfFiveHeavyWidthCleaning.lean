import OnlineReachabilityPreservers.HalfFiveSharedWidthCleaning

/-! Peeling on the actual vertex support when overfull vertices carry most of the mass. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

private theorem sum_length_filter_eq_degrees {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup) (A : Finset V) :
    (∑ i, ((paths i).filter fun v => decide (v ∈ A)).length) =
      ∑ v ∈ A, (occurrences (fun j => (paths j).toFinset) v).card := by
  let clean (i : I) := (paths i).filter fun v => decide (v ∈ A)
  let original (i : I) := (paths i).toFinset
  let clipped (i : I) := (clean i).toFinset
  calc
    _ = ∑ i, (clipped i).card :=
      sum_congr rfl fun i _ => (List.toFinset_card_of_nodup (List.filter_sublist.nodup (simple i))).symm
    _ = ∑ v, (occurrences clipped v).card := (sum_occurrences clipped).symm
    _ = ∑ v, if v ∈ A then (occurrences original v).card else 0 := by
      apply sum_congr rfl
      intro v _
      by_cases inside : v ∈ A
      · rw [ite_eq_left inside]
        apply congrArg Finset.card
        ext j
        simp [mem_occurrences,clipped,clean,original,inside]
      · rw [ite_eq_right inside,card_eq_zero]
        ext j
        simp [mem_occurrences,clipped,clean,inside]
    _ = _ := by
      rw [← sum_filter]
      congr 1
      ext v
      simp

private theorem width_times_degree_support {I V : Type*} [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V]
    (paths : I → List V) (A : Finset V) (D : ℕ) :
    D*(univ.filter (fun v : ListVertexBlockIndex paths D => v.fst ∈ A)).card ≤
      D*A.card + ∑ v ∈ A, (occurrences (fun i => (paths i).toFinset) v).card := by
  let deg (v : V) := (occurrences (fun i => (paths i).toFinset) v).card
  let copies := univ.filter (fun v : ListVertexBlockIndex paths D => v.fst ∈ A)
  have count : copies.card = ∑ v ∈ A, (deg v/D+1) := by
    rw [show copies.card = ∑ _ ∈ copies, (1:ℕ) by simp]
    unfold copies
    rw [sum_filter]
    change (∑ v : (Σ x : V, Fin (blockCount (occurrences (fun i => (paths i).toFinset) x) D)),
      if v.fst ∈ A then (1:ℕ) else 0) = _
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ v, if v ∈ A then deg v/D+1 else 0 := by
        apply sum_congr rfl
        intro v _
        by_cases h : v ∈ A
        · rw [ite_eq_left h]
          simp only [ite_eq_left h, Finset.sum_const, nsmul_eq_mul, mul_one]
          exact Finset.card_univ.trans (Fintype.card_fin _)
        · simp [h]
      _ = _ := by
        rw [← sum_filter]
        congr 1
        ext v
        simp
  calc
    _ = ∑ v ∈ A, D*(deg v/D+1) := by rw [show _ = copies.card from rfl,count,mul_sum]
    _ ≤ ∑ v ∈ A, (D+deg v) := by
      apply sum_le_sum
      intro v _
      have floor := Nat.div_mul_le_self (deg v) D
      rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm D]
      omega
    _ = _ := by rw [sum_add_distrib]; simp [Nat.mul_comm,deg]

/-- If the overfull vertices carry at least 71 percent of the mass,
their actual copy budget suffices for half-five cleaning. -/
theorem regularization_list_frozen_half_five_of_overfull_degree_mass {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (large : let M := ∑ i, (paths i).length
      let D := 4*M/n
      let degree (x : Fin n) := (occurrences (fun i => (paths i).toFinset) x).card
      71*M ≤ 100*(∑ v ∈ univ.filter (fun x => D < degree x), degree v)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n',hn',p',hp',clean,cleanSimple,legal,mass,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free (by decide) hn hp dense long low
    exact ⟨n',hn',p',hp',clean,cleanSimple,fun _ small b _ => (legal small).false b,
      mass.trans (Nat.mul_le_mul_right _ (by decide)),upper,caps⟩
  let D := 4*M/n
  let L := 4*M/p
  let J := ListBlockIndex paths L
  let raw := splitListPaths paths L
  let degree (x : Fin n) := (occurrences (fun i => (paths i).toFinset) x).card
  let A := (univ : Finset (Fin n)).filter fun v => D < degree v
  let S := ∑ v ∈ A, degree v
  change 71*M ≤ 100*S at large
  have dPos : 0 < D := (four_average_width hn dense).1
  have lPos : 0 < L := (four_average_width hp long).1
  have pDense : 8*p ≤ M := by have bound := le_max_right n p; omega
  have capacity : 31*M ≤ 8*(D*n) := by
    have bound := le_max_left n p
    have floor := four_average_width_product hn (M := M)
    change 4*M < D*n+n at floor
    omega
  obtain ⟨B,budget,rowLoss⟩ := trimSplitListPaths_at_original_width paths simple hp pDense
  let Y := ∑ j ∈ univ \ B, (raw j).length
  change 31*Y ≤ 2*M at rowLoss
  let rawHeavy (j : J) := (raw j).filter fun v => decide (v ∈ A)
  have rawSimple (j : J) : (raw j).Nodup := List.filter_sublist.nodup (simple j.fst)
  have rawHeavySimple (j : J) : (rawHeavy j).Nodup := List.filter_sublist.nodup (rawSimple j)
  have rawMass : (∑ j : J, (raw j).length) = M := splitListPaths_size paths simple L
  have rawHeavyMass : (∑ j : J, (rawHeavy j).length) = S := by
    refine (sum_length_filter_eq_degrees raw rawSimple A).trans ?_
    exact sum_congr rfl (fun v _ => splitListPaths_degree_eq paths simple L v)
  have upperS : S ≤ M := by
    rw [← rawHeavyMass,← rawMass]
    exact sum_le_sum fun j _ => List.filter_sublist.length_le
  have heavyRawRetained : S ≤ (∑ j ∈ B, (rawHeavy j).length)+Y := by
    rw [← rawHeavyMass,← sum_sdiff (subset_univ B)]
    exact (Nat.add_le_add_right (sum_le_sum fun _ _ => List.filter_sublist.length_le) _).trans_eq (Nat.add_comm _ _)
  let affected := pieceIncidences rawHeavy B
  let col (a : J × Fin n) := reversePartnerColor paths a.2 a.1.fst
  obtain ⟨c,removed⟩ := exists_smallBoolColor affected col
  let deleted := sharedWidthDeletion paths D L c
  let rows := erasePieceIncidences raw deleted
  let heavyRows (j : J) := (rows j).filter fun v => decide (v ∈ A)
  let K := ∑ j ∈ B, (heavyRows j).length
  have rowSimple (j : J) : (rows j).Nodup := (erasePieceIncidences_sublist raw deleted j).nodup (rawSimple j)
  have heavySimple (j : J) : (heavyRows j).Nodup := List.filter_sublist.nodup (rowSimple j)
  have affected_eq : pieceIncidences heavyRows B = affected \ (affected.filter fun a => col a = c) := by
    ext a
    rcases a with ⟨j,v⟩
    have equality : (v ∈ heavyRows j) = (v ∈ raw j ∧ (j,v) ∉ deleted ∧ v ∈ A) := by
      apply propext
      simp only [heavyRows,List.mem_filter,decide_eq_true_eq,mem_erasePieceIncidences,and_assoc,rows]
    by_cases h : v ∈ A
    · by_cases inside : v ∈ raw j
      · have on : (j,v) ∈ pieceIncidences raw univ := mem_pieceIncidences.mpr ⟨mem_univ _,inside⟩
        have inUnion : (j,v) ∈ sharedWidthAffected paths D L := mem_union_right _
          (mem_filter.mpr ⟨on,(mem_filter.mp h).2⟩)
        by_cases onRow : j ∈ B <;>
          simp [mem_pieceIncidences,equality,h,inside,affected,rawHeavy,deleted,sharedWidthDeletion,inUnion,col,onRow]
      · simp [mem_pieceIncidences,equality,h,inside,affected,rawHeavy]
    · simp [mem_pieceIncidences,equality,h,affected,rawHeavy]
  have exactHeavy : K+(affected.filter fun a => col a = c).card = ∑ j ∈ B, (rawHeavy j).length := by
    change (∑ j ∈ B, (heavyRows j).length)+(affected.filter fun a => col a = c).card = _
    rw [← pieceIncidences_card heavySimple B,← pieceIncidences_card rawHeavySimple B]
    rw [affected_eq]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have heavyRetained : S ≤ 2*K+Y := by
    change 2*(affected.filter fun a => col a = c).card ≤ affected.card at removed
    have rawCount : affected.card = ∑ j ∈ B, (rawHeavy j).length := pieceIncidences_card rawHeavySimple B
    rw [rawCount] at removed
    omega
  have totalHeavy : (∑ v ∈ A, (occurrences (fun j => (rows j).toFinset) v).card) ≤ K+Y := by
    rw [← sum_length_filter_eq_degrees rows rowSimple A,← sum_sdiff (subset_univ B)]
    exact (Nat.add_le_add_right (sum_le_sum fun j _ =>
      List.filter_sublist.length_le.trans (erasePieceIncidences_sublist raw deleted j).length_le) _).trans_eq (Nat.add_comm _ _)
  have heavyCapacity : D*A.card ≤ S := by
    rw [show D*A.card = ∑ v ∈ A, D by simp [Nat.mul_comm]]
    exact sum_le_sum fun v h => (mem_filter.mp h).2.le
  let pieces := splitListVertices rows D
  let Q := (univ : Finset (ListVertexBlockIndex rows D)).filter fun v => v.fst ∈ A
  have copiesWidth : D*Q.card ≤ S+K+Y := calc
    _ ≤ D*A.card + ∑ v ∈ A, (occurrences (fun j => (rows j).toFinset) v).card :=
      width_times_degree_support rows A D
    _ ≤ S+(K+Y) := Nat.add_le_add heavyCapacity totalHeavy
    _ = _ := by omega
  have copiedMass : (∑ j : J, (pieces j).length) ≤ M := calc
    _ = ∑ j : J, (rows j).length := sum_congr rfl (fun j _ => splitListVertices_length rows D j)
    _ ≤ ∑ j : J, (raw j).length := sum_le_sum (fun j _ => (erasePieceIncidences_sublist raw deleted j).length_le)
    _ = M := rawMass
  have boundKY : K+Y ≤ M := by
    rw [← rawMass,← sum_sdiff (subset_univ B)]
    have le : K ≤ ∑ j ∈ B, (raw j).length :=
      sum_le_sum (fun j _ => List.filter_sublist.length_le.trans (erasePieceIncidences_sublist raw deleted j).length_le)
    exact (Nat.add_le_add_right le _).trans_eq (Nat.add_comm _ _)
  have vertexBudget : Q.card ≤ n := by
    apply (Nat.mul_le_mul_left_iff dPos).mp
    omega
  let chosen (j : B) := pieces j.val
  have chosenSimple (j : B) : (chosen j).Nodup := splitListVertices_simple rows D j.val (rowSimple j.val)
  have outputFree := sharedWidthRepair_halfFree paths simple free D L c
  have chosenFree : HalfBridgeFree (Before chosen) 5 := by
    intro k hk b earlier
    exact outputFree hk (b.mapPaths Subtype.val Subtype.val_injective (fun _ _ _ step => step)) earlier
  have chosenLength (j : B) : (chosen j).length ≤ L :=
    (splitListVertices_length rows D j.val).trans_le
      ((erasePieceIncidences_sublist raw deleted j.val).length_le.trans (localPathBlock_length _ (simple j.val.fst) lPos _))
  have chosenDegree (v : ListVertexBlockIndex rows D) :
      (occurrences (fun j => (chosen j).toFinset) v).card ≤ D := by
    have degreeAll : (occurrences (fun j => (pieces j).toFinset) v).card ≤ D := by
      rw [show (fun j => (pieces j).toFinset) =
        splitVertices (fun j => (rows j).toFinset) D from funext (splitListVertices_toFinset rows D)]
      exact splitVertices_degree _ dPos v
    refine (card_le_card_of_injOn Subtype.val ?_ ?_).trans degreeAll
    · intro j member
      exact mem_occurrences.mpr ((mem_occurrences (marks := fun j => (chosen j).toFinset)).mp member)
    · intro a _ b _ eq
      exact Subtype.ext eq
  have retainedMass : (∑ v ∈ Q, (occurrences (fun j => (chosen j).toFinset) v).card) = K := by
    rw [← sum_length_filter_eq_degrees chosen chosenSimple Q]
    have filterLength (j : B) : ((chosen j).filter fun v => decide (v ∈ Q)).length = (heavyRows j.val).length := by
      have mapEq : ((chosen j).filter fun v => decide (v ∈ Q)).map (·.fst) = heavyRows j.val := by
        have projection : (chosen j).map (·.fst) = rows j.val := splitListVertices_project rows D j.val
        unfold heavyRows
        rw [← projection, List.filter_map]
        congr 1
        ext v
        simp [Q,Function.comp_def]
      simpa only [List.length_map] using congrArg List.length mapEq
    rw [show (∑ j, ((chosen j).filter fun v => decide (v ∈ Q)).length) = ∑ j : B, (heavyRows j.val).length
      from sum_congr rfl (fun j _ => filterLength j)]
    exact sum_attach B (fun j => (heavyRows j).length)
  have upper : (∑ j : B, (chosen j).length) ≤ M := by
    rw [show (∑ j : B, (chosen j).length) = ∑ j ∈ B, (pieces j).length from sum_attach B (fun j => (pieces j).length)]
    exact (sum_le_sum_of_subset (subset_univ B)).trans copiedMass
  refine regularization_list_frozen_after_kept_vertices (half := true) (k := 5) (retention := 5000)
    chosen chosenSimple chosenFree hn hp dense long (by decide) Q vertexBudget
    (by simpa only [Fintype.card_coe] using budget) chosenLength chosenDegree upper ?_
  change (M:ℝ)/5000 ≤
    ((∑ v ∈ Q, (occurrences (fun j : B => (chosen j).toFinset) v).card : ℕ):ℝ)
      -(M:ℝ)/(4*(n:ℝ))*Q.card-(M:ℝ)/(4*(p:ℝ))*(Fintype.card B:ℝ)
  rw [retainedMass,Fintype.card_coe]
  have feeV : (M:ℝ)/(4*(n:ℝ))*(Q.card:ℝ) ≤ (D:ℝ)*(Q.card:ℝ)/(31/2) := by
    have cap : 31*(M:ℝ) ≤ 8*((D:ℝ)*(n:ℝ)) := by exact_mod_cast capacity
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 4*(n:ℝ))).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<31/2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right cap (show 0 ≤ (Q.card:ℝ) by positivity)]
  have feeP : (M:ℝ)/(4*(p:ℝ))*(B.card:ℝ) ≤ (M:ℝ)/4 := calc
    _ ≤ (M:ℝ)/(4*(p:ℝ))*(p:ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr budget) (by positivity)
    _ = _ := by field_simp [show (p:ℝ) ≠ 0 by exact_mod_cast hp.ne']
  have cw : (D:ℝ)*(Q.card:ℝ) ≤ (S:ℝ)+K+Y := by exact_mod_cast copiesWidth
  have hs : 71*(M:ℝ) ≤ 100*(S:ℝ) := by exact_mod_cast large
  have hk : (S:ℝ) ≤ 2*(K:ℝ)+Y := by exact_mod_cast heavyRetained
  have hy : 31*(Y:ℝ) ≤ 2*(M:ℝ) := by exact_mod_cast rowLoss
  linarith only [feeV,feeP,cw,hs,hk,hy,Nat.cast_nonneg (α := ℝ) M]

end OnlineReachabilityPreservers
