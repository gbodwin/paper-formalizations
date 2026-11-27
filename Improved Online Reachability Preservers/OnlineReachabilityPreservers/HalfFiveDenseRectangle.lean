import OnlineReachabilityPreservers.HalfFiveProjection
import OnlineReachabilityPreservers.LocalFrozenLowMass

/-! A small support rectangle allows both width splits after opposite pruning. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

/-- The mass on the specified vertex and row sets of a simple list family. -/
def listRectangleMass {V I : Type*} [DecidableEq V] (paths : I → List V)
    (vertices : Finset V) (rows : Finset I) : ℕ :=
  ∑ i ∈ rows, ((paths i).toFinset ∩ vertices).card

private theorem dense_rectangle_support_charge {M K q width count support : ℕ}
    (positive : 0 < M) (qPos : 0 < q) (widthPos : 0 < width)
    (capacity : 31*M ≤ 8*(width*q)) (used : width*count ≤ support+K)
    (supportBudget : support ≤ M) (upper : K ≤ M) :
    count ≤ q ∧ ((M:ℝ)/(4*(q:ℝ)))*(count:ℝ) ≤ 2*((support:ℝ)+(K:ℝ))/31 := by
  have fit : count ≤ q := by
    apply (Nat.mul_le_mul_left_iff widthPos).mp
    omega
  have paid : 31*M*count ≤ 8*q*(support+K) := calc
    _ ≤ (8*(width*q))*count := Nat.mul_le_mul_right _ capacity
    _ = (8*q)*(width*count) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ used
  have realPaid : 31*(M:ℝ)*(count:ℝ) ≤ 8*(q:ℝ)*((support:ℝ)+(K:ℝ)) := by exact_mod_cast paid
  have qp : (0:ℝ) < q := by exact_mod_cast qPos
  refine ⟨fit,(mul_le_mul_iff_right₀ (show 0 < 124*(q:ℝ) by positivity)).mp ?_⟩
  calc
    _ = 31*(M:ℝ)*(count:ℝ) := by
      field_simp
      ring
    _ ≤ _ := realPaid
    _ = _ := by ring

/-- Keep a small support rectangle, prune opposite intersections, and
split at the original widths. Each support times its width must fit the
original mass. The last inequality pays for peeling on the split supports. -/
theorem regularization_list_frozen_half_five_of_dense_rectangle {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (A : Finset (Fin n)) (B : Finset (Fin p))
    (vRoom : (4*(∑ i, (paths i).length)/n)*A.card ≤ ∑ i, (paths i).length)
    (pRoom : (4*(∑ i, (paths i).length)/p)*B.card ≤ ∑ i, (paths i).length)
    (margin : let M := ∑ i, (paths i).length
      31*M+1280*((4*M/n)*A.card+(4*M/p)*B.card) ≤ 8640*listRectangleMass paths A B) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 640*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  classical
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retain,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free (by decide) hn hp dense long low
    exact ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree.halfFree,by omega,upper,caps⟩
  let D := 4*M/n
  let L := 4*M/p
  let selected (i : Fin p) := if i ∈ B then (paths i).filter (fun v => decide (v ∈ A)) else []
  have selectedSub (i : Fin p) : (selected i).Sublist (paths i) := by
    by_cases h : i ∈ B <;> simp only [selected, ite_eq_left, h]
    · exact List.filter_sublist
    · exact List.nil_sublist _
  have selectedSimple (i : Fin p) : (selected i).Nodup := (selectedSub i).nodup (simple i)
  have selectedFree : HalfBridgeFree (Before selected) 5 := fun _ small b earlier =>
    free small (b.mapPaths id Function.injective_id (fun i _ _ step =>
      listBefore_of_sublist (simple i) (selectedSub i) step)) earlier
  have selectMass : (∑ i, (selected i).length) = listRectangleMass paths A B := calc
    _ = ∑ i, if i ∈ B then ((paths i).toFinset ∩ A).card else 0 := by
      apply sum_congr rfl
      intro i _
      by_cases hi : i ∈ B
      · rw [ite_eq_left hi]
        have mapped := congrArg List.length (restrictListPath_map (paths i) A)
        rw [List.length_map] at mapped
        simpa only [selected,ite_eq_left hi] using mapped.symm.trans (restrictListPath_length (simple i) A)
      · simp [hi,selected]
    _ = _ := by
      rw [← sum_filter]
      congr 1
      ext i
      simp
  let pruned := removeOppositeIntersections selected
  have prunedSub (i : Fin p) : (pruned i).Sublist (selected i) :=
    removeOppositeIntersections_sublist selected i
  have prunedSimple (i : Fin p) : (pruned i).Nodup := (prunedSub i).nodup (selectedSimple i)
  have prunedFree := removeOppositeIntersections_halfFree selectedSimple selectedFree
  have onRectangle {i : Fin p} {x : Fin n} (present : x ∈ pruned i) : i ∈ B ∧ x ∈ A := by
    have existsOld := (prunedSub i).subset present
    by_cases onRow : i ∈ B
    · rw [show selected i = (paths i).filter (fun v => decide (v ∈ A)) by simp [selected,onRow]] at existsOld
      exact ⟨onRow,of_decide_eq_true (List.mem_filter.mp existsOld).2⟩
    · simp [selected,onRow] at existsOld
  let kept := restrictListPaths pruned A B
  let K := ∑ i, (kept i).length
  have keptSimple (i : B) : (kept i).Nodup := restrictListPath_nodup (prunedSimple i.val) A
  have keptFree := restrictListPaths_halfFree prunedSimple prunedFree A B
  have unique {i j : B} {x y : A} (ne : i ≠ j)
      (xi : x ∈ kept i) (xj : x ∈ kept j) (yi : y ∈ kept i) (yj : y ∈ kept j) : x = y :=
    restrictListPaths_unique
      (fun {_ _ _ _} different xa xb ya yb =>
        removeOppositeIntersections_unique selectedSimple selectedFree (by decide) different xa xb ya yb)
      A B ne xi xj yi yj
  have prunedMass : K = ∑ i, (pruned i).length := calc
    _ = ∑ i : B, (pruned i.val).length := by
      apply sum_congr rfl
      intro i _
      change (restrictListPath (pruned i.val) A).length = _
      rw [restrictListPath_length (prunedSimple i.val),
        inter_eq_left.mpr (fun x hx => (onRectangle (List.mem_toFinset.mp hx)).2),
        List.toFinset_card_of_nodup (prunedSimple i.val)]
    _ = ∑ i ∈ B, (pruned i).length := B.sum_coe_sort (fun i => (pruned i).length)
    _ = _ := sum_subset (subset_univ _) (fun i _ out => List.length_eq_zero_iff.mpr
      (List.eq_nil_iff_forall_not_mem.mpr (fun _ present => out (onRectangle present).1)))
  have halfMass : listRectangleMass paths A B ≤ 2*K := by
    rw [← selectMass,prunedMass]
    exact removeOppositeIntersections_mass selectedSimple selectedFree (by decide)
  have Kupper : K ≤ M := by
    rw [prunedMass]
    exact sum_le_sum (fun i _ => ((prunedSub i).trans (selectedSub i)).length_le)
  have Dpos : 0 < D := (four_average_width hn dense).1
  have Lpos : 0 < L := (four_average_width hp long).1
  have capacityD : 31*M ≤ 8*(D*n) := by
    have high : 8*n ≤ M := by have w := le_max_left n p; omega
    have floor := four_average_width_product hn (M := M)
    change 4*M < D*n+n at floor
    omega
  have capacityL : 31*M ≤ 8*(L*p) := by
    have high : 8*p ≤ M := by have w := le_max_right n p; omega
    have floor := four_average_width_product hp (M := M)
    change 4*M < L*p+p at floor
    omega
  let rows := listRegularizedPaths kept D L
  let v := Fintype.card (ListVertexBlockIndex kept D)
  let q := Fintype.card (ListBlockIndex (splitListVertices kept D) L)
  obtain ⟨vSize,qSize⟩ := regularization_list_counts kept keptSimple Dpos Lpos
  change v ≤ Fintype.card A+K/D at vSize
  change q ≤ Fintype.card B+K/L at qSize
  rw [Fintype.card_coe] at vSize qSize
  have vCost : D*v ≤ D*A.card+K := calc
    _ ≤ D*(A.card+K/D) := Nat.mul_le_mul_left _ vSize
    _ = D*A.card+(K/D)*D := by ring
    _ ≤ _ := Nat.add_le_add_left (Nat.div_mul_le_self _ _) _
  have qCost : L*q ≤ L*B.card+K := calc
    _ ≤ L*(B.card+K/L) := Nat.mul_le_mul_left _ qSize
    _ = L*B.card+(K/L)*L := by ring
    _ ≤ _ := Nat.add_le_add_left (Nat.div_mul_le_self _ _) _
  obtain ⟨vFit,vFee⟩ := dense_rectangle_support_charge (hn.trans_le dense) hn Dpos capacityD vCost vRoom Kupper
  obtain ⟨qFit,qFee⟩ := dense_rectangle_support_charge (hp.trans_le long) hp Lpos capacityL qCost pRoom Kupper
  have rowsSimple := listRegularizedPaths_simple kept keptSimple D L
  have rowsFree := listRegularizedPaths_halfFree_five_of_unique_intersections keptSimple keptFree
    (fun {_ _ _ _} => unique) D L
  obtain ⟨mass, lengthCap, degreeCap⟩ := regularization_list_mass_caps kept keptSimple D L Dpos Lpos
  have counted : (∑ i, (rows i).toFinset.card) = K :=
    (sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (rowsSimple i))).trans mass
  apply regularization_list_frozen_after_kept_vertices (half := true) (k := 5) (retention := 640)
    rows rowsSimple rowsFree hn hp dense long (by decide) univ (by simpa only [card_univ] using vFit) qFit
    lengthCap degreeCap (mass.trans_le Kupper)
  rw [card_univ, sum_occurrences]
  change (M:ℝ)/640 ≤ ((∑ i, (rows i).toFinset.card : ℕ):ℝ)-(M:ℝ)/(4*(n:ℝ))*v-(M:ℝ)/(4*(p:ℝ))*q
  rw [counted]
  have curve : 31*M+1280*(D*A.card+L*B.card) ≤ 17280*K := calc
    _ ≤ 8640*listRectangleMass paths A B := margin
    _ ≤ 8640*(2*K) := Nat.mul_le_mul_left _ halfMass
    _ = _ := by ring
  have enough : 31*(M:ℝ)+1280*((D:ℝ)*A.card+(L:ℝ)*B.card) ≤ 17280*(K:ℝ) := by
    exact_mod_cast curve
  change (M:ℝ)/(4*(n:ℝ))*v ≤ 2*(((D*A.card:ℕ):ℝ)+(K:ℝ))/31 at vFee
  change (M:ℝ)/(4*(p:ℝ))*q ≤ 2*(((L*B.card:ℕ):ℝ)+(K:ℝ))/31 at qFee
  simp only [Nat.cast_mul] at vFee qFee
  change (M:ℝ)/640 ≤ (K:ℝ)-(M:ℝ)/(4*(n:ℝ))*v-(M:ℝ)/(4*(p:ℝ))*q
  linarith only [vFee,qFee,enough,Nat.cast_nonneg (α := ℝ) M]

private theorem listRectangleMass_row_union {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (A : Finset (Fin n)) (B : Finset (Fin p)) :
    (∑ x ∈ A, (occurrences (fun i => (paths i).toFinset) x).card) + (∑ i ∈ B, (paths i).length) ≤
      (∑ i, (paths i).length) + listRectangleMass paths A B := by
  let Z (i : Fin p) := (paths i).toFinset
  have vMass : (∑ x ∈ A, (occurrences Z x).card) = ∑ i, (Z i ∩ A).card := calc
    _ = ∑ i : (univ : Finset (Fin p)), (rectanglePaths Z A univ i).card :=
      (rectanglePaths_univ_rows_mass Z A).symm
    _ = ∑ i : (univ : Finset (Fin p)), (Z i.val ∩ A).card := by
      apply sum_congr rfl
      intro i _
      rw [← restrictListPaths_toFinset paths A univ]
      change (restrictListPath (paths i.val) A).toFinset.card = _
      rw [List.toFinset_card_of_nodup (restrictListPath_nodup (simple i.val) A)]
      exact restrictListPath_length (simple i.val) A
    _ = _ := by simp
  have maskedSplit : (∑ i, (Z i ∩ A).card) =
      (∑ i ∈ univ \ B, (Z i ∩ A).card)+(∑ i ∈ B, (Z i ∩ A).card) :=
    (sum_sdiff (subset_univ B)).symm
  have rowSplit : (∑ i, (paths i).length) =
      (∑ i ∈ univ \ B, (paths i).length)+(∑ i ∈ B, (paths i).length) :=
    (sum_sdiff (subset_univ B)).symm
  have outside : (∑ i ∈ univ \ B, (Z i ∩ A).card) ≤ ∑ i ∈ univ \ B, (paths i).length :=
    sum_le_sum (fun i _ => by
      rw [← List.toFinset_card_of_nodup (simple i)]
      exact card_le_card inter_subset_left)
  change (∑ x ∈ A, (occurrences Z x).card) + (∑ i ∈ B, (paths i).length) ≤
    (∑ i, (paths i).length) + (∑ i ∈ B, (Z i ∩ A).card)
  rw [vMass,maskedSplit,rowSplit]
  omega

/-- As an application, the same conclusion holds when vertices over the
degree cap and paths over the length cap share at least 57/320 of
the original mass. An incidence in both supports is counted only once
when bounding the union of the two supports. -/
theorem regularization_list_frozen_half_five_of_overfull_rectangle {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (large : let M := ∑ i, (paths i).length
      let degree (x : Fin n) := (occurrences (fun i => (paths i).toFinset) x).card
      57*M ≤ 320*listRectangleMass paths
        (univ.filter (fun v => 4*M/n < degree v)) (univ.filter (fun i => 4*M/p < (paths i).length))) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 640*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧ frozenListCaps n p M rows := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let degree (x : Fin n) := (occurrences (fun i => (paths i).toFinset) x).card
  let A := univ.filter (fun x => D < degree x)
  let B := univ.filter (fun i => L < (paths i).length)
  have vRoom : D*A.card ≤ M := calc
    _ = ∑ x ∈ A, D := by simp [Nat.mul_comm D]
    _ ≤ ∑ x ∈ A, degree x := sum_le_sum (fun x hx => (mem_filter.mp hx).2.le)
    _ ≤ ∑ x, degree x := sum_le_sum_of_subset (subset_univ _)
    _ = M := by
      unfold degree
      rw [sum_occurrences]
      exact sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (simple i))
  have qRoom : L*B.card ≤ M := calc
    _ = ∑ i ∈ B, L := by simp [Nat.mul_comm L]
    _ ≤ ∑ i ∈ B, (paths i).length := sum_le_sum (fun i hi => (mem_filter.mp hi).2.le)
    _ ≤ M := sum_le_sum_of_subset (subset_univ _)
  have combined : D*A.card+L*B.card ≤ M+listRectangleMass paths A B := calc
    _ = (∑ x ∈ A, D)+(∑ i ∈ B, L) := by simp [Nat.mul_comm D,Nat.mul_comm L]
    _ ≤ (∑ x ∈ A, degree x)+(∑ i ∈ B, (paths i).length) :=
      Nat.add_le_add (sum_le_sum (fun x hx => (mem_filter.mp hx).2.le))
        (sum_le_sum (fun i hi => (mem_filter.mp hi).2.le))
    _ ≤ _ := listRectangleMass_row_union paths simple A B
  change 57*M ≤ 320*listRectangleMass paths A B at large
  apply regularization_list_frozen_half_five_of_dense_rectangle paths simple free hn hp dense long
    A B vRoom qRoom
  change 31*M+1280*(D*A.card+L*B.card) ≤ 8640*listRectangleMass paths A B
  omega

end OnlineReachabilityPreservers
