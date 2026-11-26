import OnlineReachabilityPreservers.VertexPartitionCleaning

/-! A common vertex partition with controlled clipping at the path cap. -/

namespace OnlineReachabilityPreservers

open Finset

private theorem same_color_count {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    {x y : V} (different : x ≠ y) :
    q*((univ : Finset (V → Fin q)).filter (fun f => f x = f y)).card = Fintype.card (V → Fin q) := by
  classical
  let matched := (univ : Finset (V → Fin q)).filter (fun f => f x = f y)
  let assign : matched × Fin q → (V → Fin q) := fun a => Function.update a.1.val y a.2
  have atMatch (f : matched) : f.val x = f.val y := (mem_filter.mp f.property).2
  let undo (f : V → Fin q) : matched × Fin q :=
    (⟨Function.update f y (f x),mem_filter.mpr ⟨mem_univ _,by simp [Function.update_of_ne different]⟩⟩,f y)
  let bijection : matched × Fin q ≃ (V → Fin q) :=
    { toFun := assign
      invFun := undo
      left_inv := by
        rintro ⟨f,c⟩
        apply Prod.ext
        · apply Subtype.ext
          funext z
          change Function.update (assign (f,c)) y (assign (f,c) x) z = f.val z
          by_cases same : z = y
          · subst z
            simpa [assign,Function.update_of_ne different] using atMatch f
          · simp [assign,Function.update_of_ne same]
        · simp [assign,undo]
      right_inv := by
        intro f
        funext z
        change Function.update (Function.update f y (f x)) y (f y) z = f z
        by_cases same : z = y
        · subst z
          simp
        · simp [Function.update_of_ne same] }
  simpa only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,Nat.mul_comm] using Fintype.card_congr bijection

private def coloredPairCount {V : Type*} [DecidableEq V] {q : ℕ} (S : Finset V) (part : V → Fin q) : ℕ :=
  (S.offDiag.filter fun edge => part edge.1 = part edge.2).card

private theorem coloredPairCount_sum {V : Type*} [DecidableEq V] [Fintype V] {q : ℕ} (S : Finset V) :
    q*(∑ part : V → Fin q, coloredPairCount S part) = Fintype.card (V → Fin q)*S.offDiag.card := by
  classical
  have count {edge : V × V} (inside : edge ∈ S.offDiag) :
      q*(∑ part : V → Fin q, if part edge.1 = part edge.2 then 1 else 0) = Fintype.card (V → Fin q) := by
    rw [← card_filter]
    exact same_color_count (mem_offDiag.mp inside).2.2
  calc
    _ = q*(∑ edge ∈ S.offDiag, ∑ part : V → Fin q, if part edge.1 = part edge.2 then 1 else 0) := by
      congr 1
      simp only [coloredPairCount,card_filter]
      rw [sum_comm]
    _ = ∑ edge ∈ S.offDiag, q*(∑ part : V → Fin q, if part edge.1 = part edge.2 then 1 else 0) :=
      mul_sum ..
    _ = _ := by
      rw [sum_congr rfl (fun edge h => count h),sum_const,nsmul_eq_mul,Nat.mul_comm]
      simp

private theorem exists_color_with_few_pairs {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (sets : I → Finset V) {q : ℕ} (positive : 0 < q) :
    ∃ part : V → Fin q, q*(∑ i, coloredPairCount (sets i) part) ≤ ∑ i, (sets i).offDiag.card := by
  classical
  let cost (part : V → Fin q) := ∑ i, coloredPairCount (sets i) part
  have nonempty : (univ : Finset (V → Fin q)).Nonempty := ⟨fun _ => ⟨0,positive⟩,mem_univ _⟩
  obtain ⟨best,_,minimal⟩ := exists_min_image univ cost nonempty
  let C := Fintype.card (V → Fin q)
  have cardPos : 0 < C := card_pos.mpr nonempty
  have sumCost : C*cost best ≤ ∑ part : V → Fin q, cost part := by
    calc
      _ = ∑ _part : V → Fin q, cost best := by simp [C]
      _ ≤ _ := sum_le_sum (fun p hp => minimal p hp)
  have total : q*(∑ part : V → Fin q, cost part) = C*(∑ i, (sets i).offDiag.card) := by
    change q*(∑ part : V → Fin q, ∑ i, coloredPairCount (sets i) part) = _
    rw [sum_comm,mul_sum,mul_sum]
    exact sum_congr rfl (fun i _ => coloredPairCount_sum (sets i))
  refine ⟨best,Nat.le_of_mul_le_mul_left ?_ cardPos⟩
  calc
    C*(q*cost best) = q*(C*cost best) := by ring
    _ ≤ q*(∑ part : V → Fin q, cost part) := Nat.mul_le_mul_left _ sumCost
    _ = _ := total

private theorem coloredPairCount_sum_fibers {V : Type*} [DecidableEq V] {q : ℕ}
    (S : Finset V) (part : V → Fin q) :
    coloredPairCount S part = ∑ b : Fin q, (S.filter (fun x => part x = b)).offDiag.card := by
  let edges := S.offDiag.filter fun edge => part edge.1 = part edge.2
  have equal (b : Fin q) : edges.filter (fun edge => part edge.1 = b) =
      (S.filter (fun x => part x = b)).offDiag := by
    ext e
    simp only [edges,mem_filter,mem_offDiag]
    exact ⟨fun h => ⟨⟨h.1.1.1,h.2⟩,⟨h.1.1.2.1,h.1.2.symm.trans h.2⟩,h.1.1.2.2⟩,
      fun h => ⟨⟨⟨h.1.1,h.2.1.1,h.2.2⟩,h.1.2.trans h.2.1.2.symm⟩,h.1.2⟩⟩
  change edges.card = _
  rw [card_eq_sum_card_fiberwise (f := fun edge : V × V => part edge.1) (t := univ) (by simp)]
  exact sum_congr rfl (fun b _ => congrArg Finset.card (equal b))

private theorem overflow_le_ordered_pairs {x cap : ℕ} (positive : 0 < cap) :
    (4*cap-2)*(x-cap) ≤ x*x-x := by
  by_cases small : x ≤ cap
  · simp [Nat.sub_eq_zero_of_le small]
  have large : cap ≤ x := (lt_of_not_ge small).le
  have capBound : 2 ≤ 4*cap := by omega
  have selfBound : x ≤ x*x := by
    have xn : 1 ≤ x := positive.trans_le large
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left x xn
  have product : 0 ≤ ((x:ℤ)-2*(cap:ℤ)+1)*((x:ℤ)-2*(cap:ℤ)) := by
    by_cases low : x < 2*cap
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  have bound : (4*(cap:ℤ)-2)*((x:ℤ)-(cap:ℤ)) ≤ (x:ℤ)*(x:ℤ)-(x:ℤ) := by nlinarith
  exact_mod_cast (by push_cast [Nat.cast_sub large,Nat.cast_sub capBound,Nat.cast_sub selfBound]; exact bound :
    (↑((4*cap-2)*(x-cap)) : ℤ) ≤ ↑(x*x-x))

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype V] [Fintype I]

/-- Cap each piece after restricting a path to a common vertex part. -/
def clippedPartitionListPaths {q : ℕ} (paths : I → List V) (part : V → Fin q) (cap : ℕ)
    (piece : I ×ₗ Fin q) : List V :=
  (partitionListPaths paths part piece).take cap

omit [LinearOrder I] in
/-- Some common partition loses no more incidences than the ordered-pair
count divided by the number of parts and the clipping coefficient. -/
theorem exists_clippedPartitionListPaths {q cap : ℕ} (positive : 0 < q) (capPositive : 0 < cap)
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup) :
    ∃ part : V → Fin q, q*(4*cap-2)*
        ((∑ i, (paths i).length) - ∑ j, (clippedPartitionListPaths paths part cap j).length) ≤
      ∑ i, (paths i).length*((paths i).length-1) := by
  let sets := fun i => (paths i).toFinset
  obtain ⟨part,good⟩ := exists_color_with_few_pairs sets positive
  refine ⟨part,?_⟩
  let pieces := partitionListPaths paths part
  let kept := clippedPartitionListPaths paths part cap
  have length (i : I) (b : Fin q) : (pieces (toLex (i,b))).length = ((sets i).filter (fun x => part x = b)).card := by
    have relevant : (pieces (toLex (i,b))).Nodup := List.filter_sublist.nodup (simple i)
    rw [← List.toFinset_card_of_nodup relevant]
    congr 1
    ext x
    change x ∈ ((paths i).filter fun v => decide (part v = b)).toFinset ↔
      x ∈ (paths i).toFinset.filter (fun v => part v = b)
    simp only [List.mem_toFinset,List.mem_filter,mem_filter,decide_eq_true_eq]
  let loss (j : I ×ₗ Fin q) := (pieces j).length-cap
  have sumLoss : (∑ j, loss j)+(∑ j, (kept j).length) = ∑ i, (paths i).length := by
    rw [← partitionListPaths_mass paths part simple,← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    change (pieces j).length-cap+((pieces j).take cap).length = _
    rw [List.length_take]
    change (pieces j).length-cap+min cap (pieces j).length = (pieces j).length
    omega
  have bounds : (4*cap-2)*(∑ j, loss j) ≤ ∑ i, coloredPairCount (sets i) part := calc
    _ = ∑ j, (4*cap-2)*loss j := mul_sum ..
    _ = ∑ a : I × Fin q, (4*cap-2)*loss (toLex a) :=
      (Equiv.sum_comp (toLex : (I × Fin q) ≃ (I ×ₗ Fin q)) _).symm
    _ = ∑ i, ∑ b : Fin q, (4*cap-2)*loss (toLex (i,b)) := Fintype.sum_prod_type _
    _ ≤ ∑ i, ∑ b : Fin q, ((sets i).filter fun x => part x = b).offDiag.card := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro b _
      rw [offDiag_card]
      change (4*cap-2)*((pieces (toLex (i,b))).length-cap) ≤ _
      rw [length]
      exact overflow_le_ordered_pairs capPositive
    _ = _ := sum_congr rfl (fun i _ => (coloredPairCount_sum_fibers (sets i) part).symm)
  have lossEq : (∑ i, (paths i).length) - (∑ j, (kept j).length) = ∑ j, loss j := by omega
  change q*(4*cap-2)*((∑ i, (paths i).length) - (∑ j, (kept j).length)) ≤ _
  rw [lossEq,Nat.mul_assoc]
  refine ((Nat.mul_le_mul_left q bounds).trans good).trans_eq (sum_congr rfl fun i _ => ?_)
  rw [offDiag_card,List.toFinset_card_of_nodup (simple i),Nat.mul_sub_one]

local notation "Before" => SourceAudit.BeforeIn

omit [Fintype V] [Fintype I] in
private theorem clipped_partition_allowed {q k cap : ℕ} {half : Bool}
    (paths : I → List V) (part : V → Fin q) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) :
    localOrderAdmissible half k (clippedPartitionListPaths paths part cap) := by
  let pieces := partitionListPaths paths part
  let kept := clippedPartitionListPaths paths part cap
  have valid : localOrderAdmissible half k pieces := partitionListPaths_admissible paths part simple allowed
  have lift {j x y} (step : Before kept j x y) : Before pieces j x y := by
    have nodup : (pieces j).Nodup := List.filter_sublist.nodup (simple (ofLex j).1)
    exact listBefore_of_sublist nodup (List.take_sublist cap (pieces j)) step
  cases half
  · intro d h
    exact ⟨fun b => (valid h).false (b.mapPaths id Function.injective_id (fun _ _ _ step => lift step))⟩
  · intro d h b earlier
    exact valid h (b.mapPaths id Function.injective_id (fun _ _ _ step => lift step)) earlier

/-- A subfamily with enough mass and a bounded sum of ordered pairs can
be clipped after a common vertex partition. The budget counts each
possible part separately. The pieces satisfy the original four caps after
degree regularization and peeling. -/
theorem regularization_list_frozen_by_clipped_vertex_partition {q k n p M lossBudget : ℕ}
    {half : Bool} (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths)
    (degreeCondition : (half = true → k ≤ 4) ∨
      (∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ 4*M/n))
    (qPos : 0 < q) (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertices : Fintype.card V ≤ n) (room : Fintype.card I*q ≤ p)
    (pairs : (∑ i, (paths i).length*((paths i).length-1)) ≤ q*(4*(4*M/p)-2)*lossBudget)
    (enough : 3*M+4*lossBudget ≤ 4*(∑ i, (paths i).length))
    (massCap : (∑ i, (paths i).length) ≤ M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let width := 4*M/p
  have widthAtLeast : 4 ≤ width := (Nat.le_div_iff_mul_le hp).mpr (Nat.mul_le_mul_left _ long)
  have widthPositive : 0 < width := by omega
  obtain ⟨part,loss⟩ := exists_clippedPartitionListPaths qPos widthPositive paths simple
  let pieces := partitionListPaths paths part
  let kept := clippedPartitionListPaths paths part width
  have coefficient : 0 < q*(4*width-2) := Nat.mul_pos qPos (by omega)
  have less : (∑ i, (paths i).length) - (∑ i, (kept i).length) ≤ lossBudget :=
    Nat.le_of_mul_le_mul_left (loss.trans pairs) coefficient
  have sub (i) : (kept i).Sublist (pieces i) := List.take_sublist width (pieces i)
  have pieceSimple (i) : (pieces i).Nodup := List.filter_sublist.nodup (simple (ofLex i).1)
  have resultSimple (i) : (kept i).Nodup := (sub i).nodup (pieceSimple i)
  have resultAdmissible : localOrderAdmissible half k kept := clipped_partition_allowed paths part simple allowed
  have degree : (half = true → k ≤ 4) ∨ (∀ v, (occurrences (fun i => (kept i).toFinset) v).card ≤ 4*M/n) :=
    degreeCondition.imp_right fun bounded v => by
      have subset : occurrences (fun i => (kept i).toFinset) v ⊆ occurrences (fun i => (pieces i).toFinset) v := by
        intro i inside
        have onKept : v ∈ (kept i).toFinset := (mem_occurrences (marks := fun j => (kept j).toFinset)).mp inside
        exact mem_occurrences.mpr (List.mem_toFinset.mpr ((sub i).subset (List.mem_toFinset.mp onKept)))
      exact (card_le_card subset).trans ((partitionListPaths_degree paths part v).le.trans (bounded v))
  have upper : (∑ i, (kept i).length) ≤ M :=
    (sum_le_sum (fun i _ => (sub i).length_le)).trans ((partitionListPaths_mass paths part simple).trans_le massCap)
  refine regularization_list_frozen_after_length_cap kept resultSimple resultAdmissible hn hp dense long vertices ?_
    (fun i => ?_) degree (by omega) upper
  · simpa only [Fintype.card_lex,Fintype.card_prod,Fintype.card_fin] using room
  · exact List.length_take.trans_le (min_le_left _ _)

end OnlineReachabilityPreservers
