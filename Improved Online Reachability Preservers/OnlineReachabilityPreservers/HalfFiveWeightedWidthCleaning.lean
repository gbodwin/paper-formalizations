import OnlineReachabilityPreservers.HalfFiveSharedWidthCleaning

/-! Trim path pieces by the mass retained in both deletion colors. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

private theorem weightedRows_mass_bound {M W K Y C : ℕ}
    (positive : 0 < M) (wLow : 28*M ≤ 25*W) (wHigh : W ≤ 2*M)
    (rowCapacity : 31*M ≤ 8*C) (rowLoss : 4*C*Y ≤ W^2)
    (retained : W ≤ 2*K+Y) : 83*M ≤ 160*K := by
  have omitted : 31*M*Y ≤ 2*W^2 := calc
    _ ≤ (8*C)*Y := Nat.mul_le_mul_right _ rowCapacity
    _ = 2*(4*C*Y) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ rowLoss
  have paid : 31*M*W ≤ 62*M*K+2*W^2 := calc
    _ ≤ (31*M)*(2*K+Y) := Nat.mul_le_mul_left _ retained
    _ = 62*M*K+31*M*Y := by ring
    _ ≤ _ := Nat.add_le_add_left omitted _
  have paidReal : 31*(M:ℝ)*W ≤ 62*(M:ℝ)*K+2*(W:ℝ)^2 := by exact_mod_cast paid
  have low : (28/25)*(M:ℝ) ≤ W := by
    have h : 28*(M:ℝ) ≤ 25*(W:ℝ) := by exact_mod_cast wLow
    linarith
  have high : (W:ℝ) ≤ 2*(M:ℝ) := by exact_mod_cast wHigh
  have middle := mul_nonneg (sub_nonneg.mpr low)
    (show 0 ≤ 31*(M:ℝ)-2*((W:ℝ)+(28/25)*(M:ℝ)) by linarith)
  have enough : (83*(M:ℝ))*M ≤ (160*(K:ℝ))*M := by
    nlinarith only [paidReal,middle,sq_nonneg (M:ℝ)]
  apply (Nat.mul_le_mul_right_iff positive).mp
  exact_mod_cast enough

private theorem weightedRows_final_mass {M K C : ℕ} {p q : ℕ}
    (positive : 0 < M) (pathPos : 0 < p) (pathBudget : q ≤ p)
    (large : 83*M ≤ 160*K) (upper : K ≤ M) (capacity : 31*M ≤ 8*C) :
    (M:ℝ)/5000 ≤ (K:ℝ)-(K:ℝ)^2/(4*(C:ℝ))-(M:ℝ)/4-(M:ℝ)/(4*(p:ℝ))*(q:ℝ) := by
  have cap : 31*(M:ℝ) ≤ 8*(C:ℝ) := by exact_mod_cast capacity
  have mp : 0 < (M:ℝ) := by exact_mod_cast positive
  have cp : 0 < (C:ℝ) := by linarith
  have pathFee : (M:ℝ)/(4*(p:ℝ))*(q:ℝ) ≤ (M:ℝ)/4 := calc
    _ ≤ (M:ℝ)/(4*(p:ℝ))*(p:ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr pathBudget) (by positivity)
    _ = _ := by field_simp [show (p:ℝ) ≠ 0 by exact_mod_cast pathPos.ne']
  have vertexFee : (K:ℝ)^2/(4*(C:ℝ)) ≤ 2*(K:ℝ)^2/(31*(M:ℝ)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*(C:ℝ)) (by positivity : 0 < 31*(M:ℝ))).mpr
    nlinarith only [mul_le_mul_of_nonneg_right cap (sq_nonneg (K:ℝ))]
  have low : (83/160)*(M:ℝ) ≤ K := by
    have h : 83*(M:ℝ) ≤ 160*(K:ℝ) := by exact_mod_cast large
    linarith
  have high : (K:ℝ) ≤ M := by exact_mod_cast upper
  have difference := mul_nonneg (sub_nonneg.mpr low)
    (show 0 ≤ 31*(M:ℝ)-2*((K:ℝ)+(83/160)*(M:ℝ)) by linarith)
  have enough : (M:ℝ)/5000+(M:ℝ)/2+2*(K:ℝ)^2/(31*(M:ℝ)) ≤ K := by
    rw [← sub_nonneg]
    have strong : 2*(K:ℝ)^2/(31*(M:ℝ)) ≤ (K:ℝ)-(M:ℝ)/2-(M:ℝ)/5000 := by
      apply (div_le_iff₀ (show 0 < 31*(M:ℝ) by positivity)).mpr
      nlinarith only [difference,sq_nonneg (M:ℝ)]
    linarith only [strong]
  linarith only [pathFee,vertexFee,enough]

private theorem sharedWidthAffected_subset {n p : ℕ} (paths : Fin p → List (Fin n)) (D L : ℕ) :
    sharedWidthAffected paths D L ⊆ pieceIncidences (splitListPaths paths L) univ := by
  classical
  intro a involved
  rcases mem_union.mp involved with cut | overfull
  · rcases (mem_filter.mp cut).2 with ⟨b,edge⟩ | ⟨b,edge⟩
    · exact mem_pieceIncidences.mpr ⟨mem_univ _,edge.left_mem⟩
    · exact mem_pieceIncidences.mpr ⟨mem_univ _,edge.right_mem⟩
  · exact (mem_filter.mp overfull).1

private theorem sharedWidth_two_colors_mass {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (D L : ℕ) (B : Finset (ListBlockIndex paths L)) :
    let raw := splitListPaths paths L
    let deleted := sharedWidthDeletion paths D L
    let weight (i : ListBlockIndex paths L) :=
      (erasePieceIncidences raw (deleted false) i).length+(erasePieceIncidences raw (deleted true) i).length
    (∑ i ∈ B, weight i)+(pieceIncidences raw B ∩ sharedWidthAffected paths D L).card =
      2*(∑ i ∈ B, (raw i).length) := by
  classical
  let raw := splitListPaths paths L
  let deleted := sharedWidthDeletion paths D L
  let affected := sharedWidthAffected paths D L
  have colors : deleted false ∪ deleted true = affected := by
    ext a
    cases eq : reversePartnerColor paths a.2 a.1.fst <;> simp [deleted,affected,sharedWidthDeletion,eq]
  have distinct : Disjoint (deleted false) (deleted true) := by
    apply disjoint_left.mpr
    intro a left right
    have l := (mem_filter.mp left).2
    have r := (mem_filter.mp right).2
    exact Bool.false_ne_true (l.symm.trans r)
  have rawSimple (i : ListBlockIndex paths L) : (raw i).Nodup :=
    List.filter_sublist.nodup (simple i.fst)
  have left := erasePieceIncidences_mass_add_loss rawSimple B (deleted false)
  have right := erasePieceIncidences_mass_add_loss rawSimple B (deleted true)
  change (∑ i ∈ B, (erasePieceIncidences raw (deleted false) i).length)+
    (pieceIncidences raw B ∩ deleted false).card = ∑ i ∈ B, (raw i).length at left
  change (∑ i ∈ B, (erasePieceIncidences raw (deleted true) i).length)+
    (pieceIncidences raw B ∩ deleted true).card = ∑ i ∈ B, (raw i).length at right
  change (∑ i ∈ B, ((erasePieceIncidences raw (deleted false) i).length+
    (erasePieceIncidences raw (deleted true) i).length)) + (pieceIncidences raw B ∩ affected).card = _
  rw [← colors,inter_union_distrib_left,card_union_of_disjoint (distinct.mono inter_subset_right inter_subset_right),
    sum_add_distrib]
  calc
    _ = ((∑ i ∈ B, (erasePieceIncidences raw (deleted false) i).length)+
          (pieceIncidences raw B ∩ deleted false).card)+
        ((∑ i ∈ B, (erasePieceIncidences raw (deleted true) i).length)+
          (pieceIncidences raw B ∩ deleted true).card) := add_add_add_comm _ _ _ _
    _ = _ := by rw [left,right,Nat.two_mul]

/-- Weight each path piece by the total that survives the two shared
deletion colors. Choosing the row support before choosing its color gives a
half-five witness when the affected union uses at most 22/25 of the mass. -/
theorem regularization_list_frozen_half_five_of_weighted_width_budget {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (bound : let M := ∑ i, (paths i).length; 25*(sharedWidthAffected paths (4*M/n) (4*M/p)).card ≤ 22*M) :
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
  let affected := sharedWidthAffected paths D L
  let deleted := sharedWidthDeletion paths D L
  let repaired (c : Bool) := erasePieceIncidences raw (deleted c)
  let weight (i : J) := (repaired false i).length+(repaired true i).length
  let W := ∑ i : J, weight i
  have nDense : 8*n ≤ M := by have h := le_max_left n p; omega
  have pDense : 8*p ≤ M := by have h := le_max_right n p; omega
  have mPos := hn.trans_le dense
  have dPos : 0 < D := (four_average_width hn dense).1
  have lPos : 0 < L := (four_average_width hp long).1
  have vertexCapacity : 31*M ≤ 8*(D*n) := by
    have floor := four_average_width_product hn (M := M)
    change 4*M < D*n+n at floor
    omega
  have pathCapacity : 31*M ≤ 8*(L*p) := by
    have floor := four_average_width_product hp (M := M)
    change 4*M < L*p+p at floor
    omega
  have rawMass : (∑ i : J, (raw i).length) = M := splitListPaths_size paths simple L
  have weightExact : W+affected.card = 2*M := by
    have count := sharedWidth_two_colors_mass paths simple D L (univ : Finset J)
    change W+(pieceIncidences raw univ ∩ affected).card = 2*(∑ i : J, (raw i).length) at count
    rw [inter_eq_right.mpr (sharedWidthAffected_subset paths D L),rawMass] at count
    exact count
  change 25*affected.card ≤ 22*M at bound
  have lowerW : 28*M ≤ 25*W := by omega
  have upperW : W ≤ 2*M := by omega
  have weightLower (i : J) : (raw i).length ≤ weight i := by
    have count := sharedWidth_two_colors_mass paths simple D L {i}
    change (∑ j ∈ {i}, weight j)+(pieceIncidences raw {i} ∩ affected).card =
      2*(∑ j ∈ {i}, (raw j).length) at count
    rw [sum_singleton,sum_singleton] at count
    have rawSimple (j : J) : (raw j).Nodup := List.filter_sublist.nodup (simple j.fst)
    have le : (pieceIncidences raw {i} ∩ affected).card ≤ (raw i).length := by
      refine (card_le_card inter_subset_left).trans_eq ?_
      rw [pieceIncidences_card rawSimple,sum_singleton]
    omega
  obtain ⟨filled,full,remainder⟩ := splitListPaths_full_block_profile paths simple lPos
  have rem : (univ \ filled).card ≤ p := by simpa only [Fintype.card_fin] using remainder.le
  have capacityW : W ≤ L*p := by omega
  obtain ⟨B,budget,loss⟩ := trim_full_weight_blocks_quadratic_of_lower_bound weight filled lPos
    (fun j h => (full j h).ge.trans (weightLower j)) rem capacityW
  let Y := ∑ j ∈ univ \ B, weight j
  have lost : 4*(L*p)*Y ≤ W^2 := loss
  have keptWeight : W = (∑ j ∈ B, (repaired false j).length)+(∑ j ∈ B, (repaired true j).length)+Y := by
    have eq : Y+(∑ j ∈ B, weight j) = W := sum_sdiff (subset_univ B)
    rw [show (∑ j ∈ B, weight j) =
      (∑ j ∈ B, (repaired false j).length)+(∑ j ∈ B, (repaired true j).length) from sum_add_distrib] at eq
    omega
  obtain ⟨c,kept⟩ : ∃ c : Bool, W ≤ 2*(∑ j ∈ B, (repaired c j).length)+Y := by
    rcases le_total (∑ j ∈ B, (repaired false j).length) (∑ j ∈ B, (repaired true j).length) with h | h
    · exact ⟨true,by omega⟩
    · exact ⟨false,by omega⟩
  let rows (j : B) := repaired c j.val
  let pieces := splitListVertices rows D
  let K := ∑ j : B, (pieces j).length
  have lengthSum : K = ∑ j ∈ B, (repaired c j).length := by
    calc
      _ = ∑ j : B, (rows j).length := sum_congr rfl (fun j _ => splitListVertices_length rows D j)
      _ = _ := sum_attach B (fun j => (repaired c j).length)
  have enoughK : 83*M ≤ 160*K :=
    weightedRows_mass_bound mPos lowerW upperW pathCapacity lost (lengthSum.symm ▸ kept)
  have upperK : K ≤ M := by
    rw [lengthSum,← rawMass]
    refine (sum_le_sum fun j _ => ?_).trans (sum_le_sum_of_subset (subset_univ B))
    exact (erasePieceIncidences_sublist raw (deleted c) j).length_le
  have rowsSimple (j : B) : (rows j).Nodup :=
    (erasePieceIncidences_sublist raw (deleted c) j.val).nodup (List.filter_sublist.nodup (simple j.val.fst))
  have simplePieces (j : B) : (pieces j).Nodup := splitListVertices_simple rows D j (rowsSimple j)
  have legal : HalfBridgeFree (Before pieces) 5 :=
    sharedWidthRepair_onRows_halfFree paths simple free D L c Subtype.val (fun _ _ h => h)
  have lengthCap (j : B) : (pieces j).length ≤ L :=
    (splitListVertices_length rows D j).trans_le ((erasePieceIncidences_sublist raw (deleted c) j.val).length_le.trans
      (localPathBlock_length _ (simple j.val.fst) lPos _))
  have degreeCap (v : ListVertexBlockIndex rows D) :
      (occurrences (fun j => (pieces j).toFinset) v).card ≤ D := by
    rw [show (fun j => (pieces j).toFinset) = splitVertices (fun j => (rows j).toFinset) D from
      funext (splitListVertices_toFinset rows D)]
    exact splitVertices_degree _ dPos v
  obtain ⟨fullV,filledV,remV⟩ := splitListVertices_full_block_profile rows dPos
  have remV' : (univ \ fullV).card ≤ n := by simpa only [Fintype.card_fin] using remV.le
  have budgetB : Fintype.card B ≤ p := by simpa only [Fintype.card_coe] using budget
  exact regularization_list_frozen_trim_vertices_quadratic_of_width (half := true) (k := 5)
    (retention := 5000) pieces simplePieces legal hn hp dense long (by decide)
    fullV filledV remV' budgetB lengthCap degreeCap upperK
    (weightedRows_final_mass mPos hp budgetB enoughK upperK vertexCapacity)

end OnlineReachabilityPreservers
