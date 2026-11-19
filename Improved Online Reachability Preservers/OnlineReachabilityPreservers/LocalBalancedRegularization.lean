import OnlineReachabilityPreservers.LocalInducedPaths

/-! Both cleaning budgets for locally ordered paths. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]

local notation "ListBefore" => SourceAudit.BeforeIn

/-- The two split counts, before deleting any unused copies. -/
theorem regularization_list_counts (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    {D L : ℕ} (hD : 0 < D) (hL : 0 < L) :
    let M := ∑ i, (paths i).length
    Fintype.card (ListVertexBlockIndex paths D) ≤ Fintype.card V + M/D ∧
      Fintype.card (ListBlockIndex (splitListVertices paths D) L) ≤ Fintype.card I + M/L := by
  have sourceLength (i : I) : (paths i).toFinset.card = (paths i).length := List.toFinset_card_of_nodup (simple i)
  have copiedLength (i : I) : (splitListVertices paths D i).toFinset.card = (paths i).length := by
    rw [splitListVertices_toFinset, splitVertices_length, sourceLength]
  have vertices := blockIndex_card_precise (occurrences (fun i => (paths i).toFinset)) hD
  rw [sum_occurrences] at vertices
  have pathCount := blockIndex_card_precise (fun i => (splitListVertices paths D i).toFinset) hL
  have copyMass : (∑ i, (splitListVertices paths D i).toFinset.card) = ∑ i, (paths i).length :=
    sum_congr rfl (fun i _ => copiedLength i)
  rw [copyMass] at pathCount
  exact ⟨by simpa only [sourceLength] using vertices, pathCount⟩

private theorem mass_le_average_width {M q : ℕ} (positive : 0 < q) (enough : q ≤ M) :
    M ≤ q * ((4 * M) / q) := by
  have lower := Nat.lt_mul_div_succ (4 * M) positive
  rw [Nat.mul_succ] at lower
  omega

private theorem regularization_list_balanced_caps_of_splits (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup) (size : ℕ)
    (half : ∀ D L, HalfBridgeFree (ListBefore paths) size →
      HalfBridgeFree (ListBefore (listRegularizedPaths paths D L)) size)
    (full : ∀ D L, BridgeFree (ListBefore paths) size →
      BridgeFree (ListBefore (listRegularizedPaths paths D L)) size)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (dense : Fintype.card V ≤ ∑ i, (paths i).length) (long : Fintype.card I ≤ ∑ i, (paths i).length) :
    let n := Fintype.card V
    let p := Fintype.card I
    let M := ∑ i, (paths i).length
    let D := (4 * M) / n
    let L := (4 * M) / p
    let after := listRegularizedPaths paths D L
    ∃ A : Finset (ListVertexBlockIndex paths D),
      ∃ B : Finset (ListBlockIndex (splitListVertices paths D) L),
        let clean := restrictListPaths after A B
        A.card ≤ n ∧ B.card ≤ p ∧ M ≤ 16 * (∑ i, (clean i).length) ∧
          (∑ i, (clean i).length) ≤ M ∧
          (∀ v : A, (M : ℝ) / (4 * (n : ℝ)) ≤ (occurrences (fun i => (clean i).toFinset) v).card ∧
            ((occurrences (fun i => (clean i).toFinset) v).card : ℝ) ≤ 4 * (M : ℝ) / (n : ℝ)) ∧
          (∀ i : B, (M : ℝ) / (4 * (p : ℝ)) ≤ (clean i).length ∧
            ((clean i).length : ℝ) ≤ 4 * (M : ℝ) / (p : ℝ)) ∧
          (HalfBridgeFree (ListBefore paths) size → HalfBridgeFree (ListBefore clean) size) ∧
          (BridgeFree (ListBefore paths) size → BridgeFree (ListBefore clean) size) := by
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).length
  let D := (4 * M) / n
  let L := (4 * M) / p
  let copies := splitListVertices paths D
  let after := listRegularizedPaths paths D L
  let Z (i : ListBlockIndex copies L) := (after i).toFinset
  obtain ⟨hD, trimD, capD⟩ := four_average_width hn dense
  obtain ⟨hL, trimL, capL⟩ := four_average_width hp long
  obtain ⟨_, _, afterMass, length, degree⟩ := regularization_list_size paths simple D L hD hL
    (mass_le_average_width hn dense) (mass_le_average_width hp long)
  have afterSimple (i : ListBlockIndex copies L) : (after i).Nodup := listRegularizedPaths_simple paths simple D L i
  have total : (∑ i, (Z i).card) = M :=
    (sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (afterSimple i))).trans afterMass
  obtain ⟨countV,countI⟩ := regularization_list_counts paths simple hD hL
  have vertices : 3 * Fintype.card (ListVertexBlockIndex paths D) ≤ 4 * n := by
    change Fintype.card (ListVertexBlockIndex paths D) ≤ n + M/D at countV
    change 3*(M/D) ≤ n at trimD
    omega
  have pathsCap : 3 * Fintype.card (ListBlockIndex copies L) ≤ 4 * p := by
    change Fintype.card (ListBlockIndex copies L) ≤ p+M/L at countI
    change 3*(M/L) ≤ p at trimL
    omega
  obtain ⟨A,B,aCap,bCap,retained,minDegree,minLength⟩ := balancedRectangle_subsystem Z hn hp vertices pathsCap
  rw [total] at retained minDegree minLength
  let clean := restrictListPaths after A B
  let rectangle := rectanglePaths Z A B
  have same (i : B) : (clean i).toFinset = rectangle i := restrictListPaths_toFinset after A B i
  have cleanLength (i : B) : (clean i).length = (rectangle i).card := by
    have nodup := restrictListPath_nodup (afterSimple i.val) A
    change (restrictListPath (after i.val) A).length = _
    rw [← List.toFinset_card_of_nodup nodup]
    exact congrArg Finset.card (same i)
  have equals : (fun i => (clean i).toFinset) = rectangle := funext same
  have mass : (∑ i : B, (clean i).length) = ∑ i : B, (rectangle i).card :=
    sum_congr rfl (fun i _ => cleanLength i)
  refine ⟨A,B,aCap,bCap,?_,?_,?_,?_,?_,?_⟩
  · change M ≤ 16 * ∑ i : B, (clean i).length
    rw [mass]
    exact retained
  · change (∑ i : B, (clean i).length) ≤ M
    rw [mass]
    exact (rectanglePaths_mass_le Z A B).trans_eq total
  · intro v
    change (M : ℝ)/(4*(n:ℝ)) ≤ _ ∧ _
    rw [equals]
    exact ⟨minDegree v, (Nat.cast_le.mpr ((rectanglePaths_degree_le Z A B v).trans (degree v.val))).trans capD⟩
  · intro i
    change (M : ℝ)/(4*(p:ℝ)) ≤ ((clean i).length : ℝ) ∧ _
    refine ⟨by rw [cleanLength]; exact minLength i, ?_⟩
    have bound : (clean i).length ≤ (after i.val).length := by
      rw [show (clean i).length = ((after i.val).toFinset ∩ A).card from restrictListPath_length (afterSimple i.val) A]
      exact (card_le_card inter_subset_left).trans (List.toFinset_card_le _)
    exact (Nat.cast_le.mpr (bound.trans (length i.val))).trans capL
  · intro free
    exact restrictListPaths_halfFree afterSimple (half D L free) A B
  · intro free
    exact restrictListPaths_fullFree afterSimple (full D L free) A B

/-- For a family with unique intersections, restrict the two splits back to
both original budgets. Keep one sixteenth of the mass and all four caps
relative to the input averages. The exclusions are preserved through size four. -/
theorem regularization_list_balanced_caps (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (dense : Fintype.card V ≤ ∑ i, (paths i).length) (long : Fintype.card I ≤ ∑ i, (paths i).length) :
    let n := Fintype.card V
    let p := Fintype.card I
    let M := ∑ i, (paths i).length
    let D := (4 * M) / n
    let L := (4 * M) / p
    let after := listRegularizedPaths paths D L
    ∃ A : Finset (ListVertexBlockIndex paths D),
      ∃ B : Finset (ListBlockIndex (splitListVertices paths D) L),
        let clean := restrictListPaths after A B
        A.card ≤ n ∧ B.card ≤ p ∧ M ≤ 16 * (∑ i, (clean i).length) ∧
          (∀ v : A, (M : ℝ) / (4 * (n : ℝ)) ≤ (occurrences (fun i => (clean i).toFinset) v).card ∧
            ((occurrences (fun i => (clean i).toFinset) v).card : ℝ) ≤ 4 * (M : ℝ) / (n : ℝ)) ∧
          (∀ i : B, (M : ℝ) / (4 * (p : ℝ)) ≤ (clean i).length ∧
            ((clean i).length : ℝ) ≤ 4 * (M : ℝ) / (p : ℝ)) ∧
          (HalfBridgeFree (ListBefore paths) 4 → HalfBridgeFree (ListBefore clean) 4) ∧
          (BridgeFree (ListBefore paths) 4 → BridgeFree (ListBefore clean) 4) := by
  obtain ⟨A,B,aCap,bCap,mass,_,degree,length,half,full⟩ :=
    regularization_list_balanced_caps_of_splits paths simple 4
      (fun D L free => listRegularizedPaths_halfFree simple unique free D L)
      (fun D L free => listRegularizedPaths_fullFree simple unique free D L) hn hp dense long
  exact ⟨A,B,aCap,bCap,mass,degree,length,half,full⟩

/-- Both original budgets and all four caps hold for arbitrary simple paths
when preserving bridge exclusion through size three. -/
theorem regularization_list_balanced_caps_short (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    {size : ℕ} (short : size ≤ 3)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (dense : Fintype.card V ≤ ∑ i, (paths i).length) (long : Fintype.card I ≤ ∑ i, (paths i).length) :
    let n := Fintype.card V
    let p := Fintype.card I
    let M := ∑ i, (paths i).length
    let D := (4 * M) / n
    let L := (4 * M) / p
    let after := listRegularizedPaths paths D L
    ∃ A : Finset (ListVertexBlockIndex paths D),
      ∃ B : Finset (ListBlockIndex (splitListVertices paths D) L),
        let clean := restrictListPaths after A B
        A.card ≤ n ∧ B.card ≤ p ∧ M ≤ 16 * (∑ i, (clean i).length) ∧
          (∑ i, (clean i).length) ≤ M ∧
          (∀ v : A, (M : ℝ) / (4 * (n : ℝ)) ≤ (occurrences (fun i => (clean i).toFinset) v).card ∧
            ((occurrences (fun i => (clean i).toFinset) v).card : ℝ) ≤ 4 * (M : ℝ) / (n : ℝ)) ∧
          (∀ i : B, (M : ℝ) / (4 * (p : ℝ)) ≤ (clean i).length ∧
            ((clean i).length : ℝ) ≤ 4 * (M : ℝ) / (p : ℝ)) ∧
          (HalfBridgeFree (ListBefore paths) size → HalfBridgeFree (ListBefore clean) size) ∧
          (BridgeFree (ListBefore paths) size → BridgeFree (ListBefore clean) size) :=
  regularization_list_balanced_caps_of_splits paths simple size
    (fun D L free => listRegularizedPaths_halfFree_short simple free short D L)
    (fun D L free => listRegularizedPaths_fullFree_short simple free short D L) hn hp dense long

theorem regularization_list_balanced_caps_three (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (dense : Fintype.card V ≤ ∑ i, (paths i).length) (long : Fintype.card I ≤ ∑ i, (paths i).length) :
    let n := Fintype.card V
    let p := Fintype.card I
    let M := ∑ i, (paths i).length
    let D := (4 * M) / n
    let L := (4 * M) / p
    let after := listRegularizedPaths paths D L
    ∃ A : Finset (ListVertexBlockIndex paths D),
      ∃ B : Finset (ListBlockIndex (splitListVertices paths D) L),
        let clean := restrictListPaths after A B
        A.card ≤ n ∧ B.card ≤ p ∧ M ≤ 16 * (∑ i, (clean i).length) ∧
          (∑ i, (clean i).length) ≤ M ∧
          (∀ v : A, (M : ℝ) / (4 * (n : ℝ)) ≤ (occurrences (fun i => (clean i).toFinset) v).card ∧
            ((occurrences (fun i => (clean i).toFinset) v).card : ℝ) ≤ 4 * (M : ℝ) / (n : ℝ)) ∧
          (∀ i : B, (M : ℝ) / (4 * (p : ℝ)) ≤ (clean i).length ∧
            ((clean i).length : ℝ) ≤ 4 * (M : ℝ) / (p : ℝ)) ∧
          (HalfBridgeFree (ListBefore paths) 3 → HalfBridgeFree (ListBefore clean) 3) ∧
          (BridgeFree (ListBefore paths) 3 → BridgeFree (ListBefore clean) 3) :=
  regularization_list_balanced_caps_short paths simple le_rfl hn hp dense long

/-- Prune a general system before performing the two splits. The lower
caps lose at most a factor of two, and both original budgets are met. -/
theorem regularization_list_after_pruning {p : ℕ} (paths : Fin p → List V) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) 4) (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card (Fin p))
    (dense : 2 * Fintype.card V ≤ ∑ i, (paths i).length)
    (long : 2 * Fintype.card (Fin p) ≤ ∑ i, (paths i).length) :
    let n := Fintype.card V
    let P := Fintype.card (Fin p)
    let M := ∑ i, (paths i).length
    let kept := removeOppositeIntersections paths
    let m := ∑ i, (kept i).length
    let D := (4 * m) / n
    let L := (4 * m) / P
    let after := listRegularizedPaths kept D L
    ∃ A : Finset (ListVertexBlockIndex kept D),
      ∃ B : Finset (ListBlockIndex (splitListVertices kept D) L),
        let clean := restrictListPaths after A B
        A.card ≤ n ∧ B.card ≤ P ∧ M ≤ 32 * (∑ i, (clean i).length) ∧
          (∀ v : A, (M : ℝ) / (8 * (n : ℝ)) ≤ (occurrences (fun i => (clean i).toFinset) v).card ∧
            ((occurrences (fun i => (clean i).toFinset) v).card : ℝ) ≤ 4 * (M : ℝ) / (n : ℝ)) ∧
          (∀ i : B, (M : ℝ) / (8 * (P : ℝ)) ≤ (clean i).length ∧
            ((clean i).length : ℝ) ≤ 4 * (M : ℝ) / (P : ℝ)) ∧
          HalfBridgeFree (ListBefore clean) 4 ∧
          (BridgeFree (ListBefore paths) 4 → BridgeFree (ListBefore clean) 4) := by
  let kept := removeOppositeIntersections paths
  let m := ∑ i, (kept i).length
  let M := ∑ i, (paths i).length
  have half : M ≤ 2*m := removeOppositeIntersections_mass simple free (by decide)
  have below : m ≤ M := sum_le_sum fun i _ => (removeOppositeIntersections_sublist paths i).length_le
  have halfReal : (M : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast half
  have belowReal : (m : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr below
  have keptSimple (i : Fin p) : (kept i).Nodup :=
    (removeOppositeIntersections_sublist paths i).nodup (simple i)
  obtain ⟨A, B, aCap, bCap, mass, degrees, lengths, halfFree, fullFree⟩ :=
    regularization_list_balanced_caps kept keptSimple
      (fun different a b c d => removeOppositeIntersections_unique simple free (by decide) different a b c d)
      hn hp (by change Fintype.card V ≤ m; omega) (by change Fintype.card (Fin p) ≤ m; omega)
  refine ⟨A, B, aCap, bCap, ?_, ?_, ?_, halfFree (removeOppositeIntersections_halfFree simple free),
    fun original => fullFree (removeOppositeIntersections_fullFree simple original)⟩
  · simpa only [← Nat.mul_assoc] using half.trans (Nat.mul_le_mul_left 2 mass)
  · intro v
    refine ⟨?_, ?_⟩
    · apply le_trans _ (degrees v).1
      have eq : (m : ℝ) / (4 * (Fintype.card V : ℝ)) = 2 * (m : ℝ) / (8 * (Fintype.card V : ℝ)) := by ring
      rw [eq]
      exact div_le_div_of_nonneg_right halfReal (by positivity)
    · exact (degrees v).2.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left belowReal (by norm_num)) (by positivity))
  · intro i
    refine ⟨?_, ?_⟩
    · apply le_trans _ (lengths i).1
      have eq : (m : ℝ) / (4 * (Fintype.card (Fin p) : ℝ)) =
          2 * (m : ℝ) / (8 * (Fintype.card (Fin p) : ℝ)) := by ring
      rw [eq]
      exact div_le_div_of_nonneg_right halfReal (by positivity)
    · exact (lengths i).2.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left belowReal (by norm_num)) (by positivity))

end OnlineReachabilityPreservers
