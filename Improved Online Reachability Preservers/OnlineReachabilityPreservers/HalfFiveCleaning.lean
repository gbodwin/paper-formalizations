import OnlineReachabilityPreservers.FrozenDegreeClipping
import OnlineReachabilityPreservers.FrozenOverlongPaths
import OnlineReachabilityPreservers.HalfFiveDegreeRepair

/-! Frozen-average half-five cleaning after a bounded amount of length clipping. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

variable {n p : ℕ}

private abbrev listDegree (paths : Fin p → List (Fin n)) (v : Fin n) : ℕ :=
  (occurrences (fun i => (paths i).toFinset) v).card

private def overfullVertices (paths : Fin p → List (Fin n)) (D : ℕ) : Finset (Fin n) :=
  univ.filter fun v => D < listDegree paths v

private def overfullCopies (paths : Fin p → List (Fin n)) (D : ℕ) : Finset (ListVertexBlockIndex paths D) :=
  univ.filter fun v => D < listDegree paths v.fst

private def lightCopies (paths : Fin p → List (Fin n)) (D : ℕ) : Finset (ListVertexBlockIndex paths D) :=
  univ.filter fun v => listDegree paths v.fst ≤ D ∧ v.snd.val = 0

private abbrev copyDegree (paths : Fin p → List (Fin n)) (D : ℕ) (v : ListVertexBlockIndex paths D) : ℕ :=
  (occurrences (fun i => (splitListVertices paths D i).toFinset) v).card

private noncomputable abbrev repairedDegree (paths : Fin p → List (Fin n)) (D : ℕ) (c : Bool)
    (v : ListVertexBlockIndex paths D) : ℕ :=
  (occurrences (fun i => (halfFiveDegreeRepair paths D c i).toFinset) v).card

private theorem listDegreeExcess_above_width (paths : Fin p → List (Fin n)) (D : ℕ) :
    listDegreeExcess paths D+(overfullVertices paths D).card*D =
      ∑ v ∈ overfullVertices paths D, listDegree paths v := by
  let H := overfullVertices paths D
  have excess : listDegreeExcess paths D = ∑ v ∈ H, (listDegree paths v-D) := by
    unfold listDegreeExcess H overfullVertices
    rw [sum_filter]
    apply sum_congr rfl
    intro v _
    by_cases h : D < listDegree paths v
    · simp [h]
    · simp [h,Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)]
  have widths : (∑ _ ∈ H, D) = H.card*D := by simp
  rw [excess,← widths,← sum_add_distrib]
  exact sum_congr rfl fun v member => Nat.sub_add_cancel (mem_filter.mp member).2.le

private theorem sum_overfullCopies (paths : Fin p → List (Fin n)) (D : ℕ)
    (f : ListVertexBlockIndex paths D → ℕ) :
    (∑ v ∈ overfullCopies paths D, f v) =
      ∑ x ∈ overfullVertices paths D,
        ∑ j : Fin (blockCount (occurrences (fun i => (paths i).toFinset) x) D), f ⟨x,j⟩ := by
  unfold overfullCopies overfullVertices
  rw [sum_filter,sum_filter]
  change (∑ v : (Σ x : Fin n, Fin (blockCount (occurrences (fun i => (paths i).toFinset) x) D)),
    if D < listDegree paths v.fst then f v else 0) = _
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro v _
  by_cases h : D < listDegree paths v <;> simp [h]

private theorem overfullCopies_width (paths : Fin p → List (Fin n)) (D : ℕ) :
    D*(overfullCopies paths D).card ≤ (overfullVertices paths D).card*D +
      ∑ v ∈ overfullVertices paths D, listDegree paths v := by
  let H := overfullVertices paths D
  have count : (overfullCopies paths D).card = ∑ v ∈ H, (listDegree paths v/D+1) := by
    rw [show (overfullCopies paths D).card = ∑ _ ∈ overfullCopies paths D, (1:ℕ) by simp,
      sum_overfullCopies]
    refine sum_congr rfl fun v _ => ?_
    rw [← Fintype.card_eq_sum_ones, Fintype.card_fin,blockCount]
  calc
    _ = ∑ v ∈ H, D*(listDegree paths v/D+1) := by rw [count,mul_sum]
    _ ≤ ∑ v ∈ H, (D+listDegree paths v) := by
      apply sum_le_sum
      intro v _
      have floor := Nat.div_mul_le_self (listDegree paths v) D
      rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm D]
      omega
    _ = _ := by rw [sum_add_distrib]; simp [H]

private theorem overfullCopies_mass (paths : Fin p → List (Fin n)) (D : ℕ) :
    (∑ v ∈ overfullCopies paths D, copyDegree paths D v) =
      ∑ v ∈ overfullVertices paths D, listDegree paths v := by
  rw [sum_overfullCopies]
  apply sum_congr rfl
  intro v _
  let marks (i : Fin p) := (paths i).toFinset
  have copies : (fun i => (splitListVertices paths D i).toFinset) = splitVertices marks D :=
    funext (splitListVertices_toFinset paths D)
  calc
    _ = ∑ j : Fin (blockCount (occurrences marks v) D),
        (orderBlock (occurrences marks v) D j.val).card := by
      apply sum_congr rfl
      intro j _
      change (occurrences (fun i => (splitListVertices paths D i).toFinset)
        (⟨v,j⟩ : ListVertexBlockIndex paths D)).card = _
      rw [copies]
      exact congrArg Finset.card (splitVertices_occurrences marks D
        (⟨v,j⟩ : ListVertexBlockIndex paths D))
    _ = _ := orderBlock_sum _ _

private theorem lightCopies_count (paths : Fin p → List (Fin n)) (D : ℕ) :
    (lightCopies paths D).card ≤ n-(overfullVertices paths D).card := by
  have count : (lightCopies paths D).card ≤ (univ \ overfullVertices paths D).card := by
    apply card_le_card_of_injOn (fun v : ListVertexBlockIndex paths D => v.fst)
    · intro v member
      have le := (mem_filter.mp member).2.1
      exact mem_sdiff.mpr ⟨mem_univ _,fun high => (not_lt_of_ge le) (mem_filter.mp high).2⟩
    · intro a ha b hb same
      exact vertexBlock_eq_of_same_label same ((mem_filter.mp ha).2.2.trans (mem_filter.mp hb).2.2.symm)
  have parts := card_sdiff_add_card_eq_card (subset_univ (overfullVertices paths D))
  rw [card_univ,Fintype.card_fin] at parts
  omega

private theorem heavy_light_disjoint (paths : Fin p → List (Fin n)) (D : ℕ) :
    Disjoint (overfullCopies paths D) (lightCopies paths D) :=
  disjoint_left.mpr fun _ heavy light => (not_lt_of_ge (mem_filter.mp light).2.1) (mem_filter.mp heavy).2

private theorem lightCopies_mass (paths : Fin p → List (Fin n)) (D : ℕ) (simple : ∀ i, (paths i).Nodup) :
    (∑ v ∈ lightCopies paths D, copyDegree paths D v) +
      (∑ v ∈ overfullVertices paths D, listDegree paths v) = ∑ i, (paths i).length := by
  rw [← overfullCopies_mass paths D, ← sum_union (heavy_light_disjoint paths D).symm]
  calc
    _ = ∑ v, copyDegree paths D v := by
      apply sum_subset (subset_univ _)
      intro v _ notKept
      change (occurrences (fun i => (splitListVertices paths D i).toFinset) v).card = 0
      rw [card_eq_zero]
      apply eq_empty_iff_forall_notMem.mpr
      intro i occurs
      have present : v ∈ splitListVertices paths D i := List.mem_toFinset.mp
        ((mem_occurrences (marks := fun j => (splitListVertices paths D j).toFinset)).mp occurs)
      by_cases heavy : D < listDegree paths v.fst
      · exact notKept (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,heavy⟩))
      · have block : v.snd.val = 0 := by
          by_contra h
          exact heavy (degree_width_lt_of_positive_block present (Nat.pos_of_ne_zero h))
        exact notKept (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, Nat.le_of_not_gt heavy,block⟩))
    _ = _ := by
      rw [show (∑ v, copyDegree paths D v) = ∑ i, (splitListVertices paths D i).toFinset.card
        from sum_occurrences _]
      exact sum_congr rfl fun i _ => by
        rw [splitListVertices_toFinset,splitVertices_length,List.toFinset_card_of_nodup (simple i)]

private theorem repairedDegree_at_heavy {paths : Fin p → List (Fin n)} {D : ℕ} {v : ListVertexBlockIndex paths D}
    (heavy : D < listDegree paths v.fst) (c : Bool) :
    occurrences (fun i => (halfFiveDegreeRepair paths D c i).toFinset) v =
      (occurrences (fun i => (splitListVertices paths D i).toFinset) v).filter
        (fun i => reversePartnerColor paths v.fst i ≠ c) := by
  ext i
  simp only [mem_occurrences,List.mem_toFinset,mem_filter,mem_halfFiveDegreeRepair]
  exact and_congr_right fun _ => or_iff_right (not_le_of_gt heavy)

private theorem repairedDegree_at_light {paths : Fin p → List (Fin n)} {D : ℕ} {v : ListVertexBlockIndex paths D}
    (light : listDegree paths v.fst ≤ D) (c : Bool) : repairedDegree paths D c v = copyDegree paths D v := by
  apply congrArg Finset.card
  ext i
  simp only [mem_occurrences,List.mem_toFinset,mem_halfFiveDegreeRepair,light,true_or,and_true]

private theorem halfFiveDegreeRepair_heavy_mass (paths : Fin p → List (Fin n)) (D : ℕ) :
    ∃ c : Bool, (∑ v ∈ overfullVertices paths D, listDegree paths v) ≤
      2*(∑ v ∈ overfullCopies paths D, repairedDegree paths D c v) := by
  let H := overfullCopies paths D
  let weight := repairedDegree paths D
  have eq : (∑ v ∈ H, weight false v)+(∑ v ∈ H, weight true v) =
      ∑ v ∈ overfullVertices paths D, listDegree paths v := by
    rw [← overfullCopies_mass paths D,← sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    have heavy := (mem_filter.mp hv).2
    change (occurrences (fun i => (halfFiveDegreeRepair paths D false i).toFinset) v).card +
      (occurrences (fun i => (halfFiveDegreeRepair paths D true i).toFinset) v).card = _
    rw [repairedDegree_at_heavy heavy,repairedDegree_at_heavy heavy]
    have complement (i : Fin p) : reversePartnerColor paths v.fst i ≠ true ↔ ¬(reversePartnerColor paths v.fst i ≠ false) := by
      cases reversePartnerColor paths v.fst i <;> simp
    simpa only [complement] using
      (card_filter_add_card_filter_not (s := occurrences (fun i => (splitListVertices paths D i).toFinset) v)
        (fun i => reversePartnerColor paths v.fst i ≠ false))
  by_cases better : (∑ v ∈ H, weight true v) ≤ ∑ v ∈ H, weight false v
  · refine ⟨false,?_⟩
    change _ ≤ 2*(∑ v ∈ H, weight false v)
    omega
  · refine ⟨true,?_⟩
    change _ ≤ 2*(∑ v ∈ H, weight true v)
    omega

/-- Clip degrees in a length-capped subsystem while charging the loss
against the original mass and budgets. -/
theorem regularization_list_frozen_half_five_after_degree_clipping {M P : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < P)
    (dense : n ≤ M) (long : P ≤ M) (rowCount : p ≤ P)
    (lengthCap : ∀ i, (paths i).length ≤ 4*M/P) (upper : (∑ i, (paths i).length) ≤ M)
    (enough : 5002*M+10000*listDegreeExcess paths (4*M/n) ≤ 10000*(∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ P, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n P M clean := by
  let D := 4*M/n
  let clipped := clipListDegrees paths D
  obtain ⟨counts,exactLoss⟩ := clipListDegrees_counts paths D simple
  have mass : (∑ i, (clipped i).length) + listDegreeExcess paths D = ∑ i, (paths i).length :=
    exactLoss
  have admissible : localOrderAdmissible true 5 clipped := by
    intro j small bridge earlier
    exact free small (bridge.mapPaths id Function.injective_id
      (fun i _ _ => listBefore_of_sublist (simple i) (clipListDegrees_sublist paths D i))) earlier
  refine regularization_list_frozen_after_caps_with_ratios_of_mass
    (vNum := 1) (vDen := 1) (pNum := 1) (pDen := 1)
    clipped (fun i => (clipListDegrees_sublist paths D i).nodup (simple i))
    admissible hn hp dense long (by decide) (by decide) le_rfl le_rfl
    (by simp) (by simpa only [one_mul,Fintype.card_fin] using rowCount)
    (fun i => (clipListDegrees_sublist paths D i).length_le.trans (lengthCap i))
    (fun v => (counts v).trans_le (min_le_left _ _)) (by omega) ?_
  change 5002*M ≤ 10000*(∑ i, (clipped i).length)
  change 5002*M+10000*listDegreeExcess paths D ≤ 10000*(∑ i, (paths i).length) at enough
  omega

/-- The degree repair applies with the original length cap and with at
least 43/50 of the original mass surviving. -/
theorem regularization_list_frozen_half_five_after_length_cap_with_path_budget {M P : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (hn : 0 < n) (hp : 0 < P) (dense : 8*n ≤ M) (long : P ≤ M) (rowCount : p ≤ P)
    (lengthCap : ∀ i, (paths i).length ≤ 4*M/P)
    (lower : 43*M ≤ 50*(∑ i, (paths i).length)) (upper : (∑ i, (paths i).length) ≤ M) :
    ∃ n' ≤ n, ∃ p' ≤ P, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n P M clean := by
  let D := 4*M/n
  let K := ∑ i, (paths i).length
  let T := listDegreeExcess paths D
  have vertexBudget : n ≤ M := by omega
  have positive : 0 < M := hn.trans_le vertexBudget
  have capacity : 31*M ≤ 8*(D*n) := by
    have floor := four_average_width_product hn (M := M)
    change 4*M < D*n+n at floor
    omega
  obtain ⟨width,_,_⟩ := four_average_width hn vertexBudget
  change 0 < D at width
  change 43*M ≤ 50*K at lower
  change K ≤ M at upper
  by_cases clip : 50*T ≤ 17*M
  · apply regularization_list_frozen_half_five_after_degree_clipping paths simple free hn hp vertexBudget
      long rowCount lengthCap upper
    change 5002*M+10000*T ≤ 10000*K
    omega
  let heavy := overfullCopies paths D
  let light := lightCopies paths D
  let q := (overfullVertices paths D).card
  let Q := heavy.card
  let S := ∑ v ∈ overfullVertices paths D, listDegree paths v
  have excess : T+q*D = S := listDegreeExcess_above_width paths D
  have widthCount : D*Q ≤ q*D+S := overfullCopies_width paths D
  have conserved : (∑ v ∈ light, copyDegree paths D v)+S = K := lightCopies_mass paths D simple
  have fits : Q ≤ n := by
    apply Nat.le_of_mul_le_mul_left _ width
    omega
  obtain ⟨c,heavyMass⟩ := halfFiveDegreeRepair_heavy_mass paths D
  let repaired := halfFiveDegreeRepair paths D c
  let weight := repairedDegree paths D c
  have keepHeavy : S ≤ 2*(∑ v ∈ heavy, weight v) := heavyMass
  have sub (i : Fin p) : List.Sublist (repaired i) (splitListVertices paths D i) := List.filter_sublist
  have repairSimple (i : Fin p) : (repaired i).Nodup :=
    (sub i).nodup (splitListVertices_simple paths D i (simple i))
  have allowed : localOrderAdmissible true 5 repaired := halfFiveDegreeRepair_halfFree paths simple free D c
  have lengthLe (i : Fin p) : (repaired i).length ≤ (paths i).length :=
    (sub i).length_le.trans_eq (splitListVertices_length paths D i)
  have degreeCap (v : ListVertexBlockIndex paths D) : weight v ≤ D := by
    have original : copyDegree paths D v ≤ D := by
      change (occurrences (fun i => (splitListVertices paths D i).toFinset) v).card ≤ D
      rw [show (fun i => (splitListVertices paths D i).toFinset) =
        splitVertices (fun i => (paths i).toFinset) D from funext (splitListVertices_toFinset paths D)]
      exact splitVertices_degree _ width v
    apply le_trans ?_ original
    apply card_le_card
    intro i member
    have present : v ∈ repaired i := List.mem_toFinset.mp
      ((mem_occurrences (marks := fun j => (repaired j).toFinset)).mp member)
    exact mem_occurrences.mpr (List.mem_toFinset.mpr ((sub i).subset present))
  have repairUpper : (∑ i, (repaired i).length) ≤ M :=
    (sum_le_sum (s := univ) fun i _ => lengthLe i).trans upper
  have p0 : (P:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have n0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have rowFee : (M:ℝ)/(4*(P:ℝ))*(Fintype.card (Fin p):ℝ) ≤ (M:ℝ)/4 := calc
    _ ≤ (M:ℝ)/(4*(P:ℝ))*(P:ℝ) := by
      rw [Fintype.card_fin]
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr rowCount) (by positivity)
    _ = _ := by field_simp [p0]
  have finish (A : Finset (ListVertexBlockIndex paths D)) (room : A.card ≤ n)
      (enough : (M:ℝ)/5000 ≤ ((∑ v ∈ A, weight v : ℕ):ℝ)
        -(M:ℝ)/(4*(n:ℝ))*A.card-(M:ℝ)/4) :
      ∃ n' ≤ n, ∃ p' ≤ P, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
        M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n P M clean := by
    refine regularization_list_frozen_after_kept_vertices repaired repairSimple allowed hn hp vertexBudget
      long (by decide) A room (by simpa only [Fintype.card_fin] using rowCount)
      (fun i => (lengthLe i).trans (lengthCap i)) degreeCap repairUpper ?_
    exact enough.trans (sub_le_sub_left rowFee _)
  by_cases large : 31*M ≤ 50*S
  · apply finish heavy fits
    have realWidth : (D:ℝ)*(Q:ℝ)+(T:ℝ) ≤ 2*(S:ℝ) := by
      exact_mod_cast (show D*Q+T ≤ 2*S by omega)
    have realCapacity : 31*(M:ℝ) ≤ 8*((D:ℝ)*(n:ℝ)) := by exact_mod_cast capacity
    have fee : (M:ℝ)/(4*(n:ℝ))*(Q:ℝ) ≤ (D:ℝ)*(Q:ℝ)/(31/2) := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 4*(n:ℝ))).mpr
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<31/2)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right realCapacity (show 0 ≤ (Q:ℝ) by positivity)]
    have realS : 31*(M:ℝ) ≤ 50*(S:ℝ) := by exact_mod_cast large
    have realT : 17*(M:ℝ) ≤ 50*(T:ℝ) := by exact_mod_cast (show 17*M ≤ 50*T by omega)
    have realMass : (S:ℝ) ≤ 2*((∑ v ∈ heavy, weight v : ℕ):ℝ) := by exact_mod_cast keepHeavy
    change (M:ℝ)/5000 ≤ ((∑ v ∈ heavy, weight v : ℕ):ℝ) -(M:ℝ)/(4*(n:ℝ))*(Q:ℝ)-(M:ℝ)/4
    linarith only [realWidth,fee,realS,realT,realMass,show (0:ℝ) ≤ M by positivity]
  have expanded : 5*Q ≤ n+4*q := by
    apply Nat.le_of_mul_le_mul_left _ width
    rw [show D*(5*Q) = 5*(D*Q) by ring,show D*(n+4*q) = D*n+4*(q*D) by ring]
    omega
  have lightCount : light.card ≤ n-q := lightCopies_count paths D
  have qLe : q ≤ n := by simpa [q] using card_le_univ (overfullVertices paths D)
  obtain ⟨kept,inLight,keptCount,keptWeight⟩ := trim_weights_ratio light weight
    (show 4 ≤ 5 by decide) (show 4*light.card ≤ 5*(n-Q) by omega)
  have disjoint : Disjoint heavy kept := (heavy_light_disjoint paths D).mono_right inLight
  have vertices : (heavy ∪ kept).card ≤ n := by rw [card_union_of_disjoint disjoint]; omega
  have lightMass : ∑ v ∈ light, weight v = ∑ v ∈ light, copyDegree paths D v :=
    sum_congr rfl fun v hv => repairedDegree_at_light (mem_filter.mp hv).2.1 c
  rw [lightMass] at keptWeight
  have mass : 251*M ≤ 500*(∑ v ∈ heavy ∪ kept, weight v) := by
    rw [sum_union disjoint]
    omega
  apply finish _ vertices
  have fullFee : (M:ℝ)/(4*(n:ℝ))*((heavy ∪ kept).card:ℝ) ≤ (M:ℝ)/4 := calc
    _ ≤ (M:ℝ)/(4*(n:ℝ))*(n:ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr vertices) (by positivity)
    _ = _ := by field_simp [n0]
  have realMass : 251*(M:ℝ) ≤ 500*((∑ v ∈ heavy ∪ kept, weight v : ℕ):ℝ) := by exact_mod_cast mass
  linarith only [fullFee,realMass,show (0:ℝ) ≤ M by positivity]

/-- The degree repair applies with the original length cap and with at
least 43/50 of the original mass surviving. -/
theorem regularization_list_frozen_half_five_after_length_cap {M : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (hn : 0 < n) (hp : 0 < p) (dense : 8*n ≤ M) (long : p ≤ M)
    (lengthCap : ∀ i, (paths i).length ≤ 4*M/p)
    (lower : 43*M ≤ 50*(∑ i, (paths i).length)) (upper : (∑ i, (paths i).length) ≤ M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_half_five_after_length_cap_with_path_budget
    paths simple free hn hp dense long le_rfl lengthCap lower upper

/-- Small total excess at the original length cap suffices for frozen
half-five cleaning even when two paths can meet more than once. -/
theorem regularization_list_frozen_half_five_of_small_length_excess (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) 5)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (excess : let M := ∑ i, (paths i).length; 50*listLengthExcess paths (4*M/p) ≤ 7*M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 5000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n',hn',p',hp',clean,simpleClean,legal,mass,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free (by decide) hn hp dense long low
    exact ⟨n',hn',p',hp',clean,simpleClean,fun _ small bridge _ => (legal small).false bridge,
      mass.trans (Nat.mul_le_mul_right _ (by decide)),upper,caps⟩
  let L := 4*M/p
  let clipped (i : Fin p) := (paths i).take L
  have sub (i : Fin p) : List.Sublist (clipped i) (paths i) := List.take_sublist _ _
  have allowed : HalfBridgeFree (Before clipped) 5 := by
    intro j small b earlier
    exact free small (b.mapPaths id Function.injective_id
      (fun i _ _ => listBefore_of_sublist (simple i) (sub i))) earlier
  have count : (∑ i, (clipped i).length)+listLengthExcess paths L = M := by
    unfold listLengthExcess M
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [show (clipped i).length = min L (paths i).length from List.length_take]
    omega
  have enough : 43*M ≤ 50*(∑ i, (clipped i).length) := by
    change 50*listLengthExcess paths L ≤ 7*M at excess
    omega
  have big : 8*n ≤ M := by omega
  exact regularization_list_frozen_half_five_after_length_cap clipped (fun i => (sub i).nodup (simple i))
    allowed hn hp big long (fun i => List.length_take_le _ _) enough (by omega)

end OnlineReachabilityPreservers
