import OnlineReachabilityPreservers.FrozenQuadraticTrimming

/-! Frozen cleaning when the initial subsystem has few paths. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex

local notation "Before" => SourceAudit.BeforeIn

private theorem half_path_peel_inequality {M K : ℕ} (positive : 0 < M)
    (large : 7 * M ≤ 16 * K) (upper : K ≤ M) {cost : ℝ}
    (pay : cost ≤ (M : ℝ) / 8 + (K : ℝ) / 12) :
    (M : ℝ) / 104 ≤ (K : ℝ) - (K : ℝ) ^ 2 / (12 * (M : ℝ)) - (M : ℝ) / 4 - cost := by
  have mpos : (0 : ℝ) < M := by exact_mod_cast positive
  have left : 0 ≤ 16 * (K : ℝ) - 7 * M := sub_nonneg.mpr (by exact_mod_cast large)
  have high : (K : ℝ) ≤ M := by exact_mod_cast upper
  have right : 0 ≤ 169 * (M : ℝ) - 16 * K := by linarith
  have paid : ((M : ℝ) / 104 + 3 * (M : ℝ) / 8) * (12 * (M : ℝ)) ≤
      11 * (M : ℝ) * K - (K : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg left right, sq_nonneg (M : ℝ)]
  have bound : (M : ℝ) / 104 + 3 * (M : ℝ) / 8 ≤ 11 * (K : ℝ) / 12 - (K : ℝ) ^ 2 / (12 * (M : ℝ)) := by
    have div := (le_div_iff₀ (by positivity : 0 < 12 * (M : ℝ))).mpr paid
    convert div using 1
    field_simp
  linarith

/-- A subsystem with at most half the path budget and at least seven sixteenths
of the original mass has room for width splits and frozen peeling. -/
theorem regularization_list_frozen_after_half_path_width_splits {V I : Type*}
    [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I] {half : Bool} {k n p M : ℕ}
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k (listRegularizedPaths paths (4 * M / n) (4 * M / p)))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertices : Fintype.card V ≤ n) (rows : 2 * Fintype.card I ≤ p)
    (upper : ∑ i, (paths i).length ≤ M) (lower : 7 * M ≤ 16 * (∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let K := ∑ i, (paths i).length
  let D := 4 * M / n
  let L := 4 * M / p
  let pieces := listRegularizedPaths paths D L
  let Q := Fintype.card (ListBlockIndex (splitListVertices paths D) L)
  obtain ⟨Dpos, _, _⟩ := four_average_width hn dense
  obtain ⟨Lpos, limit, _⟩ := four_average_width hp long
  change 0 < D at Dpos
  change 0 < L at Lpos
  change 3 * (M / L) ≤ p at limit
  have count : Q ≤ Fintype.card I + K / L := (regularization_list_counts paths simple Dpos Lpos).2
  have Kdiv : K / L ≤ M / L := Nat.div_le_div_right upper
  have pieceBudget : Q ≤ p := by omega
  have capacity : 3 * M ≤ L * p := by
    have floor := Nat.lt_mul_div_succ (4 * M) hp
    change 4 * M < p * (L + 1) at floor
    rw [Nat.mul_succ, Nat.mul_comm p L] at floor
    omega
  have chargeBound : 3 * M * (K / L) ≤ p * K := calc
    _ ≤ (L * p) * (K / L) := Nat.mul_le_mul_right _ capacity
    _ = p * ((K / L) * L) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
  let unit : ℝ := (M : ℝ) / (4 * (p : ℝ))
  have nonnegative : 0 ≤ unit := by dsimp [unit]; positivity
  have ppos : (0 : ℝ) < p := by exact_mod_cast hp
  have origCharge : unit * (Fintype.card I : ℝ) ≤ (M : ℝ) / 8 := by
    have ratio : 2 * (Fintype.card I : ℝ) ≤ p := by exact_mod_cast rows
    have h := mul_le_mul_of_nonneg_left ratio nonnegative
    have fee : unit * (p : ℝ) = (M : ℝ) / 4 := by dsimp [unit]; field_simp
    rw [fee] at h
    linarith
  have extraCharge : unit * ((K / L : ℕ) : ℝ) ≤ (K : ℝ) / 12 := by
    have ratio : 3 * (M : ℝ) * ((K / L : ℕ) : ℝ) ≤ (p : ℝ) * K := by exact_mod_cast chargeBound
    calc
      _ = (3 * (M : ℝ) * ((K / L : ℕ) : ℝ)) / (12 * (p : ℝ)) := by dsimp [unit]; ring
      _ ≤ ((p : ℝ) * K) / (12 * (p : ℝ)) := (div_le_div_iff_of_pos_right (by positivity)).mpr ratio
      _ = _ := by field_simp
  have overall : unit * (Q : ℝ) ≤ (M : ℝ) / 8 + (K : ℝ) / 12 := calc
    _ ≤ unit * ((Fintype.card I : ℝ) + ((K / L : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast count) nonnegative
    _ = unit * (Fintype.card I : ℝ) + unit * ((K / L : ℕ) : ℝ) := mul_add _ _ _
    _ ≤ _ := add_le_add origCharge extraCharge
  have math := half_path_peel_inequality (hn.trans_le dense) lower upper overall
  have pieceSimple := listRegularizedPaths_simple paths simple D L
  obtain ⟨mass, length, degree⟩ := regularization_list_mass_caps paths simple D L Dpos Lpos
  obtain ⟨fullV, _, filledV, restV, _, _⟩ := listRegularizedPaths_full_block_profiles paths simple Dpos Lpos
  apply regularization_list_frozen_trim_vertices_quadratic pieces pieceSimple allowed hn hp dense long
    (retention := 104) (by decide) fullV filledV (restV.le.trans vertices) pieceBudget length degree (mass.trans_le upper)
  dsimp only
  rw [mass]
  exact math

private theorem frozen_of_unique_row_subset {half : Bool} {k n p : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (A : Finset (Fin p))
    (unique : ∀ {a b x y}, a ∈ A → b ∈ A → a ≠ b → x ∈ paths a → x ∈ paths b →
      y ∈ paths a → y ∈ paths b → x = y)
    (enough : let M := ∑ i, (paths i).length
      9 * M ≤ 16 * (∑ i ∈ A, (paths i).length) ∨
        (2 * A.card ≤ p ∧ 7 * M ≤ 16 * (∑ i ∈ A, (paths i).length))) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let weight (i : Fin p) := (paths i).length
  let M := ∑ i, weight i
  let working := restrictListPaths paths (univ : Finset (Fin n)) A
  have simpleWorking (i : A) : (working i).Nodup := restrictListPath_nodup (simple i.val) _
  have uniqueWorking {a b : A} {x y : (univ : Finset (Fin n))} (different : a ≠ b)
      (xa : x ∈ working a) (xb : x ∈ working b) (ya : y ∈ working a) (yb : y ∈ working b) : x = y := by
    apply Subtype.ext
    have member (i : A) (v : (univ : Finset (Fin n))) (h : v ∈ working i) : v.val ∈ paths i.val := by
      exact mem_restrictListPath.mp h
    exact unique a.property b.property
      (fun eq => different (Subtype.ext eq)) (member a x xa) (member b x xb) (member a y ya) (member b y yb)
  have legal : localOrderAdmissible half k working := by
    cases half
    · exact restrictListPaths_fullFree simple allowed _ _
    · exact restrictListPaths_halfFree simple allowed _ _
  have keeps : (∑ i, (working i).length) = ∑ i ∈ A, weight i := by
    rw [Finset.sum_subtype A (fun _ => Iff.rfl) weight]
    apply sum_congr rfl
    intro i _
    change (restrictListPath (paths i.val) univ).length = (paths i.val).length
    rw [restrictListPath_length (simple i.val), inter_univ, List.toFinset_card_of_nodup (simple i.val)]
  have upper : ∑ i, (working i).length ≤ M := by
    rw [keeps]
    exact sum_le_sum_of_subset (subset_univ A)
  have safe (D L : ℕ) : localOrderAdmissible half k (listRegularizedPaths working D L) := by
    rcases cutoff with rfl | ⟨rfl, rfl⟩
    · cases half
      · exact listRegularizedPaths_fullFree simpleWorking uniqueWorking legal D L
      · exact listRegularizedPaths_halfFree simpleWorking uniqueWorking legal D L
    · have four : BridgeFree (Before working) 4 := fun _ h => legal (h.trans (by decide))
      exact regularizedSix_bridge_free simpleWorking (fun {_ _ _ _} => uniqueWorking) four legal D L
  have vertices : Fintype.card ↥(univ : Finset (Fin n)) ≤ n := by simp
  rcases enough with large | ⟨small, large⟩
  · exact regularization_list_frozen_after_quadratic_width_trim working simpleWorking (safe _ _)
      hn hp dense long vertices (by simpa only [Fintype.card_coe, Fintype.card_fin] using card_le_univ A)
      upper (by rw [keeps]; exact large)
  · exact regularization_list_frozen_after_half_path_width_splits working simpleWorking (safe _ _)
      hn hp dense long vertices (by simpa only [Fintype.card_coe] using small)
      upper (by rw [keeps]; exact large)

/-- Frozen caps when all reversed intersections occur within disjoint
pairs of rows. Choosing one row from each pair makes intersections unique. -/
theorem regularization_list_frozen_of_matched_reverse_partners {half : Bool} {k n p : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (partner : Fin p → Fin p) (paired : Function.Involutive partner)
    (reversals : ∀ {i j x y}, i ≠ j → Before paths i x y → Before paths j y x → partner i = j)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  classical
  let rows := (univ : Finset (Fin p))
  let weight (i : Fin p) := (paths i).length
  let M := ∑ i, weight i
  let key (i : Fin p) : ℕ ×ₗ Fin p := toLex (weight i, i)
  have key_injective : Function.Injective key := fun _ _ eq =>
    congrArg (fun k : ℕ ×ₗ Fin p => (ofLex k).2) eq
  let move : Fin p ↪ Fin p := ⟨partner, paired.injective⟩
  let matched := rows.filter (fun i => partner i ≠ i)
  let first := rows.filter (fun i => key (partner i) < key i)
  let second := first.map move
  let singles := rows \ matched
  let allKept := first ∪ singles
  have firstMember (i : Fin p) : i ∈ first ↔ key (partner i) < key i := by simp [first, rows]
  have secondMember (i : Fin p) : i ∈ second ↔ key i < key (partner i) := by
    constructor
    · intro present
      obtain ⟨j, selected, eq⟩ := mem_map.mp present
      have same : partner j = i := eq
      rw [← same, paired]
      exact (firstMember _).mp selected
    · intro order
      apply mem_map.mpr
      refine ⟨partner i, (firstMember _).mpr ?_, paired i⟩
      rw [paired i]
      exact order
  have partition : first ∪ second = matched := by
    ext i
    simp only [mem_union, firstMember, secondMember, matched, rows, mem_filter, mem_univ, true_and]
    constructor
    · intro order equal
      rcases order with smaller | larger
      · exact smaller.ne (congrArg key equal)
      · exact larger.ne (congrArg key equal.symm)
    · intro different
      exact lt_or_gt_of_ne (fun eq => different (key_injective eq))
  have disjointParts : Disjoint first second := disjoint_left.mpr fun i a b =>
    ((firstMember i).mp a).asymm ((secondMember i).mp b)
  have firstInside : first ⊆ matched := fun i found => partition ▸ mem_union_left second found
  have disjointKept : Disjoint first singles := disjoint_left.mpr fun i a b =>
    (mem_sdiff.mp b).2 (firstInside a)
  have count : 2 * first.card ≤ p := by
    have equality : matched.card = first.card + first.card := by
      rw [← partition, card_union_of_disjoint disjointParts, card_map]
    have cap : matched.card ≤ p := by simpa only [Fintype.card_fin] using card_le_univ matched
    omega
  have pairWeight (i : Fin p) (member : i ∈ first) : weight (partner i) ≤ weight i := by
    rcases Prod.Lex.lt_iff.mp ((firstMember i).mp member) with smaller | ⟨equal, _⟩
    · exact smaller.le
    · exact equal.le
  let pairedMass := ∑ i ∈ matched, weight i
  let firstMass := ∑ i ∈ first, weight i
  let singleMass := ∑ i ∈ singles, weight i
  have retainedPair : pairedMass ≤ 2 * firstMass := by
    change (∑ i ∈ matched, weight i) ≤ 2 * firstMass
    rw [← partition, sum_union disjointParts, sum_map]
    calc
      _ ≤ firstMass + firstMass := Nat.add_le_add_left (sum_le_sum pairWeight) _
      _ = _ := by omega
  have total : singleMass + pairedMass = M := sum_sdiff (subset_univ matched)
  have retainedAll : (∑ i ∈ allKept, weight i) = firstMass + singleMass := sum_union disjointKept
  have two : 2 ≤ k := by rcases cutoff with rfl | ⟨rfl, _⟩ <;> decide
  have halfFree : HalfBridgeFree (Before paths) k := by
    cases half
    · exact (show BridgeFree (Before paths) k from allowed).halfFree
    · exact allowed
  have chosenInPair {i : Fin p} (chosen : i ∈ allKept) (different : partner i ≠ i) : i ∈ first := by
    rcases mem_union.mp chosen with found | single
    · exact found
    · exact ((mem_sdiff.mp single).2 (mem_filter.mpr ⟨mem_univ _, different⟩)).elim
  have noReverse {a b : Fin p} (aIn : a ∈ allKept) (bIn : b ∈ allKept)
      (different : a ≠ b) (ab : partner a = b) : False := by
    have ba : partner b = a := by rw [← ab, paired]
    have firstA := chosenInPair aIn (ab.symm ▸ different.symm)
    have firstB := chosenInPair bIn (ba.symm ▸ different)
    have one := (firstMember a).mp firstA
    have two := (firstMember b).mp firstB
    rw [ab] at one
    rw [ba] at two
    exact one.asymm two
  have originalUnique {a b : Fin p} (ha : a ∈ allKept) (hb : b ∈ allKept)
      (different : a ≠ b) {x y : Fin n}
      (xa : x ∈ paths a) (xb : x ∈ paths b) (ya : y ∈ paths a) (yb : y ∈ paths b) : x = y := by
    by_contra same
    rcases listBefore_total xa ya same with ax | ay <;> rcases listBefore_total xb yb same with bx | byy
    · exact no_parallel_list_steps halfFree two different ax bx
    · exact noReverse ha hb different (reversals different ax byy)
    · exact noReverse ha hb different (reversals different ay bx)
    · exact no_parallel_list_steps halfFree two different ay byy
  by_cases light : 8 * pairedMass ≤ 7 * M
  · apply frozen_of_unique_row_subset cutoff paths simple allowed hn hp dense long allKept
      (fun {_ _ _ _} ha hb different xa xb ya yb => originalUnique ha hb different xa xb ya yb)
    left
    change 9 * M ≤ 16 * (∑ i ∈ allKept, weight i)
    rw [retainedAll]
    omega
  · apply frozen_of_unique_row_subset cutoff paths simple allowed hn hp dense long first
      (fun {_ _ _ _} ha hb different xa xb ya yb =>
        originalUnique (mem_union_left _ ha) (mem_union_left _ hb) different xa xb ya yb)
    right
    change 2 * first.card ≤ p ∧ 7 * M ≤ 16 * firstMass
    exact ⟨count, by omega⟩

/-- Frozen cleaning for a partition into two classes, each excluding
reversed pairs. When both carry less than nine sixteenths of the mass,
the class with fewer rows meets the half-budget condition. -/
theorem regularization_list_frozen_of_two_reverse_classes {half : Bool} {k n p : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (classes : Fin p → Bool)
    (separated : ∀ {i j x y}, i ≠ j → Before paths i x y → Before paths j y x → classes i ≠ classes j)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let group (c : Bool) := (univ : Finset (Fin p)).filter (fun i => classes i = c)
  let mass (c : Bool) := ∑ i ∈ group c, (paths i).length
  have member {i : Fin p} {c : Bool} (found : i ∈ group c) : classes i = c := (mem_filter.mp found).2
  have full : group false ∪ group true = univ := by
    ext i
    cases seen : classes i <;> simp [group, seen]
  have disjointGroups : Disjoint (group false) (group true) := by
    rw [disjoint_left]
    exact fun i left right => Bool.false_ne_true ((member left).symm.trans (member right))
  have totalMass : mass false + mass true = M := by
    change _ = ∑ i ∈ (univ : Finset (Fin p)), (paths i).length
    rw [← full, sum_union disjointGroups]
  have totalRows : (group false).card + (group true).card = p := by
    rw [← card_union_of_disjoint disjointGroups, full, card_univ, Fintype.card_fin]
  have two : 2 ≤ k := by rcases cutoff with rfl | ⟨rfl, _⟩ <;> decide
  have halfFree : HalfBridgeFree (Before paths) k := by
    cases half
    · exact (show BridgeFree (Before paths) k from allowed).halfFree
    · exact allowed
  have unique (c : Bool) {i j x y} (iGroup : i ∈ group c) (jGroup : j ∈ group c) (different : i ≠ j)
      (xi : x ∈ paths i) (xj : x ∈ paths j) (yi : y ∈ paths i) (yj : y ∈ paths j) : x = y := by
    by_contra unequal
    have same : classes i = classes j := (member iGroup).trans (member jGroup).symm
    rcases listBefore_total xi yi unequal with xy | yx <;> rcases listBefore_total xj yj unequal with xy' | yx'
    · exact no_parallel_list_steps halfFree two different xy xy'
    · exact separated different xy yx' same
    · exact separated different yx xy' same
    · exact no_parallel_list_steps halfFree two different yx yx'
  have enough (c : Bool) (bound : 9 * M ≤ 16 * mass c ∨ (2 * (group c).card ≤ p ∧ 7 * M ≤ 16 * mass c)) :
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        M ≤ 104 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
    frozen_of_unique_row_subset cutoff paths simple allowed hn hp dense long (group c)
      (fun {_ _ _ _} => unique c) bound
  by_cases zeroLarge : 9 * M ≤ 16 * mass false
  · exact enough false (Or.inl zeroLarge)
  by_cases oneLarge : 9 * M ≤ 16 * mass true
  · exact enough true (Or.inl oneLarge)
  by_cases zeroFew : 2 * (group false).card ≤ p
  · exact enough false (Or.inr ⟨zeroFew, by omega⟩)
  · exact enough true (Or.inr ⟨by omega, by omega⟩)

end OnlineReachabilityPreservers
