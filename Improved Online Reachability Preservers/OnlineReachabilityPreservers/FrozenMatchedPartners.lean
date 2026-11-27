import OnlineReachabilityPreservers.FrozenQuadraticTrimming
import OnlineReachabilityPreservers.HalfFiveProjection
import OnlineReachabilityPreservers.LocalFrozenLowMass
import OnlineReachabilityPreservers.OppositeLinkForest

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

private theorem frozen_after_half_path_splits_of_charge {V I : Type*}
    [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I] {half : Bool} {k n p M retention : ℕ}
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k (listRegularizedPaths paths (4 * M / n) (4 * M / p)))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertices : Fintype.card V ≤ n) (rows : 2 * Fintype.card I ≤ p)
    (upper : ∑ i, (paths i).length ≤ M) (positive : 0 < retention)
    (enough : let K := ∑ i, (paths i).length
      (M : ℝ) / retention ≤ (K : ℝ) - (K : ℝ)^2/(4*((4*M/n*n : ℕ) : ℝ)) - (M : ℝ)/4 -
        ((M : ℝ)/(4*(p : ℝ)))*((Fintype.card I + K/(4*M/p) : ℕ) : ℝ)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
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
  have pieceSimple := listRegularizedPaths_simple paths simple D L
  obtain ⟨mass, length, degree⟩ := regularization_list_mass_caps paths simple D L Dpos Lpos
  obtain ⟨fullV, _, filledV, restV, _, _⟩ := listRegularizedPaths_full_block_profiles paths simple Dpos Lpos
  apply regularization_list_frozen_trim_vertices_quadratic_of_width pieces pieceSimple allowed hn hp dense long
    positive fullV filledV (restV.le.trans vertices) pieceBudget length degree (mass.trans_le upper)
  dsimp only
  rw [mass]
  have charge : ((M : ℝ)/(4*(p : ℝ)))*(Q : ℝ) ≤
      ((M : ℝ)/(4*(p : ℝ)))*((Fintype.card I + K/L : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast count) (by positivity)
  exact enough.trans (sub_le_sub_left charge _)

private theorem frozen_half_path_peel_charge {M K p L r a b : ℕ}
    (hp : 0 < p) (ha : 0 < a) (rows : 2*r ≤ p) (capacity : a*M ≤ b*(L*p)) :
    ((M : ℝ)/(4*(p : ℝ)))*((r + K/L : ℕ) : ℝ) ≤ (M : ℝ)/8 + (b : ℝ)*(K : ℝ)/(4*(a : ℝ)) := by
  have chargeBound : a*M*(K/L) ≤ b*p*K := calc
    _ ≤ (b*(L*p))*(K/L) := Nat.mul_le_mul_right _ capacity
    _ = (b*p)*((K/L)*L) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
  let unit : ℝ := (M : ℝ) / (4 * (p : ℝ))
  have nonnegative : 0 ≤ unit := by dsimp [unit]; positivity
  have ppos : (0 : ℝ) < p := by exact_mod_cast hp
  have apos : (0 : ℝ) < a := by exact_mod_cast ha
  have origCharge : unit * (r : ℝ) ≤ (M : ℝ) / 8 := by
    have ratio : 2 * (r : ℝ) ≤ p := by exact_mod_cast rows
    have h := mul_le_mul_of_nonneg_left ratio nonnegative
    have fee : unit * (p : ℝ) = (M : ℝ) / 4 := by dsimp [unit]; field_simp
    rw [fee] at h
    linarith
  have extraCharge : unit * ((K/L : ℕ) : ℝ) ≤ (b : ℝ)*K/(4*(a : ℝ)) := by
    have ratio : (a : ℝ)*M*((K/L : ℕ) : ℝ) ≤ (b : ℝ)*p*K := by exact_mod_cast chargeBound
    calc
      _ = ((a : ℝ)*M*((K/L : ℕ) : ℝ))/(4*(a : ℝ)*p) := by dsimp [unit]; field_simp
      _ ≤ ((b : ℝ)*p*K)/(4*(a : ℝ)*p) := (div_le_div_iff_of_pos_right (by positivity)).mpr ratio
      _ = _ := by field_simp
  rw [Nat.cast_add, mul_add]
  exact add_le_add origCharge extraCharge

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
  apply frozen_after_half_path_splits_of_charge paths simple allowed hn hp dense long vertices rows upper (by decide)
  let K := ∑ i, (paths i).length
  let Q : ℝ := ((M : ℝ)/(4*(p : ℝ)))*((Fintype.card I + K/(4*M/p) : ℕ) : ℝ)
  have floorP := four_average_width_product hp (M := M)
  have floorN := four_average_width_product hn (M := M)
  have capacity : 3*M ≤ 1*((4*M/p)*p) := by omega
  have vertexCapacity : 3*(M : ℝ) ≤ ((4*M/n*n : ℕ) : ℝ) := by
    exact_mod_cast (show 3*M ≤ (4*M/n)*n by omega)
  have mpos : (0 : ℝ) < M := by exact_mod_cast hn.trans_le dense
  have charge : Q ≤ (M : ℝ)/8 + (K : ℝ)/12 := by
    have bound := frozen_half_path_peel_charge (K := K) hp (show 0 < 3 by decide) rows capacity
    norm_num [Q] at bound ⊢
    exact bound
  have lost : (K : ℝ)^2/(4*((4*M/n*n : ℕ) : ℝ)) ≤ (K : ℝ)^2/(12*(M : ℝ)) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    linarith
  have enough := half_path_peel_inequality (hn.trans_le dense) lower upper charge
  change (M : ℝ) / 104 ≤ (K : ℝ) - (K : ℝ)^2/(4*((4*M/n*n : ℕ) : ℝ)) - (M : ℝ)/4 - Q
  linarith

private theorem unique_row_width_splits_admissible_extended {V I : Type*}
    [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I] {half : Bool} {k : ℕ}
    (cutoff : (k = 4 ∨ (k = 6 ∧ half = false)) ∨ (k = 5 ∧ half = true)) (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b →
      y ∈ paths a → y ∈ paths b → x = y)
    (allowed : localOrderAdmissible half k paths) (D L : ℕ) :
    localOrderAdmissible half k (listRegularizedPaths paths D L) := by
  rcases cutoff with (rfl | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
  · cases half
    · exact listRegularizedPaths_fullFree simple (fun {_ _ _ _} => unique) allowed D L
    · exact listRegularizedPaths_halfFree simple (fun {_ _ _ _} => unique) allowed D L
  · have four : BridgeFree (Before paths) 4 := fun _ h => allowed (h.trans (by decide))
    exact regularizedSix_bridge_free simple (fun {_ _ _ _} => unique) four allowed D L

  · exact listRegularizedPaths_halfFree_five_of_unique_intersections simple allowed
      (fun {_ _ _ _} => unique) D L

private theorem unique_row_width_splits_admissible {V I : Type*}
    [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I] {half : Bool} {k : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {a b x y}, a ≠ b → x ∈ paths a → x ∈ paths b →
      y ∈ paths a → y ∈ paths b → x = y)
    (allowed : localOrderAdmissible half k paths) (D L : ℕ) :
    localOrderAdmissible half k (listRegularizedPaths paths D L) :=
  unique_row_width_splits_admissible_extended (Or.inl cutoff) paths simple
    (fun {_ _ _ _} => unique) allowed D L

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
  have safe := unique_row_width_splits_admissible cutoff working simpleWorking (fun {_ _ _ _} => uniqueWorking) legal
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

private theorem dense_width_capacity {M q : ℕ} (positive : 0 < q) (large : 8*q ≤ M) :
    31*M ≤ 8*((4*M/q)*q) := by
  have floor := four_average_width_product positive (M := M)
  omega

private theorem dense_two_support_crop {M K R lostV lostI vertexCapacity pathCapacity : ℕ}
    (positive : 0 < M) (upper : K ≤ M) (lower : 13*M ≤ 24*K)
    (retained : K ≤ R + (lostV + lostI))
    (roomV : 31*M ≤ 8*vertexCapacity) (roomI : 31*M ≤ 8*pathCapacity)
    (chargeV : 4*vertexCapacity*lostV ≤ K^2) (chargeI : 4*pathCapacity*lostI ≤ K^2) :
    290*M ≤ 576*R := by
  have lossV : 31*M*lostV ≤ 2*K^2 := calc
    _ ≤ (8*vertexCapacity)*lostV := Nat.mul_le_mul_right _ roomV
    _ = 2*(4*vertexCapacity*lostV) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ chargeV
  have lossI : 31*M*lostI ≤ 2*K^2 := calc
    _ ≤ (8*pathCapacity)*lostI := Nat.mul_le_mul_right _ roomI
    _ = 2*(4*pathCapacity*lostI) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ chargeI
  have paid : 31*M*K ≤ 31*M*R+4*K^2 := calc
    _ ≤ 31*M*(R+(lostV+lostI)) := Nat.mul_le_mul_left _ retained
    _ = 31*M*R+(31*M*lostV+31*M*lostI) := by ring
    _ ≤ _ := by have h := add_le_add lossV lossI; omega
  have paidReal : 31*(M:ℝ)*K ≤ 31*(M:ℝ)*R+4*(K:ℝ)^2 := by exact_mod_cast paid
  have lowerReal : 0 ≤ 24*(K:ℝ)-13*M := sub_nonneg.mpr (by exact_mod_cast lower)
  have upperReal : (K:ℝ) ≤ M := by exact_mod_cast upper
  have room : 0 ≤ 692*(M:ℝ)-96*K := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have enough : 290*(M:ℝ)*M ≤ 576*(R:ℝ)*M := by
    nlinarith only [paidReal, mul_nonneg lowerReal room, sq_nonneg (M:ℝ)]
  apply (Nat.mul_le_mul_right_iff positive).mp
  exact_mod_cast enough

private theorem dense_half_support_mass {M K p n r : ℕ} (positive : 0 < M) (hp : 0 < p)
    (upper : K ≤ M) (lower : 5*M ≤ 12*K) (rows : 2*r ≤ p)
    (roomV : 31*M ≤ 8*((4*M/n)*n)) (roomI : 31*M ≤ 8*((4*M/p)*p)) :
    (M:ℝ)/288 ≤ (K:ℝ)-(K:ℝ)^2/(4*((4*M/n*n : ℕ):ℝ))-(M:ℝ)/4-
      ((M:ℝ)/(4*(p:ℝ)))*((r+K/(4*M/p) : ℕ):ℝ) := by
  have mPos : (0:ℝ) < M := by exact_mod_cast positive
  have capacity : 31*(M:ℝ) ≤ 8*((4*M/n*n : ℕ):ℝ) := by exact_mod_cast roomV
  have loss : (K:ℝ)^2/(4*((4*M/n*n : ℕ):ℝ)) ≤ (K:ℝ)^2/(31*(M:ℝ)/2) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    linarith
  have charge := frozen_half_path_peel_charge (K := K) hp (show 0 < 31 by decide) rows roomI
  have lowerReal : 0 ≤ 12*(K:ℝ)-5*M := sub_nonneg.mpr (by exact_mod_cast lower)
  have upperReal : (K:ℝ) ≤ M := by exact_mod_cast upper
  have room : 0 ≤ 338*(M:ℝ)-24*K := by linarith
  have paid : ((M:ℝ)/288+3*(M:ℝ)/8)*(31*(M:ℝ)) ≤ 29*(M:ℝ)*K-2*(K:ℝ)^2 := by
    nlinarith only [mul_nonneg lowerReal room, sq_nonneg (M:ℝ)]
  have bound : (M:ℝ)/288+3*(M:ℝ)/8 ≤ 29*(K:ℝ)/31-(K:ℝ)^2/(31*(M:ℝ)/2) := by
    have div := (le_div_iff₀ (by positivity : 0 < 31*(M:ℝ))).mpr paid
    convert div using 1
    field_simp
  norm_num at charge
  push_cast at loss ⊢
  linarith

private theorem frozen_of_two_reverse_classes_of_mass {half : Bool} {k n p : ℕ}
    (cutoff : (k = 4 ∨ (k = 6 ∧ half = false)) ∨ (k = 5 ∧ half = true)) (paths kept : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (sub : ∀ i, (kept i).Sublist (paths i)) (classes : Fin p → Bool)
    (separated : ∀ {i j x y}, i ≠ j → Before kept i x y → Before kept j y x → classes i ≠ classes j)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retained : let M := ∑ i, (paths i).length
      let mass (c : Bool) := ∑ i ∈ (univ : Finset (Fin p)).filter (fun i => classes i = c), (kept i).length
      (∃ c, 13*M ≤ 24*mass c) ∨ 23*M ≤ 24*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  have two : 2 ≤ k := by rcases cutoff with (rfl | ⟨rfl, _⟩) | ⟨rfl, _⟩ <;> decide
  have free : HalfBridgeFree (Before paths) k := by
    cases half
    · exact (show BridgeFree (Before paths) k from allowed).halfFree
    · exact allowed
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n', hn', p', hp', clean, cleanSimple, cleanFree, mass, upper, caps⟩ :=
      regularization_list_frozen_low_mass paths simple free two hn hp dense long low
    have cleanAllowed : localOrderAdmissible half k clean := by cases half; exact cleanFree; exact cleanFree.halfFree
    exact ⟨n', hn', p', hp', clean, cleanSimple, cleanAllowed, by omega, upper, caps⟩
  have vRoom := dense_width_capacity hn (show 8*n ≤ M by have h := le_max_left n p; omega)
  have iRoom := dense_width_capacity hp (show 8*p ≤ M by have h := le_max_right n p; omega)
  let group (c : Bool) := (univ : Finset (Fin p)).filter (fun i => classes i = c)
  let mass (c : Bool) := ∑ i ∈ group c, (kept i).length
  have member {i : Fin p} {c : Bool} (found : i ∈ group c) : classes i = c := (mem_filter.mp found).2
  have full : group false ∪ group true = univ := by
    ext i
    cases seen : classes i <;> simp [group, seen]
  have disjointGroups : Disjoint (group false) (group true) := by
    rw [disjoint_left]
    exact fun i left right => Bool.false_ne_true ((member left).symm.trans (member right))
  have totalMass : mass false + mass true = ∑ i, (kept i).length := by
    rw [← full, sum_union disjointGroups]
  have totalRows : (group false).card + (group true).card = p := by
    rw [← card_union_of_disjoint disjointGroups, full, card_univ, Fintype.card_fin]
  have enough (c : Bool) (bound : 13*M ≤ 24*mass c ∨ (2*(group c).card ≤ p ∧ 5*M ≤ 12*mass c)) :
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
    let chosen (i : group c) := kept i.val
    have chosenSimple (i : group c) : (chosen i).Nodup := (sub i.val).nodup (simple i.val)
    have liftStep (i : group c) (x y : Fin n) (step : Before chosen i x y) : Before paths i.val x y :=
      listBefore_of_sublist (simple i.val) (sub i.val) step
    have chosenAllowed : localOrderAdmissible half k chosen := by
      cases half
      · intro j size
        exact ⟨fun b => (allowed size).false (b.mapPaths Subtype.val Subtype.val_injective liftStep)⟩
      · intro j size b earlier
        exact allowed size (b.mapPaths Subtype.val Subtype.val_injective liftStep) earlier
    have unique {i j : group c} {x y : Fin n} (different : i ≠ j)
        (xi : x ∈ chosen i) (xj : x ∈ chosen j) (yi : y ∈ chosen i) (yj : y ∈ chosen j) : x = y := by
      by_contra unequal
      have different' : i.val ≠ j.val := fun eq => different (Subtype.ext eq)
      have same : classes i.val = classes j.val := (member i.property).trans (member j.property).symm
      rcases listBefore_total xi yi unequal with xy | yx <;> rcases listBefore_total xj yj unequal with xy' | yx'
      · exact no_parallel_list_steps free two different' (liftStep i x y xy) (liftStep j x y xy')
      · exact separated different' xy yx' same
      · exact separated different' yx xy' same
      · exact no_parallel_list_steps free two different' (liftStep i y x yx) (liftStep j y x yx')
    have safe := unique_row_width_splits_admissible_extended cutoff chosen chosenSimple (fun {_ _ _ _} => unique) chosenAllowed
    have counted : (∑ i, (chosen i).length) = mass c :=
      (sum_subtype (group c) (fun _ => Iff.rfl) (fun i => (kept i).length)).symm
    have upper : (∑ i, (chosen i).length) ≤ M := calc
      _ = mass c := counted
      _ ≤ ∑ i, (kept i).length := sum_le_sum_of_subset (subset_univ _)
      _ ≤ M := sum_le_sum (fun i _ => (sub i).length_le)
    rcases bound with large | ⟨few, sufficient⟩
    · apply regularization_list_frozen_after_quadratic_width_trim_of_loss chosen chosenSimple (safe _ _) hn hp dense long
        (by simp) (by simpa [Fintype.card_coe, Fintype.card_fin] using card_le_univ (group c)) upper
      dsimp only
      intro R lostV lostI keptMass lostVBound lostIBound
      exact dense_two_support_crop (hn.trans_le dense) upper (by rwa [counted]) keptMass vRoom iRoom lostVBound lostIBound
    · apply frozen_after_half_path_splits_of_charge chosen chosenSimple (safe _ _) hn hp dense long (by simp)
        (by simpa only [Fintype.card_coe] using few) upper (by decide)
      exact dense_half_support_mass (hn.trans_le dense) hp upper (by rwa [counted])
        (by simpa only [Fintype.card_coe] using few) vRoom iRoom
  by_cases zeroLarge : 13*M ≤ 24*mass false
  · exact enough false (Or.inl zeroLarge)
  by_cases oneLarge : 13*M ≤ 24*mass true
  · exact enough true (Or.inl oneLarge)
  have combined : 23*M ≤ 24*(∑ i, (kept i).length) := by
    rcases retained with ⟨c, hc⟩ | hc
    · cases c
      · exact (zeroLarge hc).elim
      · exact (oneLarge hc).elim
    · exact hc
  by_cases zeroFew : 2*(group false).card ≤ p
  · exact enough false (Or.inr ⟨zeroFew, by omega⟩)
  · exact enough true (Or.inr ⟨by omega, by omega⟩)

/-- Repair a two-class partition by deleting at most one twenty-fourth of
all incidences. At cutoff four in either mode, or cutoff six in full mode,
frozen cleaning then keeps at least one 288th of the input mass. -/
theorem regularization_list_frozen_of_repaired_reverse_classes {half : Bool} {k n p : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths kept : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (sub : ∀ i, (kept i).Sublist (paths i)) (classes : Fin p → Bool)
    (separated : ∀ {i j x y}, i ≠ j → Before kept i x y → Before kept j y x → classes i ≠ classes j)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retained : 23*(∑ i, (paths i).length) ≤ 24*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  frozen_of_two_reverse_classes_of_mass (Or.inl cutoff) paths kept simple allowed sub classes (fun {_ _ _ _} => separated)
    hn hp dense long (Or.inr retained)

private theorem frozen_of_large_unique_sublists {half : Bool} {k n p : ℕ}
    (cutoff : (k = 4 ∨ (k = 6 ∧ half = false)) ∨ (k = 5 ∧ half = true)) (paths kept : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (sub : ∀ i, (kept i).Sublist (paths i))
    (unique : ∀ {i j x y}, i ≠ j → x ∈ kept i → x ∈ kept j → y ∈ kept i → y ∈ kept j → x = y)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retained : 13*(∑ i, (paths i).length) ≤ 24*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine frozen_of_two_reverse_classes_of_mass cutoff paths kept simple allowed sub (fun _ => false)
    ?separated hn hp dense long ?mass
  case separated =>
    intro i j x y different xy yx _
    exact listBefore_ne xy (unique different xy.1 yx.2.1 xy.2.1 yx.1)
  case mass =>
    left
    refine ⟨false, ?_⟩
    simpa using retained

/-- A rowwise sublist family with unique intersections suffices when its mass
is at least thirteen twenty-fourths of the original mass. -/
theorem regularization_list_frozen_of_large_unique_sublists {half : Bool} {k n p : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths kept : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (sub : ∀ i, (kept i).Sublist (paths i))
    (unique : ∀ {i j x y}, i ≠ j → x ∈ kept i → x ∈ kept j → y ∈ kept i → y ∈ kept j → x = y)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retained : 13*(∑ i, (paths i).length) ≤ 24*(∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  frozen_of_large_unique_sublists (Or.inl cutoff) paths kept simple allowed sub
    (fun {_ _ _ _} => unique) hn hp dense long retained

/-- If the number of opposite links is at most eleven twenty-fourths of
the input mass, opposite-intersection pruning supplies a large unique family. -/
theorem regularization_list_frozen_of_eleven_twentyfourths_links {half : Bool} {k n p : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (two : HalfBridgeFree (Before paths) 2)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (links : 24*Nat.card (oppositeLinkGraphOfHalfTwo paths two).edgeSet ≤ 11*(∑ i, (paths i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have loss := removeOppositeIntersections_mass_with_half_two_link_count two simple
  exact regularization_list_frozen_of_large_unique_sublists cutoff paths (removeOppositeIntersections paths)
    simple allowed (removeOppositeIntersections_sublist paths)
    (fun {_ _ _ _} different xi xj yi yj => removeOppositeIntersections_unique simple two (by decide) different xi xj yi yj)
    hn hp dense long (by omega)

/-- In the earlier row of a reversed pair in one class, remove the later
endpoint of the reversed comparison. -/
noncomputable def removeSameClassReverseEnds {V : Type*} [DecidableEq V] {p : ℕ}
    (paths : Fin p → List V) (classes : Fin p → Bool) (i : Fin p) : List V := by
  classical
  exact (paths i).filter fun v => decide (¬ ∃ j, classes i = classes j ∧ LaterReversePartner paths v i j)

theorem removeSameClassReverseEnds_sublist {V : Type*} [DecidableEq V] {p : ℕ}
    (paths : Fin p → List V) (classes : Fin p → Bool) (i : Fin p) :
    (removeSameClassReverseEnds paths classes i).Sublist (paths i) := List.filter_sublist

theorem removeSameClassReverseEnds_separates {V : Type*} [DecidableEq V] {p : ℕ}
    (paths : Fin p → List V) (simple : ∀ i, (paths i).Nodup) (classes : Fin p → Bool)
    {i j : Fin p} {x y : V} (different : i ≠ j)
    (xy : Before (removeSameClassReverseEnds paths classes) i x y)
    (yx : Before (removeSameClassReverseEnds paths classes) j y x) : classes i ≠ classes j := by
  have survives {a : Fin p} {v : V} (hv : v ∈ removeSameClassReverseEnds paths classes a) :
      ¬ ∃ b, classes a = classes b ∧ LaterReversePartner paths v a b := by
    classical
    have test : v ∈ paths a ∧ ¬ ∃ b, classes a = classes b ∧ LaterReversePartner paths v a b := by
      simpa only [removeSameClassReverseEnds, List.mem_filter, decide_eq_true_eq] using hv
    exact test.2
  have beforeXY := listBefore_of_sublist (simple i) (removeSameClassReverseEnds_sublist paths classes i) xy
  have beforeYX := listBefore_of_sublist (simple j) (removeSameClassReverseEnds_sublist paths classes j) yx
  intro same
  rcases lt_or_gt_of_ne different with earlier | later
  · exact survives xy.2.1 ⟨j, same, earlier, x, beforeXY, beforeYX⟩
  · exact survives yx.2.1 ⟨i, same.symm, later, y, beforeYX, beforeXY⟩

/-- Count each removed occurrence once, even if several reversed comparisons
would mark it. This provides a direct sufficient test for two-class repair. -/
theorem regularization_list_frozen_of_sparse_same_class_reverse_ends {half : Bool} {k n p : ℕ}
    (cutoff : k = 4 ∨ (k = 6 ∧ half = false)) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths) (classes : Fin p → Bool)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (loss : 24*(∑ i, ((paths i).length-(removeSameClassReverseEnds paths classes i).length)) ≤
      ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let kept := removeSameClassReverseEnds paths classes
  have sub := removeSameClassReverseEnds_sublist paths classes
  change 24*(∑ i, ((paths i).length-(kept i).length)) ≤ ∑ i, (paths i).length at loss
  have accounted : (∑ i, ((paths i).length-(kept i).length)) + (∑ i, (kept i).length) = ∑ i, (paths i).length := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => Nat.sub_add_cancel (sub i).length_le
  exact regularization_list_frozen_of_repaired_reverse_classes cutoff paths kept simple allowed sub classes
    (fun {_ _ _ _} => removeSameClassReverseEnds_separates paths simple classes) hn hp dense long (by omega)

/-- If pruning opposite intersections preserves at least thirteen
twenty-fourths of the mass, the original caps hold at half cutoff five. -/
theorem regularization_list_frozen_half_five_after_opposite_pruning {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retained : 13*(∑ i, (paths i).length) ≤ 24*(∑ i, (removeOppositeIntersections paths i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  exact frozen_of_large_unique_sublists (half := true) (k := 5) (Or.inr ⟨rfl,rfl⟩)
    paths (removeOppositeIntersections paths) simple free (removeOppositeIntersections_sublist paths)
    (fun {_ _ _ _} different xa xb ya yb =>
      removeOppositeIntersections_unique simple free (by decide) different xa xb ya yb)
    hn hp dense long retained

/-- The last vertex on each nonempty path survives pruning. The added mass
suffices at half cutoff five if there are at least (M/12) nonempty paths. -/
theorem regularization_list_frozen_half_five_of_many_nonempty_paths {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (many : (∑ i, (paths i).length) ≤ 12*(univ.filter fun i => paths i ≠ []).card) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  apply regularization_list_frozen_half_five_after_opposite_pruning paths simple free hn hp dense long
  have gain := removeOppositeIntersections_mass_with_nonempty_paths simple free (by decide)
  omega

/-- Each pruned incidence charges an opposite link. When the number of
links is at most eleven twenty-fourths of the mass, half-five cleaning works. -/
theorem regularization_list_frozen_half_five_of_few_opposite_links {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (few : 24*Nat.card (oppositeLinkGraphOfHalfTwo paths (fun _ h => free (h.trans (by decide)))).edgeSet ≤
      11*(∑ i, (paths i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 288*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let two : HalfBridgeFree (Before paths) 2 := fun _ h => free (h.trans (by decide))
  let E := Nat.card (oppositeLinkGraphOfHalfTwo paths two).edgeSet
  change 24*E ≤ 11*(∑ i, (paths i).length) at few
  have loss : (∑ i, (paths i).length) ≤ (∑ i, (removeOppositeIntersections paths i).length)+E :=
    removeOppositeIntersections_mass_with_half_two_link_count two simple
  apply regularization_list_frozen_half_five_after_opposite_pruning paths simple free hn hp dense long
  omega

/-- At half cutoff five, a rowwise sublist family with unique intersections
and at least thirteen twenty-fourths of the mass gives the frozen caps. -/
theorem regularization_list_frozen_half_five_of_large_unique_sublists {n p : ℕ}
    (paths kept : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (sub : ∀ i, (kept i).Sublist (paths i))
    (unique : ∀ {i j x y}, i ≠ j → x ∈ kept i → x ∈ kept j → y ∈ kept i → y ∈ kept j → x = y)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (retained : 13 * (∑ i, (paths i).length) ≤ 24 * (∑ i, (kept i).length)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (Before clean) 5 ∧
      M ≤ 288 * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  frozen_of_large_unique_sublists (half := true) (k := 5) (Or.inr ⟨rfl,rfl⟩)
    paths kept simple free sub (fun {_ _ _ _} => unique) hn hp dense long retained

end OnlineReachabilityPreservers
