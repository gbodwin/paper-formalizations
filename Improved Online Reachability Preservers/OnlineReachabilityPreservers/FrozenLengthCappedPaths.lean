import OnlineReachabilityPreservers.FrozenOverlongPaths

/-! Frozen cleaning of a sufficiently massive length-capped subfamily. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

private theorem frozen_length_capped_retention {M K : ℝ} (positive : 0 < M) (lower : 8*M ≤ 15*K)
    (upper : K ≤ M) : M/104 ≤ K-K^2/(12*M)-M/2 := by
  rw [show K-K^2/(12*M)-M/2 = (12*M*K-K^2-6*M^2)/(12*M) from by
    field_simp [positive.ne']
    ring]
  apply (le_div_iff₀ (by positivity)).mpr
  have quadratic := mul_nonneg (show 0 ≤ K-8*M/15 by linarith) (show 0 ≤ 12*M-K-8*M/15 by linarith)
  nlinarith

/-- A length-capped subfamily needs only vertex splits. Use its actual
path count and exact original vertex width in the trimming and peeling charges. -/
theorem regularization_list_frozen_of_length_capped_exact_budget {I : Type*} [LinearOrder I] [Fintype I]
    {half : Bool} {k n p M retention : ℕ} (paths : I → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (size : half = true → k ≤ 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (pathsCap : Fintype.card I ≤ p) (lengthCap : ∀ i, (paths i).length ≤ 4*M/p)
    (upper : (∑ i, (paths i).length) ≤ M) (positive : 0 < retention)
    (enough : let K := (∑ i, (paths i).length : ℕ)
      (M:ℝ)/retention ≤ (K:ℝ)-(K:ℝ)^2/(4*((4*M/n*n : ℕ):ℝ))-(M:ℝ)/4-(M:ℝ)/(4*(p:ℝ))*(Fintype.card I:ℝ)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let D := 4*M/n
  let K := ∑ i, (paths i).length
  let copied := splitListVertices paths D
  obtain ⟨width,_,_⟩ := four_average_width hn dense
  have copiedSimple (i : I) : (copied i).Nodup := splitListVertices_simple paths D i (simple i)
  have steps {i : I} {x y : ListVertexBlockIndex paths D} (step : ListBefore copied i x y) :
      ListBefore paths i x.fst y.fst := splitListVertices_step (simple i) step
  have legal : localOrderAdmissible half k copied := by
    cases half
    · exact BridgeFree.split_list_vertices_any allowed (·.fst) (fun {_ _ _} => steps)
    · exact HalfBridgeFree.split_list_vertices_short allowed (size rfl) (·.fst) (fun {_ _ _} => steps)
  have copyLength (i : I) : (copied i).length = (paths i).length := splitListVertices_length paths D i
  have copiesAsSets : (fun i => (copied i).toFinset) = splitVertices (fun i => (paths i).toFinset) D :=
    funext (splitListVertices_toFinset paths D)
  have degreeCap (v : ListVertexBlockIndex paths D) : (occurrences (fun i => (copied i).toFinset) v).card ≤ D := by
    rw [copiesAsSets]
    exact splitVertices_degree _ width v
  have mass : (∑ i, (copied i).length) = K := sum_congr rfl (fun i _ => copyLength i)
  obtain ⟨filled,exactFilled,other⟩ := splitListVertices_full_block_profile paths width
  have remainders : (univ \ filled).card ≤ n := by rw [other,Fintype.card_fin]
  refine regularization_list_frozen_trim_vertices_quadratic_of_width copied copiedSimple legal hn hp dense long
    positive filled exactFilled remainders pathsCap
    (fun i => (copyLength i).trans_le (lengthCap i)) degreeCap (mass.trans_le upper) ?_
  rw [mass]
  exact enough

/-- A frozen length-capped bound with the vertex loss expressed using only the original mass. -/
theorem regularization_list_frozen_of_length_capped_budget {I : Type*} [LinearOrder I] [Fintype I]
    {half : Bool} {k n p M retention : ℕ} (paths : I → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (size : half = true → k ≤ 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (pathsCap : Fintype.card I ≤ p) (lengthCap : ∀ i, (paths i).length ≤ 4*M/p)
    (upper : (∑ i, (paths i).length) ≤ M) (positive : 0 < retention)
    (enough : let K := (∑ i, (paths i).length : ℕ)
      (M:ℝ)/retention ≤ (K:ℝ)-(K:ℝ)^2/(12*(M:ℝ))-(M:ℝ)/4-(M:ℝ)/(4*(p:ℝ))*(Fintype.card I:ℝ)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  apply regularization_list_frozen_of_length_capped_exact_budget paths simple allowed size hn hp dense long
    pathsCap lengthCap upper positive
  let K : ℝ := ((∑ i, (paths i).length : ℕ) : ℝ)
  have floor := four_average_width_product hn (M := M)
  have budget : 3*M ≤ (4*M/n)*n := by omega
  have budgetReal : 3*(M:ℝ) ≤ ((4*M/n*n : ℕ):ℝ) := by exact_mod_cast budget
  have mPos : (0:ℝ) < M := by exact_mod_cast hn.trans_le dense
  have charged : K^2/(4*((4*M/n*n : ℕ):ℝ)) ≤ K^2/(12*(M:ℝ)) := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    linarith
  change (M:ℝ)/retention ≤ K-K^2/(4*((4*M/n*n : ℕ):ℝ))-(M:ℝ)/4-((M:ℝ)/(4*(p:ℝ)))*(Fintype.card I)
  change (M:ℝ)/retention ≤ K-K^2/(12*M)-(M:ℝ)/4-((M:ℝ)/(4*(p:ℝ)))*(Fintype.card I) at enough
  linarith

/-- Row splitting is unnecessary for a length-capped subfamily carrying
at least eight fifteenths of the original mass. Vertex trimming and
peeling then give both budgets and all four frozen caps. -/
theorem regularization_list_frozen_of_length_capped_mass {I : Type*} [LinearOrder I] [Fintype I]
    {half : Bool} {k n p M : ℕ} (paths : I → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (size : half = true → k ≤ 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (pathsCap : Fintype.card I ≤ p) (lengthCap : ∀ i, (paths i).length ≤ 4*M/p)
    (upper : (∑ i, (paths i).length) ≤ M) (lower : 8*M ≤ 15*(∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_of_length_capped_budget paths simple allowed size hn hp dense long
    pathsCap lengthCap upper (by decide) ?_
  let K := ∑ i, (paths i).length
  have massPos : (0:ℝ) < M := by exact_mod_cast hn.trans_le dense
  let l : ℝ := (M:ℝ)/(4*(p:ℝ))
  have total : l*(p:ℝ) = (M:ℝ)/4 := by
    have p0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    dsimp [l]
    field_simp [p0]
  have pathLoss : l*(Fintype.card I:ℝ) ≤ (M:ℝ)/4 :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr pathsCap) (by positivity)).trans_eq total
  have retain := frozen_length_capped_retention (M := (M:ℝ)) (K := (K:ℝ)) massPos
    (by exact_mod_cast lower) (by exact_mod_cast upper)
  change (M:ℝ)/104 ≤ (K:ℝ)-(K:ℝ)^2/(12*(M:ℝ))-(M:ℝ)/4-l*(Fintype.card I:ℝ)
  linarith

private theorem frozen_half_path_budget_retention {M K : ℝ} (positive : 0 < M) (lower : 2*M ≤ 5*K)
    (upper : K ≤ M) : M/90 ≤ K-K^2/(12*M)-3*M/8 := by
  rw [show K-K^2/(12*M)-3*M/8 = (24*M*K-2*K^2-9*M^2)/(24*M) from by
    field_simp [positive.ne']
    ring]
  apply (le_div_iff₀ (by positivity)).mpr
  have quadratic := mul_nonneg (show 0 ≤ K-2*M/5 by linarith) (show 0 ≤ 12*M-K-2*M/5 by linarith)
  nlinarith [sq_nonneg M]

/-- A subfamily of length-capped paths needs only two fifths of the
original mass when it uses at most half of the path budget. -/
theorem regularization_list_frozen_of_length_capped_half_path_budget {I : Type*} [LinearOrder I] [Fintype I]
    {half : Bool} {k n p M : ℕ} (paths : I → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (size : half = true → k ≤ 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (pathsCap : 2 * Fintype.card I ≤ p) (lengthCap : ∀ i, (paths i).length ≤ 4*M/p)
    (upper : (∑ i, (paths i).length) ≤ M) (lower : 2*M ≤ 5*(∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 90*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_of_length_capped_budget paths simple allowed size hn hp dense long
    (by omega) lengthCap upper (by decide) ?_
  let K := ∑ i, (paths i).length
  let fee : ℝ := (M:ℝ)/(4*(p:ℝ))
  have p0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have count : (Fintype.card I : ℝ) ≤ (p:ℝ)/2 := by
    have cap : (2:ℝ)*(Fintype.card I:ℝ) ≤ p := by exact_mod_cast pathsCap
    linarith
  have charge : fee*(Fintype.card I:ℝ) ≤ (M:ℝ)/8 := calc
    _ ≤ fee*((p:ℝ)/2) := mul_le_mul_of_nonneg_left count (by positivity)
    _ = _ := by
      dsimp [fee]
      field_simp [p0]
      ring
  have retained := frozen_half_path_budget_retention (M := (M:ℝ)) (K := (K:ℝ))
    (by exact_mod_cast hn.trans_le dense) (by exact_mod_cast lower) (by exact_mod_cast upper)
  change (M:ℝ)/90 ≤ (K:ℝ)-(K:ℝ)^2/(12*(M:ℝ))-(M:ℝ)/4-fee*(Fintype.card I:ℝ)
  linarith

/-- In particular, it suffices that at most seven fifteenths of the
input mass lies on rows exceeding the original upper length cap. -/
theorem regularization_list_frozen_of_small_overlong_mass {half : Bool} {k n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (size : half = true → k ≤ 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (small : let M := ∑ i, (paths i).length; 15*listMassAboveWidth paths (4*M/p) ≤ 7*M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let L := 4*M/p
  let short := univ.filter (fun i => (paths i).length ≤ L)
  let chosen (i : short) := paths i.val
  let K := ∑ i, (chosen i).length
  have cap : Fintype.card short ≤ p := by
    simpa only [Fintype.card_coe,card_univ,Fintype.card_fin] using card_le_card (subset_univ short)
  have oldMass : K+listMassAboveWidth paths L = M := by
    change (∑ i : short, (paths i.val).length)+listMassAboveWidth paths L = M
    have extract : (∑ i : short, (paths i.val).length) = ∑ i ∈ short, (paths i).length :=
      sum_attach short (fun i => (paths i).length)
    rw [extract]
    unfold short listMassAboveWidth M
    simpa only [not_le] using sum_filter_add_sum_filter_not (univ : Finset (Fin p))
      (fun i => (paths i).length ≤ L) (fun i => (paths i).length)
  have admissible : localOrderAdmissible half k chosen := by
    cases half
    · change BridgeFree (ListBefore paths) k at allowed
      change BridgeFree (ListBefore chosen) k
      intro t former
      exact ⟨fun b => (allowed former).false (b.mapPaths Subtype.val Subtype.val_injective (fun _ _ _ step => step))⟩
    · change HalfBridgeFree (ListBefore paths) k at allowed
      change HalfBridgeFree (ListBefore chosen) k
      intro t former b earlier
      exact allowed former (b.mapPaths Subtype.val Subtype.val_injective (fun _ _ _ step => step)) earlier
  exact regularization_list_frozen_of_length_capped_mass chosen (fun i => simple i.val) admissible size hn hp dense long
    cap (fun i => (mem_filter.mp i.property).2) (by omega) (by change 15*listMassAboveWidth paths L ≤ 7*M at small; omega)

/-- Clipping every row at the upper length cap suffices if it deletes at
most seven fifteenths of the original incidence mass. -/
theorem regularization_list_frozen_of_small_length_excess {half : Bool} {k n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (size : half = true → k ≤ 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (small : let M := ∑ i, (paths i).length; 15*listLengthExcess paths (4*M/p) ≤ 7*M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let L := 4*M/p
  let clipped (i : Fin p) := (paths i).take L
  let K := ∑ i, (clipped i).length
  have sub (i : Fin p) : List.Sublist (clipped i) (paths i) := List.take_sublist _ _
  have lengths : K+listLengthExcess paths L = M := by
    unfold K listLengthExcess M
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [show (clipped i).length = min L (paths i).length from List.length_take]
    omega
  have admissible : localOrderAdmissible half k clipped := by
    have steps (i : Fin p) (x y : Fin n) : ListBefore clipped i x y → ListBefore paths i x y :=
      listBefore_of_sublist (simple i) (sub i)
    cases half
    · change BridgeFree (ListBefore paths) k at allowed
      change BridgeFree (ListBefore clipped) k
      intro t former
      exact ⟨fun b => (allowed former).false (b.mapPaths id Function.injective_id steps)⟩
    · change HalfBridgeFree (ListBefore paths) k at allowed
      change HalfBridgeFree (ListBefore clipped) k
      intro t former b earlier
      exact allowed former (b.mapPaths id Function.injective_id steps) earlier
  exact regularization_list_frozen_of_length_capped_mass clipped (fun i => (sub i).nodup (simple i)) admissible size
    hn hp dense long (by simp) (fun i => by change ((paths i).take L).length ≤ L; rw [List.length_take]; exact min_le_left _ _) (by omega)
    (by change 15*listLengthExcess paths L ≤ 7*M at small; omega)

/-- At least seven twelfths of the mass on overlong rows suffices by
combining the bounded clipping loss and the pruned overlong cases. -/
theorem regularization_list_frozen_of_seven_twelfths_overlong_mass {n p : ℕ} (half : Bool)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half (if half then 4 else 6) paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (overlong : let M := ∑ i, (paths i).length; 7*M ≤ 12*listMassAboveWidth paths (4*M/p)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half (if half then 4 else 6) clean ∧
      M ≤ 2000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let T := listLengthExcess paths (4*M/p)
  by_cases short : 15*T ≤ 7*M
  · have cutoff (h : half = true) : (if half then (4:ℕ) else 6) ≤ 4 := by simp [h]
    obtain ⟨v,vCap,r,rCap,clean,simpleClean,free,retained,total,caps⟩ :=
      regularization_list_frozen_of_small_length_excess paths simple allowed cutoff hn hp dense long short
    exact ⟨v,vCap,r,rCap,clean,simpleClean,free,retained.trans (Nat.mul_le_mul_right _ (by decide)),total,caps⟩
  · exact regularization_list_frozen_of_overlong_mass_and_excess half paths simple allowed hn hp dense long overlong
      (by change 7*M ≤ 15*T; omega)

end OnlineReachabilityPreservers
