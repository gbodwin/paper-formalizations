import OnlineReachabilityPreservers.HalfFiveProjection
import OnlineReachabilityPreservers.WidthBlockProfiles

/-! Frozen-average cleaning when the overlong rows carry most of the mass. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

/-- The incidences in the rows whose lengths exceed the given width. -/
def listMassAboveWidth {V : Type*} {p : ℕ} (paths : Fin p → List V) (width : ℕ) : ℕ :=
  ∑ i ∈ univ.filter (fun i => width < (paths i).length), (paths i).length

/-- Count only the excess above the given row width. -/
def listLengthExcess {V : Type*} {p : ℕ} (paths : Fin p → List V) (width : ℕ) : ℕ :=
  ∑ i, ((paths i).length-width)

theorem listLengthExcess_add_count_mul {V : Type*} {p : ℕ} (paths : Fin p → List V) (width : ℕ) :
    listLengthExcess paths width+(univ.filter (fun i => width < (paths i).length)).card*width =
      listMassAboveWidth paths width := by
  let chosen := univ.filter (fun i => width < (paths i).length)
  have excess : listLengthExcess paths width = ∑ i ∈ chosen, ((paths i).length-width) := by
    unfold listLengthExcess chosen
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases long : width < (paths i).length
    · simp [long]
    · simp [long,Nat.sub_eq_zero_of_le (Nat.le_of_not_gt long)]
  have widths : (∑ _ ∈ chosen, width) = chosen.card*width := by rw [sum_const_nat]; simp
  change listLengthExcess paths width+chosen.card*width = ∑ i ∈ chosen, (paths i).length
  rw [excess,← widths,← sum_add_distrib]
  exact sum_congr rfl (fun i member => Nat.sub_add_cancel (mem_filter.mp member).2.le)

private theorem quarterAverage_mul_le {M p x y c : ℕ} (pPos : 0 < p) (cPos : 0 < c)
    (room : c*M*x ≤ p*y) : (M:ℝ)/(4*(p:ℝ))*x ≤ (y:ℝ)/(4*(c:ℝ)) := by
  have p0 : (p:ℝ) ≠ 0 := by exact_mod_cast pPos.ne'
  have c0 : (c:ℝ) ≠ 0 := by exact_mod_cast cPos.ne'
  have cast : (c:ℝ)*M*x ≤ (p:ℝ)*y := by exact_mod_cast room
  calc
    _ = ((c:ℝ)*M*x)/(4*(c:ℝ)*p) := by field_simp [p0,c0]
    _ ≤ ((p:ℝ)*y)/(4*(c:ℝ)*p) := div_le_div_of_nonneg_right cast (by positivity)
    _ = _ := by field_simp [p0,c0]

private theorem frozen_overlong_retention {M S K : ℝ} (positive : 0 < M) (overlong : 2*M ≤ 3*S)
    (upper : S ≤ M) (half : S ≤ 2*K) (kept : K ≤ M) :
    M/216 ≤ K-K^2/(12*M)-M/4-(S/16+K/12) := by
  rw [show K-K^2/(12*M)-M/4-(S/16+K/12) = (44*M*K-4*K^2-12*M^2-3*M*S)/(48*M) from by
    field_simp [positive.ne']
    ring]
  apply (le_div_iff₀ (by positivity)).mpr
  have first := mul_nonneg (show 0 ≤ K-S/2 by linarith) (show 0 ≤ 11*M-K-S/2 by linarith)
  have second := mul_nonneg (show 0 ≤ S-2*M/3 by linarith) (show 0 ≤ 19*M-S-2*M/3 by linarith)
  nlinarith

set_option maxHeartbeats 1300000 in
/-- Pruning and trimming the overlong subfamily uses any width split
that preserves admissibility on simple paths with unique intersections. -/
private theorem regularization_list_frozen_from_overlong_budget_of_split {n p k retention : ℕ} {half : Bool}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (positive : 0 < retention) (cutoff : 3 ≤ k)
    (split : ∀ {q : ℕ} (rows : Fin q → List (Fin n)), (∀ i, (rows i).Nodup) →
      localOrderAdmissible half k rows →
      (∀ {a b x y}, a ≠ b → x ∈ rows a → x ∈ rows b → y ∈ rows a → y ∈ rows b → x = y) →
      ∀ D L, localOrderAdmissible half k (listRegularizedPaths rows D L))
    (enough : let M := ∑ i, (paths i).length
      let S := listMassAboveWidth paths (4*M/p)
      let T := listLengthExcess paths (4*M/p)
      ∀ K : ℕ, S ≤ 2*K → K ≤ M → (M:ℝ)/retention ≤
        (K:ℝ)-(K:ℝ)^2/(12*(M:ℝ))-(M:ℝ)/4-(min ((S:ℝ)/16) (((S:ℝ)-(T:ℝ))/12)+(K:ℝ)/12)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let longRows := univ.filter (fun i => L < (paths i).length)
  let q := longRows.card
  let label : Fin q ≃o longRows := Fintype.orderIsoFinOfCardEq _ (Fintype.card_coe _)
  let chosen (i : Fin q) := paths (label i).val
  let S := ∑ i, (chosen i).length
  let T := listLengthExcess paths L
  let kept := removeOppositeIntersections chosen
  let K := ∑ i, (kept i).length
  let pieces := listRegularizedPaths kept D L
  have massChosen : S = listMassAboveWidth paths L := by
    change (∑ i, (paths (label.toEquiv i).val).length) = ∑ i ∈ longRows, (paths i).length
    rw [Equiv.sum_comp label.toEquiv (fun i : longRows => (paths i.val).length)]
    exact sum_attach longRows (fun i => (paths i).length)
  have sUpper : S ≤ M := massChosen.trans_le (sum_le_sum_of_subset (subset_univ _))
  have massPos : 0 < M := hn.trans_le dense
  have injective : Function.Injective (fun i : Fin q => (label i).val) := Subtype.val_injective.comp label.injective
  have isLong (i : Fin q) : L+1 ≤ (chosen i).length := Nat.succ_le_of_lt (mem_filter.mp (label i).property).2
  have many : q*(L+1) ≤ S := by
    calc
      _ = ∑ _ : Fin q, (L+1) := by rw [sum_const_nat,card_univ,Fintype.card_fin]; simp
      _ ≤ ∑ i : Fin q, (chosen i).length := sum_le_sum (s := univ) (fun i _ => isLong i)
  have chosenSimple (i : Fin q) : (chosen i).Nodup := simple (label i).val
  have chosenLegal : localOrderAdmissible half k chosen := by
    cases half
    · change BridgeFree (ListBefore paths) k at allowed
      change BridgeFree (ListBefore chosen) k
      intro k size
      exact ⟨fun b => (allowed size).false (b.mapPaths _ injective (fun _ _ _ step => step))⟩
    · change HalfBridgeFree (ListBefore paths) k at allowed
      change HalfBridgeFree (ListBefore chosen) k
      intro k size b arrival
      exact allowed size (b.mapPaths _ injective (fun _ _ _ step => step)) (label.strictMono arrival)
  have halfThree : HalfBridgeFree (ListBefore chosen) 3 := by
    cases half
    · change BridgeFree (ListBefore chosen) k at chosenLegal
      exact fun _ size => chosenLegal.halfFree (size.trans cutoff)
    · change HalfBridgeFree (ListBefore chosen) k at chosenLegal
      exact fun _ size => chosenLegal (size.trans cutoff)
  have lowerMass : S ≤ 2*K := removeOppositeIntersections_mass chosenSimple halfThree le_rfl
  have kUpper : K ≤ M := (sum_le_sum fun i _ => (removeOppositeIntersections_sublist chosen i).length_le).trans sUpper
  have keptSimple (i : Fin q) : (kept i).Nodup := (removeOppositeIntersections_sublist chosen i).nodup (chosenSimple i)
  have unique {a b : Fin q} {x y : Fin n} (ab : a ≠ b) (xa : x ∈ kept a) (xb : x ∈ kept b)
      (ya : y ∈ kept a) (yb : y ∈ kept b) : x = y :=
    removeOppositeIntersections_unique chosenSimple halfThree (by decide) ab xa xb ya yb
  have keptLegal : localOrderAdmissible half k kept := by
    cases half
    · exact removeOppositeIntersections_fullFree chosenSimple chosenLegal
    · exact removeOppositeIntersections_halfFree chosenSimple chosenLegal
  have piecesLegal : localOrderAdmissible half k pieces :=
    split kept keptSimple keptLegal (fun {_ _ _ _} => unique) D L
  obtain ⟨dPos,_,_⟩ := four_average_width hn dense
  obtain ⟨lPos,divL,_⟩ := four_average_width hp long
  let Pieces := ListBlockIndex (splitListVertices kept D) L
  have blocks : Fintype.card Pieces ≤ q+K/L := by
    simpa only [Fintype.card_fin] using (regularization_list_counts kept keptSimple dPos lPos).2
  have floor : 4*M < p*(L+1) := Nat.lt_mul_div_succ _ hp
  have qMass : 4*M*q ≤ p*S := calc
    _ ≤ (p*(L+1))*q := Nat.mul_le_mul_right _ floor.le
    _ = p*(q*(L+1)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ many
  have qCap : 4*q ≤ p := by
    apply Nat.le_of_mul_le_mul_right _ massPos
    rw [show (4*q)*M = 4*M*q by ring]
    exact qMass.trans (Nat.mul_le_mul_left _ sUpper)
  have more : 3*(K/L) ≤ p := (Nat.mul_le_mul_left 3 (Nat.div_le_div_right kUpper)).trans divL
  have pathCap : Fintype.card Pieces ≤ p := by omega
  have room : 3*M ≤ p*L := by rw [Nat.mul_succ] at floor; omega
  have blockMass : 3*M*(K/L) ≤ p*K := calc
    _ ≤ (p*L)*(K/L) := Nat.mul_le_mul_right _ room
    _ = p*((K/L)*L) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
  let l : ℝ := (M:ℝ)/(4*(p:ℝ))
  have qRoom : 3*M*q ≤ p*(q*L) := (Nat.mul_le_mul_right q room).trans_eq (by ring)
  have tails : T+q*L = S := (listLengthExcess_add_count_mul paths L).trans massChosen.symm
  have tailsReal : (T:ℝ)+(q:ℝ)*(L:ℝ) = S := by exact_mod_cast tails
  have scaled : l*(q:ℝ) ≤ min ((S:ℝ)/16) (((S:ℝ)-(T:ℝ))/12) := by
    apply le_min
    · have prior := quarterAverage_mul_le hp (by decide) qMass
      norm_num at prior
      exact prior
    · have prior := quarterAverage_mul_le hp (by decide) qRoom
      push_cast at prior
      norm_num at prior
      linarith
  have fee : l*(Fintype.card Pieces:ℝ) ≤ min ((S:ℝ)/16) (((S:ℝ)-(T:ℝ))/12)+(K:ℝ)/12 := calc
    _ ≤ l*((q+K/L : ℕ):ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr blocks) (by positivity)
    _ = l*(q:ℝ)+l*((K/L : ℕ):ℝ) := by push_cast; ring
    _ ≤ _ := by
      have combined := add_le_add scaled (quarterAverage_mul_le hp (by decide) blockMass)
      norm_num at combined
      exact combined
  obtain ⟨equalMass,lenCap,degreeCap⟩ := regularization_list_mass_caps kept keptSimple D L dPos lPos
  obtain ⟨filled,_,filledSize,rest,_,_⟩ := listRegularizedPaths_full_block_profiles kept keptSimple dPos lPos
  have vertexRoom : (univ \ filled).card ≤ n := by rw [rest,Fintype.card_fin]
  refine regularization_list_frozen_trim_vertices_quadratic pieces (listRegularizedPaths_simple kept keptSimple D L)
    piecesLegal hn hp dense long positive filled filledSize vertexRoom
    pathCap lenCap degreeCap (equalMass.trans_le kUpper) ?_
  change (∑ i, (pieces i).length) = K at equalMass
  rw [equalMass]
  have massBudget := enough K (by rw [← massChosen]; exact lowerMass) kUpper
  change (M:ℝ)/retention ≤ (K:ℝ)-(K:ℝ)^2/(12*(M:ℝ))-(M:ℝ)/4-
    (min ((listMassAboveWidth paths L:ℝ)/16) (((listMassAboveWidth paths L:ℝ)-(T:ℝ))/12)+(K:ℝ)/12) at massBudget
  rw [← massChosen] at massBudget
  refine massBudget.trans ?_
  exact sub_le_sub_left fee _

/-- Prune opposite intersections in the overlong rows and clean the resulting bounded family. -/
theorem regularization_list_frozen_from_overlong_budget {n p retention : ℕ} (half : Bool)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half (if half then 4 else 6) paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (positive : 0 < retention)
    (enough : let M := ∑ i, (paths i).length
      let S := listMassAboveWidth paths (4*M/p)
      let T := listLengthExcess paths (4*M/p)
      ∀ K : ℕ, S ≤ 2*K → K ≤ M → (M:ℝ)/retention ≤
        (K:ℝ)-(K:ℝ)^2/(12*(M:ℝ))-(M:ℝ)/4-(min ((S:ℝ)/16) (((S:ℝ)-(T:ℝ))/12)+(K:ℝ)/12)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half (if half then 4 else 6) clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  refine regularization_list_frozen_from_overlong_budget_of_split paths simple allowed hn hp dense long
    positive (by cases half <;> decide) ?_ enough
  intro q rows nodup legal unique D L
  cases half
  · change BridgeFree (ListBefore rows) 6 at legal
    exact regularizedSix_bridge_free (half := false) nodup (fun {_ _ _ _} => unique)
      (fun _ size => legal (size.trans (by decide))) legal D L
  · exact listRegularizedPaths_halfFree nodup (fun {_ _ _ _} => unique) legal D L

/-- If the rows above the original upper length cap carry at least two
thirds of the mass, pruning this subfamily and trimming vertices gives
all four frozen caps. This holds through half cutoff four or full cutoff six. -/
theorem regularization_list_frozen_of_overlong_mass {n p : ℕ} (half : Bool)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half (if half then 4 else 6) paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (overlong : let M := ∑ i, (paths i).length; 2*M ≤ 3*listMassAboveWidth paths (4*M/p)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half (if half then 4 else 6) clean ∧
      M ≤ 216*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let S := listMassAboveWidth paths (4*M/p)
  let T := listLengthExcess paths (4*M/p)
  have upper : S ≤ M := sum_le_sum_of_subset (subset_univ _)
  refine regularization_list_frozen_from_overlong_budget half paths simple allowed hn hp dense long
    (retention := 216) (by decide) (fun K lower kept => ?_)
  have mass := frozen_overlong_retention (M := (M:ℝ)) (S := (S:ℝ)) (K := (K:ℝ))
    (by exact_mod_cast hn.trans_le dense) (by exact_mod_cast overlong) (by exact_mod_cast upper)
    (by exact_mod_cast lower) (by exact_mod_cast kept)
  refine mass.trans ?_
  exact sub_le_sub_left (add_le_add (min_le_left ((S:ℝ)/16) (((S:ℝ)-(T:ℝ))/12)) le_rfl) _

private theorem frozen_overlong_retention_with_excess {M S T K : ℝ} (positive : 0 < M)
    (overlong : 7*M ≤ 12*S) (excess : 7*M ≤ 15*T) (upper : S ≤ M) (half : S ≤ 2*K) (kept : K ≤ M) :
    M/2000 ≤ K-K^2/(12*M)-M/4-((S-T)/12+K/12) := by
  rw [show K-K^2/(12*M)-M/4-((S-T)/12+K/12) = (44*M*K-4*K^2-12*M^2-4*M*S+4*M*T)/(48*M) from by
    field_simp [positive.ne']
    ring]
  apply (le_div_iff₀ (by positivity)).mpr
  have first := mul_nonneg (show 0 ≤ K-S/2 by linarith) (show 0 ≤ 11*M-K-S/2 by linarith)
  have second := mul_nonneg (show 0 ≤ S-7*M/12 by linarith) (show 0 ≤ 18*M-S-7*M/12 by linarith)
  have third := mul_nonneg positive.le (show 0 ≤ T-7*M/15 by linarith)
  nlinarith

/-- When clipping loses many incidences, the count of overlong rows gives
a sharper peeling charge for their pruned pieces. -/
theorem regularization_list_frozen_of_overlong_mass_and_excess {n p : ℕ} (half : Bool)
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half (if half then 4 else 6) paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (overlong : let M := ∑ i, (paths i).length; 7*M ≤ 12*listMassAboveWidth paths (4*M/p))
    (excess : let M := ∑ i, (paths i).length; 7*M ≤ 15*listLengthExcess paths (4*M/p)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half (if half then 4 else 6) clean ∧
      M ≤ 2000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let S := listMassAboveWidth paths (4*M/p)
  let T := listLengthExcess paths (4*M/p)
  have upper : S ≤ M := sum_le_sum_of_subset (subset_univ _)
  refine regularization_list_frozen_from_overlong_budget half paths simple allowed hn hp dense long
    (retention := 2000) (by decide) (fun K lower kept => ?_)
  have mass := frozen_overlong_retention_with_excess (M := (M:ℝ)) (S := (S:ℝ)) (T := (T:ℝ)) (K := (K:ℝ))
    (by exact_mod_cast hn.trans_le dense) (by exact_mod_cast overlong) (by exact_mod_cast excess)
    (by exact_mod_cast upper) (by exact_mod_cast lower) (by exact_mod_cast kept)
  refine mass.trans ?_
  exact sub_le_sub_left (add_le_add (min_le_right ((S:ℝ)/16) (((S:ℝ)-(T:ℝ))/12)) le_rfl) _

/-- At half cutoff five, overlong rows carrying two thirds of the mass
suffice for both budgets and all four original-average caps. -/
theorem regularization_list_frozen_half_five_of_overlong_mass {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : HalfBridgeFree (ListBefore paths) 5)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (overlong : let M := ∑ i, (paths i).length; 2*M ≤ 3*listMassAboveWidth paths (4*M/p)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) 5 ∧
      M ≤ 216*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let S := listMassAboveWidth paths (4*M/p)
  let T := listLengthExcess paths (4*M/p)
  have upper : S ≤ M := sum_le_sum_of_subset (subset_univ _)
  refine regularization_list_frozen_from_overlong_budget_of_split (half := true) (k := 5)
    paths simple allowed hn hp dense long
    (retention := 216) (by decide) (by decide)
    (fun rows nodup free unique D L => listRegularizedPaths_halfFree_five_of_unique nodup free
      (fun {_ _ _ _} => unique) D L) (fun K lower kept => ?_)
  have mass := frozen_overlong_retention (M := (M:ℝ)) (S := (S:ℝ)) (K := (K:ℝ))
    (by exact_mod_cast hn.trans_le dense) (by exact_mod_cast overlong) (by exact_mod_cast upper)
    (by exact_mod_cast lower) (by exact_mod_cast kept)
  refine mass.trans ?_
  exact sub_le_sub_left (add_le_add (min_le_left ((S:ℝ)/16) (((S:ℝ)-(T:ℝ))/12)) le_rfl) _

/-- Large length excess lowers the mass needed on overlong rows at half cutoff five. -/
theorem regularization_list_frozen_half_five_of_overlong_mass_and_excess {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : HalfBridgeFree (ListBefore paths) 5)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (overlong : let M := ∑ i, (paths i).length; 7*M ≤ 12*listMassAboveWidth paths (4*M/p))
    (excess : let M := ∑ i, (paths i).length; 7*M ≤ 15*listLengthExcess paths (4*M/p)) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) 5 ∧
      M ≤ 2000*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let S := listMassAboveWidth paths (4*M/p)
  let T := listLengthExcess paths (4*M/p)
  have upper : S ≤ M := sum_le_sum_of_subset (subset_univ _)
  refine regularization_list_frozen_from_overlong_budget_of_split (half := true) (k := 5)
    paths simple allowed hn hp dense long
    (retention := 2000) (by decide) (by decide)
    (fun rows nodup free unique D L => listRegularizedPaths_halfFree_five_of_unique nodup free
      (fun {_ _ _ _} => unique) D L) (fun K lower kept => ?_)
  have mass := frozen_overlong_retention_with_excess (M := (M:ℝ)) (S := (S:ℝ)) (T := (T:ℝ)) (K := (K:ℝ))
    (by exact_mod_cast hn.trans_le dense) (by exact_mod_cast overlong) (by exact_mod_cast excess)
    (by exact_mod_cast upper) (by exact_mod_cast lower) (by exact_mod_cast kept)
  refine mass.trans ?_
  exact sub_le_sub_left (add_le_add (min_le_right ((S:ℝ)/16) (((S:ℝ)-(T:ℝ))/12)) le_rfl) _

end OnlineReachabilityPreservers
