import OnlineReachabilityPreservers.LocalFrozenCleaning
import OnlineReachabilityPreservers.WidthBlockProfiles

/-! Frozen-average cleaning when the overlong rows carry most of the mass. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

/-- The incidences in the rows whose lengths exceed the given width. -/
def listMassAboveWidth {V : Type*} {p : ℕ} (paths : Fin p → List V) (width : ℕ) : ℕ :=
  ∑ i ∈ univ.filter (fun i => width < (paths i).length), (paths i).length

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
  let D := 4*M/n
  let L := 4*M/p
  let longRows := univ.filter (fun i => L < (paths i).length)
  let q := longRows.card
  let label : Fin q ≃o longRows := Fintype.orderIsoFinOfCardEq _ (Fintype.card_coe _)
  let chosen (i : Fin q) := paths (label i).val
  let S := ∑ i, (chosen i).length
  let kept := removeOppositeIntersections chosen
  let K := ∑ i, (kept i).length
  let pieces := listRegularizedPaths kept D L
  have massChosen : S = listMassAboveWidth paths L := by
    change (∑ i, (paths (label.toEquiv i).val).length) = ∑ i ∈ longRows, (paths i).length
    rw [Equiv.sum_comp label.toEquiv (fun i : longRows => (paths i.val).length)]
    exact sum_attach longRows (fun i => (paths i).length)
  have sUpper : S ≤ M := massChosen.trans_le (sum_le_sum_of_subset (subset_univ _))
  have sLower : 2*M ≤ 3*S := by rw [massChosen]; exact overlong
  have massPos : 0 < M := hn.trans_le dense
  have injective : Function.Injective (fun i : Fin q => (label i).val) := Subtype.val_injective.comp label.injective
  have isLong (i : Fin q) : L+1 ≤ (chosen i).length := Nat.succ_le_of_lt (mem_filter.mp (label i).property).2
  have many : q*(L+1) ≤ S := by
    calc
      _ = ∑ _ : Fin q, (L+1) := by rw [sum_const_nat,card_univ,Fintype.card_fin]; simp
      _ ≤ ∑ i : Fin q, (chosen i).length := sum_le_sum (s := univ) (fun i _ => isLong i)
  have chosenSimple (i : Fin q) : (chosen i).Nodup := simple (label i).val
  have chosenLegal : localOrderAdmissible half (if half then 4 else 6) chosen := by
    cases half
    · change BridgeFree (ListBefore paths) 6 at allowed
      change BridgeFree (ListBefore chosen) 6
      intro k size
      exact ⟨fun b => (allowed size).false (b.mapPaths _ injective (fun _ _ _ step => step))⟩
    · change HalfBridgeFree (ListBefore paths) 4 at allowed
      change HalfBridgeFree (ListBefore chosen) 4
      intro k size b arrival
      exact allowed size (b.mapPaths _ injective (fun _ _ _ step => step)) (label.strictMono arrival)
  have halfThree : HalfBridgeFree (ListBefore chosen) 3 := by
    cases half
    · change BridgeFree (ListBefore chosen) 6 at chosenLegal
      exact fun _ size => chosenLegal.halfFree (size.trans (by decide))
    · change HalfBridgeFree (ListBefore chosen) 4 at chosenLegal
      exact fun _ size => chosenLegal (size.trans (by decide))
  have lowerMass : S ≤ 2*K := removeOppositeIntersections_mass chosenSimple halfThree le_rfl
  have kUpper : K ≤ M := (sum_le_sum fun i _ => (removeOppositeIntersections_sublist chosen i).length_le).trans sUpper
  have keptSimple (i : Fin q) : (kept i).Nodup := (removeOppositeIntersections_sublist chosen i).nodup (chosenSimple i)
  have unique {a b : Fin q} {x y : Fin n} (ab : a ≠ b) (xa : x ∈ kept a) (xb : x ∈ kept b)
      (ya : y ∈ kept a) (yb : y ∈ kept b) : x = y :=
    removeOppositeIntersections_unique chosenSimple halfThree (by decide) ab xa xb ya yb
  have piecesLegal : localOrderAdmissible half (if half then 4 else 6) pieces := by
    cases half
    · change BridgeFree (ListBefore chosen) 6 at chosenLegal
      change BridgeFree (ListBefore pieces) 6
      have free : BridgeFree (ListBefore kept) 6 := removeOppositeIntersections_fullFree chosenSimple chosenLegal
      exact regularizedSix_bridge_free (half := false) keptSimple (fun {_ _ _ _} => unique)
        (fun _ size => free (size.trans (by decide))) free D L
    · change HalfBridgeFree (ListBefore chosen) 4 at chosenLegal
      change HalfBridgeFree (ListBefore pieces) 4
      exact listRegularizedPaths_halfFree keptSimple (fun {_ _ _ _} => unique)
        (removeOppositeIntersections_halfFree chosenSimple chosenLegal) D L
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
  have fee : l*(Fintype.card Pieces:ℝ) ≤ (S:ℝ)/16+(K:ℝ)/12 := calc
    _ ≤ l*((q+K/L : ℕ):ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr blocks) (by positivity)
    _ = l*(q:ℝ)+l*((K/L : ℕ):ℝ) := by push_cast; ring
    _ ≤ _ := by
      have combined := add_le_add (quarterAverage_mul_le hp (by decide) qMass) (quarterAverage_mul_le hp (by decide) blockMass)
      norm_num at combined
      exact combined
  obtain ⟨equalMass,lenCap,degreeCap⟩ := regularization_list_mass_caps kept keptSimple D L dPos lPos
  obtain ⟨filled,_,filledSize,rest,_,_⟩ := listRegularizedPaths_full_block_profiles kept keptSimple dPos lPos
  have vertexRoom : (univ \ filled).card ≤ n := by rw [rest,Fintype.card_fin]
  refine regularization_list_frozen_trim_vertices_quadratic pieces (listRegularizedPaths_simple kept keptSimple D L)
    piecesLegal hn hp dense long (retention := 216) (by decide) filled filledSize vertexRoom
    pathCap lenCap degreeCap (equalMass.trans_le kUpper) ?_
  change (∑ i, (pieces i).length) = K at equalMass
  rw [equalMass]
  refine (frozen_overlong_retention (M := (M:ℝ)) (S := (S:ℝ)) (K := (K:ℝ))
    (by exact_mod_cast massPos) (by exact_mod_cast sLower) (by exact_mod_cast sUpper)
    (by exact_mod_cast lowerMass) (by exact_mod_cast kUpper)).trans ?_
  exact sub_le_sub_left fee _

end OnlineReachabilityPreservers
