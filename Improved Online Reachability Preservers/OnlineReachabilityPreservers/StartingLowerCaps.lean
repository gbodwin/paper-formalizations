import OnlineReachabilityPreservers.FrozenQuadraticTrimming
import OnlineReachabilityPreservers.LiteralFrozenFullLowMass

/-! Half-bridge cleaning with prescribed lower fractions of the starting averages. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

private theorem lower_le_quarter {M x s : ℝ} (mass : 0 ≤ M)
    (bound : x ≤ 1/4) (positive : 0 < s) : x*M/s ≤ M/(4*s) := calc
  _ ≤ (1/4)*M/s := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right bound mass) positive.le
  _ = _ := by field_simp

/-- A lower bound on the incidence mass after cropping both original
supports, with starting mass `M` and pruned mass `K`. -/
noncomputable def halfPrunedCropScore (M K : ℕ) : ℝ :=
  K-4*(K:ℝ)^2/(31*(M:ℝ))

private theorem half_pruned_crop_mass {M K R lostV lostI : ℕ} (positive : 0 < M)
    (trimmed : K ≤ R+lostV+lostI) (loss : 31*M*(lostV+lostI) ≤ 4*K^2) :
    halfPrunedCropScore M K ≤ (R:ℝ) := by
  have paid : 31*M*K ≤ 31*M*R+4*K^2 := calc
    _ ≤ (31*M)*(R+(lostV+lostI)) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ _ := by rw [Nat.mul_add]; exact Nat.add_le_add_left loss _
  have mixed : 31*(M:ℝ)*K ≤ 31*(M:ℝ)*R+4*(K:ℝ)^2 := by exact_mod_cast paid
  have realPos : (0:ℝ) < M := by exact_mod_cast positive
  have denominator : 0 < 31*(M:ℝ) := by positivity
  unfold halfPrunedCropScore
  apply (mul_le_mul_iff_right₀ denominator).mp
  rw [mul_sub,mul_comm (31*(M:ℝ)) (4*(K:ℝ)^2/(31*(M:ℝ))),div_mul_cancel₀ _ denominator.ne']
  linarith only [mixed]

private theorem half_pruned_crop_score_ge {M K : ℕ} {u : ℝ} (positive : 0 < M)
    (lo : u ≤ (K:ℝ)) (upper : K ≤ M) :
    u-4*u^2/(31*(M:ℝ)) ≤ halfPrunedCropScore M K := by
  have realPos : (0:ℝ) < M := by exact_mod_cast positive
  have hi : (K:ℝ) ≤ M := by exact_mod_cast upper
  have monotone := mul_nonneg (sub_nonneg.mpr lo)
    (show 0 ≤ 31*(M:ℝ)-4*((K:ℝ)+u) by linarith only [lo,hi,realPos])
  have denominator : 0 < 31*(M:ℝ) := by positivity
  unfold halfPrunedCropScore
  apply (mul_le_mul_iff_right₀ denominator).mp
  calc
    _ = (31*(M:ℝ))*u-4*u^2 := by rw [mul_sub,mul_comm _ (4*u^2/(31*(M:ℝ))),
        div_mul_cancel₀ _ denominator.ne']
    _ ≤ (31*(M:ℝ))*K-4*(K:ℝ)^2 := by nlinarith only [monotone]
    _ = _ := by rw [mul_sub,mul_comm _ (4*(K:ℝ)^2/(31*(M:ℝ))),
      div_mul_cancel₀ _ denominator.ne']

/-- With half the mass after opposite pruning, the width-crop score is
at least twenty-nine sixty-seconds of the input. -/
theorem half_pruned_crop_score_of_half_mass {M K : ℕ} (positive : 0 < M)
    (pruned : M ≤ 2*K) (upper : K ≤ M) : (29/62)*(M:ℝ) ≤ halfPrunedCropScore M K := by
  have half : (M:ℝ) ≤ 2*(K:ℝ) := by exact_mod_cast pruned
  have realPos : (0:ℝ) < M := by exact_mod_cast positive
  apply le_trans _ (half_pruned_crop_score_ge (u := (M:ℝ)/2) positive (by linarith only [half]) upper)
  apply (mul_le_mul_iff_right₀ (show 0 < 31*(M:ℝ) by positivity)).mp
  rw [mul_sub,mul_comm _ (4*((M:ℝ)/2)^2/(31*(M:ℝ))),
    div_mul_cancel₀ _ (by positivity : (31*(M:ℝ)) ≠ 0)]
  nlinarith

/-- The degree and length coefficients in this range and a retention
factor of 930 fit the score after any half-three-safe opposite pruning. -/
theorem half_pruned_crop_score_of_lower_fractions {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (cutoff : 3 ≤ k)
    (positive : 0 < ∑ i, (paths i).length) {a b : ℝ} (scale : a+b ≤ 7/15) :
    let M := ∑ i, (paths i).length
    let K := ∑ i, (removeOppositeIntersections paths i).length
    (a+b+1/930)*(M:ℝ) ≤ halfPrunedCropScore M K := by
  let M := ∑ i, (paths i).length
  let K := ∑ i, (removeOppositeIntersections paths i).length
  have upper : K ≤ M := sum_le_sum (fun i _ => (removeOppositeIntersections_sublist paths i).length_le)
  have half := removeOppositeIntersections_mass simple free cutoff
  apply le_trans _ (half_pruned_crop_score_of_half_mass positive half upper)
  exact mul_le_mul_of_nonneg_right (by linarith only [scale]) (Nat.cast_nonneg _)

/-- When thirteen twenty-fourths of the incidence mass survives pruning,
the crop score pays for both exact one-quarter caps and retention M/288. -/
theorem half_pruned_crop_score_of_large_mass {M K : ℕ} (positive : 0 < M)
    (pruned : 13*M ≤ 24*K) (upper : K ≤ M) :
    ((1/2:ℝ)+1/288)*(M:ℝ) ≤ halfPrunedCropScore M K := by
  have lower : 13*(M:ℝ) ≤ 24*(K:ℝ) := by exact_mod_cast pruned
  have realPos : (0:ℝ) < M := by exact_mod_cast positive
  let u := (13/24)*(M:ℝ)
  have fit : u ≤ (K:ℝ) := by dsimp [u]; linarith only [lower]
  apply le_trans _ (half_pruned_crop_score_ge positive fit upper)
  apply (mul_le_mul_iff_right₀ (show 0 < 31*(M:ℝ) by positivity)).mp
  rw [mul_sub,mul_comm _ (4*u^2/(31*(M:ℝ))),
    div_mul_cancel₀ _ (by positivity : (31*(M:ℝ)) ≠ 0)]
  dsimp only [u]
  nlinarith only [sq_nonneg (M:ℝ)]

/-- After pruning opposite intersections, use safe width splits and crop
both supports. The crop score pays for the lower caps and the requested
incidence mass. -/
theorem regularization_list_half_of_starting_lower_caps_and_mass {n p k : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (cutoff : 3 ≤ k)
    (splitSafe : let M := ∑ i, (paths i).length
      HalfBridgeFree (Before (listRegularizedPaths (removeOppositeIntersections paths) (4*M/n) (4*M/p))) k)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    {a b : ℝ} (a0 : 0 ≤ a) (b0 : 0 ≤ b) (aMax : a ≤ 1/4) (bMax : b ≤ 1/4)
    {target : ℝ} (targetFit : target ≤ (∑ i, (paths i).length : ℕ)/(8:ℝ))
    (score : let M := ∑ i, (paths i).length
      let K := ∑ i, (removeOppositeIntersections paths i).length
      (a+b)*(M:ℝ)+target ≤ halfPrunedCropScore M K) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) k ∧
      target ≤ (∑ i, (rows i).length : ℕ) ∧ (∑ i, (rows i).length) ≤ M ∧
      (∀ x, a*(M:ℝ)/n ≤ (occurrences (fun i => (rows i).toFinset) x).card ∧
        ((occurrences (fun i => (rows i).toFinset) x).card:ℝ) ≤ 4*(M:ℝ)/n) ∧
      (∀ i, b*(M:ℝ)/p ≤ (rows i).length ∧ ((rows i).length:ℝ) ≤ 4*(M:ℝ)/p) := by
  let M := ∑ i, (paths i).length
  let d := a*(M:ℝ)/n
  let l := b*(M:ℝ)/p
  have mPos : 0 < M := hn.trans_le dense
  have realPos : (0:ℝ) < M := by exact_mod_cast mPos
  have rn : (0:ℝ) < n := by exact_mod_cast hn
  have rp : (0:ℝ) < p := by exact_mod_cast hp
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retain,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free (by omega) hn hp dense long low
    have castRetain : (M:ℝ) ≤ 8*((∑ i, (rows i).length : ℕ):ℝ) := by exact_mod_cast retain
    exact ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree.halfFree,
      targetFit.trans (by linarith only [castRetain]),upper,
      fun x => ⟨(lower_le_quarter realPos.le aMax rn).trans (caps.1 x).1,(caps.1 x).2⟩,
      fun i => ⟨(lower_le_quarter realPos.le bMax rp).trans (caps.2 i).1,(caps.2 i).2⟩⟩
  let D := 4*M/n
  let L := 4*M/p
  let kept := removeOppositeIntersections paths
  let K := ∑ i, (kept i).length
  let pieces := listRegularizedPaths kept D L
  let Z := fun i => (pieces i).toFinset
  have keptSimple (i : Fin p) : (kept i).Nodup :=
    (removeOppositeIntersections_sublist paths i).nodup (simple i)
  have upper : K ≤ M := sum_le_sum (fun i _ => (removeOppositeIntersections_sublist paths i).length_le)
  have capacity {q : ℕ} (qPos : 0 < q) (high : 8*q ≤ M) : 31*M ≤ 8*((4*M/q)*q) := by
    have floor := four_average_width_product (M := M) qPos
    omega
  have vCap : 31*M ≤ 8*(D*n) := capacity hn (by have bound := le_max_left n p; omega)
  have iCap : 31*M ≤ 8*(L*p) := capacity hp (by have bound := le_max_right n p; omega)
  obtain ⟨dPos,_,dUpper⟩ := four_average_width hn dense
  obtain ⟨lPos,_,lUpper⟩ := four_average_width hp long
  have pieceSimple (i) : (pieces i).Nodup := listRegularizedPaths_simple kept keptSimple D L i
  have pieceFree : HalfBridgeFree (Before pieces) k := splitSafe
  obtain ⟨mass,lengthCap,degreeCap⟩ := regularization_list_mass_caps kept keptSimple D L dPos lPos
  obtain ⟨Fv,Fi,vFull,vRest,iFull,iRest⟩ := listRegularizedPaths_full_block_profiles kept keptSimple dPos lPos
  have series : (∑ i, (Z i).card) = K := calc
    _ = ∑ i, (pieces i).length := sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (pieceSimple i))
    _ = _ := mass
  have vRestFit : (univ \ Fv).card ≤ n := by simpa only [Fintype.card_fin] using vRest.le
  have iRestFit : (univ \ Fi).card ≤ p := by simpa only [Fintype.card_fin] using iRest.le
  have vRoom : (∑ i, (Z i).card) ≤ D*n := by rw [series]; omega
  have iRoom : (∑ i, (Z i).card) ≤ L*p := by rw [series]; omega
  obtain ⟨A,B,lostV,lostI,vFit,iFit,trim,vLoss,iLoss⟩ := trim_width_supports Z Fv Fi
    dPos lPos (fun v hv => (vFull v hv).ge) vRestFit
    (fun i hi => (iFull i hi).ge.trans_eq (List.toFinset_card_of_nodup (pieceSimple i)).symm)
    iRestFit vRoom iRoom
  rw [series] at trim vLoss iLoss
  have paid {q w loss : ℕ} (room : 31*M ≤ 8*(w*q)) (charge : 4*(w*q)*loss ≤ K^2) :
      31*M*loss ≤ 2*K^2 := calc
    _ ≤ (8*(w*q))*loss := Nat.mul_le_mul_right _ room
    _ = 2*(4*(w*q)*loss) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ charge
  have combined : 31*M*(lostV+lostI) ≤ 4*K^2 := by
    rw [Nat.mul_add]
    exact (Nat.add_le_add (paid vCap vLoss) (paid iCap iLoss)).trans_eq (by ring)
  have rectangleMass_eq (A' : Finset (ListVertexBlockIndex kept D))
      (B' : Finset (ListBlockIndex (splitListVertices kept D) L)) :
      (∑ i : B', (rectanglePaths Z A' B' i).card) = ∑ i ∈ B', ((Z i) ∩ A').card := by
    rw [← B'.sum_coe_sort (fun i => ((Z i) ∩ A').card)]
    apply sum_congr rfl
    intro i _
    calc
      _ = (restrictListPaths pieces A' B' i).toFinset.card :=
        congrArg Finset.card (restrictListPaths_toFinset pieces A' B' i).symm
      _ = (restrictListPaths pieces A' B' i).length :=
        List.toFinset_card_of_nodup (restrictListPath_nodup (pieceSimple i.val) A')
      _ = _ := restrictListPath_length (pieceSimple i.val) A'
  let R := ∑ i ∈ B, ((Z i) ∩ A).card
  have trimFit : K ≤ R+lostV+lostI := trim.trans_eq (Nat.add_assoc _ _ _).symm
  have retained : halfPrunedCropScore M K ≤ ((∑ i : B, (rectanglePaths Z A B i).card : ℕ):ℝ) := by
    rw [rectangleMass_eq A B]
    exact half_pruned_crop_mass mPos trimFit combined
  have d0 : 0 ≤ d := div_nonneg (mul_nonneg a0 realPos.le) rn.le
  have l0 : 0 ≤ l := div_nonneg (mul_nonneg b0 realPos.le) rp.le
  obtain ⟨C,cSub,E,eSub,afterPeel,minD,minL⟩ := rectanglePaths_prune Z A B d0 l0
  have lowerFee (x : ℝ) (x0 : 0 ≤ x) {s count : ℕ} (positive : 0 < s) (bound : count ≤ s) :
      (x*(M:ℝ)/s)*(count:ℝ) ≤ x*(M:ℝ) := calc
    _ ≤ (x*(M:ℝ)/s)*(s:ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr bound)
      (div_nonneg (mul_nonneg x0 realPos.le) (Nat.cast_nonneg _))
    _ = _ := div_mul_cancel₀ _ ((Nat.cast_pos.mpr positive : (0:ℝ)<s).ne')
  have vertexFee : d*(A.card:ℝ) ≤ a*(M:ℝ) := lowerFee a a0 hn vFit
  have pathFee : l*(B.card:ℝ) ≤ b*(M:ℝ) := lowerFee b b0 hp iFit
  have sumFee : d*(A.card:ℝ)+l*(B.card:ℝ) ≤ (a+b)*(M:ℝ) := calc
    _ ≤ a*(M:ℝ)+b*(M:ℝ) := add_le_add vertexFee pathFee
    _ = (a+b)*(M:ℝ) := by ring
  have enough : target ≤ ((∑ i : E, (rectanglePaths Z C E i).card : ℕ):ℝ) := by
    change (a+b)*(M:ℝ)+target ≤ halfPrunedCropScore M K at score
    linarith only [retained,afterPeel,sumFee,score]
  let witness := restrictListPaths pieces C E
  have witnessSimple (i : E) : (witness i).Nodup := restrictListPath_nodup (pieceSimple i.val) C
  have witnessFree := restrictListPaths_halfFree pieceSimple pieceFree C E
  have same (i : E) : (witness i).toFinset = rectanglePaths Z C E i :=
    restrictListPaths_toFinset pieces C E i
  have rowLength (i : E) : (witness i).length = (rectanglePaths Z C E i).card := by
    rw [← same i,List.toFinset_card_of_nodup (witnessSimple i)]
  have witnessMass : (∑ i, (witness i).length) = ∑ i : E, (rectanglePaths Z C E i).card :=
    sum_congr rfl (fun i _ => rowLength i)
  let clean := relabelListPathsFin witness
  obtain ⟨cleanSimple,cleanFree,cleanMass,cleanDeg,cleanLen⟩ :=
    relabelListPathsFin_spec witness witnessSimple (half := true) (k := k) witnessFree
  have cleanRetain : target ≤ (∑ i, (clean i).length : ℕ) := by rwa [cleanMass,witnessMass]
  have cleanUpper : (∑ i, (clean i).length) ≤ M := by
    rw [cleanMass,witnessMass]
    exact (rectanglePaths_mass_le Z C E).trans (series.trans_le upper)
  refine ⟨Fintype.card C,?_,Fintype.card E,?_,clean,cleanSimple,cleanFree,cleanRetain,cleanUpper,?_,?_⟩
  · simpa only [Fintype.card_coe] using (card_le_card cSub).trans vFit
  · simpa only [Fintype.card_coe] using (card_le_card eSub).trans iFit
  · intro v
    rw [cleanDeg]
    let w : C := (Fintype.orderIsoFinOfCardEq C rfl) v
    change d ≤ ((occurrences (fun i => (witness i).toFinset) w).card:ℝ) ∧
      ((occurrences (fun i => (witness i).toFinset) w).card:ℝ) ≤ 4*(M:ℝ)/n
    have sameMarks : (fun i => (witness i).toFinset) = rectanglePaths Z C E := funext same
    rw [sameMarks]
    refine ⟨minD w,?_⟩
    exact (Nat.cast_le.mpr ((rectanglePaths_degree_le Z C E w).trans (degreeCap _))).trans dUpper
  · intro i
    rw [cleanLen,rowLength]
    refine ⟨minL _,?_⟩
    have cardBound {i : E} : (rectanglePaths Z C E i).card ≤ L := calc
      _ = (witness i).length := (rowLength i).symm
      _ = ((pieces i.val).toFinset ∩ C).card := restrictListPath_length (pieceSimple i.val) C
      _ ≤ (pieces i.val).length := (card_le_card inter_subset_left).trans (List.toFinset_card_le _)
      _ ≤ L := lengthCap _
    exact (Nat.cast_le.mpr cardBound).trans lUpper

/-- The same score gives multiplicative retention at the requested factor. -/
theorem regularization_list_half_of_starting_lower_caps {n p k r : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (cutoff : 3 ≤ k)
    (splitSafe : let M := ∑ i, (paths i).length
      HalfBridgeFree (Before (listRegularizedPaths (removeOppositeIntersections paths) (4*M/n) (4*M/p))) k)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    {a b : ℝ} (a0 : 0 ≤ a) (b0 : 0 ≤ b) (aMax : a ≤ 1/4) (bMax : b ≤ 1/4)
    (retention : 16 ≤ r)
    (score : let M := ∑ i, (paths i).length
      let K := ∑ i, (removeOppositeIntersections paths i).length
      (a+b+1/(r:ℝ))*(M:ℝ) ≤ halfPrunedCropScore M K) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) k ∧
      M ≤ r*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧
      (∀ x, a*(M:ℝ)/n ≤ (occurrences (fun i => (rows i).toFinset) x).card ∧
        ((occurrences (fun i => (rows i).toFinset) x).card:ℝ) ≤ 4*(M:ℝ)/n) ∧
      (∀ i, b*(M:ℝ)/p ≤ (rows i).length ∧ ((rows i).length:ℝ) ≤ 4*(M:ℝ)/p) := by
  let M := ∑ i, (paths i).length
  let K := ∑ i, (removeOppositeIntersections paths i).length
  have rLarge : (8:ℝ) ≤ r := by exact_mod_cast (show 8 ≤ r by omega)
  have rPos : (0:ℝ) < r := (by norm_num : (0:ℝ) < 8).trans_le rLarge
  have targetFit : (M:ℝ)/r ≤ (M:ℝ)/8 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) rLarge
  have reserve : (a+b)*(M:ℝ)+(M:ℝ)/r ≤ halfPrunedCropScore M K := by
    have prior : (a+b+1/(r:ℝ))*(M:ℝ) ≤ halfPrunedCropScore M K := score
    convert prior using 1
    ring
  obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,keep,upper,degree,length⟩ :=
    regularization_list_half_of_starting_lower_caps_and_mass paths simple free cutoff splitSafe hn hp dense long
      a0 b0 aMax bMax targetFit reserve
  have retain : M ≤ r*(∑ i, (rows i).length) := by
    have real := (div_le_iff₀ rPos).mp keep
    rw [mul_comm] at real
    exact_mod_cast real
  exact ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retain,upper,degree,length⟩

/-- The same score suffices for distinct nonempty input and output rows. -/
theorem regularization_literal_half_of_starting_lower_caps {n p k r : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) k) (cutoff : 3 ≤ k)
    (splitSafe : let M := ∑ i, (paths i).length
      HalfBridgeFree (Before (listRegularizedPaths (removeOppositeIntersections paths) (4*M/n) (4*M/p))) k)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length)
    {a b : ℝ} (a0 : 0 ≤ a) (b0 : 0 ≤ b) (aMax : a ≤ 1/4) (bMax : b ≤ 1/4)
    (retention : 16 ≤ r)
    (score : let M := ∑ i, (paths i).length
      let K := ∑ i, (removeOppositeIntersections paths i).length
      (a+b+1/(r:ℝ))*(M:ℝ) ≤ halfPrunedCropScore M K) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) k ∧
      M ≤ r*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧
      (∀ x, a*(M:ℝ)/n ≤ (occurrences (fun i => (rows i).toFinset) x).card ∧
        ((occurrences (fun i => (rows i).toFinset) x).card:ℝ) ≤ 4*(M:ℝ)/n) ∧
      (∀ i, b*(M:ℝ)/p ≤ (rows i).length ∧ ((rows i).length:ℝ) ≤ 4*(M:ℝ)/p) := by
  let M := ∑ i, (paths i).length
  let K := ∑ i, (removeOppositeIntersections paths i).length
  have mPos := hn.trans_le dense
  have realPos : (0:ℝ) < M := by exact_mod_cast mPos
  have rp : (0:ℝ) < p := by exact_mod_cast hp
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,rowsFull,retain,upper,caps⟩ :=
      regularization_literal_half_full_all_of_low_mass paths distinct valid free (by omega) hn hp dense low
    have rn : (0:ℝ) < n := by exact_mod_cast hn
    exact ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,(rowsFull k).halfFree,
      retain.trans (Nat.mul_le_mul_right _ (by omega)),upper,
      fun x => ⟨(lower_le_quarter realPos.le aMax rn).trans (caps.1 x).1,(caps.1 x).2⟩,
      fun i => ⟨(lower_le_quarter realPos.le bMax rp).trans (caps.2 i).1,(caps.2 i).2⟩⟩
  let c := max b (1/8)
  have c0 : 0 ≤ c := b0.trans (le_max_left _ _)
  have cMax : c ≤ 1/4 := max_le_iff.mpr ⟨bMax,by norm_num⟩
  have newScore : (a+c+1/(r:ℝ))*(M:ℝ) ≤ halfPrunedCropScore M K := by
    rcases le_total b (1/8) with small | large
    · dsimp [c]
      rw [max_eq_right small]
      have ret : (16:ℝ) ≤ r := by exact_mod_cast retention
      have fraction : (1:ℝ)/r ≤ 1/16 := one_div_le_one_div_of_le (by norm_num) ret
      have half : M ≤ 2*K := removeOppositeIntersections_mass (fun i => (valid i).2) free cutoff
      have upper : K ≤ M := sum_le_sum (fun i _ => (removeOppositeIntersections_sublist paths i).length_le)
      exact (mul_le_mul_of_nonneg_right (show a+1/8+1/(r:ℝ) ≤ 29/62 by
        linarith only [aMax,fraction]) realPos.le).trans (half_pruned_crop_score_of_half_mass mPos half upper)
    · simpa only [c,max_eq_left large] using score
  have long : p ≤ M := calc
    _ = ∑ _ : Fin p, (1:ℕ) := by simp
    _ ≤ _ := sum_le_sum (fun i _ => List.length_pos_iff.mpr (valid i).1)
  obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retain,upper,degree,length⟩ :=
    regularization_list_half_of_starting_lower_caps paths (fun i => (valid i).2)
      free cutoff splitSafe hn hp dense long a0 c0 aMax cMax retention newScore
  have highMean : 8*(p:ℝ) < M := by
    exact_mod_cast (show 8*p < M by have h := le_max_right n p; omega)
  have minimum : (1:ℝ) < c*(M:ℝ)/p := by
    apply (lt_div_iff₀ rp).mpr
    have floor : (1/8)*(M:ℝ) ≤ c*(M:ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) realPos.le
    linarith only [floor,highMean,rp]
  have atLeastTwo (i : Fin q) : 2 ≤ (rows i).length := by
    have real := minimum.trans_le (length i).1
    exact_mod_cast (show (1:ℝ) < (rows i).length from real)
  have oneToOne := nontrivial_halfFree_paths_injective rowsSimple atLeastTwo (by omega : 2 ≤ k) rowsFree
  refine ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨?_,rowsSimple i⟩,rowsFree,retain,upper,degree,?_⟩
  · intro empty
    simpa [empty] using atLeastTwo i
  · intro i
    have lower : b*(M:ℝ)/p ≤ c*(M:ℝ)/p :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) realPos.le) rp.le
    exact ⟨lower.trans (length i).1,(length i).2⟩

end OnlineReachabilityPreservers
