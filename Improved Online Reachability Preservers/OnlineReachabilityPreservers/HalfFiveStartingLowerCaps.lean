import OnlineReachabilityPreservers.FrozenQuadraticTrimming
import OnlineReachabilityPreservers.HalfFiveProjection
import OnlineReachabilityPreservers.LiteralFrozenFullLowMass

/-! Half-five cleaning with prescribed lower fractions of the starting averages. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped Sigma.Lex
local notation "Before" => SourceAudit.BeforeIn

private theorem lower_le_quarter {M x s : ℝ} (mass : 0 ≤ M)
    (bound : x ≤ 1/4) (positive : 0 < s) : x*M/s ≤ M/(4*s) := calc
  _ ≤ (1/4)*M/s := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right bound mass) positive.le
  _ = _ := by field_simp

private theorem half_five_trim_mass {M K R lostV lostI : ℕ} (positive : 0 < M)
    (pruned : M ≤ 2*K) (upper : K ≤ M) (trimmed : K ≤ R+lostV+lostI)
    (loss : 31*M*(lostV+lostI) ≤ 4*K^2) :
    (29/62)*(M:ℝ) ≤ (R:ℝ) := by
  have paid : 31*M*K ≤ 31*M*R+4*K^2 := calc
    _ ≤ (31*M)*(R+(lostV+lostI)) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ _ := by rw [Nat.mul_add]; exact Nat.add_le_add_left loss _
  have mixed : 31*(M:ℝ)*K ≤ 31*(M:ℝ)*R+4*(K:ℝ)^2 := by exact_mod_cast paid
  have realPos : (0:ℝ) < M := by exact_mod_cast positive
  have lo : (M:ℝ)/2 ≤ K := by
    have half : (M:ℝ) ≤ 2*(K:ℝ) := by exact_mod_cast pruned
    linarith only [half]
  have hi : (K:ℝ) ≤ M := by exact_mod_cast upper
  have monotone := mul_nonneg (sub_nonneg.mpr lo)
    (show 0 ≤ 31*(M:ℝ)-4*((K:ℝ)+(M:ℝ)/2) by linarith only [hi,realPos])
  apply (mul_le_mul_iff_right₀ realPos).mp
  nlinarith only [mixed,monotone]

/-- At half cutoff five two lower caps at the starting averages can have
coefficients with sum at most seven fifteenths. Both factor-four upper
caps and both original budgets still hold. -/
theorem regularization_list_half_five_of_starting_lower_caps {n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    {a b : ℝ} (a0 : 0 ≤ a) (b0 : 0 ≤ b) (aMax : a ≤ 1/4) (bMax : b ≤ 1/4)
    (scale : a+b ≤ 7/15) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      (∀ i, (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 930*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧
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
      regularization_list_frozen_low_mass paths simple free (by decide) hn hp dense long low
    exact ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree.halfFree,by omega,upper,
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
  have keptFree := removeOppositeIntersections_halfFree simple free
  have halfMass : M ≤ 2*K := removeOppositeIntersections_mass simple free (by decide)
  have upper : K ≤ M := sum_le_sum (fun i _ => (removeOppositeIntersections_sublist paths i).length_le)
  have capacity {q : ℕ} (qPos : 0 < q) (high : 8*q ≤ M) : 31*M ≤ 8*((4*M/q)*q) := by
    have floor := four_average_width_product (M := M) qPos
    omega
  have vCap : 31*M ≤ 8*(D*n) := capacity hn (by have bound := le_max_left n p; omega)
  have iCap : 31*M ≤ 8*(L*p) := capacity hp (by have bound := le_max_right n p; omega)
  obtain ⟨dPos,_,dUpper⟩ := four_average_width hn dense
  obtain ⟨lPos,_,lUpper⟩ := four_average_width hp long
  have pieceSimple (i) : (pieces i).Nodup := listRegularizedPaths_simple kept keptSimple D L i
  have pieceFree : HalfBridgeFree (Before pieces) 5 :=
    listRegularizedPaths_halfFree_five_of_unique_intersections keptSimple keptFree
      (fun {_ _ _ _} diff xa xb ya yb => removeOppositeIntersections_unique simple free (by decide) diff xa xb ya yb) D L
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
  have retained : (29/62)*(M:ℝ) ≤ ((∑ i : B, (rectanglePaths Z A B i).card : ℕ):ℝ) := by
    rw [rectangleMass_eq A B]
    exact half_five_trim_mass mPos halfMass upper trimFit combined
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
  have sumFee : d*(A.card:ℝ)+l*(B.card:ℝ) ≤ (7/15)*(M:ℝ) := calc
    _ ≤ a*(M:ℝ)+b*(M:ℝ) := add_le_add vertexFee pathFee
    _ = (a+b)*(M:ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right scale realPos.le
  have enough : (M:ℝ)/930 ≤ ((∑ i : E, (rectanglePaths Z C E i).card : ℕ):ℝ) := by
    linarith only [retained,afterPeel,sumFee,realPos]
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
    relabelListPathsFin_spec witness witnessSimple (half := true) (k := 5) witnessFree
  have cleanRetain : M ≤ 930*(∑ i, (clean i).length) := by
    rw [cleanMass,witnessMass]
    have real := (div_le_iff₀ (by norm_num : (0:ℝ)<930)).mp enough
    rw [mul_comm] at real
    exact_mod_cast real
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

/-- The same starting-average bounds hold for distinct nonempty input
and output rows, even when the requested lower length coefficient is zero. -/
theorem regularization_literal_half_five_of_starting_lower_caps {n p : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths)
    (valid : ∀ i, paths i ≠ [] ∧ (paths i).Nodup)
    (free : HalfBridgeFree (Before paths) 5) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length)
    {a b : ℝ} (a0 : 0 ≤ a) (b0 : 0 ≤ b) (aMax : a ≤ 1/4) (bMax : b ≤ 1/4)
    (scale : a+b ≤ 7/15) :
    let M := ∑ i, (paths i).length
    ∃ v ≤ n, ∃ q ≤ p, ∃ rows : Fin q → List (Fin v),
      Function.Injective rows ∧ (∀ i, rows i ≠ [] ∧ (rows i).Nodup) ∧ HalfBridgeFree (Before rows) 5 ∧
      M ≤ 930*(∑ i, (rows i).length) ∧ (∑ i, (rows i).length) ≤ M ∧
      (∀ x, a*(M:ℝ)/n ≤ (occurrences (fun i => (rows i).toFinset) x).card ∧
        ((occurrences (fun i => (rows i).toFinset) x).card:ℝ) ≤ 4*(M:ℝ)/n) ∧
      (∀ i, b*(M:ℝ)/p ≤ (rows i).length ∧ ((rows i).length:ℝ) ≤ 4*(M:ℝ)/p) := by
  let M := ∑ i, (paths i).length
  have realPos : (0:ℝ) < M := by exact_mod_cast hn.trans_le dense
  have rp : (0:ℝ) < p := by exact_mod_cast hp
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,rowsFull,retain,upper,caps⟩ :=
      regularization_literal_half_full_all_of_low_mass paths distinct valid free (by decide) hn hp dense low
    have rn : (0:ℝ) < n := by exact_mod_cast hn
    exact ⟨v,vFit,q,qFit,rows,oneToOne,rowsValid,(rowsFull 5).halfFree,by omega,upper,
      fun x => ⟨(lower_le_quarter realPos.le aMax rn).trans (caps.1 x).1,(caps.1 x).2⟩,
      fun i => ⟨(lower_le_quarter realPos.le bMax rp).trans (caps.2 i).1,(caps.2 i).2⟩⟩
  let c := max b (1/8)
  have c0 : 0 ≤ c := b0.trans (le_max_left _ _)
  have cMax : c ≤ 1/4 := max_le_iff.mpr ⟨bMax,by norm_num⟩
  have newScale : a+c ≤ 7/15 := by
    rcases le_total b (1/8) with small | large
    · dsimp [c]
      rw [max_eq_right small]
      linarith only [aMax]
    · simpa only [c,max_eq_left large] using scale
  have long : p ≤ M := calc
    _ = ∑ _ : Fin p, (1:ℕ) := by simp
    _ ≤ _ := sum_le_sum (fun i _ => List.length_pos_iff.mpr (valid i).1)
  obtain ⟨v,vFit,q,qFit,rows,rowsSimple,rowsFree,retain,upper,degree,length⟩ :=
    regularization_list_half_five_of_starting_lower_caps paths (fun i => (valid i).2)
      free hn hp dense long a0 c0 aMax cMax newScale
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
  have oneToOne := nontrivial_halfFree_paths_injective rowsSimple atLeastTwo (by decide : 2 ≤ 5) rowsFree
  refine ⟨v,vFit,q,qFit,rows,oneToOne,fun i => ⟨?_,rowsSimple i⟩,rowsFree,retain,upper,degree,?_⟩
  · intro empty
    simpa [empty] using atLeastTwo i
  · intro i
    have lower : b*(M:ℝ)/p ≤ c*(M:ℝ)/p :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) realPos.le) rp.le
    exact ⟨lower.trans (length i).1,(length i).2⟩

end OnlineReachabilityPreservers
