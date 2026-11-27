import OnlineReachabilityPreservers.FrozenFullNearCutoff
import OnlineReachabilityPreservers.FrozenDegreeClipping

/-! Keep the support saving when cleaning after cutoff restriction. -/

namespace OnlineReachabilityPreservers

open Finset
local notation "Before" => SourceAudit.BeforeIn

private theorem width_support_scale {M K q base count num den : ℕ} {share u : ℝ}
    (positive : 0 < q) (dense : 8*q ≤ M) (mass : (K:ℝ) ≤ u*M)
    (countBound : count ≤ base+K/(4*M/q)) (baseCap : (base:ℝ) ≤ share*q)
    (scale : (num:ℝ)*(share+(8/31)*u) = den) : num*count ≤ den*q := by
  let width := 4*M/q
  have floor := four_average_width_product (M := M) positive
  change 4*M < width*q+q at floor
  have cover : 31*M ≤ 8*(width*q) := by omega
  have expanded : (31*M)*(K/width) ≤ 8*K*q := calc
    _ ≤ (8*(width*q))*(K/width) := Nat.mul_le_mul_right _ cover
    _ = 8*((K/width)*width)*q := by ring
    _ ≤ 8*K*q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _))
  have total : (31*(M:ℝ))*((K/width:ℕ):ℝ) ≤ (31*(M:ℝ))*((8/31)*u*q) := calc
    _ ≤ 8*(K:ℝ)*q := by exact_mod_cast expanded
    _ ≤ 8*(u*M)*q := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left mass (by norm_num)) (by positivity)
    _ = _ := by ring
  have massPos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have widthBound := le_of_mul_le_mul_left total (show 0 < 31*(M:ℝ) by positivity)
  have countReal : (count:ℝ) ≤ (base:ℝ)+((K/width:ℕ):ℝ) := by exact_mod_cast countBound
  have bound : (count:ℝ) ≤ (share+(8/31)*u)*q := by linarith only [countReal,baseCap,widthBound]
  have final : (num:ℝ)*count ≤ (den:ℝ)*q := calc
    _ ≤ (num:ℝ)*((share+(8/31)*u)*q) := mul_le_mul_of_nonneg_left bound (by positivity)
    _ = ((num:ℝ)*(share+(8/31)*u))*q := by ring
    _ = _ := by rw [scale]
  exact_mod_cast final

private theorem trimmed_support_ratio_keeps_mass {M K : ℕ} (lower : 7*M ≤ 12*K) (upper : K ≤ M) :
    ((527*M+160*K)*(620*M+160*K))*258*M ≤ 512*((620*M)*(620*M))*K := by
  have first : 0 ≤ 12*(K:ℤ)-7*(M:ℤ) := sub_nonneg.mpr (by exact_mod_cast lower)
  have comparator : 7*160^2*K ≤ 12*527*620*M := by omega
  have second : 0 ≤ 12*527*620*(M:ℤ)-7*160^2*(K:ℤ) := sub_nonneg.mpr (by exact_mod_cast comparator)
  have difference : 7444*8560*(K:ℤ)*M - 84*((527*M+160*K)*(620*M+160*K)) =
      (12*K-7*M)*(12*527*620*M-7*160^2*K) := by ring
  have compare : 84*((527*M+160*K)*(620*M+160*K)) ≤ 7444*8560*K*M := by
    exact_mod_cast (sub_nonneg.mp (difference.symm ▸ mul_nonneg first second))
  refine Nat.le_of_mul_le_mul_left (c := 84) ?_ (by decide)
  calc
    _ = (258*M)*(84*((527*M+160*K)*(620*M+160*K))) := by ring
    _ ≤ (258*M)*(7444*8560*K*M) := Nat.mul_le_mul_left _ compare
    _ = (258*7444*8560)*(M*M*K) := by ring
    _ ≤ (84*512*620*620)*(M*M*K) := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring

/-- The increasing rows occupy at most seventeen twentieths of one
original support. The saving in the width trim lets seven twelfths of
the mass pay the peeling cost at the original averages. -/
private theorem frozen_full_after_trimmed_increasing_rows {n p n₀ p₀ M cutoff : ℕ}
    (rows : Fin p₀ → List (Fin n₀)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) cutoff) (rank : Fin n₀ → Fin n₀)
    (ordered : ∀ i, ((rows i).map rank).Pairwise (· < ·))
    (hn : 0 < n) (hp : 0 < p) (wideV : 8*n ≤ M) (wideP : 8*p ≤ M)
    (fitsV : n₀ ≤ n) (fitsP : p₀ ≤ p) (smallSide : 20*n₀ ≤ 17*n ∨ 20*p₀ ≤ 17*p)
    (mass : 7*M ≤ 12*(∑ i, (rows i).length)) (upper : (∑ i, (rows i).length) ≤ M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ 256*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let K := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices rows D
  let pieces := listRegularizedPaths rows D L
  let W := ListVertexBlockIndex rows D
  let J := ListBlockIndex copies L
  let Conclusion := ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
    (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
    M ≤ 256*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean
  have dense : n ≤ M := by omega
  have long : p ≤ M := by omega
  obtain ⟨dPos,_,_⟩ := four_average_width hn dense
  obtain ⟨lPos,_,_⟩ := four_average_width hp long
  obtain ⟨vCount,pCount⟩ := regularization_list_counts rows simple (D := D) (L := L) dPos lPos
  simp only [Fintype.card_fin] at vCount pCount
  change Fintype.card W ≤ n₀+K/D at vCount
  change Fintype.card J ≤ p₀+K/L at pCount
  obtain ⟨massPieces,length,degree⟩ := regularization_list_mass_caps rows simple D L dPos lPos
  have piecesFree : BridgeFree (Before pieces) cutoff :=
    listRegularizedPaths_fullFree_of_noShortPrecedenceCycle rows simple free
      (noShortPrecedenceCycle_of_increasing_order rows rank ordered (cutoff-2)) D L
  have finish {vNum vDen pNum pDen : ℕ}
      (vPos : 0 < vDen) (pPos : 0 < pDen) (vRatio : vNum ≤ vDen) (pRatio : pNum ≤ pDen)
      (verts : vNum*Fintype.card W ≤ vDen*n) (families : pNum*Fintype.card J ≤ pDen*p)
      (enough : (vDen*pDen)*258*M ≤ 512*(vNum*pNum)*K) : Conclusion := by
    apply regularization_list_frozen_after_caps_with_ratios_of_mass (half := false)
      (retention := 256) pieces (listRegularizedPaths_simple rows simple D L) piecesFree
      hn hp dense long vPos pPos vRatio pRatio verts families length degree (massPieces.trans_le upper)
    rw [massPieces]
    convert enough using 1
    ring
  let num := 620*M
  let shortDen := 527*M+160*K
  let longDen := 620*M+160*K
  have massPos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have massBound : (K:ℝ) ≤ ((K:ℝ)/M)*M := (div_mul_cancel₀ _ massPos.ne').ge
  have shortScale : (num:ℝ)*((17/20)+(8/31)*((K:ℝ)/M)) = shortDen := by
    push_cast [num,shortDen]
    field_simp
    ring
  have longScale : (num:ℝ)*(1+(8/31)*((K:ℝ)/M)) = longDen := by
    push_cast [num,longDen]
    field_simp
    ring
  have baseV : (n₀:ℝ) ≤ 1*(n:ℝ) := by
    simpa only [one_mul] using (show (n₀:ℝ) ≤ n by exact_mod_cast fitsV)
  have baseP : (p₀:ℝ) ≤ 1*(p:ℝ) := by
    simpa only [one_mul] using (show (p₀:ℝ) ≤ p by exact_mod_cast fitsP)
  change 7*M ≤ 12*K at mass
  have enough := trimmed_support_ratio_keeps_mass mass upper
  have shortRatio : num ≤ shortDen := by dsimp [num,shortDen]; omega
  have longRatio : num ≤ longDen := Nat.le_add_right _ _
  have shortPos : 0 < shortDen := by dsimp [shortDen]; omega
  have longPos : 0 < longDen := by dsimp [longDen]; omega
  change Conclusion
  rcases smallSide with shortV | shortP
  · have cap : (20:ℝ)*n₀ ≤ 17*(n:ℝ) := by exact_mod_cast shortV
    exact finish shortPos longPos shortRatio longRatio
      (width_support_scale hn wideV massBound vCount (by linarith) shortScale)
      (width_support_scale hp wideP massBound pCount baseP longScale) enough
  · have cap : (20:ℝ)*p₀ ≤ 17*(p:ℝ) := by exact_mod_cast shortP
    apply finish longPos shortPos longRatio shortRatio
      (width_support_scale hn wideV massBound vCount baseV longScale)
      (width_support_scale hp wideP massBound pCount (by linarith) shortScale)
    rw [Nat.mul_comm longDen shortDen]
    exact enough

private theorem column_rectangle_mass {I V : Type*} [LinearOrder I] [Fintype I] [DecidableEq V]
    (marks : I → Finset V) (A : Finset V) :
    (∑ i, (marks i ∩ A).card) = ∑ v ∈ A, (occurrences marks v).card := by
  have row (i : I) : (marks i ∩ A).card = ∑ v ∈ A, if v ∈ marks i then 1 else 0 := by
    rw [← sum_filter]
    rw [show A.filter (fun v => v ∈ marks i) = marks i ∩ A by ext v; simp [and_comm]]
    simp
  have col (v : V) : (occurrences marks v).card = ∑ i, if v ∈ marks i then 1 else 0 := by
    rw [← sum_filter]
    simp [occurrences]
  simp only [row,col,Finset.sum_comm (s := (univ : Finset I))]

private theorem choose_full_support {n p cutoff size a b sNum sDen : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (fraction : a ≤ b) (keep : a*min n p ≤ b*size)
    (bound : size ≤ cutoff) (saving : sNum*size ≤ sDen*min n p) :
    ∃ A : Finset (Fin n), A.card ≤ n ∧ ∃ B : Finset (Fin p), B.card ≤ p ∧
      (sNum*A.card ≤ sDen*n ∨ sNum*B.card ≤ sDen*p) ∧ min A.card B.card ≤ cutoff ∧
      a*(∑ i, (paths i).length) ≤ b*(∑ i ∈ B, ((paths i).toFinset ∩ A).card) := by
  by_cases vertices : n ≤ p
  · let degree (v : Fin n) := (occurrences (fun i => (paths i).toFinset) v).card
    have degreeSum : (∑ v, degree v) = ∑ i, (paths i).length := by
      unfold degree
      rw [sum_occurrences]
      exact sum_congr rfl fun i _ => List.toFinset_card_of_nodup (simple i)
    have fits : a*(univ : Finset (Fin n)).card ≤ b*size := by
      simpa only [min_eq_left vertices,card_univ,Fintype.card_fin] using keep
    obtain ⟨A,_,card,retained⟩ := trim_weights_ratio univ degree fraction fits
    have reduced : sNum*A.card ≤ sDen*n := (Nat.mul_le_mul_left _ card).trans
      (by simpa only [min_eq_left vertices] using saving)
    have vertexFits : A.card ≤ n := by simpa only [Fintype.card_fin] using card_le_univ A
    refine ⟨A,vertexFits,univ,by simp,Or.inl reduced,(min_le_left _ _).trans (card.trans bound),?_⟩
    rw [← degreeSum,column_rectangle_mass]
    exact retained
  · have fits : a*(univ : Finset (Fin p)).card ≤ b*size := by
      simpa only [min_eq_right (le_of_not_ge vertices),card_univ,Fintype.card_fin] using keep
    obtain ⟨B,_,card,retained⟩ := trim_weights_ratio univ (fun i => (paths i).length) fraction fits
    have reduced : sNum*B.card ≤ sDen*p := (Nat.mul_le_mul_left _ card).trans
      (by simpa only [min_eq_right (le_of_not_ge vertices)] using saving)
    have pathFits : B.card ≤ p := by simpa only [Fintype.card_fin] using card_le_univ B
    refine ⟨univ,by simp,B,pathFits,Or.inr reduced,(min_le_right _ _).trans (card.trans bound),?_⟩
    have masses : (∑ i ∈ B, ((paths i).toFinset ∩ (univ : Finset (Fin n))).card) = ∑ i ∈ B, (paths i).length := by
      exact sum_congr rfl fun i _ => by rw [inter_univ,List.toFinset_card_of_nodup (simple i)]
    rw [masses]
    exact retained

private theorem choose_near_full_support {n p cutoff : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (large : 157 ≤ min n p) (near : 5*min n p ≤ 6*cutoff) :
    ∃ A : Finset (Fin n), A.card ≤ n ∧ ∃ B : Finset (Fin p), B.card ≤ p ∧
      (20*A.card ≤ 17*n ∨ 20*B.card ≤ 17*p) ∧ min A.card B.card ≤ cutoff ∧
      5*(∑ i, (paths i).length) ≤ 6*(∑ i ∈ B, ((paths i).toFinset ∩ A).card) := by
  let q := min n p
  let size := (5*q+5)/6
  have keep : 5*q ≤ 6*size := by unfold size; omega
  have bound : size ≤ cutoff := by unfold size; change 5*q ≤ 6*cutoff at near; omega
  have saving : 20*size ≤ 17*q := by unfold size; change 157 ≤ q at large; omega
  exact choose_full_support paths simple (by decide) keep bound saving

private theorem full_increasing_restriction {n p cutoff : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) cutoff)
    (A : Finset (Fin n)) (B : Finset (Fin p)) (smallCut : min A.card B.card ≤ cutoff) :
    let R := ∑ i ∈ B, ((paths i).toFinset ∩ A).card
    ∃ (rank : Fin (Fintype.card A) → Fin (Fintype.card A))
      (kept : Fin (Fintype.card B) → List (Fin (Fintype.card A))),
      (∀ i, (kept i).Nodup) ∧ BridgeFree (Before kept) cutoff ∧
      (∀ i, ((kept i).map rank).Pairwise (· < ·)) ∧
      R ≤ (∑ i, (kept i).length)+2*A.card ∧ (∑ i, (kept i).length) ≤ R := by
  let restricted := restrictListPaths paths A B
  have restrictedSimple (i : B) : (restricted i).Nodup := restrictListPath_nodup (simple i.val) A
  have restrictedFree : BridgeFree (Before restricted) cutoff := restrictListPaths_fullFree simple free A B
  obtain ⟨relabelSimple,relabelFree,relabelMass,_,_⟩ :=
    relabelListPathsFin_spec (half := false) restricted restrictedSimple restrictedFree
  let picked := relabelListPathsFin restricted
  have originalMass : (∑ i, (picked i).length) = ∑ i ∈ B, ((paths i).toFinset ∩ A).card := by
    rw [relabelMass,← Finset.sum_attach B (fun i => ((paths i).toFinset ∩ A).card)]
    exact sum_congr rfl fun i _ => restrictListPath_length (simple i.val) A
  have all : ∀ d, IsEmpty (Bridge (Before picked) d) :=
    bridgeFree_all_of_cutoff_ge_min relabelFree (by simpa only [Fintype.card_coe] using smallCut)
  obtain ⟨rank,kept,sub,ordered,_,_,removed⟩ := fullBridgeFree_increasing_subsequences_two_of_components picked
    relabelSimple (precedenceComponent_fullFree relabelSimple all)
  have keptFree : BridgeFree (Before kept) cutoff := by
    intro d _
    exact ⟨fun bridge => (all d).false (bridge.mapPaths id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (relabelSimple i) (sub i) step))⟩
  change (∑ i, (picked i).length) ≤ (∑ i, (kept i).length)+2*Fintype.card A at removed
  have loss : (∑ i ∈ B, ((paths i).toFinset ∩ A).card) ≤ (∑ i, (kept i).length)+2*A.card := calc
    _ = ∑ i, (picked i).length := originalMass.symm
    _ ≤ (∑ i, (kept i).length)+2*Fintype.card A := removed
    _ = _ := congrArg (fun c => (∑ i, (kept i).length)+2*c) (Fintype.card_coe A)
  exact ⟨rank,kept,fun i => (sub i).nodup (relabelSimple i),keptFree,ordered,loss,
    (sum_le_sum fun i _ => (sub i).length_le).trans_eq originalMass⟩

private theorem selected_rectangle_mass_le_original {n p : ℕ} (paths : Fin p → List (Fin n))
    (A : Finset (Fin n)) (B : Finset (Fin p)) :
    (∑ i ∈ B, ((paths i).toFinset ∩ A).card) ≤ ∑ i, (paths i).length :=
  (sum_le_sum fun i (_ : i ∈ B) => (card_le_card inter_subset_left).trans (List.toFinset_card_le _)).trans
    (sum_le_sum_of_subset (subset_univ B))

/-- At a full cutoff of at least five sixths of the smaller budget,
keep both original budgets and all four original-average caps. Restrict
one support before the common-order deletion and keep that saving when
trimming the width copies. -/
theorem regularization_list_frozen_full_of_five_sixths_cutoff {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) cutoff) (two : 2 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (near : 5*min n p ≤ 6*cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ 256*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,mass,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free.halfFree two hn hp dense long low
    exact ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,by omega,upper,caps⟩
  by_cases small : n ≤ 157 ∨ p ≤ 156
  · obtain ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,mass,upper,caps⟩ :=
      regularization_list_frozen_of_small_budget_all_cutoffs (half := false) paths simple free two hn hp dense long small
    exact ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,by omega,upper,caps⟩
  have wideV : 8*n ≤ M := (Nat.mul_le_mul_left _ (le_max_left n p)).trans (Nat.lt_of_not_ge low).le
  have wideP : 8*p ≤ M := (Nat.mul_le_mul_left _ (le_max_right n p)).trans (Nat.lt_of_not_ge low).le
  have large : 157 ≤ min n p := by
    push Not at small
    exact le_min (by omega) (by omega)
  obtain ⟨A,va,B,pa,smaller,smallCut,retained⟩ := choose_near_full_support paths simple large near
  obtain ⟨rank,kept,keptSimple,keptFree,ordered,removed,keptUpper⟩ :=
    full_increasing_restriction paths simple free A B smallCut
  have mass : 7*M ≤ 12*(∑ i, (kept i).length) := by omega
  have upper : (∑ i, (kept i).length) ≤ M := keptUpper.trans (selected_rectangle_mass_le_original paths A B)
  exact frozen_full_after_trimmed_increasing_rows kept keptSimple keptFree rank ordered hn hp wideV wideP
    (by simpa only [Fintype.card_coe] using va) (by simpa only [Fintype.card_coe] using pa)
    (by simpa only [Fintype.card_coe] using smaller) mass upper

/-- Feasible literal inputs have the same five-sixths-cutoff cleaning
with distinct nonempty output rows. -/
theorem regularization_list_frozen_full_distinct_of_five_sixths_cutoff {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ [])
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) cutoff) (two : 2 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (near : 5*min n p ≤ 6*cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) cutoff ∧ M ≤ 256*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := false) (k := cutoff) (retention := 256)
    paths distinct nonempty simple free two hn hp dense (by decide)
    (fun long => regularization_list_frozen_full_of_five_sixths_cutoff paths simple free two hn hp dense long near)

/-- The five-sixths-cutoff frozen cleaning bound at the unrestricted indexed maximum. -/
theorem localOrderExtremal_frozen_full_of_five_sixths_cutoff (n p cutoff : ℕ)
    (hn : 0 < n) (hp : 0 < p) (two : 2 ≤ cutoff) (near : 5*min n p ≤ 6*cutoff) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → BridgeFree (Before other) cutoff →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
        M ≤ 256*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,simple,free,maximal,dense,long⟩ := localOrderExtremal_isDense n p cutoff false hn hp
  exact ⟨paths,simple,free,maximal,
    regularization_list_frozen_full_of_five_sixths_cutoff paths simple free two hn hp dense long near⟩

/-- The five-sixths-cutoff frozen bound at the feasible literal maximum. -/
theorem localOrderDistinctExtremal_frozen_full_of_five_sixths_cutoff {n p cutoff : ℕ}
    (hn : 0 < n) (hp : 0 < p) (two : 2 ≤ cutoff) (near : 5*min n p ≤ 6*cutoff)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → BridgeFree (Before other) cutoff →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
        BridgeFree (Before clean) cutoff ∧ M ≤ 256*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,distinct,rows,free,maximal,dense,_⟩ := localOrderDistinctExtremal_isDense false hp feasible
  exact ⟨paths,distinct,rows,free,maximal,regularization_list_frozen_full_distinct_of_five_sixths_cutoff paths
    distinct (fun i => (rows i).1) (fun i => (rows i).2) free two hn hp dense near⟩

private theorem smaller_support_peeling_charge {M K q base count : ℕ}
    (hq : 0 < q) (wide : 8*q ≤ M) (small : 25*base ≤ 19*q) (few : 12*K ≤ 7*M)
    (expanded : count ≤ base+K/(4*M/q)) :
    count ≤ q ∧ (M:ℝ)/(4*(q:ℝ))*count ≤ (19/100)*(M:ℝ)+(2/31)*(K:ℝ) := by
  have mPos : 0 < M := by omega
  have mReal : (0:ℝ) < M := by exact_mod_cast mPos
  have qReal : (0:ℝ) < q := by exact_mod_cast hq
  have mass : (K:ℝ) ≤ ((K:ℝ)/M)*M := (div_mul_cancel₀ _ mReal.ne').ge
  have short : (25:ℝ)*base ≤ 19*(q:ℝ) := by exact_mod_cast small
  have ratio : ((775*M : ℕ):ℝ)*((19/25)+(8/31)*((K:ℝ)/M)) = ((589*M+200*K : ℕ):ℝ) := by
    push_cast
    field_simp
    ring
  have countBound := width_support_scale hq wide mass expanded (by linarith only [short]) ratio
  have den : 589*M+200*K ≤ 775*M := by omega
  have fits : count ≤ q := Nat.le_of_mul_le_mul_left
    (countBound.trans (Nat.mul_le_mul_right _ den)) (Nat.mul_pos (by decide) mPos)
  have scaled : (775:ℝ)*M*count ≤ (589*(M:ℝ)+200*(K:ℝ))*q := by exact_mod_cast countBound
  have unscaled : (M:ℝ)*count ≤ ((19/25)*(M:ℝ)+(8/31)*(K:ℝ))*q := by nlinarith only [scaled]
  refine ⟨fits,?_⟩
  calc
    _ = ((M:ℝ)*count)/(4*(q:ℝ)) := by ring
    _ ≤ (((19/25)*(M:ℝ)+(8/31)*(K:ℝ))*q)/(4*(q:ℝ)) :=
      div_le_div_of_nonneg_right unscaled (by positivity)
    _ = _ := by
      field_simp [qReal.ne']
      ring

private theorem one_width_trim_loss {M K q loss : ℕ} (hq : 0 < q) (wide : 8*q ≤ M)
    (few : 12*K ≤ 7*M) (charge : 4*((4*M/q)*q)*loss ≤ K^2) : 186*loss ≤ 7*K := by
  let width := 4*M/q
  have floor := four_average_width_product (M := M) hq
  change 4*M < width*q+q at floor
  have board : 31*M ≤ 8*(width*q) := by omega
  have cost : (31*M)*loss ≤ 2*K^2 := calc
    _ ≤ (8*(width*q))*loss := Nat.mul_le_mul_right _ board
    _ = 2*(4*(width*q)*loss) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ charge
  apply Nat.le_of_mul_le_mul_left (c := M) _ (by omega)
  calc
    _ = 6*((31*M)*loss) := by ring
    _ ≤ 6*(2*K^2) := Nat.mul_le_mul_left _ cost
    _ = (12*K)*K := by ring
    _ ≤ (7*M)*K := Nat.mul_le_mul_right _ few
    _ = _ := by ring

private theorem quarter_support_charge {M q count : ℕ} (hq : 0 < q) (fits : count ≤ q) :
    (M:ℝ)/(4*(q:ℝ))*count ≤ (M:ℝ)/4 := calc
  _ ≤ (M:ℝ)/(4*(q:ℝ))*(q:ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast fits) (by positivity)
  _ = _ := by
    have positive : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp [positive]

private theorem frozen_full_from_capped_rectangle {I V : Type*}
    [LinearOrder I] [Fintype I] [LinearOrder V] [Fintype V] {n p M cutoff retention : ℕ}
    (pieces : I → List V) (simple : ∀ i, (pieces i).Nodup) (free : BridgeFree (Before pieces) cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M) (ret : 0 < retention)
    (length : ∀ i, (pieces i).length ≤ 4*M/p)
    (degree : ∀ v, (occurrences (fun i => (pieces i).toFinset) v).card ≤ 4*M/n)
    (upper : (∑ i, (pieces i).length) ≤ M)
    (A : Finset V) (B : Finset I) (va : A.card ≤ n) (pa : B.card ≤ p)
    (enough : (M:ℝ)/retention + (M:ℝ)/(4*(n:ℝ))*A.card + (M:ℝ)/(4*(p:ℝ))*B.card ≤
      ((∑ i ∈ B, ((pieces i).toFinset ∩ A).card : ℕ):ℝ)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let kept := restrictListPaths pieces A B
  have keptSimple (i : B) : (kept i).Nodup := restrictListPath_nodup (simple i.val) A
  have keptFree : BridgeFree (Before kept) cutoff := restrictListPaths_fullFree simple free A B
  have each (i : B) : (kept i).length = ((pieces i.val).toFinset ∩ A).card :=
    restrictListPath_length (simple i.val) A
  have keptLength (i : B) : (kept i).length ≤ 4*M/p :=
    (each i).le.trans ((card_le_card inter_subset_left).trans ((List.toFinset_card_le _).trans (length i.val)))
  have keptDegree (v : A) : (occurrences (fun i => (kept i).toFinset) v).card ≤ 4*M/n := by
    have same : (fun i => (kept i).toFinset) = rectanglePaths (fun i => (pieces i).toFinset) A B :=
      funext (restrictListPaths_toFinset pieces A B)
    rw [same]
    exact (rectanglePaths_degree_le (fun i => (pieces i).toFinset) A B v).trans (degree v.val)
  have mass : (∑ i, (kept i).length) = ∑ i ∈ B, ((pieces i).toFinset ∩ A).card := by
    rw [← sum_attach B (fun i => ((pieces i).toFinset ∩ A).card)]
    exact sum_congr rfl (fun i _ => each i)
  have keptUpper : (∑ i, (kept i).length) ≤ M := by
    rw [mass]
    exact (sum_le_sum fun i (_ : i ∈ B) => (card_le_card inter_subset_left).trans (List.toFinset_card_le _)).trans
      ((sum_le_sum_of_subset (subset_univ B)).trans upper)
  have counted : (∑ v : A, (occurrences (fun i => (kept i).toFinset) v).card) =
      ∑ i ∈ B, ((pieces i).toFinset ∩ A).card := by
    rw [sum_occurrences,← mass]
    exact sum_congr rfl fun i _ => List.toFinset_card_of_nodup (keptSimple i)
  apply regularization_list_frozen_after_kept_vertices (half := false) kept keptSimple keptFree
    hn hp dense long ret (univ : Finset A) (by simpa only [card_univ,Fintype.card_coe] using va)
    (by simpa only [Fintype.card_coe] using pa) keptLength keptDegree keptUpper
  simp only [card_univ,Fintype.card_coe]
  change (M:ℝ)/retention ≤ ((∑ v : A, (occurrences (fun i => (kept i).toFinset) v).card : ℕ):ℝ) -
    (M:ℝ)/(4*(n:ℝ))*A.card - (M:ℝ)/(4*(p:ℝ))*B.card
  rw [counted]
  linarith only [enough]

private theorem frozen_full_after_one_quadratic_width_trim {n p n₀ p₀ M cutoff : ℕ}
    (rows : Fin p₀ → List (Fin n₀)) (simple : ∀ i, (rows i).Nodup)
    (free : BridgeFree (Before rows) cutoff) (rank : Fin n₀ → Fin n₀)
    (ordered : ∀ i, ((rows i).map rank).Pairwise (· < ·))
    (hn : 0 < n) (hp : 0 < p) (wideV : 8*n ≤ M) (wideP : 8*p ≤ M)
    (fitsV : n₀ ≤ n) (fitsP : p₀ ≤ p) (smallSide : 25*n₀ ≤ 19*n ∨ 25*p₀ ≤ 19*p)
    (lower : M ≤ 2*(∑ i, (rows i).length)) (smallMass : 12*(∑ i, (rows i).length) ≤ 7*M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ 256*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let K := ∑ i, (rows i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices rows D
  let W := ListVertexBlockIndex rows D
  let J := ListBlockIndex copies L
  let pieces : J → List W := listRegularizedPaths rows D L
  let marks (i : J) := (pieces i).toFinset
  let Conclusion := ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
    (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
    M ≤ 256*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean
  have dense : n ≤ M := by omega
  have long : p ≤ M := by omega
  have upper : K ≤ M := by change 12*K ≤ 7*M at smallMass; omega
  obtain ⟨dPos,_,_⟩ := four_average_width hn dense
  obtain ⟨lPos,_,_⟩ := four_average_width hp long
  obtain ⟨vCount,pCount⟩ := regularization_list_counts rows simple (D := D) (L := L) dPos lPos
  simp only [Fintype.card_fin] at vCount pCount
  change Fintype.card W ≤ n₀+K/D at vCount
  change Fintype.card J ≤ p₀+K/L at pCount
  obtain ⟨mass,length,degree⟩ := regularization_list_mass_caps rows simple D L dPos lPos
  change (∑ i, (pieces i).length) = K at mass
  obtain ⟨fullV,fullI,filledV,restV,filledI,restI⟩ := listRegularizedPaths_full_block_profiles rows simple dPos lPos
  simp only [Fintype.card_fin] at restV restI
  have pieceSimple (i : J) : (pieces i).Nodup := listRegularizedPaths_simple rows simple D L i
  have piecesFree : BridgeFree (Before pieces) cutoff :=
    listRegularizedPaths_fullFree_of_noShortPrecedenceCycle rows simple free
      (noShortPrecedenceCycle_of_increasing_order rows rank ordered (cutoff-2)) D L
  have capacity {q : ℕ} (positive : 0 < q) (wide : 8*q ≤ M) : M ≤ (4*M/q)*q := by
    have floor := four_average_width_product (M := M) positive
    omega
  have enough (A : Finset W) (B : Finset J) (va : A.card ≤ n) (pa : B.card ≤ p) (loss : ℕ)
      (remaining : K ≤ (∑ i ∈ B, (marks i ∩ A).card)+loss) (paid : 186*loss ≤ 7*K)
      (peel : (M:ℝ)/(4*(n:ℝ))*A.card+(M:ℝ)/(4*(p:ℝ))*B.card ≤ (11/25)*(M:ℝ)+(2/31)*(K:ℝ)) :
      Conclusion := by
    apply frozen_full_from_capped_rectangle pieces pieceSimple piecesFree hn hp dense long
      (retention := 256) (by decide) length degree (mass.trans_le upper) A B va pa
    have low : (M:ℝ) ≤ 2*(K:ℝ) := by exact_mod_cast lower
    have cost : (186:ℝ)*loss ≤ 7*(K:ℝ) := by exact_mod_cast paid
    have kept : (K:ℝ) ≤ ((∑ i ∈ B, (marks i ∩ A).card : ℕ):ℝ)+loss := by exact_mod_cast remaining
    change (M:ℝ)/256+(M:ℝ)/(4*(n:ℝ))*A.card+(M:ℝ)/(4*(p:ℝ))*B.card ≤
      ((∑ i ∈ B, (marks i ∩ A).card : ℕ):ℝ)
    linarith only [low,cost,kept,peel,Nat.cast_nonneg (α := ℝ) M]
  change Conclusion
  rcases smallSide with shortV | shortP
  · have costV := smaller_support_peeling_charge hn wideV shortV smallMass vCount
    have pathRoom : (∑ i, (pieces i).length) ≤ L*p := mass.trans_le (upper.trans (capacity hp wideP))
    obtain ⟨B,pa,charged⟩ := trim_full_weight_blocks_quadratic (fun (i : J) => (pieces i).length) fullI lPos
      filledI (restI.trans_le fitsP) pathRoom
    let drop := ∑ i ∈ univ \ B, (pieces i).length
    rw [mass] at charged
    have remain : K ≤ (∑ i ∈ B, (marks i ∩ (univ : Finset W)).card)+drop := by
      have split : drop+(∑ i ∈ B, (pieces i).length) = K := (sum_sdiff (subset_univ B)).trans mass
      have equal : (∑ i ∈ B, (marks i ∩ (univ : Finset W)).card) = ∑ i ∈ B, (pieces i).length :=
        sum_congr rfl fun i _ => by simp only [marks,inter_univ,List.toFinset_card_of_nodup (pieceSimple i)]
      rw [equal]
      omega
    apply enough univ B (by simpa only [card_univ] using costV.1) pa drop remain
      (one_width_trim_loss hp wideP smallMass charged)
    have costP := quarter_support_charge (M := M) hp pa
    simp only [card_univ]
    linarith only [costV.2,costP]
  · have costP := smaller_support_peeling_charge hp wideP shortP smallMass pCount
    let weights (v : W) := (occurrences marks v).card
    have counted : (∑ v, weights v) = K := by
      unfold weights
      rw [sum_occurrences,← mass]
      exact sum_congr rfl fun i _ => List.toFinset_card_of_nodup (pieceSimple i)
    have vertexRoom : (∑ v, weights v) ≤ D*n := counted.trans_le (upper.trans (capacity hn wideV))
    obtain ⟨A,va,charged⟩ := trim_full_weight_blocks_quadratic weights fullV dPos
      filledV (restV.trans_le fitsV) vertexRoom
    let drop := ∑ v ∈ univ \ A, weights v
    rw [counted] at charged
    have remain : K ≤ (∑ i ∈ (univ : Finset J), (marks i ∩ A).card)+drop := by
      have split : drop+(∑ v ∈ A, weights v) = K := (sum_sdiff (subset_univ A)).trans counted
      rw [column_rectangle_mass]
      change K ≤ (∑ v ∈ A, weights v)+drop
      omega
    apply enough A univ va (by simpa only [card_univ] using costP.1) drop remain
      (one_width_trim_loss hn wideV smallMass charged)
    have costV := quarter_support_charge (M := M) hn va
    simp only [card_univ]
    linarith only [costV,costP.2]

/-- At three quarters of the smaller original budget, the original
caps can be met by charging peeling to the support actually selected. -/
theorem regularization_list_frozen_full_of_three_quarters_cutoff {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (Before paths) cutoff) (two : 2 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (near : 3*min n p ≤ 4*cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
      M ≤ 256*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases low : M ≤ 8*max n p
  · obtain ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,mass,upper,caps⟩ :=
      regularization_list_frozen_low_mass paths simple free.halfFree two hn hp dense long low
    exact ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,by omega,upper,caps⟩
  by_cases small : n ≤ 157 ∨ p ≤ 156
  · obtain ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,mass,upper,caps⟩ :=
      regularization_list_frozen_of_small_budget_all_cutoffs (half := false) paths simple free two hn hp dense long small
    exact ⟨v,vFits,q,qFits,clean,cleanSimple,cleanFree,by omega,upper,caps⟩
  have wideV : 8*n ≤ M := (Nat.mul_le_mul_left _ (le_max_left n p)).trans (Nat.lt_of_not_ge low).le
  have wideP : 8*p ≤ M := (Nat.mul_le_mul_left _ (le_max_right n p)).trans (Nat.lt_of_not_ge low).le
  let q := min n p
  have large : 157 ≤ q := by
    push Not at small
    exact le_min (by omega) (by omega)
  let size := (3*q+3)/4
  have keep : 3*q ≤ 4*size := by unfold size; omega
  have bound : size ≤ cutoff := by unfold size; change 3*q ≤ 4*cutoff at near; omega
  have saving : 25*size ≤ 19*q := by unfold size; omega
  obtain ⟨A,va,B,pa,smaller,smallCut,retained⟩ :=
    choose_full_support paths simple (by decide) keep bound saving
  obtain ⟨rank,kept,keptSimple,keptFree,ordered,removed,keptUpper⟩ :=
    full_increasing_restriction paths simple free A B smallCut
  let K := ∑ i, (kept i).length
  have mass : M ≤ 2*K := by omega
  have upper : K ≤ M := keptUpper.trans (selected_rectangle_mass_le_original paths A B)
  have vf : Fintype.card A ≤ n := by simpa only [Fintype.card_coe] using va
  have pf : Fintype.card B ≤ p := by simpa only [Fintype.card_coe] using pa
  by_cases high : 7*M ≤ 12*K
  · have enough : 20*A.card ≤ 17*n ∨ 20*B.card ≤ 17*p := by
      rcases smaller with hV | hP
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    exact frozen_full_after_trimmed_increasing_rows kept keptSimple keptFree rank ordered hn hp wideV wideP
      vf pf (by simpa only [Fintype.card_coe] using enough) high upper
  · exact frozen_full_after_one_quadratic_width_trim kept keptSimple keptFree rank ordered hn hp wideV wideP
      vf pf (by simpa only [Fintype.card_coe] using smaller) mass (by omega)

/-- Feasible literal inputs have the same three-quarters-cutoff cleaning
with distinct nonempty output rows. -/
theorem regularization_list_frozen_full_distinct_of_three_quarters_cutoff {n p cutoff : ℕ}
    (paths : Fin p → List (Fin n)) (distinct : Function.Injective paths) (nonempty : ∀ i, paths i ≠ [])
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (Before paths) cutoff) (two : 2 ≤ cutoff)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (near : 3*min n p ≤ 4*cutoff) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
      BridgeFree (Before clean) cutoff ∧ M ≤ 256*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_distinct_of_indexed (half := false) (k := cutoff) (retention := 256)
    paths distinct nonempty simple free two hn hp dense (by decide)
    (fun long => regularization_list_frozen_full_of_three_quarters_cutoff paths simple free two hn hp dense long near)

/-- The three-quarters-cutoff frozen cleaning bound at the unrestricted indexed maximum. -/
theorem localOrderExtremal_frozen_full_of_three_quarters_cutoff (n p cutoff : ℕ)
    (hn : 0 < n) (hp : 0 < p) (two : 2 ≤ cutoff) (near : 3*min n p ≤ 4*cutoff) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → BridgeFree (Before other) cutoff →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ BridgeFree (Before clean) cutoff ∧
        M ≤ 256*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,simple,free,maximal,dense,long⟩ := localOrderExtremal_isDense n p cutoff false hn hp
  exact ⟨paths,simple,free,maximal,
    regularization_list_frozen_full_of_three_quarters_cutoff paths simple free two hn hp dense long near⟩

/-- The three-quarters-cutoff frozen bound at the feasible literal maximum. -/
theorem localOrderDistinctExtremal_frozen_full_of_three_quarters_cutoff {n p cutoff : ℕ}
    (hn : 0 < n) (hp : 0 < p) (two : 2 ≤ cutoff) (near : 3*min n p ≤ 4*cutoff)
    (feasible : ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff) :
    ∃ paths : Fin p → List (Fin n), Function.Injective paths ∧
      (∀ i, paths i ≠ [] ∧ (paths i).Nodup) ∧ BridgeFree (Before paths) cutoff ∧
      (∀ other : Fin p → List (Fin n), Function.Injective other →
        (∀ i, other i ≠ [] ∧ (other i).Nodup) → BridgeFree (Before other) cutoff →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        Function.Injective clean ∧ (∀ i, clean i ≠ []) ∧ (∀ i, (clean i).Nodup) ∧
        BridgeFree (Before clean) cutoff ∧ M ≤ 256*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,distinct,rows,free,maximal,dense,_⟩ := localOrderDistinctExtremal_isDense false hp feasible
  exact ⟨paths,distinct,rows,free,maximal,regularization_list_frozen_full_distinct_of_three_quarters_cutoff paths
    distinct (fun i => (rows i).1) (fun i => (rows i).2) free two hn hp dense near⟩

end OnlineReachabilityPreservers
