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

private theorem column_rectangle_mass {n p : ℕ} (paths : Fin p → List (Fin n)) (A : Finset (Fin n)) :
    (∑ i : Fin p, ((paths i).toFinset ∩ A).card) = ∑ v ∈ A, (occurrences (fun i => (paths i).toFinset) v).card := by
  have row (i : Fin p) : ((paths i).toFinset ∩ A).card =
      ∑ v ∈ A, if v ∈ (paths i).toFinset then 1 else 0 := by
    rw [← sum_filter]
    rw [show A.filter (fun v => v ∈ (paths i).toFinset) = (paths i).toFinset ∩ A by
      ext v; simp [and_comm]]
    simp
  have col (v : Fin n) : (occurrences (fun i => (paths i).toFinset) v).card =
      ∑ i : Fin p, if v ∈ (paths i).toFinset then 1 else 0 := by
    rw [← sum_filter]
    simp [occurrences]
  simp only [row,col,Finset.sum_comm (s := (univ : Finset (Fin p)))]

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
  by_cases vertices : n ≤ p
  · let degree (v : Fin n) := (occurrences (fun i => (paths i).toFinset) v).card
    have degreeSum : (∑ v, degree v) = ∑ i, (paths i).length := by
      unfold degree
      rw [sum_occurrences]
      exact sum_congr rfl fun i _ => List.toFinset_card_of_nodup (simple i)
    have fits : 5*(univ : Finset (Fin n)).card ≤ 6*size := by
      simpa only [q,min_eq_left vertices,card_univ,Fintype.card_fin] using keep
    obtain ⟨A,_,card,retained⟩ := trim_weights_ratio univ degree (by decide : 5 ≤ 6) fits
    have reduced : 20*A.card ≤ 17*n := (Nat.mul_le_mul_left _ card).trans
      (by simpa only [q,min_eq_left vertices] using saving)
    have vertexFits : A.card ≤ n := by omega
    refine ⟨A,vertexFits,univ,by simp,Or.inl reduced,(min_le_left _ _).trans (card.trans bound),?_⟩
    rw [← degreeSum,column_rectangle_mass]
    exact retained
  · have fits : 5*(univ : Finset (Fin p)).card ≤ 6*size := by
      simpa only [q,min_eq_right (le_of_not_ge vertices),card_univ,Fintype.card_fin] using keep
    obtain ⟨B,_,card,retained⟩ := trim_weights_ratio univ (fun i => (paths i).length) (by decide : 5 ≤ 6) fits
    have reduced : 20*B.card ≤ 17*p := (Nat.mul_le_mul_left _ card).trans
      (by simpa only [q,min_eq_right (le_of_not_ge vertices)] using saving)
    have pathFits : B.card ≤ p := by omega
    refine ⟨univ,by simp,B,pathFits,Or.inr reduced,(min_le_right _ _).trans (card.trans bound),?_⟩
    have masses : (∑ i ∈ B, ((paths i).toFinset ∩ (univ : Finset (Fin n))).card) = ∑ i ∈ B, (paths i).length := by
      exact sum_congr rfl fun i _ => by rw [inter_univ,List.toFinset_card_of_nodup (simple i)]
    rw [masses]
    exact retained

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
  let restricted := restrictListPaths paths A B
  have restrictedSimple (i : B) : (restricted i).Nodup := restrictListPath_nodup (simple i.val) A
  have restrictedFree : BridgeFree (Before restricted) cutoff := restrictListPaths_fullFree simple free A B
  obtain ⟨relabelSimple,relabelFree,relabelMass,_,_⟩ :=
    relabelListPathsFin_spec (half := false) restricted restrictedSimple restrictedFree
  let picked := relabelListPathsFin restricted
  have originalMass : (∑ i, (picked i).length) = ∑ i ∈ B, ((paths i).toFinset ∩ A).card := by
    rw [relabelMass,← Finset.sum_attach B (fun i => ((paths i).toFinset ∩ A).card)]
    exact sum_congr rfl fun i _ => restrictListPath_length (simple i.val) A
  have pickedRetained : 5*M ≤ 6*(∑ i, (picked i).length) := originalMass.symm ▸ retained
  have pickedUpper : (∑ i, (picked i).length) ≤ M := by
    rw [originalMass]
    exact (sum_le_sum fun i (_ : i ∈ B) => (card_le_card inter_subset_left).trans (List.toFinset_card_le _)).trans
      (sum_le_sum_of_subset (subset_univ B))
  have all : ∀ d, IsEmpty (Bridge (Before picked) d) :=
    bridgeFree_all_of_cutoff_ge_min relabelFree (by simpa only [Fintype.card_coe] using smallCut)
  obtain ⟨rank,kept,sub,ordered,_,_,removed⟩ := fullBridgeFree_increasing_subsequences_two_of_components picked
    relabelSimple (precedenceComponent_fullFree relabelSimple all)
  have mass : 7*M ≤ 12*(∑ i, (kept i).length) := by
    have vertexBound : Fintype.card A ≤ n := by simpa only [Fintype.card_coe] using va
    change (∑ i, (picked i).length) ≤ (∑ i, (kept i).length)+2*Fintype.card A at removed
    omega
  have upper : (∑ i, (kept i).length) ≤ M :=
    (sum_le_sum fun i _ => (sub i).length_le).trans pickedUpper
  have keptFree : BridgeFree (Before kept) cutoff := by
    intro d _
    exact ⟨fun bridge => (all d).false (bridge.mapPaths id Function.injective_id
      (fun i _ _ step => listBefore_of_sublist (relabelSimple i) (sub i) step))⟩
  exact frozen_full_after_trimmed_increasing_rows kept (fun i => (sub i).nodup (relabelSimple i))
    keptFree rank ordered hn hp wideV wideP
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

end OnlineReachabilityPreservers
