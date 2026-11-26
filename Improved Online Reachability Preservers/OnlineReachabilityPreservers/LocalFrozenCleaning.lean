import OnlineReachabilityPreservers.LocalAverageCleaning
import OnlineReachabilityPreservers.SynchronizedPathSplits

/-! Cleaning with factor-four caps measured against the input averages. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

/-- All four bounds are relative to the original budgets and mass. -/
def frozenListCaps {V I : Type*} [DecidableEq V] [Fintype I]
    (n p M : ℕ) (paths : I → List V) : Prop :=
  (∀ v : V, (M:ℝ)/(4*(n:ℝ)) ≤ (occurrences (fun i => (paths i).toFinset) v).card ∧
    ((occurrences (fun i => (paths i).toFinset) v).card:ℝ) ≤ 4*(M:ℝ)/(n:ℝ)) ∧
  (∀ i : I, (M:ℝ)/(4*(p:ℝ)) ≤ ((paths i).length:ℝ) ∧ ((paths i).length:ℝ) ≤ 4*(M:ℝ)/(p:ℝ))

private theorem sparse_cleaning_block_dimensions {a b : ℕ} (bPos : 0 < b) (ordered : b ≤ a) :
    ∃ width rows : ℕ, 0 < width ∧ rows ≤ b ∧ rows*width ≤ a ∧ a ≤ 2*(rows*width) ∧
      a ≤ b*width ∧ width*b ≤ a+b-1 := by
  let width := (a+b-1)/b
  let rows := a/width
  have aPos : 0 < a := bPos.trans_le ordered
  have widthPos : 0 < width := Nat.div_pos (by omega) bPos
  have covers : a ≤ b*width := by
    have raw := Nat.lt_mul_div_succ (a+b-1) bPos
    change a+b-1 < b*(width+1) at raw
    rw [Nat.mul_succ] at raw
    omega
  have widthLe : width ≤ a := by
    have raw : a+b-1 < (a+1)*b := by
      rw [Nat.add_mul, Nat.one_mul]
      have le : a ≤ a*b := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left a bPos
      omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul bPos).mpr raw)
  have rowsPos : 0 < rows := Nat.div_pos widthLe widthPos
  have rowsLe : rows ≤ b := by
    have cap : a / width ≤ (b*width)/width := Nat.div_le_div_right covers
    simpa only [Nat.mul_div_cancel b widthPos] using cap
  have taken : rows*width ≤ a := Nat.div_mul_le_self a width
  have dbl : a ≤ 2*(rows*width) := by
    have raw := Nat.lt_mul_div_succ a widthPos
    change a < width*(rows+1) at raw
    have rowMore : rows+1 ≤ 2*rows := by omega
    exact raw.le.trans (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.mul_le_mul_left width rowMore)
  exact ⟨width,rows,widthPos,rowsLe,taken,dbl,covers,Nat.div_mul_le_self _ _⟩

private theorem sparse_cleaning_block_counts {a b M factor : ℕ} (bPos : 0 < b) (ordered : b ≤ a)
    (massLower : a ≤ M) (massUpper : M ≤ factor*a) (factorCap : factor ≤ 4) :
    ∃ width rows : ℕ, 0 < width ∧ rows ≤ b ∧ rows*width ≤ a ∧ M ≤ (2*factor)*(rows*width) ∧
      (M:ℝ)/(4*(a:ℝ)) ≤ 1 ∧ (1:ℝ) ≤ 4*(M:ℝ)/(a:ℝ) ∧
      (M:ℝ)/(4*(b:ℝ)) ≤ (width:ℝ) ∧ (width:ℝ) ≤ 4*(M:ℝ)/(b:ℝ) := by
  have aPos : 0 < a := bPos.trans_le ordered
  obtain ⟨width,rows,widthPos,rowsLe,taken,dbl,covers,slack⟩ := sparse_cleaning_block_dimensions bPos ordered
  have nonzeroA : 0 < (a:ℝ) := Nat.cast_pos.mpr aPos
  have nonzeroB : 0 < (b:ℝ) := Nat.cast_pos.mpr bPos
  have atMost : M ≤ 4*a := massUpper.trans (Nat.mul_le_mul_right _ factorCap)
  have widthLower : M ≤ 4*b*width := by
    have step : M ≤ 4*(b*width) := atMost.trans (by omega)
    simpa only [Nat.mul_assoc] using step
  have widthUpper : width*b ≤ 4*M := by
    omega
  have retained : M ≤ (2*factor)*(rows*width) := calc
    _ ≤ factor*a := massUpper
    _ ≤ factor*(2*(rows*width)) := Nat.mul_le_mul_left _ dbl
    _ = _ := by ring
  refine ⟨width,rows,widthPos,rowsLe,taken,retained,?_,?_,?_,?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 4*(a:ℝ))).mpr
    exact_mod_cast (show M ≤ 1*(4*a) by omega)
  · apply (le_div_iff₀ nonzeroA).mpr
    exact_mod_cast (show 1*a ≤ 4*M by omega)
  · apply (div_le_iff₀ (by positivity : 0 < 4*(b:ℝ))).mpr
    rw [mul_comm (width:ℝ)]
    exact_mod_cast widthLower
  · exact (le_div_iff₀ nonzeroB).mpr (by exact_mod_cast widthUpper)

private def disjointFrozenRows (rows width : ℕ) (i : Fin rows) : List (Fin (rows*width)) :=
  List.ofFn (fun j : Fin width => finProdFinEquiv (i,j))

private theorem disjointFrozenRows_owner {r w : ℕ} {i : Fin r} {x : Fin (r*w)} :
    x ∈ disjointFrozenRows r w i ↔ (finProdFinEquiv.symm x).1 = i := by
  constructor
  · intro mem
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp mem
    rw [Equiv.symm_apply_apply]
  · intro h
    let z := finProdFinEquiv.symm x
    have same : (i,z.2) = z := Prod.ext h.symm rfl
    exact List.mem_ofFn.mpr ⟨z.2, (congrArg finProdFinEquiv same).trans (finProdFinEquiv.apply_symm_apply x)⟩

private theorem disjointFrozenRows_degree (r w : ℕ) (x : Fin (r*w)) :
    (occurrences (fun i => (disjointFrozenRows r w i).toFinset) x).card = 1 := by
  have onlyOwner : occurrences (fun i => (disjointFrozenRows r w i).toFinset) x = {(finProdFinEquiv.symm x).1} := by
    ext i
    simp only [mem_occurrences, List.mem_toFinset, disjointFrozenRows_owner, mem_singleton]
    exact eq_comm
  rw [onlyOwner, card_singleton]

private def singletonFrozenRows (rows width : ℕ) (i : Fin (rows*width)) : List (Fin rows) :=
  [(finProdFinEquiv.symm i).1]

private theorem singletonFrozenRows_degree (r w : ℕ) (x : Fin r) :
    (occurrences (fun i => (singletonFrozenRows r w i).toFinset) x).card = w := by
  let along : Fin w ↪ Fin (r*w) :=
    ⟨fun j => finProdFinEquiv (x,j), fun a b same => congrArg Prod.snd (finProdFinEquiv.injective same)⟩
  have allCopies : occurrences (fun i => (singletonFrozenRows r w i).toFinset) x = (univ : Finset (Fin w)).map along := by
    ext i
    simp only [mem_occurrences, List.mem_toFinset, singletonFrozenRows, List.mem_singleton, mem_map,
      mem_univ, true_and]
    constructor
    · intro same
      let z := finProdFinEquiv.symm i
      have eq : (x,z.2) = z := Prod.ext same rfl
      exact ⟨z.2, (congrArg finProdFinEquiv eq).trans (finProdFinEquiv.apply_symm_apply i)⟩
    · rintro ⟨j,rfl⟩
      change x = (finProdFinEquiv.symm (finProdFinEquiv (x,j))).1
      rw [Equiv.symm_apply_apply]
  rw [allCopies, card_map, card_univ, Fintype.card_fin]

/-- At low mass in either coordinate, disjoint paths or repeated singletons
meet the two budgets and the same frozen averages. -/
private theorem full_frozen_cleaning_sparse_of_factor {n p M k factor : ℕ} (factorCap : factor ≤ 4) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ M) (long : p ≤ M) (small : M ≤ factor*max n p) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ (2*factor)*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  by_cases pl : p ≤ n
  · rw [max_eq_left pl] at small
    obtain ⟨w,r,_,rCap,massCap,massEnough,degLow,degHigh,lenLow,lenHigh⟩ :=
      sparse_cleaning_block_counts hp pl dense small factorCap
    let clean := disjointFrozenRows r w
    have simple (i : Fin r) : (clean i).Nodup := List.nodup_ofFn.mpr (fun _ _ eq =>
      congrArg Prod.snd (finProdFinEquiv.injective eq))
    have legal : BridgeFree (ListBefore clean) k := by
      intro j _
      refine ⟨fun b => b.river_ne_arc 0 ?_⟩
      exact (disjointFrozenRows_owner.mp b.riverStep.1).symm.trans
        (disjointFrozenRows_owner.mp (b.arcStep 0).1)
    have size : (∑ i, (clean i).length) = r*w := by simp [clean, disjointFrozenRows]
    refine ⟨r*w,massCap,r,rCap,clean,simple,legal,?_,?_,?_⟩
    · exact size.symm ▸ massEnough
    · exact size.symm ▸ massCap.trans dense
    · constructor
      · intro x
        rw [disjointFrozenRows_degree]
        simpa only [Nat.cast_one] using And.intro degLow degHigh
      · intro i
        change (M:ℝ)/(4*(p:ℝ)) ≤ ((disjointFrozenRows r w i).length:ℝ) ∧
          ((disjointFrozenRows r w i).length:ℝ) ≤ 4*(M:ℝ)/(p:ℝ)
        simpa only [disjointFrozenRows, List.length_ofFn] using And.intro lenLow lenHigh
  · have np : n ≤ p := le_of_not_ge pl
    rw [max_eq_right np] at small
    obtain ⟨w,r,_,rCap,massCap,massEnough,lenLow,lenHigh,degLow,degHigh⟩ :=
      sparse_cleaning_block_counts hn np long small factorCap
    let clean := singletonFrozenRows r w
    have simple (i : Fin (r*w)) : (clean i).Nodup := by simp [clean, singletonFrozenRows]
    have legal : BridgeFree (ListBefore clean) k := by
      intro j _
      refine ⟨fun b => listBefore_ne b.riverStep ?_⟩
      have a := List.mem_singleton.mp b.riverStep.1
      have z := List.mem_singleton.mp b.riverStep.2.1
      exact a.trans z.symm
    have size : (∑ i, (clean i).length) = r*w := by simp [clean, singletonFrozenRows]
    refine ⟨r,rCap,r*w,massCap,clean,simple,legal,?_,?_,?_⟩
    · exact size.symm ▸ massEnough
    · exact size.symm ▸ massCap.trans long
    · constructor
      · intro x
        rw [singletonFrozenRows_degree]
        exact ⟨degLow,degHigh⟩
      · intro i
        change (M:ℝ)/(4*(p:ℝ)) ≤ ((singletonFrozenRows r w i).length:ℝ) ∧
          ((singletonFrozenRows r w i).length:ℝ) ≤ 4*(M:ℝ)/(p:ℝ)
        simpa only [singletonFrozenRows, List.length_singleton, Nat.cast_one] using And.intro lenLow lenHigh

theorem full_frozen_cleaning_sparse {n p M k : ℕ} (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ M) (long : p ≤ M) (small : M ≤ 3*max n p) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ 6*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  full_frozen_cleaning_sparse_of_factor (by decide) hn hp dense long small

/-- At most four incidences per unit of the larger budget suffice for the
same sparse construction with one eighth of the input mass. -/
theorem full_frozen_cleaning_sparse_four {n p M k : ℕ} (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ M) (long : p ≤ M) (small : M ≤ 4*max n p) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  full_frozen_cleaning_sparse_of_factor (by decide) hn hp dense long small

end OnlineReachabilityPreservers

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

private theorem frozenListCaps_relabel {V I : Type*}
    [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I] (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup) {n p M k : ℕ} {half : Bool}
    (allowed : localOrderAdmissible half k paths)
    (caps : frozenListCaps n p M paths) :
    ∃ clean : Fin (Fintype.card I) → List (Fin (Fintype.card V)),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      (∑ i, (clean i).length) = (∑ i, (paths i).length) ∧ frozenListCaps n p M clean := by
  let vIso : Fin (Fintype.card V) ≃o V := Fintype.orderIsoFinOfCardEq V rfl
  let iIso : Fin (Fintype.card I) ≃o I := Fintype.orderIsoFinOfCardEq I rfl
  obtain ⟨cleanSimple, cleanLegal, mass, degrees, lengths⟩ :=
    relabelListPathsFin_spec paths simple (half := half) (k := k) allowed
  refine ⟨relabelListPathsFin paths, cleanSimple, cleanLegal, mass, ?_⟩
  exact ⟨fun v => by rw [degrees]; exact caps.1 (vIso v),
    fun i => by rw [lengths]; exact caps.2 (iIso i)⟩

end OnlineReachabilityPreservers

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]

local notation "ListBefore" => SourceAudit.BeforeIn

omit [Fintype V] in
private theorem finish_frozen_rectangle {k : ℕ} {half : Bool} (pieces : I → List V)
    (pieceSimple : ∀ i, (pieces i).Nodup) (piecesFree : localOrderAdmissible half k pieces)
    (A : Finset V) (B : Finset I) {M n p D L retention : ℕ} (aCap : A.card ≤ n) (bCap : B.card ≤ p)
    (retained : M ≤ retention*(∑ i : B, (rectanglePaths (fun j => (pieces j).toFinset) A B i).card))
    (total : (∑ i, (pieces i).toFinset.card) ≤ M)
    (minDegree : ∀ v : A, (M:ℝ)/(4*(n:ℝ)) ≤
      (occurrences (rectanglePaths (fun j => (pieces j).toFinset) A B) v).card)
    (minLength : ∀ i : B, (M:ℝ)/(4*(p:ℝ)) ≤
      (rectanglePaths (fun j => (pieces j).toFinset) A B i).card)
    (lengthCap : ∀ i : I, (pieces i).length ≤ L)
    (degreeCap : ∀ v : V, (occurrences (fun i => (pieces i).toFinset) v).card ≤ D)
    (capD : (D:ℝ) ≤ 4*(M:ℝ)/(n:ℝ)) (capL : (L:ℝ) ≤ 4*(M:ℝ)/(p:ℝ)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let Z (i : I) := (pieces i).toFinset
  let clean := restrictListPaths pieces A B
  let rectangle := rectanglePaths Z A B
  have same (i : B) : (clean i).toFinset = rectangle i := restrictListPaths_toFinset pieces A B i
  have cleanSimple (i : B) : (clean i).Nodup := restrictListPath_nodup (pieceSimple i.val) A
  have cleanLength (i : B) : (clean i).length = (rectangle i).card :=
    (List.toFinset_card_of_nodup (cleanSimple i)).symm.trans (congrArg Finset.card (same i))
  have equals : (fun i => (clean i).toFinset) = rectangle := funext same
  have mass : (∑ i : B, (clean i).length) = ∑ i : B, (rectangle i).card :=
    sum_congr rfl (fun i _ => cleanLength i)
  have caps : frozenListCaps n p M clean := by
    constructor
    · intro v
      rw [equals]
      exact ⟨minDegree v,
        (Nat.cast_le.mpr ((rectanglePaths_degree_le Z A B v).trans (degreeCap v.val))).trans capD⟩
    · intro i
      refine ⟨by rw [cleanLength]; exact minLength i, ?_⟩
      have cap : (clean i).length ≤ (pieces i.val).length := by
        rw [show (clean i).length = ((pieces i.val).toFinset ∩ A).card from
          restrictListPath_length (pieceSimple i.val) A]
        exact (card_le_card inter_subset_left).trans (List.toFinset_card_le _)
      exact (Nat.cast_le.mpr (cap.trans (lengthCap i.val))).trans capL
  have legal : localOrderAdmissible half k clean := by
    cases half
    · exact restrictListPaths_fullFree pieceSimple piecesFree A B
    · exact restrictListPaths_halfFree pieceSimple piecesFree A B
  obtain ⟨relabeled, relabeledSimple, relabeledLegal, relabeledMass, relabeledCaps⟩ :=
    frozenListCaps_relabel _ cleanSimple legal caps
  refine ⟨Fintype.card A, ?_, Fintype.card B, ?_, relabeled, relabeledSimple, relabeledLegal,
    ?_, ?_, relabeledCaps⟩
  · simpa only [Fintype.card_coe] using aCap
  · simpa only [Fintype.card_coe] using bCap
  · rw [relabeledMass, mass]
    exact retained
  · rw [relabeledMass, mass]
    exact (rectanglePaths_mass_le Z A B).trans total

private theorem frozen_cut_of_caps {k : ℕ} {half : Bool} (pieces : I → List V)
    (pieceSimple : ∀ i, (pieces i).Nodup) (piecesFree : localOrderAdmissible half k pieces)
    {M n p D L vNum vDen pNum pDen retention : ℕ} (hn : 0 < n) (hp : 0 < p)
    (vPos : 0 < vDen) (pPos : 0 < pDen) (vRatio : vNum ≤ vDen) (pRatio : pNum ≤ pDen)
    (vertices : vNum*Fintype.card V ≤ vDen*n) (families : pNum*Fintype.card I ≤ pDen*p)
    (total : (∑ i, (pieces i).toFinset.card) ≤ M)
    (enough : (vDen*pDen)*(retention+2)*M ≤ 2*(vNum*pNum)*retention*(∑ i, (pieces i).toFinset.card))
    (lengthCap : ∀ i : I, (pieces i).length ≤ L)
    (degreeCap : ∀ v : V, (occurrences (fun i => (pieces i).toFinset) v).card ≤ D)
    (capD : (D:ℝ) ≤ 4*(M:ℝ)/(n:ℝ)) (capL : (L:ℝ) ≤ 4*(M:ℝ)/(p:ℝ)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨A,B,aCap,bCap,retained,minDegree,minLength⟩ :=
    balancedRectangle_subsystem_of_ratios_frozen (fun i => (pieces i).toFinset) hn hp
      vPos pPos vRatio pRatio vertices families enough
  exact finish_frozen_rectangle pieces pieceSimple piecesFree A B aCap bCap retained total minDegree minLength
    lengthCap degreeCap capD capL

/-- Restrict upper-capped pieces to the original budgets when both expanded
supports fit within four thirds of those budgets and enough mass survives. -/
theorem regularization_list_frozen_after_caps_with_room_of_mass {half : Bool} {k n p M retention : ℕ}
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertices : 3*Fintype.card V ≤ 4*n) (families : 3*Fintype.card I ≤ 4*p)
    (lengthCap : ∀ i, (paths i).length ≤ 4*M/p)
    (degreeCap : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ 4*M/n)
    (massCap : (∑ i, (paths i).length) ≤ M)
    (massFloor : 8*(retention+2)*M ≤ 9*retention*(∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨_,_,capD⟩ := four_average_width hn dense
  obtain ⟨_,_,capL⟩ := four_average_width hp long
  have count : (∑ i, (paths i).toFinset.card) = ∑ i, (paths i).length :=
    sum_congr rfl fun i _ => List.toFinset_card_of_nodup (simple i)
  exact frozen_cut_of_caps paths simple allowed
    (M := M) (D := 4*M/n) (L := 4*M/p) (retention := retention)
    (vNum := 3) (vDen := 4) (pNum := 3) (pDen := 4)
    hn hp (by decide) (by decide) (by decide) (by decide) vertices families (count.trans_le massCap)
    (by
      rw [count]
      calc
        _ = 2*(8*(retention+2)*M) := by ring
        _ ≤ 2*(9*retention*(∑ i, (paths i).length)) := Nat.mul_le_mul_left 2 massFloor
        _ = _ := by ring)
    lengthCap degreeCap capD capL

/-- If both upper caps already hold, both supports may be larger than the
original budgets by factors of four thirds. At full original mass the
rectangle estimate and peeling keep at least one sixteenth. -/
theorem regularization_list_frozen_after_caps_with_room {half : Bool} {k n p M : ℕ}
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertices : 3*Fintype.card V ≤ 4*n) (families : 3*Fintype.card I ≤ 4*p)
    (lengthCap : ∀ i, (paths i).length ≤ 4*M/p)
    (degreeCap : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ 4*M/n)
    (mass : (∑ i, (paths i).length) = M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨_,_,capD⟩ := four_average_width hn dense
  obtain ⟨_,_,capL⟩ := four_average_width hp long
  have total : (∑ i, (paths i).toFinset.card) = M := by
    simp only [List.toFinset_card_of_nodup (simple _), mass]
  exact frozen_cut_of_caps paths simple allowed
    (M := M) (D := 4*M/n) (L := 4*M/p) (retention := 16)
    (vNum := 3) (vDen := 4) (pNum := 3) (pDen := 4)
    hn hp (by decide) (by decide) (by decide) (by decide) vertices families total.le
    (by rw [total]) lengthCap degreeCap capD capL

/-- When opposite-intersection pruning already meets the fixed upper caps,
the uncharged first incidence of every path is enough for frozen peeling.
An original mean path length at most `C` gives a retained fraction `1/(2*C)`. -/
theorem regularization_list_frozen_after_opposite_pruning {half : Bool} {k n p C : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (nonempty : ∀ i, paths i ≠ []) (allowed : localOrderAdmissible half k paths) (large : 3 ≤ k)
    (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (avg : (∑ i, (paths i).length) ≤ C*p)
    (lengthCap : ∀ i, (removeOppositeIntersections paths i).length ≤ 4*(∑ i, (paths i).length)/p)
    (degreeCap : ∀ v, (occurrences (fun i => (removeOppositeIntersections paths i).toFinset) v).card ≤
      4*(∑ i, (paths i).length)/n) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ (2*C)*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let kept := removeOppositeIntersections paths
  let K := ∑ i, (kept i).length
  have halfFree : HalfBridgeFree (ListBefore paths) k := by
    cases half
    · exact (show BridgeFree (ListBefore paths) k from allowed).halfFree
    · exact allowed
  have keptLegal : localOrderAdmissible half k kept := by
    cases half
    · exact removeOppositeIntersections_fullFree simple allowed
    · exact removeOppositeIntersections_halfFree simple allowed
  have keptSimple (i : Fin p) : (kept i).Nodup :=
    (removeOppositeIntersections_sublist paths i).nodup (simple i)
  have allPaths : univ.filter (fun i => paths i ≠ []) = univ :=
    filter_true_of_mem fun i _ => nonempty i
  have gain : M+p ≤ 2*K := by
    simpa only [allPaths,card_univ,Fintype.card_fin,M,K,kept] using
      removeOppositeIntersections_mass_with_nonempty_paths simple halfFree large
  have enough : (2*C+2)*M ≤ 2*(2*C)*K := by
    calc
      _ = (2*C)*M + 2*M := Nat.add_mul _ _ _
      _ ≤ (2*C)*M + (2*C)*p := Nat.add_le_add_left ((Nat.mul_le_mul_left 2 avg).trans_eq
        (Nat.mul_assoc _ _ _).symm) _
      _ = (2*C)*(M+p) := (Nat.mul_add _ _ _).symm
      _ ≤ _ := (Nat.mul_le_mul_left _ gain).trans_eq (by ring)
  have count : (∑ i, (kept i).toFinset.card) = K :=
    sum_congr rfl fun i _ => List.toFinset_card_of_nodup (keptSimple i)
  have total : K ≤ M :=
    sum_le_sum fun i _ => (removeOppositeIntersections_sublist paths i).length_le
  obtain ⟨_,_,capD⟩ := four_average_width hn dense
  obtain ⟨_,_,capL⟩ := four_average_width hp long
  exact frozen_cut_of_caps kept keptSimple keptLegal
    (M := M) (D := 4*M/n) (L := 4*M/p) (retention := 2*C)
    (vNum := 1) (vDen := 1) (pNum := 1) (pDen := 1)
    hn hp (by decide) (by decide) (by decide) (by decide)
    (by simp) (by simp) (count.trans_le total)
    (by rw [count]; simpa only [one_mul,mul_one] using enough)
    lengthCap degreeCap capD capL

/-- If a length-capped subsystem retains three quarters of the original mass,
peeling retains at least one sixteenth under both budgets. Split vertices
when the bridge cutoff allows it, or use already capped degrees. -/
theorem regularization_list_frozen_after_length_cap {half : Bool} {k n p M : ℕ}
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vertices : Fintype.card V ≤ n) (families : Fintype.card I ≤ p)
    (lengthCap : ∀ i, (paths i).length ≤ 4*M/p)
    (degreeCondition : (half = true → k ≤ 4) ∨
      (∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ 4*M/n))
    (loss : 3*M ≤ 4*(∑ i, (paths i).length)) (massCap : (∑ i, (paths i).length) ≤ M) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let D := 4*M/n
  obtain ⟨dPos, dBudget, capD⟩ := four_average_width hn dense
  obtain ⟨_, _, capL⟩ := four_average_width hp long
  rcases degreeCondition with short | degreeCap
  case inr =>
    have total : (∑ i, (paths i).toFinset.card) = ∑ i, (paths i).length :=
      sum_congr rfl fun i _ => List.toFinset_card_of_nodup (simple i)
    exact frozen_cut_of_caps (retention := 16) paths simple allowed
      (M := M) (n := n) (p := p) (D := D) (L := 4*M/p)
      (vNum := 1) (vDen := 1) (pNum := 1) (pDen := 1)
      hn hp (by decide) (by decide) (by decide) (by decide)
      (by simpa only [one_mul] using vertices) (by simpa only [one_mul] using families)
      (total.trans_le massCap) (by rw [total]; omega) lengthCap degreeCap capD capL
  let copies := splitListVertices paths D
  have copiesSimple (i : I) : (copies i).Nodup :=
    List.Nodup.of_map (fun v => v.fst) ((splitListVertices_project paths D i).symm ▸ simple i)
  have step {i : I} {x y : ListVertexBlockIndex paths D} (h : ListBefore copies i x y) :
      ListBefore paths i x.fst y.fst := by
    have orig := listBefore_map (fun v : ListVertexBlockIndex paths D => v.fst)
      ((splitListVertices_project paths D i).symm ▸ simple i) h
    simpa only [copies, splitListVertices_project] using orig
  have legal : localOrderAdmissible half k copies := by
    cases half
    · exact (show BridgeFree (ListBefore paths) k from allowed).split_list_vertices_any (·.fst) step
    · exact (show HalfBridgeFree (ListBefore paths) k from allowed).split_list_vertices_short
        (short rfl) (·.fst) step
  have total : (∑ i, (copies i).toFinset.card) = ∑ i, (paths i).length := by
    apply sum_congr rfl
    intro i _
    rw [List.toFinset_card_of_nodup (copiesSimple i), splitListVertices_length]
  have copiedVertices : 3*Fintype.card (ListVertexBlockIndex paths D) ≤ 4*n := by
    have count := blockIndex_card_precise (occurrences (fun i => (paths i).toFinset)) dPos
    rw [sum_occurrences] at count
    simp only [List.toFinset_card_of_nodup (simple _)] at count
    change Fintype.card (ListVertexBlockIndex paths D) ≤
      Fintype.card V + (∑ i, (paths i).length)/D at count
    have small := Nat.div_le_div_right (c := D) massCap
    change 3*(M/D) ≤ n at dBudget
    omega
  have copiedDegree (v : ListVertexBlockIndex paths D) :
      (occurrences (fun i => (copies i).toFinset) v).card ≤ D := by
    simpa only [copies, splitListVertices_toFinset] using
      (splitVertices_degree (fun i => (paths i).toFinset) dPos v)
  exact frozen_cut_of_caps (retention := 16) copies copiesSimple legal
      (M := M) (n := n) (p := p) (D := D) (L := 4*M/p)
      (vNum := 3) (vDen := 4) (pNum := 1) (pDen := 1)
      hn hp (by decide) (by decide) (by decide) (by decide) copiedVertices
      (by simpa only [one_mul] using families) (total.trans_le massCap)
      (by
        change 4 * (16 + 2) * M ≤ 2 * 3 * 16 * (∑ i, (copies i).toFinset.card)
        rw [total]
        omega) (fun i => by simpa only [copies, splitListVertices_length] using lengthCap i)
      copiedDegree capD capL

/-- Truncating each path at the original upper length cap suffices when
these prefixes retain at least three quarters of the incidences. -/
theorem regularization_list_frozen_shortened_paths {half : Bool} {k : ℕ}
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths)
    (degreeCondition : (half = true → k ≤ 4) ∨
      (∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤
        4*(∑ i, (paths i).length)/Fintype.card V))
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (dense : Fintype.card V ≤ ∑ i, (paths i).length) (long : Fintype.card I ≤ ∑ i, (paths i).length)
    (retained : 3*(∑ i, (paths i).length) ≤
      4*(∑ i, min ((4 * ∑ j, (paths j).length) / Fintype.card I) (paths i).length)) :
    let n := Fintype.card V
    let p := Fintype.card I
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 16*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let L := 4*M/Fintype.card I
  let shortened (i : I) := (paths i).take L
  have sub (i : I) : List.Sublist (shortened i) (paths i) := List.take_sublist _ _
  have step {i : I} {x y : V} (h : ListBefore shortened i x y) : ListBefore paths i x y :=
    listBefore_of_sublist (simple i) (sub i) h
  have valid : localOrderAdmissible half k shortened := by
    cases half
    · intro j hj
      exact ⟨fun b => (allowed hj).false (b.mapPaths id Function.injective_id (fun _ _ _ h => step h))⟩
    · intro j hj b earlier
      exact allowed hj (b.mapPaths id Function.injective_id (fun _ _ _ h => step h)) earlier
  have degrees (v : V) : (occurrences (fun i => (shortened i).toFinset) v).card ≤
      (occurrences (fun i => (paths i).toFinset) v).card := by
    apply card_le_card
    intro i hi
    simp only [mem_occurrences, List.mem_toFinset] at hi ⊢
    exact (sub i).subset hi
  exact regularization_list_frozen_after_length_cap shortened (fun i => (sub i).nodup (simple i)) valid
    hn hp dense long le_rfl le_rfl (fun i => by
      change ((paths i).take L).length ≤ L
      rw [List.length_take]
      exact min_le_left _ _) (degreeCondition.imp_right (fun cap v => (degrees v).trans (cap v)))
    (by simpa [shortened, L, M] using retained)
    (sum_le_sum fun i _ => (sub i).length_le)

private theorem regularization_list_balanced_synchronized {half : Bool} {k : ℕ} (three : 3 ≤ k)
    (five : k ≤ 5) (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup) (freeThree : BridgeFree (ListBefore paths) 3)
    (free : localOrderAdmissible half k paths)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (dense : 3*Fintype.card V ≤ ∑ i, (paths i).length) (long : 3*Fintype.card I ≤ ∑ i, (paths i).length) :
    let n := Fintype.card V
    let p := Fintype.card I
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 119*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let copies := splitListVertices paths D
  have copiesSimple (i : I) : (copies i).Nodup :=
    List.Nodup.of_map (fun v => v.fst) ((splitListVertices_project paths D i).symm ▸ simple i)
  have project {i : I} {x y : ListVertexBlockIndex paths D} (step : ListBefore copies i x y) :
      ListBefore paths i x.fst y.fst := by
    have orig := listBefore_map (fun v : ListVertexBlockIndex paths D => v.fst)
      ((splitListVertices_project paths D i).symm ▸ simple i) step
    simpa only [copies, splitListVertices_project] using orig
  have copiesFreeThree : BridgeFree (ListBefore copies) 3 :=
    freeThree.split_list_vertices_any (fun v => v.fst) (fun {_ _ _} => project)
  have copiesFree : localOrderAdmissible half k copies := by
    cases half
    · exact (show BridgeFree (ListBefore paths) k from free).split_list_vertices_any
        (fun v => v.fst) (fun {_ _ _} => project)
    · exact (show HalfBridgeFree (ListBefore paths) k from free).split_list_vertices_of_full
        freeThree five (fun v => v.fst) (fun {_ _ _} => project)
  obtain ⟨indexes⟩ := exists_packedPathRanks copies copiesSimple copiesFreeThree
  let selected := baseRankCuts (fun i => (copies i).length) L
  let cuts := synchronizedCuts selected (oppositeCutPartner indexes)
  let pieces := packedPathPiece indexes cuts
  let Z (i : PackedBlockIndex cuts) := (pieces i).toFinset
  have copiesMass : (∑ i, (copies i).length) = M :=
    sum_congr rfl (fun i _ => splitListVertices_length paths D i)
  have pieceSimple (i : PackedBlockIndex cuts) : (pieces i).Nodup :=
    packedPathPiece_simple copiesSimple indexes cuts i
  have lens (i : PackedBlockIndex cuts) : (Z i).card = (pieces i).length :=
    List.toFinset_card_of_nodup (pieceSimple i)
  have total : (∑ i, (Z i).card) = M :=
    (sum_congr rfl (fun i _ => lens i)).trans ((packedPathPiece_sum copiesSimple indexes cuts).trans copiesMass)
  obtain ⟨hD,dBudget,capD⟩ := three_dense_width hn dense
  obtain ⟨hL,lBudget,capL⟩ := three_dense_width hp long
  have vertices : 11*Fintype.card (ListVertexBlockIndex paths D) ≤ 14*n := by
    have newCount := blockIndex_card_precise (occurrences (fun i => (paths i).toFinset)) hD
    rw [sum_occurrences] at newCount
    have massBefore : (∑ i, (paths i).toFinset.card) = M :=
      sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (simple i))
    rw [massBefore] at newCount
    change Fintype.card (ListVertexBlockIndex paths D) ≤ n + M/D at newCount
    change 11*(M/D) ≤ 3*n at dBudget
    omega
  have families : 11*Fintype.card (PackedBlockIndex cuts) ≤ 17*p := by
    have base := baseRankCuts_card (fun i => (copies i).length) hL
    change selected.card ≤ (∑ i, (copies i).length)/L at base
    rw [copiesMass] at base
    have synced := synchronizedCuts_card selected (oppositeCutPartner indexes)
    change cuts.card ≤ 2*selected.card at synced
    change 11*(M/L) ≤ 3*p at lBudget
    rw [packedBlockIndex_card]
    change 11*(p+cuts.card) ≤ 17*p
    omega
  have containsBase : selected ⊆ cuts := by
    intro j h
    exact mem_union_left _ h
  have lengthCap (i : PackedBlockIndex cuts) : (pieces i).length ≤ L :=
    packedPathPiece_length copiesSimple indexes cuts i hL containsBase
  have degreeCap (v : ListVertexBlockIndex paths D) : (occurrences Z v).card ≤ D := by
    apply (packedPathPiece_degree_le indexes cuts v).trans
    simpa only [copies, splitListVertices_toFinset] using
      (splitVertices_degree (fun i => (paths i).toFinset) hD v)
  have piecesFree : localOrderAdmissible half k pieces := by
    cases half
    · exact packedPathPiece_fullFree_short copiesSimple three five indexes copiesFree selected
    · exact packedPathPiece_halfFree_short copiesSimple five indexes copiesFreeThree copiesFree selected
  exact frozen_cut_of_caps (retention := 119) pieces pieceSimple piecesFree
      (M := M) (n := n) (p := p) (D := D) (L := L)
      hn hp (by decide) (by decide) (by decide) (by decide) vertices families total.le
      (by
        change (14*17) * (119+2) * M ≤ 2 * (11*11) * 119 * (∑ i, (Z i).card)
        rw [total]) lengthCap degreeCap capD capL

/-- Preserve both original budgets and the frozen four-factor caps for
simple systems with full bridge exclusion through size five. -/
theorem regularization_list_balanced_full_short_dense {k : ℕ} (three : 3 ≤ k) (five : k ≤ 5) (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (ListBefore paths) k)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (dense : 3*Fintype.card V ≤ ∑ i, (paths i).length) (long : 3*Fintype.card I ≤ ∑ i, (paths i).length) :
    let n := Fintype.card V
    let p := Fintype.card I
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ 119*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_balanced_synchronized (half := false) three five paths simple
    (fun _ bound => free (bound.trans three)) free hn hp dense long

end OnlineReachabilityPreservers

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

/-- For full-bridge cutoffs three through five, keep the original vertex and
path budgets and the factor-four caps relative to the input averages. -/
theorem regularization_list_frozen_full_short {n p k : ℕ} (three : 3 ≤ k) (five : k ≤ 5)
    (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (ListBefore paths) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ 119*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases thin : M ≤ 3*max n p
  · obtain ⟨n',vn,p',ip,clean,nodup,legal,retained,upper,caps⟩ :=
      full_frozen_cleaning_sparse (k := k) hn hp dense long thin
    exact ⟨n',vn,p',ip,clean,nodup,legal,by omega,upper,caps⟩
  · have nHigh : 3*n ≤ M := (Nat.mul_le_mul_left 3 (le_max_left _ _)).trans (le_of_not_ge thin)
    have pHigh : 3*p ≤ M := (Nat.mul_le_mul_left 3 (le_max_right _ _)).trans (le_of_not_ge thin)
    simpa only [Fintype.card_fin] using
      (regularization_list_balanced_full_short_dense three five paths simple free
        (by simpa only [Fintype.card_fin] using hn) (by simpa only [Fintype.card_fin] using hp)
        (by simpa only [Fintype.card_fin] using nHigh) (by simpa only [Fintype.card_fin] using pHigh))

/-- With full exclusion through size three, the original budgets and all
four frozen caps hold for half-bridge cutoffs from three through five. -/
theorem regularization_list_frozen_half_short_of_full_three {n p k : ℕ}
    (three : 3 ≤ k) (five : k ≤ 5) (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (fullThree : BridgeFree (ListBefore paths) 3)
    (free : HalfBridgeFree (ListBefore paths) k)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) k ∧
      M ≤ 119*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  by_cases thin : M ≤ 3*max n p
  · obtain ⟨n',vn,p',ip,clean,nodup,legal,retained,upper,caps⟩ :=
      full_frozen_cleaning_sparse (k := k) hn hp dense long thin
    exact ⟨n',vn,p',ip,clean,nodup,legal.halfFree,by omega,upper,caps⟩
  · have nHigh : 3*n ≤ M := (Nat.mul_le_mul_left 3 (le_max_left _ _)).trans (le_of_not_ge thin)
    have pHigh : 3*p ≤ M := (Nat.mul_le_mul_left 3 (le_max_right _ _)).trans (le_of_not_ge thin)
    simpa only [Fintype.card_fin, localOrderAdmissible, Bool.true_eq, ↓reduceIte] using
      (regularization_list_balanced_synchronized (half := true) three five
        paths simple fullThree free (by simpa only [Fintype.card_fin] using hn)
        (by simpa only [Fintype.card_fin] using hp) (by simpa only [Fintype.card_fin] using nHigh)
        (by simpa only [Fintype.card_fin] using pHigh))

/-- The half-four instance allows nested reversals when full bridges
through size three are excluded. -/
theorem regularization_list_frozen_half_four_of_full_three {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (fullThree : BridgeFree (ListBefore paths) 3)
    (free : HalfBridgeFree (ListBefore paths) 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ HalfBridgeFree (ListBefore clean) 4 ∧
      M ≤ 119*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_half_short_of_full_three (by decide) (by decide)
    paths simple fullThree free hn hp dense long

/-- A maximizing family through size five has a full-bridge-free cleaned
witness with the original caps and at least one 119th of its mass. -/
theorem localOrderExtremal_frozen_full_short (n p : ℕ) {k : ℕ} (three : 3 ≤ k) (five : k ≤ 5) (hn : 0 < n) (hp : 0 < p) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ BridgeFree (ListBefore paths) k ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → BridgeFree (ListBefore other) k →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
        (∑ i, (paths i).length) ≤ 119*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧
        frozenListCaps n p (∑ i, (paths i).length) clean := by
  obtain ⟨paths,simple,legal,maximal,dense,long⟩ := localOrderExtremal_isDense n p k false hn hp
  exact ⟨paths,simple,legal,maximal,regularization_list_frozen_full_short three five paths simple legal hn hp dense long⟩


variable {V I : Type*} [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]

/-- Preserve both original budgets and the frozen four-factor caps for
simple systems with full bridge exclusion through size four. -/
theorem regularization_list_balanced_full_four_dense (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (ListBefore paths) 4)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (dense : 3*Fintype.card V ≤ ∑ i, (paths i).length) (long : 3*Fintype.card I ≤ ∑ i, (paths i).length) :
    let n := Fintype.card V
    let p := Fintype.card I
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) 4 ∧
      M ≤ 119*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_balanced_full_short_dense (by decide) (by decide) paths simple free hn hp dense long

/-- For full bridge exclusion through four, keep the original vertex and path
budgets and the factor-four caps relative to the input averages. -/
theorem regularization_list_frozen_full_four {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : BridgeFree (ListBefore paths) 4)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) 4 ∧
      M ≤ 119*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_full_short (by decide) (by decide) paths simple free hn hp dense long

/-- A maximizing family through size four has a full-bridge-free cleaned
witness with the original caps and at least one 119th of its mass. -/
theorem localOrderExtremal_frozen_full_four (n p : ℕ) (hn : 0 < n) (hp : 0 < p) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ BridgeFree (ListBefore paths) 4 ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → BridgeFree (ListBefore other) 4 →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) 4 ∧
        (∑ i, (paths i).length) ≤ 119*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧
        frozenListCaps n p (∑ i, (paths i).length) clean :=
  localOrderExtremal_frozen_full_short n p (by decide) (by decide) hn hp

private def pairedFrozenVertex {r w : ℕ} (i : Fin (r*2)) (j : Fin w) : Fin (r*w) :=
  let row := (finProdFinEquiv : Fin r × Fin 2 ≃ Fin (r*2)).symm i
  finProdFinEquiv (row.1, if row.2 = 0 then j else j.rev)

private def pairedFrozenRows (r w : ℕ) (i : Fin (r*2)) : List (Fin (r*w)) :=
  List.ofFn (pairedFrozenVertex i)

private theorem pairedFrozenVertex_injective {r w : ℕ} (i : Fin (r*2)) :
    Function.Injective (pairedFrozenVertex (w := w) i) := by
  intro x y same
  have order := congrArg Prod.snd (finProdFinEquiv.injective same)
  split at order
  · exact order
  · simpa only [Fin.rev_inj] using order

private theorem pairedFrozenRows_simple {r w : ℕ} (i : Fin (r*2)) :
    (pairedFrozenRows r w i).Nodup := List.nodup_ofFn.mpr (pairedFrozenVertex_injective i)

private theorem pairedFrozenRows_owner {r w : ℕ} {i : Fin (r*2)} {x : Fin (r*w)} :
    x ∈ pairedFrozenRows r w i ↔ (finProdFinEquiv.symm x).1 = (finProdFinEquiv.symm i).1 := by
  constructor
  · intro mem
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp mem
    simp [pairedFrozenVertex, Equiv.symm_apply_apply]
  · intro same
    let q : Fin r × Fin w := finProdFinEquiv.symm x
    let row : Fin r × Fin 2 := finProdFinEquiv.symm i
    change q.1 = row.1 at same
    let j := if row.2 = 0 then q.2 else q.2.rev
    refine List.mem_ofFn.mpr ⟨j,?_⟩
    apply finProdFinEquiv.symm.injective
    simp only [pairedFrozenVertex, Equiv.symm_apply_apply]
    change (row.1,if row.2 = 0 then j else j.rev) = q
    by_cases side : row.2 = 0
    · exact Prod.ext same.symm (by simp [j, side])
    · exact Prod.ext same.symm (by simp [j, side])

private theorem pairedFrozenRows_index {r w : ℕ} {i : Fin (r*2)} {x : Fin (r*w)}
    (present : x ∈ pairedFrozenRows r w i) :
    (pairedFrozenRows r w i).idxOf x =
      if (finProdFinEquiv.symm i).2 = 0 then ((finProdFinEquiv.symm x).2 : Fin w).val
      else ((finProdFinEquiv.symm x).2 : Fin w).rev.val := by
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp present
  have jFit : j.val < (pairedFrozenRows r w i).length := by
    simp only [pairedFrozenRows, List.length_ofFn]
    exact j.isLt
  have value : (pairedFrozenRows r w i)[j.val]'jFit = pairedFrozenVertex i j := List.getElem_ofFn jFit
  conv_lhs => rw [← value, (pairedFrozenRows_simple i).idxOf_getElem]
  by_cases side : (finProdFinEquiv.symm i).2 = 0 <;>
    simp only [pairedFrozenVertex, Equiv.symm_apply_apply, side, ite_true, ite_false, Fin.rev_rev]

private theorem pairedFrozenRows_degree (r w : ℕ) (x : Fin (r*w)) :
    (occurrences (fun i => (pairedFrozenRows r w i).toFinset) x).card = 2 := by
  let block : Fin r := (finProdFinEquiv.symm x).1
  let copies : Fin 2 ↪ Fin (r*2) :=
    ⟨fun side => finProdFinEquiv (block,side), fun a b same => congrArg Prod.snd (finProdFinEquiv.injective same)⟩
  have exactly : occurrences (fun i => (pairedFrozenRows r w i).toFinset) x = univ.map copies := by
    ext i
    simp only [mem_occurrences, List.mem_toFinset, pairedFrozenRows_owner, mem_map, mem_univ, true_and]
    constructor
    · intro same
      let q := (finProdFinEquiv : Fin r × Fin 2 ≃ Fin (r*2)).symm i
      have pair : (block,q.2) = q := Prod.ext same rfl
      exact ⟨q.2, (congrArg finProdFinEquiv pair).trans (finProdFinEquiv.apply_symm_apply i)⟩
    · rintro ⟨side,rfl⟩
      change block = ((finProdFinEquiv : Fin r × Fin 2 ≃ Fin (r*2)).symm
        (finProdFinEquiv (block,side))).1
      rw [Equiv.symm_apply_apply]
  rw [exactly, card_map, card_univ, Fintype.card_fin]

/-- Within each disjoint vertex block there are two opposite paths. A
bridge must stay in one block, and opposite paths cannot make a 2-bridge. -/
private theorem pairedFrozenRows_free (r w k : ℕ) : BridgeFree (ListBefore (pairedFrozenRows r w)) k := by
  intro q _
  refine ⟨fun b => ?_⟩
  let labels : Fin (r*2) ≃ Fin r × Fin 2 := finProdFinEquiv.symm
  let owner (x : Fin (r*w)) : Fin r := (finProdFinEquiv.symm x).1
  have step (i : Fin q.succ) : owner (b.vertex i.castSucc) = (labels (b.arc i)).1 ∧
      owner (b.vertex i.succ) = (labels (b.arc i)).1 :=
    ⟨pairedFrozenRows_owner.mp (b.arcStep i).1, pairedFrozenRows_owner.mp (b.arcStep i).2.1⟩
  have corners (i : Fin (q+2)) : owner (b.vertex i) = (labels b.river).1 := by
    refine Fin.induction ?_ (fun j previous => ?_) i
    · exact pairedFrozenRows_owner.mp b.riverStep.1
    · exact (step j).2.trans ((step j).1.symm.trans previous)
  have sameBlock (i : Fin (q+1)) : (labels (b.arc i)).1 = (labels b.river).1 :=
    (step i).1.symm.trans (corners i.castSucc)
  let paths (i : Option (Fin (q+1))) : Fin (r*2) := i.elim b.river b.arc
  have distinct : Function.Injective paths := by
    intro i j eq
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact (b.river_ne_arc j eq).elim
    | some i =>
      cases j with
      | none => exact (b.river_ne_arc i eq.symm).elim
      | some j => exact congrArg some (b.distinctArcs eq)
  have first (i : Option (Fin (q+1))) : (labels (paths i)).1 = (labels b.river).1 := by
    cases i with
    | none => rfl
    | some i => exact sameBlock i
  have two : Function.Injective (fun i : Option (Fin (q+1)) => (labels (paths i)).2) := by
    intro i j eq
    exact distinct (labels.injective (Prod.ext ((first i).trans (first j).symm) eq))
  have short := Fintype.card_le_of_injective _ two
  simp only [Fintype.card_option, Fintype.card_fin] at short
  have eq : q = 0 := by omega
  subst q
  let x := b.vertex 0
  let y := b.vertex (Fin.last 1)
  have river : ListBefore (pairedFrozenRows r w) b.river x y := b.riverStep
  have arc : ListBefore (pairedFrozenRows r w) (b.arc 0) x y := b.arcStep 0
  have riverEarlier := river.2.2
  have arcEarlier := arc.2.2
  rw [pairedFrozenRows_index river.1, pairedFrozenRows_index river.2.1] at riverEarlier
  rw [pairedFrozenRows_index arc.1, pairedFrozenRows_index arc.2.1] at arcEarlier
  change (if (labels b.river).2 = 0 then ((finProdFinEquiv.symm x).2 : Fin w).val else
    ((finProdFinEquiv.symm x).2 : Fin w).rev.val) <
    (if (labels b.river).2 = 0 then ((finProdFinEquiv.symm y).2 : Fin w).val else
      ((finProdFinEquiv.symm y).2 : Fin w).rev.val) at riverEarlier
  change (if (labels (b.arc 0)).2 = 0 then ((finProdFinEquiv.symm x).2 : Fin w).val else
    ((finProdFinEquiv.symm x).2 : Fin w).rev.val) <
    (if (labels (b.arc 0)).2 = 0 then ((finProdFinEquiv.symm y).2 : Fin w).val else
      ((finProdFinEquiv.symm y).2 : Fin w).rev.val) at arcEarlier
  have different : (labels b.river).2 ≠ (labels (b.arc 0)).2 :=
    fun equal => b.river_ne_arc 0 (labels.injective (Prod.ext (sameBlock 0).symm equal))
  let xj : Fin w := (finProdFinEquiv.symm x).2
  let yj : Fin w := (finProdFinEquiv.symm y).2
  have xFit := xj.isLt
  have yFit := yj.isLt
  by_cases side : (labels b.river).2 = 0 <;>
    by_cases other : (labels (b.arc 0)).2 = 0
  · exact different (side.trans other.symm)
  · simp only [side,other,ite_true,ite_false, Fin.val_rev] at riverEarlier arcEarlier
    change xj.val < yj.val at riverEarlier
    change w - (xj.val+1) < w - (yj.val+1) at arcEarlier
    omega
  · simp only [side,other,ite_true,ite_false, Fin.val_rev] at riverEarlier arcEarlier
    change w - (xj.val+1) < w - (yj.val+1) at riverEarlier
    change xj.val < yj.val at arcEarlier
    omega
  · have left : (labels b.river).2 = 1 := Fin.ext (by
      have bounds := (labels b.river).2.isLt
      have nz : (labels b.river).2.val ≠ 0 := fun same => side (Fin.ext same)
      omega)
    have right : (labels (b.arc 0)).2 = 1 := Fin.ext (by
      have bounds := (labels (b.arc 0)).2.isLt
      have nz : (labels (b.arc 0)).2.val ≠ 0 := fun same => other (Fin.ext same)
      omega)
    exact different (left.trans right.symm)

/-- Pairs of opposite paths meet the original caps in a bounded-density
range with at most as many paths as vertices. The witness excludes every
full bridge, so it also meets the half-bridge condition at any cutoff. -/
theorem frozen_cleaning_paired_rows {n p M k : ℕ} (pPos : 2 ≤ p) (ordered : p ≤ n)
    (massLower : 2*n ≤ M) (massUpper : M ≤ 8*n) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  have pPositive : 0 < p := by omega
  have nPositive : 0 < n := pPositive.trans_le ordered
  let b := p/2
  have bPos : 0 < b := Nat.div_pos pPos (by decide)
  have bLe : b ≤ n := (Nat.div_le_self p 2).trans ordered
  have bBudget : 2*b ≤ p := by
    have cap := Nat.div_mul_le_self p 2
    change b*2 ≤ p at cap
    omega
  have pLe : p ≤ 3*b := by
    have bound := Nat.lt_mul_div_succ p (by decide : 0 < 2)
    change p < 2*(b+1) at bound
    omega
  obtain ⟨width,rows,widthPos,rowsLe,taken,dbl,covers,slack⟩ := sparse_cleaning_block_dimensions bPos bLe
  let clean := pairedFrozenRows rows width
  have rowsWidth : (∑ i, (clean i).length) = 2*(rows*width) := by
    simp [clean, pairedFrozenRows]
    ring
  have pBound : rows*2 ≤ p := by omega
  have long : M ≤ 4*p*width := calc
    _ ≤ 8*n := massUpper
    _ ≤ 8*(b*width) := Nat.mul_le_mul_left _ covers
    _ = (4*(2*b))*width := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ bBudget)
  have short : width*p ≤ 4*M := calc
    _ ≤ width*(3*b) := Nat.mul_le_mul_left _ pLe
    _ = 3*(width*b) := by ring
    _ ≤ 3*(n+b-1) := Nat.mul_le_mul_left _ slack
    _ ≤ _ := by omega
  refine ⟨rows*width,taken,rows*2,pBound,clean,pairedFrozenRows_simple,pairedFrozenRows_free rows width k,?_,?_,?_⟩
  · rw [rowsWidth]
    omega
  · rw [rowsWidth]
    omega
  · constructor
    · intro x
      rw [pairedFrozenRows_degree]
      norm_num only [Nat.cast_ofNat]
      constructor
      · apply (div_le_iff₀ (by positivity : 0 < (4:ℝ)*n)).mpr
        exact_mod_cast (show M ≤ 2*(4*n) by omega)
      · apply (le_div_iff₀ (by positivity : 0 < (n:ℝ))).mpr
        exact_mod_cast (show 2*n ≤ 4*M by omega)
    · intro i
      have len : (clean i).length = width := by simp [clean, pairedFrozenRows]
      rw [len]
      constructor
      · apply (div_le_iff₀ (by positivity : 0 < (4:ℝ)*p)).mpr
        rw [mul_comm (width : ℝ)]
        exact_mod_cast long
      · exact (le_div_iff₀ (by positivity : 0 < (p:ℝ))).mpr (by exact_mod_cast short)

/-- Under the smaller path budget, the sparse witnesses and paired rows
cover every incidence mass from the vertex count through eight times it. -/
theorem frozen_cleaning_at_most_eight_per_vertex {n p M k : ℕ} (hp : 0 < p) (ordered : p ≤ n)
    (massLower : n ≤ M) (massUpper : M ≤ 8*n) (fits : M ≤ n*p) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ BridgeFree (ListBefore clean) k ∧
      M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  by_cases low : M ≤ 3*n
  · have sparse : M ≤ 3*max n p := by simpa only [max_eq_left ordered] using low
    obtain ⟨n',v,p',i,clean,simple,free,retained,upper,caps⟩ :=
      full_frozen_cleaning_sparse (k := k) (hp.trans_le ordered) hp massLower (ordered.trans massLower) sparse
    exact ⟨n',v,p',i,clean,simple,free,by omega,upper,caps⟩
  · have two : 2 ≤ p := by
      by_contra! small
      have only : p = 1 := by omega
      rw [only,Nat.mul_one] at fits
      omega
    exact frozen_cleaning_paired_rows two ordered (by omega) massUpper

/-- For at most eight paths and a vertex budget at least as large, an
unrestricted maximum has a constant-mass cleaned witness with the frozen
caps in either mode at every cutoff. -/
theorem localOrderExtremal_frozen_up_to_eight_paths (n p k : ℕ) (half : Bool)
    (hp : 0 < p) (ordered : p ≤ n) (few : p ≤ 8) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        M ≤ 8*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths,simple,free,maximal,dense,_⟩ :=
    localOrderExtremal_isDense n p k half (hp.trans_le ordered) hp
  have fit : (∑ i, (paths i).length) ≤ n*p := calc
    _ ≤ ∑ _ : Fin p, n := by
      apply sum_le_sum
      intro i _
      rw [← List.toFinset_card_of_nodup (simple i)]
      simpa only [Fintype.card_fin] using (Finset.card_le_univ (paths i).toFinset)
    _ = n*p := by simp [Nat.mul_comm]
  have low : (∑ i, (paths i).length) ≤ 8*n :=
    fit.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left n few)
  obtain ⟨n',v,p',i,clean,nodup,legal,mass,upper,caps⟩ :=
    frozen_cleaning_at_most_eight_per_vertex (k := k) hp ordered dense low fit
  refine ⟨paths,simple,free,maximal,n',v,p',i,clean,nodup,?_,mass,upper,caps⟩
  cases half
  · exact legal
  · intro j small b _
    exact (legal small).false b

/-- Split with the original width caps when a retained subsystem has
sufficient mass, and the bridge condition survives those particular splits. -/
theorem regularization_list_frozen_after_width_blocks_of_mass {half : Bool} {k n p M retention : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k (listRegularizedPaths paths (4*M/n) (4*M/p)))
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (upper : (∑ i, (paths i).length) ≤ M)
    (lower : 8*(retention+2)*M ≤ 9*retention*(∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let K := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let pieces := listRegularizedPaths paths D L
  obtain ⟨widthD,trimD,_⟩ := four_average_width hn dense
  obtain ⟨widthL,trimL,_⟩ := four_average_width hp long
  change 0 < D at widthD
  change 0 < L at widthL
  obtain ⟨rawV,rawI⟩ := regularization_list_counts paths simple widthD widthL
  have vCap : 3*Fintype.card (ListVertexBlockIndex paths D) ≤ 4*n := by
    have less : K/D ≤ M/D := Nat.div_le_div_right upper
    simp only [Fintype.card_fin] at rawV
    change 3*(M/D) ≤ n at trimD
    change Fintype.card (ListVertexBlockIndex paths D) ≤ n+K/D at rawV
    omega
  have iCap : 3*Fintype.card (ListBlockIndex (splitListVertices paths D) L) ≤ 4*p := by
    have less : K/L ≤ M/L := Nat.div_le_div_right upper
    simp only [Fintype.card_fin] at rawI
    change 3*(M/L) ≤ p at trimL
    change Fintype.card (ListBlockIndex (splitListVertices paths D) L) ≤ p+K/L at rawI
    omega
  obtain ⟨mass,length,degree⟩ := regularization_list_mass_caps paths simple D L widthD widthL
  exact regularization_list_frozen_after_caps_with_room_of_mass pieces
    (listRegularizedPaths_simple paths simple D L) allowed
    hn hp dense long vCap iCap length degree (mass.trans_le upper) (by rw [mass]; exact lower)

private theorem large_average_width_budget {M q : ℕ} (hq : 0 < q) (large : 8*q ≤ M) :
    31*(M/(4*M/q)) ≤ 8*q := by
  let width := 4*M/q
  obtain ⟨widthPos,_,_⟩ := four_average_width hq (show q ≤ M by omega)
  change 0 < width at widthPos
  have floor := Nat.lt_mul_div_succ (4*M) hq
  change 4*M < q*(width+1) at floor
  rw [Nat.mul_succ] at floor
  have lower : 31*M ≤ 8*(q*width) := by omega
  have product : (31*(M/width))*width ≤ (8*q)*width := calc
    _ = 31*((M/width)*width) := by ring
    _ ≤ 31*M := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
    _ ≤ 8*(q*width) := lower
    _ = _ := by ring
  exact (Nat.mul_le_mul_right_iff widthPos).mp product

/-- At larger averages the actual width blocks need at most 39/31 of each
budget. If pruning loses at most one eighth of the original mass, the
frozen peeling step still retains at least one thirty-second. -/
theorem regularization_list_frozen_after_large_width_blocks {half : Bool} {k n p M : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k (listRegularizedPaths paths (4*M/n) (4*M/p)))
    (hn : 0 < n) (hp : 0 < p) (dense : 8*n ≤ M) (long : 8*p ≤ M)
    (upper : (∑ i, (paths i).length) ≤ M) (lower : 7*M ≤ 8*(∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 32*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let K := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let pieces := listRegularizedPaths paths D L
  obtain ⟨widthD,_,capD⟩ := four_average_width hn (show n ≤ M by omega)
  obtain ⟨widthL,_,capL⟩ := four_average_width hp (show p ≤ M by omega)
  change 0 < D at widthD
  change 0 < L at widthL
  obtain ⟨rawV,rawI⟩ := regularization_list_counts paths simple widthD widthL
  have vCap : 31*Fintype.card (ListVertexBlockIndex paths D) ≤ 39*n := by
    have less : K/D ≤ M/D := Nat.div_le_div_right upper
    have short : 31*(M/D) ≤ 8*n := large_average_width_budget hn dense
    simp only [Fintype.card_fin] at rawV
    change Fintype.card (ListVertexBlockIndex paths D) ≤ n+K/D at rawV
    omega
  have iCap : 31*Fintype.card (ListBlockIndex (splitListVertices paths D) L) ≤ 39*p := by
    have less : K/L ≤ M/L := Nat.div_le_div_right upper
    have short : 31*(M/L) ≤ 8*p := large_average_width_budget hp long
    simp only [Fintype.card_fin] at rawI
    change Fintype.card (ListBlockIndex (splitListVertices paths D) L) ≤ p+K/L at rawI
    omega
  obtain ⟨mass,length,degree⟩ := regularization_list_mass_caps paths simple D L widthD widthL
  have keptSimple := listRegularizedPaths_simple paths simple D L
  have count : (∑ i, (pieces i).toFinset.card) = K :=
    (sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (keptSimple i))).trans mass
  exact frozen_cut_of_caps pieces keptSimple allowed
    (M := M) (D := D) (L := L) (retention := 32)
    (vNum := 31) (vDen := 39) (pNum := 31) (pDen := 39)
    hn hp (by decide) (by decide) (by decide) (by decide) vCap iCap (count.trans_le upper)
    (by
      change 39*39*(32+2)*M ≤ 2*(31*31)*32*(∑ i, (pieces i).toFinset.card)
      rw [count]
      change 7*M ≤ 8*K at lower
      omega)
    length degree capD capL

/-- A rectangle with separate vertex and path ratios can absorb some
earlier loss while trimming and peeling at the original averages. -/
theorem regularization_list_frozen_after_caps_with_ratios_of_mass {half : Bool}
    {k n p M retention vNum vDen pNum pDen : ℕ}
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vPos : 0 < vDen) (pPos : 0 < pDen) (vRatio : vNum ≤ vDen) (pRatio : pNum ≤ pDen)
    (vertices : vNum * Fintype.card V ≤ vDen * n) (families : pNum * Fintype.card I ≤ pDen * p)
    (lengthCap : ∀ i, (paths i).length ≤ 4 * M / p)
    (degreeCap : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ 4 * M / n)
    (mass : (∑ i, (paths i).length) ≤ M)
    (enough : (vDen * pDen) * (retention + 2) * M ≤
      2 * (vNum * pNum) * retention * (∑ i, (paths i).length)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨_, _, capD⟩ := four_average_width hn dense
  obtain ⟨_, _, capL⟩ := four_average_width hp long
  have total : (∑ i, (paths i).toFinset.card) = ∑ i, (paths i).length :=
    sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (simple i))
  exact frozen_cut_of_caps paths simple allowed hn hp vPos pPos vRatio pRatio vertices families
    (total.trans_le mass) (by rw [total]; exact enough) lengthCap degreeCap capD capL

/-- Fit upper-capped pieces of unchanged mass within the original budgets
using separate bounds for the two expanded supports. -/
theorem regularization_list_frozen_after_caps_with_ratios {half : Bool}
    {k n p M retention vNum vDen pNum pDen : ℕ}
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup) (allowed : localOrderAdmissible half k paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M)
    (vPos : 0 < vDen) (pPos : 0 < pDen) (vRatio : vNum ≤ vDen) (pRatio : pNum ≤ pDen)
    (vertices : vNum * Fintype.card V ≤ vDen * n) (families : pNum * Fintype.card I ≤ pDen * p)
    (lengthCap : ∀ i, (paths i).length ≤ 4 * M / p)
    (degreeCap : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ 4 * M / n)
    (mass : (∑ i, (paths i).length) = M)
    (enough : (vDen * pDen) * (retention + 2) ≤ 2 * (vNum * pNum) * retention) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention * (∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_after_caps_with_ratios_of_mass paths simple allowed hn hp dense long vPos pPos
    vRatio pRatio vertices families lengthCap degreeCap mass.le
    (by rw [mass]; exact Nat.mul_le_mul_right M enough)

/-- If all pieces fit in the path budget, only the vertex blocks need
trimming. Peeling pays for the actual number of pieces. -/
theorem regularization_list_frozen_trim_vertices_quadratic {half : Bool} {k n p M retention : ℕ}
    (pieces : I → List V) (simple : ∀ i, (pieces i).Nodup) (allowed : localOrderAdmissible half k pieces)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ M) (long : p ≤ M) (positive : 0 < retention)
    (full : Finset V) (filled : ∀ v ∈ full, (occurrences (fun i => (pieces i).toFinset) v).card = 4*M/n)
    (rest : (univ \ full).card ≤ n) (pathsCap : Fintype.card I ≤ p)
    (lengthCap : ∀ i, (pieces i).length ≤ 4*M/p)
    (degreeCap : ∀ v, (occurrences (fun i => (pieces i).toFinset) v).card ≤ 4*M/n)
    (mass : (∑ i, (pieces i).length) ≤ M)
    (enough : let K : ℝ := ((∑ i, (pieces i).length : ℕ) : ℝ)
      (M:ℝ)/retention ≤ K-K^2/(12*M)-(M:ℝ)/4-((M:ℝ)/(4*(p:ℝ)))*(Fintype.card I)) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ retention*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let D := 4*M/n
  let Z (i : I) := (pieces i).toFinset
  let K := ∑ i, (pieces i).length
  let all := (univ : Finset I)
  obtain ⟨width,_,capD⟩ := four_average_width hn dense
  obtain ⟨_,_,capL⟩ := four_average_width hp long
  have capacity : 3*M ≤ D*n := by
    have bound := Nat.lt_mul_div_succ (4*M) hn
    change 4*M < n*(D+1) at bound
    rw [Nat.mul_succ,Nat.mul_comm n D] at bound
    omega
  have counted : (∑ i, (Z i).card) = K := sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (simple i))
  have fits : (∑ i, (Z i).card) ≤ D*n := by rw [counted]; omega
  obtain ⟨A,capA,loss,trim,crop⟩ := trim_full_vertex_blocks_quadratic Z full width filled rest fits
  rw [counted] at trim crop
  have trim' : 12*M*loss ≤ K^2 := calc
    _ = (4*(3*M))*loss := by ring
    _ ≤ (4*(D*n))*loss := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ capacity)
    _ ≤ _ := trim
  have massPos : (0:ℝ) < M := by exact_mod_cast hn.trans_le dense
  have lossLe : (loss:ℝ) ≤ (K:ℝ)^2/(12*(M:ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [mul_comm]
    exact_mod_cast trim'
  let d : ℝ := (M:ℝ)/(4*(n:ℝ))
  let l : ℝ := (M:ℝ)/(4*(p:ℝ))
  have d0 : 0 ≤ d := by dsimp [d]; positivity
  have l0 : 0 ≤ l := by dsimp [l]; positivity
  have bigD : d*(n:ℝ) = (M:ℝ)/4 := by
    have n0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    dsimp [d]
    field_simp [n0]
  have vertexLoss : d*(A.card:ℝ) ≤ (M:ℝ)/4 :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr capA) d0).trans_eq bigD
  have realCrop : ((∑ i : all, (rectanglePaths Z A all i).card : ℕ) : ℝ)+(loss:ℝ) = K := by
    exact_mod_cast crop
  obtain ⟨C,cSub,B,bSub,lower,minD,minL⟩ := rectanglePaths_prune Z A all d0 l0
  have lower' : (M:ℝ)/retention ≤ ((∑ i : B, (rectanglePaths Z C B i).card : ℕ) : ℝ) := by
    refine enough.trans ?_
    have piecesCount : (all.card:ℝ) = Fintype.card I := by rw [card_univ]
    rw [piecesCount] at lower
    change (K:ℝ)-(K:ℝ)^2/(12*(M:ℝ))-(M:ℝ)/4-l*(Fintype.card I:ℝ) ≤ _
    linarith
  have retained : M ≤ retention*(∑ i : B, (rectanglePaths Z C B i).card) := by
    have rPos : (0:ℝ) < retention := by exact_mod_cast positive
    have scaled := (div_le_iff₀ rPos).mp lower'
    rw [mul_comm] at scaled
    exact_mod_cast scaled
  have bCap : B.card ≤ p := (card_le_card bSub).trans (by simpa [all] using pathsCap)
  exact finish_frozen_rectangle pieces simple allowed C B ((card_le_card cSub).trans capA) bCap retained
    (counted.trans_le mass) minD minL lengthCap degreeCap capD capL

end OnlineReachabilityPreservers
