import OnlineReachabilityPreservers.LocalOrderExtremal

/-! Cleaning locally ordered simple paths relative to the output averages. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "ListBefore" => SourceAudit.BeforeIn

/-- Each degree and length is within a factor of four of the corresponding
average of the displayed family. -/
def listOutputAverageCaps {V I : Type*} [DecidableEq V] [Fintype V] [Fintype I]
    (paths : I → List V) : Prop :=
  let M : ℕ := ∑ i, (paths i).length
  let d : ℝ := (M : ℝ) / Fintype.card V
  let l : ℝ := (M : ℝ) / Fintype.card I
  (∀ v, d/4 ≤ (occurrences (fun i => (paths i).toFinset) v).card ∧
    ((occurrences (fun i => (paths i).toFinset) v).card : ℝ) ≤ 4*d) ∧
  (∀ i, l/4 ≤ (paths i).length ∧ ((paths i).length : ℝ) ≤ 4*l)

private theorem average_caps_of_width {X : Type*} [Fintype X] (values : X → ℕ) (w : ℝ)
    (bounds : ∀ x, w/4 ≤ values x ∧ (values x : ℝ) ≤ w) (x : X) :
    let average : ℝ := ((∑ y, values y : ℕ) : ℝ) / Fintype.card X
    average/4 ≤ values x ∧ (values x : ℝ) ≤ 4*average := by
  let N := Fintype.card X
  have positive : (0 : ℝ) < N := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨x⟩)
  have lower : (w/4)*N ≤ ((∑ y, values y : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    calc
      _ = ∑ _y : X, w/4 := by simp [nsmul_eq_mul, N, mul_comm]
      _ ≤ _ := sum_le_sum (fun y _ => (bounds y).1)
  have upper : ((∑ y, values y : ℕ) : ℝ) ≤ w*N := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ _y : X, w := sum_le_sum (fun y _ => (bounds y).2)
      _ = _ := by simp [nsmul_eq_mul, N, mul_comm]
  have avgLower := (le_div_iff₀ positive).mpr lower
  have avgUpper := (div_le_iff₀ positive).mpr upper
  exact ⟨by linarith only [avgUpper, (bounds x).1], by linarith only [avgLower, (bounds x).2]⟩

private theorem listOutputAverageCaps_of_widths {V I : Type*} [DecidableEq V] [Fintype V] [Fintype I]
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup) (D L : ℝ)
    (degree : ∀ v, D/4 ≤ (occurrences (fun i => (paths i).toFinset) v).card ∧
      ((occurrences (fun i => (paths i).toFinset) v).card : ℝ) ≤ D)
    (length : ∀ i, L/4 ≤ (paths i).length ∧ ((paths i).length : ℝ) ≤ L) :
    listOutputAverageCaps paths := by
  have degreeMass : (∑ v, (occurrences (fun i => (paths i).toFinset) v).card) = ∑ i, (paths i).length := by
    rw [sum_occurrences]
    exact sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (simple i))
  refine ⟨?_, average_caps_of_width (fun i => (paths i).length) L length⟩
  intro v
  simpa only [degreeMass] using
    average_caps_of_width (fun v => (occurrences (fun i => (paths i).toFinset) v).card) D degree v

/-- A width at twice the average leaves room for copies of a quarter-sized
support and limits the loss from pruning below a quarter of that width. -/
private theorem outputAverageWidth {M q : ℕ} (hq : 0 < q) (dense : q ≤ M) :
    let w := (2*M)/q
    2 ≤ w ∧ q/4 + M/w ≤ q ∧ 2*w*(q/4+M/w) ≤ 3*M := by
  let w := (2*M)/q
  have h2 : 2 ≤ w := (Nat.le_div_iff_mul_le hq).mpr (Nat.mul_le_mul_left 2 dense)
  have hw : 0 < w := by omega
  have next := Nat.lt_mul_div_succ (2*M) hq
  change 2*M < q*(w+1) at next
  have widthProduct : q*w ≤ 2*M := by
    simpa only [w,Nat.mul_comm] using Nat.div_mul_le_self (2*M) q
  rw [Nat.mul_succ] at next
  have lower : 4*M ≤ (3*q)*w := by
    have twice : 2*q ≤ q*w := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left q h2
    nlinarith only [next, twice]
  have copies : 4*(M/w) ≤ 3*q := by
    apply Nat.le_of_mul_le_mul_right _ hw
    calc
      _ = 4*((M/w)*w) := by ring
      _ ≤ 4*M := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ ≤ _ := lower
  have quarter : 4*(q/4) ≤ q := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self q 4
  have left : 4*w*(q/4) ≤ 2*M := by
    calc
      _ = (4*(q/4))*w := by ring
      _ ≤ q*w := Nat.mul_le_mul_right w quarter
      _ ≤ _ := widthProduct
  have right : 2*w*(M/w) ≤ 2*M := by
    simpa only [Nat.mul_assoc,Nat.mul_comm w (M/w)] using
      Nat.mul_le_mul_left 2 (Nat.div_mul_le_self M w)
  change 2 ≤ w ∧ q/4 + M/w ≤ q ∧ 2*w*(q/4+M/w) ≤ 3*M
  refine ⟨h2,by omega,?_⟩
  rw [Nat.mul_add]
  have left' : 2*w*(q/4) ≤ M := by nlinarith only [left]
  omega

/-- Relabel both finite ordered supports by their canonical finite ordinals. -/
def relabelListPathsFin {V I : Type*} [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]
    (paths : I → List V) (i : Fin (Fintype.card I)) : List (Fin (Fintype.card V)) :=
  let vIso : Fin (Fintype.card V) ≃o V := Fintype.orderIsoFinOfCardEq V rfl
  let iIso : Fin (Fintype.card I) ≃o I := Fintype.orderIsoFinOfCardEq I rfl
  (paths (iIso i)).map vIso.symm

/-- Finite ordinal relabeling preserves mass, degrees, lengths, and bridge exclusion. -/
theorem relabelListPathsFin_spec {V I : Type*}
    [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I] (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup) {half : Bool} {k : ℕ} (allowed : localOrderAdmissible half k paths) :
    let vIso : Fin (Fintype.card V) ≃o V := Fintype.orderIsoFinOfCardEq V rfl
    let iIso : Fin (Fintype.card I) ≃o I := Fintype.orderIsoFinOfCardEq I rfl
    let clean := relabelListPathsFin paths
    (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      (∑ i, (clean i).length) = (∑ i, (paths i).length) ∧
      (∀ v, (occurrences (fun i => (clean i).toFinset) v).card =
        (occurrences (fun i => (paths i).toFinset) (vIso v)).card) ∧
      (∀ i, (clean i).length = (paths (iIso i)).length) := by
  let vIso : Fin (Fintype.card V) ≃o V := Fintype.orderIsoFinOfCardEq V rfl
  let iIso : Fin (Fintype.card I) ≃o I := Fintype.orderIsoFinOfCardEq I rfl
  let clean := relabelListPathsFin paths
  have project : (fun i => (clean i).map vIso) = fun i => paths (iIso i) := by
    funext i
    simp [clean, relabelListPathsFin, vIso, iIso, List.map_map, Function.comp_def]
  have steps {i u v} (step : ListBefore clean i u v) : ListBefore paths (iIso i) (vIso u) (vIso v) := by
    have old := listBefore_map vIso (by rw [congrFun project i]; exact simple _) step
    rw [project] at old
    exact old
  have noBridge : localOrderAdmissible half k clean := by
    cases half
    · intro k hk
      exact ⟨fun b => (allowed hk).false ((b.mapVertices vIso vIso.injective
        (fun _ _ _ h => steps h)).mapPaths iIso iIso.injective (fun _ _ _ h => h))⟩
    · intro k hk b earlier
      exact allowed hk ((b.mapVertices vIso vIso.injective (fun _ _ _ h => steps h)).mapPaths
        iIso iIso.injective (fun _ _ _ h => h)) (iIso.strictMono earlier)
  have mass : (∑ i, (clean i).length) = ∑ i, (paths i).length := by
    simp only [clean, relabelListPathsFin, List.length_map]
    exact Equiv.sum_comp iIso.toEquiv (fun i => (paths i).length)
  have degrees (v : Fin (Fintype.card V)) :
      (occurrences (fun i => (clean i).toFinset) v).card =
        (occurrences (fun i => (paths i).toFinset) (vIso v)).card := by
    have eq : occurrences (fun i => (clean i).toFinset) v =
        (occurrences (fun i => (paths i).toFinset) (vIso v)).map iIso.symm.toEquiv.toEmbedding := by
      ext j
      simp only [mem_map_equiv, mem_occurrences, List.mem_toFinset]
      change v ∈ clean j ↔ vIso v ∈ paths (iIso j)
      constructor
      · intro member
        change v ∈ (paths (iIso j)).map vIso.symm at member
        obtain ⟨a, inside, equal⟩ := List.mem_map.mp member
        have original : a = vIso v := by simpa only [OrderIso.apply_symm_apply] using congrArg vIso equal
        exact original ▸ inside
      · exact fun inside => List.mem_map.mpr ⟨vIso v, inside, vIso.symm_apply_apply v⟩
    rw [eq, card_map]
  exact ⟨fun i => (simple (iIso i)).map vIso.symm.injective, noBridge, mass, degrees,
    fun i => by simp only [relabelListPathsFin, List.length_map]⟩

private theorem listOutputAverageCaps_relabel {V I : Type*}
    [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I] (paths : I → List V)
    (simple : ∀ i, (paths i).Nodup) (half : Bool) (allowed : localOrderAdmissible half 4 paths)
    (caps : listOutputAverageCaps paths) :
    ∃ clean : Fin (Fintype.card I) → List (Fin (Fintype.card V)),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half 4 clean ∧
      (∑ i, (clean i).length) = (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  let vIso : Fin (Fintype.card V) ≃o V := Fintype.orderIsoFinOfCardEq V rfl
  let iIso : Fin (Fintype.card I) ≃o I := Fintype.orderIsoFinOfCardEq I rfl
  obtain ⟨cleanSimple, cleanLegal, mass, degrees, lengths⟩ := relabelListPathsFin_spec paths simple allowed
  refine ⟨relabelListPathsFin paths, cleanSimple, cleanLegal, mass, ?_⟩
  unfold listOutputAverageCaps at caps ⊢
  simp only [mass, Fintype.card_fin]
  exact ⟨fun v => by rw [degrees]; exact caps.1 (vIso v),
    fun i => by rw [lengths]; exact caps.2 (iIso i)⟩

private theorem restrictListPaths_mass_eq {V I : Type*} [LinearOrder V]
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup) (A : Finset V) (B : Finset I) :
    (∑ i : B, (restrictListPaths paths A B i).length) =
      ∑ i : B, (rectanglePaths (fun i => (paths i).toFinset) A B i).card := by
  apply sum_congr rfl
  intro i _
  have nodup : (restrictListPaths paths A B i).Nodup := restrictListPath_nodup (simple i.val) A
  rw [← List.toFinset_card_of_nodup nodup, restrictListPaths_toFinset]

private theorem clean_quarter_support {V I : Type*}
    [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]
    (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (half : Bool) (allowed : localOrderAdmissible half 4 paths)
    {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (vertices : Fintype.card V ≤ n/4) (indices : Fintype.card I ≤ p/4)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half 4 clean ∧
      (∑ i, (paths i).length) ≤ 4*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  let M := ∑ i, (paths i).length
  let D := (2*M)/n
  let L := (2*M)/p
  let W := ListVertexBlockIndex paths D
  let J := ListBlockIndex (splitListVertices paths D) L
  let after := listRegularizedPaths paths D L
  let Z (i : J) := (after i).toFinset
  obtain ⟨twoD, budgetV, lossV⟩ := outputAverageWidth hn dense
  obtain ⟨twoL, budgetI, lossI⟩ := outputAverageWidth hp long
  have hD : 0 < D := lt_of_lt_of_le (by decide : 0 < 2) twoD
  have hL : 0 < L := lt_of_lt_of_le (by decide : 0 < 2) twoL
  obtain ⟨rawV, rawI⟩ := regularization_list_counts paths simple hD hL
  have countV : Fintype.card W ≤ n/4 + M/D := rawV.trans (Nat.add_le_add_right vertices _)
  have countI : Fintype.card J ≤ p/4 + M/L := rawI.trans (Nat.add_le_add_right indices _)
  have vSize : Fintype.card W ≤ n := countV.trans budgetV
  have iSize : Fintype.card J ≤ p := countI.trans budgetI
  have vLoss : (D : ℝ)/4 * Fintype.card W ≤ 3*(M : ℝ)/8 := by
    have nat : 2*D*Fintype.card W ≤ 3*M := (Nat.mul_le_mul_left (2*D) countV).trans lossV
    have real : 2*(D : ℝ)*Fintype.card W ≤ 3*(M : ℝ) := by exact_mod_cast nat
    linarith only [real]
  have iLoss : (L : ℝ)/4 * Fintype.card J ≤ 3*(M : ℝ)/8 := by
    have nat : 2*L*Fintype.card J ≤ 3*M := (Nat.mul_le_mul_left (2*L) countI).trans lossI
    have real : 2*(L : ℝ)*Fintype.card J ≤ 3*(M : ℝ) := by exact_mod_cast nat
    linarith only [real]
  obtain ⟨afterMass, length, degree⟩ := regularization_list_mass_caps paths simple D L hD hL
  have afterSimple (i : J) : (after i).Nodup := listRegularizedPaths_simple paths simple D L i
  have total : (∑ i, (Z i).card) = M :=
    (sum_congr rfl (fun i _ => List.toFinset_card_of_nodup (afterSimple i))).trans afterMass
  obtain ⟨A,_,B,_,keep,minDegree,minLength⟩ := rectanglePaths_prune Z (univ : Finset W) (univ : Finset J)
    (show (0:ℝ) ≤ (D:ℝ)/4 by positivity) (show (0:ℝ) ≤ (L:ℝ)/4 by positivity)
  simp only [rectanglePaths_univ_mass, total, card_univ] at keep
  let restricted := restrictListPaths after A B
  have restrictedSimple (i : B) : (restricted i).Nodup := restrictListPath_nodup (afterSimple i.val) A
  have marks : (fun i => (restricted i).toFinset) = rectanglePaths Z A B :=
    funext (restrictListPaths_toFinset after A B)
  have mass : (∑ i : B, (restricted i).length) = ∑ i : B, (rectanglePaths Z A B i).card :=
    restrictListPaths_mass_eq after afterSimple A B
  have rowLength (i : B) : (restricted i).length = (rectanglePaths Z A B i).card :=
    (List.toFinset_card_of_nodup (restrictedSimple i)).symm.trans (congrArg Finset.card (congrFun marks i))
  have cap : listOutputAverageCaps restricted := by
    apply listOutputAverageCaps_of_widths restricted restrictedSimple D L
    · intro v
      rw [marks]
      exact ⟨minDegree v, Nat.cast_le.mpr ((rectanglePaths_degree_le Z A B v).trans (degree v.val))⟩
    · intro i
      have bound : (restricted i).length ≤ L := by
        rw [show (restricted i).length = ((after i.val).toFinset ∩ A).card from
          restrictListPath_length (afterSimple i.val) A]
        exact (card_le_card inter_subset_left).trans ((List.toFinset_card_le _).trans (length i.val))
      exact ⟨by rw [rowLength]; exact minLength i, Nat.cast_le.mpr bound⟩
  have legal : localOrderAdmissible half 4 restricted := by
    cases half
    · exact restrictListPaths_fullFree afterSimple (listRegularizedPaths_fullFree simple unique allowed D L) A B
    · exact restrictListPaths_halfFree afterSimple (listRegularizedPaths_halfFree simple unique allowed D L) A B
  obtain ⟨clean,cleanSimple,cleanLegal,cleanMass,cleanCaps⟩ :=
    listOutputAverageCaps_relabel restricted restrictedSimple half legal cap
  refine ⟨Fintype.card A, ?_, Fintype.card B, ?_, clean, cleanSimple, cleanLegal, ?_, ?_, cleanCaps⟩
  · simpa only [Fintype.card_coe] using (card_le_univ A).trans vSize
  · simpa only [Fintype.card_coe] using (card_le_univ B).trans iSize
  · rw [cleanMass, mass]
    exact_mod_cast (show (M : ℝ) ≤ 4*((∑ i : B, (rectanglePaths Z A B i).card : ℕ) : ℝ) by
      linarith only [vLoss, iLoss, keep])
  · rw [cleanMass, mass]
    exact (rectanglePaths_mass_le Z A B).trans_eq total

private theorem clean_linear_mass {n p M : ℕ} (half : Bool) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ M) (long : p ≤ M) (mass : M ≤ 392 * max n p) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half 4 clean ∧
      M ≤ 392*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ listOutputAverageCaps clean := by
  by_cases nle : n ≤ p
  · let clean : Fin p → List (Fin 1) := fun _ => [0]
    have free : BridgeFree (ListBefore clean) 4 := by
      intro k _
      exact ⟨fun b => listBefore_ne b.riverStep (Subsingleton.elim _ _)⟩
    have allowed : localOrderAdmissible half 4 clean := by cases half; exacts [free, free.halfFree]
    have simple (i : Fin p) : (clean i).Nodup := by simp [clean]
    have length : (∑ i, (clean i).length) = p := by simp [clean]
    have degree (v : Fin 1) : (occurrences (fun i => (clean i).toFinset) v).card = p := by
      have eq : v = 0 := Subsingleton.elim _ _
      simp [occurrences, clean, eq]
    refine ⟨1,hn,p,le_rfl,clean,simple,allowed,?_,by rw [length]; exact long,?_⟩
    · simpa only [length, max_eq_right nle] using mass
    · apply listOutputAverageCaps_of_widths clean simple (p:ℝ) 1
      · intro v
        rw [degree]
        exact ⟨by linarith only [Nat.cast_nonneg (α := ℝ) p], le_rfl⟩
      · intro i
        norm_num [clean]
  · let clean : Fin 1 → List (Fin n) := fun _ => List.finRange n
    have free : BridgeFree (ListBefore clean) 4 := by
      intro k _
      exact ⟨fun b => b.river_ne_arc 0 (Subsingleton.elim _ _)⟩
    have allowed : localOrderAdmissible half 4 clean := by cases half; exacts [free, free.halfFree]
    have simple (i : Fin 1) : (clean i).Nodup := List.nodup_finRange _
    have length : (∑ i, (clean i).length) = n := by simp [clean]
    have degree (v : Fin n) : (occurrences (fun i => (clean i).toFinset) v).card = 1 := by
      simp [occurrences, clean]
    refine ⟨n,le_rfl,1,hp,clean,simple,allowed,?_,by rw [length]; exact dense,?_⟩
    · simpa only [length, max_eq_left (le_of_not_ge nle)] using mass
    · apply listOutputAverageCaps_of_widths clean simple 1 (n:ℝ)
      · intro v
        norm_num [degree v]
      · intro i
        change (n : ℝ)/4 ≤ ((List.finRange n).length : ℝ) ∧ _
        rw [List.length_finRange]
        exact ⟨by linarith only [Nat.cast_nonneg (α := ℝ) n], le_rfl⟩

/-- Through size four, retain a constant fraction of the mass within both original
budgets. Each degree and length is within a factor of four of its output average. -/
theorem regularization_list_output_average_four {n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (half : Bool) (allowed : localOrderAdmissible half 4 paths)
    (hn : 0 < n) (hp : 0 < p) (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) :
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half 4 clean ∧
      (∑ i, (paths i).length) ≤ 392*(∑ i, (clean i).length) ∧
      (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  let M := ∑ i, (paths i).length
  by_cases budgets : 4 ≤ n ∧ 4 ≤ p
  · have free : HalfBridgeFree (ListBefore paths) 4 := by
      cases half
      · exact (show BridgeFree (ListBefore paths) 4 from allowed).halfFree
      · exact allowed
    let kept := removeOppositeIntersections paths
    let marks (i : Fin p) := (kept i).toFinset
    have keptSimple (i : Fin p) : (kept i).Nodup := (removeOppositeIntersections_sublist paths i).nodup (simple i)
    have halfMass : M ≤ 2*(∑ i, (kept i).length) := removeOppositeIntersections_mass simple free (by decide)
    have keptMass : (∑ i, (kept i).length) ≤ M :=
      sum_le_sum (fun i _ => (removeOppositeIntersections_sublist paths i).length_le)
    have lengths (i : Fin p) : (marks i).card = (kept i).length := List.toFinset_card_of_nodup (keptSimple i)
    obtain ⟨A,B,vBudget,iBudget,retained⟩ := rectanglePaths_quarter marks
      (by simpa only [Fintype.card_fin] using budgets.1) (by simpa only [Fintype.card_fin] using budgets.2)
    let quarter := restrictListPaths kept A B
    let m := ∑ i : B, (quarter i).length
    have mass : m = ∑ i : B, (rectanglePaths marks A B i).card :=
      restrictListPaths_mass_eq kept keptSimple A B
    simp only [lengths, ← mass] at retained
    have large : M ≤ 98*m := by omega
    have upper : m ≤ M := by
      rw [mass]
      exact (rectanglePaths_mass_le marks A B).trans (by simpa only [lengths] using keptMass)
    by_cases enough : n ≤ m ∧ p ≤ m
    · have quarterSimple (i : B) : (quarter i).Nodup := restrictListPath_nodup (keptSimple i.val) A
      have quarterUnique : ∀ {i j x y}, i ≠ j → x ∈ quarter i → x ∈ quarter j → y ∈ quarter i → y ∈ quarter j → x = y :=
        restrictListPaths_unique (fun different a b c d =>
          removeOppositeIntersections_unique simple free (by decide) different a b c d) A B
      have quarterAllowed : localOrderAdmissible half 4 quarter := by
        cases half
        · exact restrictListPaths_fullFree keptSimple (removeOppositeIntersections_fullFree simple allowed) A B
        · exact restrictListPaths_halfFree keptSimple (removeOppositeIntersections_halfFree simple allowed) A B
      obtain ⟨n',vn,p',ip,clean,cleanSimple,cleanAllowed,cleanMass,cleanUpper,caps⟩ :=
        clean_quarter_support quarter quarterSimple quarterUnique half quarterAllowed hn hp
          (by simpa only [Fintype.card_coe, Fintype.card_fin] using vBudget)
          (by simpa only [Fintype.card_coe, Fintype.card_fin] using iBudget) enough.1 enough.2
      refine ⟨n',vn,p',ip,clean,cleanSimple,cleanAllowed,?_,cleanUpper.trans upper,caps⟩
      change m ≤ 4*(∑ i, (clean i).length) at cleanMass
      change M ≤ 392*(∑ i, (clean i).length)
      omega
    · apply clean_linear_mass half hn hp dense long
      have bound : m ≤ max n p := by
        rcases not_and_or.mp enough with tooFew | tooShort
        · exact (Nat.le_of_lt (Nat.lt_of_not_ge tooFew)).trans (le_max_left _ _)
        · exact (Nat.le_of_lt (Nat.lt_of_not_ge tooShort)).trans (le_max_right _ _)
      change M ≤ _
      omega
  · apply clean_linear_mass half hn hp dense long
    have count (i : Fin p) : (paths i).length ≤ n := by
      rw [← List.toFinset_card_of_nodup (simple i)]
      simpa only [Fintype.card_fin] using card_le_univ (paths i).toFinset
    have total : M ≤ p*n := (sum_le_sum (fun i _ => count i)).trans_eq (by simp)
    change M ≤ _
    rcases not_and_or.mp budgets with small | small
    · have bound := total.trans (Nat.mul_le_mul_left p (show n ≤ 4 by omega))
      have leMax : p ≤ max n p := le_max_right _ _
      omega
    · have bound := total.trans (Nat.mul_le_mul_right n (show p ≤ 4 by omega))
      have leMax : n ≤ max n p := le_max_left _ _
      omega

/-- At the unrestricted maximum through size four, the cleaned system
retains a constant fraction of the mass and satisfies the output-average caps. -/
theorem localOrderExtremal_output_average_four (n p : ℕ) (half : Bool) (hn : 0 < n) (hp : 0 < p) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half 4 paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half 4 other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half 4 clean ∧
        (∑ i, (paths i).length) ≤ 392*(∑ i, (clean i).length) ∧
        (∑ i, (clean i).length) ≤ (∑ i, (paths i).length) ∧ listOutputAverageCaps clean := by
  obtain ⟨paths,simple,allowed,maximal,dense,long⟩ := localOrderExtremal_isDense n p 4 half hn hp
  exact ⟨paths,simple,allowed,maximal,
    regularization_list_output_average_four paths simple half allowed hn hp dense long⟩

end OnlineReachabilityPreservers
