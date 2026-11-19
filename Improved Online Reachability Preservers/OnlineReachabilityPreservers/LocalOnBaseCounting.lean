import OnlineReachabilityPreservers.LocalBranchingDegrees
import OnlineReachabilityPreservers.LocalSourceCounting

/-! The filtered on-base count in Lemma 35 for local path orders. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]

local notation "ListBefore" => SourceAudit.BeforeIn

/-- All strict successors of a vertex on the paths containing it. -/
def listSuccessorSupport (paths : I → List V) (u : V) : Finset V :=
  (occurrences (fun i => (paths i).toFinset) u).biUnion fun i =>
    (paths i).toFinset.filter fun v => (paths i).idxOf u < (paths i).idxOf v

omit [LinearOrder I] in
theorem mem_listSuccessorSupport {paths : I → List V} {u v : V} :
    v ∈ listSuccessorSupport paths u ↔ ∃ i, ListBefore paths i u v := by
  constructor
  · intro hv
    obtain ⟨i, hi, hv⟩ := mem_biUnion.mp hv
    have hu := (mem_occurrences (marks := fun j => (paths j).toFinset)).mp hi
    obtain ⟨hv, before⟩ := mem_filter.mp hv
    exact ⟨i, List.mem_toFinset.mp hu, List.mem_toFinset.mp hv, before⟩
  · rintro ⟨i, hu, hv, before⟩
    exact mem_biUnion.mpr ⟨i, mem_occurrences.mpr (List.mem_toFinset.mpr hu),
      mem_filter.mpr ⟨List.mem_toFinset.mpr hv, before⟩⟩

omit [LinearOrder I] in
theorem listSuccessorSupport_card (paths : I → List V) (u : V) (L : ℕ)
    (lengths : ∀ i, (paths i).toFinset.card ≤ L) :
    (listSuccessorSupport paths u).card ≤ (occurrences (fun i => (paths i).toFinset) u).card*L := by
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ _ ∈ occurrences (fun i => (paths i).toFinset) u, L :=
      sum_le_sum fun i _ => (card_filter_le _ _).trans (lengths i)
    _ = _ := by simp

/-- Keep only the on-base endpoints preceded on the base by a predecessor of `u`. -/
noncomputable def listImportantTargets (paths : I → List V) (u : V) (h : ℕ) (b : I) : Finset V := by
  classical
  exact (listSuccessorSupport paths u).filter fun v =>
    ∃ z ∈ listPredecessorSupport paths u h, ListBefore paths b z v

omit [LinearOrder I] in
theorem mem_listImportantTargets {paths : I → List V} {u v : V} {h : ℕ} {b : I} :
    v ∈ listImportantTargets paths u h b ↔
      v ∈ listSuccessorSupport paths u ∧ ∃ z ∈ listPredecessorSupport paths u h, ListBefore paths b z v := by
  classical
  simp only [listImportantTargets, mem_filter]

noncomputable def listImportantBaseIncidences (paths : I → List V) (u : V) (h x : ℕ) : ℕ :=
  ∑ b ∈ listLargeBranchBases paths u h x, (listImportantTargets paths u h b).card

/-- Take a suffix from the earliest predecessor on every eligible base. This
keeps every counted right endpoint and gives the restricted family its sources. -/
theorem lemma35_list_important_incidence {paths : I → List V}
    (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (u : V) (h x : ℕ) (hx : 0 < x) :
    let n := (listPredecessorSupport paths u h ∪ listSuccessorSupport paths u).card
    let p := (listLargeBranchBases paths u h x).card
    let s := (listPredecessorSupport paths u h).card
    let m := listImportantBaseIncidences paths u h x
    m^2 ≤ n*(m+2*(p*s)) := by
  classical
  let A := listPredecessorSupport paths u h
  let B := listSuccessorSupport paths u
  let S := A ∪ B
  let J := listLargeBranchBases paths u h x
  have earliest (i : J) : ∃ z ∈ (paths i.val).toFinset ∩ A,
      ∀ y ∈ (paths i.val).toFinset ∩ A, (paths i.val).idxOf z ≤ (paths i.val).idxOf y := by
    have hcount : x ≤ ((paths i.val).toFinset ∩ A).card := (mem_filter.mp i.2).2.2
    exact exists_min_image _ (paths i.val).idxOf (card_pos.mp (hx.trans_le hcount))
  let anchor (i : J) := Classical.choose (earliest i)
  have anchor_mem (i : J) : anchor i ∈ (paths i.val).toFinset ∩ A :=
    (Classical.choose_spec (earliest i)).1
  have anchor_le (i : J) (v : V) (hv : v ∈ (paths i.val).toFinset ∩ A) :
      (paths i.val).idxOf (anchor i) ≤ (paths i.val).idxOf v :=
    (Classical.choose_spec (earliest i)).2 v hv
  let suffix (i : I) := if hi : i ∈ J then
    (paths i).filter fun v => decide ((paths i).idxOf (anchor ⟨i, hi⟩) ≤ (paths i).idxOf v)
    else paths i
  have suffix_sub (i : I) : List.Sublist (suffix i) (paths i) := by
    by_cases hi : i ∈ J
    · simpa only [suffix, dite_eq_left hi] using
        (List.filter_sublist : ((paths i).filter fun v =>
          decide ((paths i).idxOf (anchor ⟨i, hi⟩) ≤ (paths i).idxOf v)).Sublist (paths i))
    · simp [suffix, hi]
  have mem_suffix (i : J) (v : V) : v ∈ suffix i.val ↔
      v ∈ paths i.val ∧ (paths i.val).idxOf (anchor i) ≤ (paths i.val).idxOf v := by
    simp only [suffix, dite_eq_left i.property, List.mem_filter, decide_eq_true_eq]
  have suffix_simple (i : I) : (suffix i).Nodup := (suffix_sub i).nodup (simple i)
  have suffix_free : HalfBridgeFree (ListBefore suffix) 4 := by
    intro k hk b earlier
    exact free hk (b.mapPaths id Function.injective_id (fun i _ _ step => listBefore_of_sublist (simple i) (suffix_sub i) step)) earlier
  have suffix_unique {i j v w : _} (ne : i ≠ j) (vi : v ∈ suffix i) (vj : v ∈ suffix j)
      (wi : w ∈ suffix i) (wj : w ∈ suffix j) : v = w :=
    unique ne ((suffix_sub i).subset vi) ((suffix_sub j).subset vj)
      ((suffix_sub i).subset wi) ((suffix_sub j).subset wj)
  let P := restrictListPaths suffix S J
  let sources : Finset S := S.attach.filter (fun w => w.val ∈ A)
  let first (i : J) : S := ⟨anchor i, mem_union_left _ (mem_inter.mp (anchor_mem i)).2⟩
  have initial (i : J) : first i ∈ sources :=
    mem_filter.mpr ⟨mem_attach _ _, (mem_inter.mp (anchor_mem i)).2⟩
  have first_mem (i : J) : first i ∈ P i :=
    mem_restrictListPath.mpr ((mem_suffix i (anchor i)).mpr
      ⟨List.mem_toFinset.mp (mem_inter.mp (anchor_mem i)).1, le_rfl⟩)
  have first_step (i : J) (v : S) (hv : v ∈ (P i).toFinset.erase (first i)) :
      ListBefore P i (first i) v := by
    obtain ⟨different, member⟩ := mem_erase.mp hv
    have vP := List.mem_toFinset.mp member
    rcases listBefore_total (first_mem i) vP different.symm with forward | backward
    · exact forward
    · have old := listBefore_of_sublist (simple i.val) (suffix_sub i.val)
        (restrictListPaths_step (suffix_simple i.val) backward)
      have late := ((mem_suffix i v.val).mp (mem_restrictListPath.mp vP)).2
      exact ((not_lt_of_ge late) old.2.2).elim
  have sCap : sources.card ≤ A.card :=
    card_le_card_of_injOn Subtype.val (fun _ hv => (mem_filter.mp hv).2) Subtype.val_injective.injOn
  let m' := ∑ i, ((P i).toFinset.erase (first i)).card
  have marks (i : J) : (listImportantTargets paths u h i.val).card ≤
      ((P i).toFinset.erase (first i)).card := calc
    _ ≤ (((P i).toFinset.erase (first i)).image (Subtype.val : S → V)).card := by
      apply card_le_card
      intro v hv
      obtain ⟨hb, z, hz, step⟩ := mem_listImportantTargets.mp hv
      have later := (anchor_le i z (mem_inter.mpr ⟨List.mem_toFinset.mpr step.1, hz⟩)).trans_lt step.2.2
      let q : S := ⟨v, mem_union_right _ hb⟩
      have qP : q ∈ P i :=
        mem_restrictListPath.mpr ((mem_suffix i v).mpr ⟨step.2.1, later.le⟩)
      refine mem_image.mpr ⟨q, mem_erase.mpr ⟨?_, List.mem_toFinset.mpr qP⟩, rfl⟩
      intro equal
      have values : v = anchor i := congrArg Subtype.val equal
      exact later.ne (congrArg (paths i.val).idxOf values).symm
    _ = _ := card_image_of_injective _ Subtype.val_injective
  let m := listImportantBaseIncidences paths u h x
  let q := J.card*A.card
  have sub : m ≤ m' := calc
    _ = ∑ i : J, (listImportantTargets paths u h i.val).card :=
      (J.sum_coe_sort (fun i => (listImportantTargets paths u h i).card)).symm
    _ ≤ _ := sum_le_sum fun i _ => marks i
  have bound := list_source_restricted_square (restrictListPaths_halfFree suffix_simple suffix_free S J)
    (restrictListPaths_unique suffix_unique S J) sources first initial first_step
  change m'^2 ≤ Fintype.card S*(m'+2*(Fintype.card J*sources.card)) at bound
  rw [Fintype.card_coe, Fintype.card_coe] at bound
  have larger : m'^2 ≤ S.card*(m'+2*q) := bound.trans (by dsimp only [q]; gcongr)
  change m^2 ≤ S.card*(m+2*q)
  by_cases small : m ≤ S.card
  · rw [pow_two]
    exact (Nat.mul_le_mul_right m small).trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
  · have gap : 0 ≤ (m':ℤ)-(m:ℤ) := by omega
    have factor : 0 ≤ (m':ℤ)+(m:ℤ)-(S.card:ℤ) := by omega
    have product := mul_nonneg gap factor
    have upper : (m':ℤ)^2 ≤ (S.card:ℤ)*((m':ℤ)+2*(q:ℤ)) := by exact_mod_cast larger
    have mono : (m:ℤ)^2 ≤ (S.card:ℤ)*((m:ℤ)+2*(q:ℤ)) := by nlinarith only [product, upper]
    exact_mod_cast mono

theorem lemma35_list_important_upper {paths : I → List V}
    (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (u : V) (h x : ℕ) (hx : 0 < x) :
    let n : ℝ := (listPredecessorSupport paths u h ∪ listSuccessorSupport paths u).card
    let p : ℝ := (listLargeBranchBases paths u h x).card
    let s : ℝ := (listPredecessorSupport paths u h).card
    (listImportantBaseIncidences paths u h x : ℝ) ≤ n+Real.sqrt (2*n*(p*s)) := by
  simpa only [Nat.cast_mul] using sqrt_budget (lemma35_list_important_incidence simple free unique u h x hx)


variable [Fintype V]

/-- At a vertex on the base, each branch distinct from the base starts at that vertex. -/
noncomputable def listOtherBranchesThrough (paths : I → List V) (b : I) (h : ℕ) (v : V) : Finset (I × V) :=
  (listBranchesThrough paths b h v).filter fun w => w.1 ≠ b

theorem listOtherBranchesThrough_card {paths : I → List V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    {b : I} {v : V} {h : ℕ} (onBase : v ∈ paths b) :
    (listOtherBranchesThrough paths b h v).card ≤ (occurrences (fun i => (paths i).toFinset) v).card := by
  apply card_le_card_of_injOn Prod.fst
  · rintro ⟨i, z⟩ inside
    exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_listBranchesThrough.mp (mem_filter.mp inside).1).2.2.1)
  · rintro ⟨i, z⟩ ha ⟨j, w⟩ hb same
    change i = j at same
    subst j
    obtain ⟨za, ne⟩ := mem_filter.mp ha
    obtain ⟨wa, _⟩ := mem_filter.mp hb
    obtain ⟨zb, zi, vi, _, _⟩ := mem_listBranchesThrough.mp za
    obtain ⟨wb, wi, _, _, _⟩ := mem_listBranchesThrough.mp wa
    change (i, z) = (i, w)
    rw [unique ne zi zb vi onBase, unique ne wi wb vi onBase]

/-- The filtered on-base tuple family used for the close-pair charge. -/
noncomputable def listOnBaseBranchTuples (paths : I → List V) (b : I) (h : ℕ) :
    Finset (BranchTuple V I) := by
  classical
  exact (listBranchTuples paths b h).filter (fun w => w.y ∈ paths b)

theorem listBranchTuples_partition (paths : I → List V) (b : I) (h : ℕ) :
    (listBranchTuples paths b h).card =
      (listOnBaseBranchTuples paths b h).card + (listOffBaseBranchTuples paths b h).card := by
  classical
  exact (card_filter_add_card_filter_not (s := listBranchTuples paths b h)
    (fun w : BranchTuple V I => w.y ∈ paths b)).symm

private noncomputable def listOnBaseBucket (paths : I → List V) (b : I) (h x : ℕ) : Finset (BranchTuple V I) := by
  classical
  exact (listOnBaseBranchTuples paths b h).filter fun w =>
    x ≤ (listBranchesThrough paths b h w.x).card ∧ (listBranchesThrough paths b h w.x).card < 2*x

/-- Each important pair is charged by at most `2*x` left branches and `D` right branches. -/
theorem lemma35_list_on_base_count {paths : I → List V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (h x D : ℕ) (degree : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) :
    (∑ b, (listOnBaseBucket paths b h x).card) ≤
      (2*x*D)*∑ u, listImportantBaseIncidences paths u h x := by
  classical
  let collected := (univ : Finset I).sigma fun b => listOnBaseBucket paths b h x
  let targets := (univ : Finset V).sigma fun u =>
    (listLargeBranchBases paths u h x).sigma fun b => listImportantTargets paths u h b
  let charge (z : Σ _ : I, BranchTuple V I) : Σ _ : V, Σ _ : I, V :=
    ⟨z.2.x, z.1, z.2.y⟩
  have maps : Set.MapsTo charge (collected : Set _) targets := by
    rintro ⟨b, w⟩ hw
    obtain ⟨counted, lower, _⟩ := mem_filter.mp (mem_sigma.mp hw).2
    obtain ⟨counted, onBase⟩ := mem_filter.mp counted
    obtain ⟨left, _, outside, order, m, middle⟩ := mem_listBranchTuples.mp counted
    have before := (order onBase).2
    have near : w.leftStart ∈ listPredecessorSupport paths w.x h :=
      mem_listPredecessorSupport.mpr ⟨w.left,
        ⟨left.2.1, left.2.2.1, left.2.2.2.1.lt_of_ne (fun equal =>
          outside ((List.idxOf_inj left.2.1).mp equal ▸ left.1))⟩, left.2.2.2.2⟩
    apply mem_sigma.mpr
    refine ⟨mem_univ _, mem_sigma.mpr ⟨?_, mem_listImportantTargets.mpr
      ⟨mem_listSuccessorSupport.mpr ⟨m, middle.middle_step⟩, w.leftStart, near, before⟩⟩⟩
    exact mem_filter.mpr ⟨mem_univ _, outside, (listBranchesThrough_card unique outside) ▸ lower⟩
  have fibers (z : Σ _ : V, Σ _ : I, V) :
      ((collected.filter fun a => charge a = z).card) ≤ 2*x*D := by
    rcases z with ⟨u, b, v⟩
    let F := collected.filter fun a => charge a = ⟨u, b, v⟩
    by_cases empty : F = ∅
    · simp [F, empty]
    have members {a : Σ _ : I, BranchTuple V I} (ha : a ∈ F) :
        a.1 = b ∧ a.2.x = u ∧ a.2.y = v := by
      have eq := (mem_filter.mp ha).2
      exact ⟨congrArg (fun z => z.2.1) eq, congrArg Sigma.fst eq, congrArg (fun z => z.2.2) eq⟩
    obtain ⟨⟨b', w⟩, hw⟩ := nonempty_iff_ne_empty.mpr empty
    obtain ⟨hb, hu, hv⟩ := members hw
    change b' = b at hb
    subst b'
    obtain ⟨q, _, lt⟩ := mem_filter.mp (mem_sigma.mp (mem_filter.mp hw).1).2
    have leftCount : (listBranchesThrough paths b h u).card ≤ 2*x := (hu ▸ lt).le
    have rightCount : (listOtherBranchesThrough paths b h v).card ≤ D :=
      (listOtherBranchesThrough_card unique (hv ▸ (mem_filter.mp q).2)).trans (degree v)
    let decode (a : Σ _ : I, BranchTuple V I) := ((a.2.left, a.2.leftStart), (a.2.right, a.2.rightStart))
    have cap : F.card ≤ (listBranchesThrough paths b h u ×ˢ listOtherBranchesThrough paths b h v).card := by
      apply card_le_card_of_injOn decode
      · rintro ⟨i, w⟩ hw
        obtain ⟨hi, hu, hv⟩ := members hw
        change i = b at hi
        subst i
        obtain ⟨counted, onBase⟩ := mem_filter.mp (mem_filter.mp (mem_sigma.mp (mem_filter.mp hw).1).2).1
        have valid := mem_listBranchTuples.mp counted
        exact mem_product.mpr ⟨mem_listBranchesThrough.mpr (hu ▸ valid.1),
          mem_filter.mpr ⟨mem_listBranchesThrough.mpr (hv ▸ valid.2.1), (valid.2.2.2.1 onBase).1⟩⟩
      · rintro ⟨a, ⟨l, r, ls, rs, u', v'⟩⟩ h₁ ⟨c, ⟨l', r', ls', rs', u'', v''⟩⟩ h₂ e
        have loc₁ := members h₁
        have loc₂ := members h₂
        change a = b ∧ u' = u ∧ v' = v at loc₁
        change c = b ∧ u'' = u ∧ v'' = v at loc₂
        obtain ⟨rfl, rfl, rfl⟩ := loc₁
        obtain ⟨rfl, rfl, rfl⟩ := loc₂
        change ((l, ls), (r, rs)) = ((l', ls'), (r', rs')) at e
        simp only [Prod.mk.injEq] at e
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := e
        rfl
    exact cap.trans (by rw [card_product]; exact Nat.mul_le_mul leftCount rightCount)
  have result : collected.card ≤ (2*x*D)*targets.card := by
    rw [card_eq_sum_card_fiberwise maps]
    calc
      _ ≤ ∑ _ ∈ targets, 2*x*D := sum_le_sum fun z _ => fibers z
      _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  simpa only [collected, targets, card_sigma, listImportantBaseIncidences] using result

/-- The dyadic number of filtered tuples with right endpoint on the base. -/
theorem lemma35_list_on_base_dyadic_count {paths : I → List V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (h D : ℕ) (degree : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) :
    (∑ b, (listOnBaseBranchTuples paths b h).card) ≤
      ∑ j ∈ range (Nat.log 2 D+1),
        (2*(2^j)*(D+h+1))*∑ u, listImportantBaseIncidences paths u h (2^j) := by
  classical
  let J := range (Nat.log 2 D+1)
  have perBase (b : I) : (listOnBaseBranchTuples paths b h).card ≤
      ∑ j ∈ J, (listOnBaseBucket paths b h (2^j)).card := by
    let target := J.sigma fun j => listOnBaseBucket paths b h (2^j)
    have bound : (listOnBaseBranchTuples paths b h).card ≤ target.card := by
      apply card_le_card_of_injOn (fun w : BranchTuple V I =>
        (⟨Nat.log 2 (listBranchesThrough paths b h w.x).card, w⟩ : Σ _ : ℕ, BranchTuple V I))
      · intro w hw
        obtain ⟨counted, _⟩ := mem_filter.mp hw
        obtain ⟨start, _, outside, _, _, _⟩ := mem_listBranchTuples.mp counted
        let d := (listBranchesThrough paths b h w.x).card
        have hd : 0 < d := card_pos.mpr ⟨(w.left, w.leftStart), mem_listBranchesThrough.mpr start⟩
        have cap : d ≤ D := (listBranchesThrough_le_degree unique outside).trans (degree w.x)
        have j := Nat.lt_succ_of_le (Nat.log_mono_right (b := 2) cap)
        have lower := Nat.pow_log_le_self 2 hd.ne'
        have upper := Nat.lt_pow_succ_log_self (by decide : 1 < 2) d
        rw [Nat.pow_succ, Nat.mul_comm] at upper
        exact mem_sigma.mpr ⟨mem_range.mpr j, mem_filter.mpr ⟨hw, lower, upper⟩⟩
      · intro w _ z _ eq
        exact congrArg (fun a : Σ _ : ℕ, BranchTuple V I => a.2) eq
    simpa only [target, card_sigma] using bound
  calc
    _ ≤ ∑ b, ∑ j ∈ J, (listOnBaseBucket paths b h (2^j)).card :=
      sum_le_sum (fun b _ => perBase b)
    _ = ∑ j ∈ J, ∑ b, (listOnBaseBucket paths b h (2^j)).card := sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro j _
      exact (lemma35_list_on_base_count unique h (2^j) D degree).trans (by gcongr; omega)

end OnlineReachabilityPreservers
