import OnlineReachabilityPreservers.LocalOnBaseCounting

/-! A collision bound for important targets before a near predecessor on the base. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]

local notation "ListBefore" => SourceAudit.BeforeIn

/-- Successor targets that precede some near predecessor on their base. -/
noncomputable def listBackwardTargets (paths : I → List V) (u : V) (h : ℕ) (b : I) : Finset V := by
  classical
  exact (listSuccessorSupport paths u).filter fun v =>
    ∃ z ∈ listPredecessorSupport paths u h, ListBefore paths b v z

omit [LinearOrder I] in
theorem mem_listBackwardTargets {paths : I → List V} {u v : V} {h : ℕ} {b : I} :
    v ∈ listBackwardTargets paths u h b ↔
      v ∈ listSuccessorSupport paths u ∧ ∃ z ∈ listPredecessorSupport paths u h, ListBefore paths b v z := by
  classical
  simp only [listBackwardTargets, mem_filter]

noncomputable def listBackwardBaseIncidences (paths : I → List V) (u : V) (h x : ℕ) : ℕ :=
  ∑ b ∈ listLargeBranchBases paths u h x, (listBackwardTargets paths u h b).card

omit [Fintype I] in
private theorem backward_collision_forbidden {paths : I → List V}
    (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    {u a x y : V} {i j k l m m' : I} (ij : i < j) (iAvoid : u ∉ paths i)
    (jAvoid : u ∉ paths j) (kAvoid : u ∉ paths k)
    (base : ListBefore paths i x y) (beforeA : ListBefore paths j x a)
    (beforeA' : ListBefore paths k y a) (incoming : ListBefore paths l a u)
    (outgoing : ListBefore paths m u x) (outgoing' : ListBefore paths m' u y) : False := by
  have mi : m ≠ i := fun eq => iAvoid (eq ▸ outgoing.1)
  have m'i : m' ≠ i := fun eq => iAvoid (eq ▸ outgoing'.1)
  have mm' : m ≠ m' := by
    intro eq
    exact (listBefore_ne base) (unique mi outgoing.2.1 base.1 (eq.symm ▸ outgoing'.2.1) base.2.1)
  have notEarlier : ¬ i < m' :=
    free (by decide) (threeListBridge mi mm'.symm m'i outgoing base outgoing')
  have earlier : m' < i := lt_of_le_of_ne (le_of_not_gt notEarlier) m'i
  have jl : j ≠ l := fun eq => jAvoid (eq.symm ▸ incoming.2.1)
  have jm' : j ≠ m' := fun eq => jAvoid (eq.symm ▸ outgoing'.1)
  have lk : l ≠ k := fun eq => kAvoid (eq ▸ incoming.2.1)
  have lm' : l ≠ m' := by
    intro eq
    exact (listBefore_ne beforeA').symm (unique lk incoming.1 beforeA'.2.1
      (eq.symm ▸ outgoing'.2.1) beforeA'.1)
  have il : i ≠ l := fun eq => iAvoid (eq.symm ▸ incoming.2.1)
  let b : Bridge (ListBefore paths) 2 := {
    vertex := ![x, a, u, y]
    arc := ![j, l, m']
    river := i
    distinctVertices := by
      intro s t eq
      have xa := listBefore_ne beforeA
      have xu := (listBefore_ne outgoing).symm
      have xy := listBefore_ne base
      have au := listBefore_ne incoming
      have ay := (listBefore_ne beforeA').symm
      have uy := listBefore_ne outgoing'
      fin_cases s <;> fin_cases t <;> simp_all
    distinctArcs := by
      intro s t eq
      fin_cases s <;> fin_cases t <;> simp_all
    river_ne_arc := by intro s; fin_cases s; exacts [ij.ne, il, m'i.symm]
    riverStep := base
    arcStep := by intro s; fin_cases s; exacts [beforeA, incoming, outgoing'] }
  exact free (by decide) b earlier

private theorem list_backward_collision {paths : I → List V}
    (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    {u a x y : V} {h : ℕ} {i j k : I} (ij : i < j) (ik : i < k)
    (iAvoid : u ∉ paths i) (jAvoid : u ∉ paths j) (kAvoid : u ∉ paths k)
    (xi : x ∈ paths i) (yi : y ∈ paths i)
    (xj : ListBefore paths j x a) (yk : ListBefore paths k y a)
    (ha : a ∈ listPredecessorSupport paths u h)
    (hx : x ∈ listSuccessorSupport paths u) (hy : y ∈ listSuccessorSupport paths u) :
    x = y ∧ j = k := by
  by_cases same : x = y
  · subst y
    refine ⟨rfl, ?_⟩
    by_contra different
    exact (listBefore_ne xj) (unique different xj.1 yk.1 xj.2.1 yk.2.1)
  obtain ⟨l, incoming, _⟩ := mem_listPredecessorSupport.mp ha
  obtain ⟨m, outgoing⟩ := mem_listSuccessorSupport.mp hx
  obtain ⟨m', outgoing'⟩ := mem_listSuccessorSupport.mp hy
  rcases listBefore_total xi yi same with forward | backward
  · exact (backward_collision_forbidden free unique ij iAvoid jAvoid kAvoid
      forward xj yk incoming outgoing outgoing').elim
  · exact (backward_collision_forbidden free unique ik iAvoid kAvoid jAvoid
      backward yk xj incoming outgoing' outgoing).elim

/-- Collisions of two backward targets charge injectively to the earlier
base and the last near predecessor on the later base. -/
theorem lemma35_list_backward_incidence {paths : I → List V}
    (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (u : V) (h x : ℕ) (hx : 0 < x) :
    let n := (listPredecessorSupport paths u h ∪ listSuccessorSupport paths u).card
    let p := (listLargeBranchBases paths u h x).card
    let s := (listPredecessorSupport paths u h).card
    let m := listBackwardBaseIncidences paths u h x
    m^2 ≤ n*(m+2*(p*s)) := by
  classical
  let A := listPredecessorSupport paths u h
  let B := listSuccessorSupport paths u
  let S := A ∪ B
  let J := listLargeBranchBases paths u h x
  have outside (i : J) : u ∉ paths i.val := (mem_filter.mp i.property).2.1
  have latest (i : J) : ∃ z ∈ (paths i.val).toFinset ∩ A,
      ∀ v ∈ (paths i.val).toFinset ∩ A, (paths i.val).idxOf v ≤ (paths i.val).idxOf z := by
    have lower : x ≤ ((paths i.val).toFinset ∩ A).card := (mem_filter.mp i.property).2.2
    exact exists_max_image _ (paths i.val).idxOf (card_pos.mp (hx.trans_le lower))
  let anchor (i : J) := Classical.choose (latest i)
  have inA (i : J) : anchor i ∈ A := (mem_inter.mp (Classical.choose_spec (latest i)).1).2
  have anchorStep (i : J) {v : V} (hv : v ∈ listBackwardTargets paths u h i.val) :
      ListBefore paths i.val v (anchor i) := by
    obtain ⟨_, z, zA, step⟩ := mem_listBackwardTargets.mp hv
    obtain ⟨anchorIn, latest⟩ := Classical.choose_spec (latest i)
    exact ⟨step.1, List.mem_toFinset.mp (mem_inter.mp anchorIn).1,
      step.2.2.trans_le (latest z (mem_inter.mpr ⟨List.mem_toFinset.mpr step.2.1, zA⟩))⟩
  let marks (i : J) : Finset S :=
    S.attach.filter fun v => v.val ∈ listBackwardTargets paths u h i.val
  let charge (z : S × J × J) := (z.2.1, anchor z.2.2)
  have cap : (collisions marks).card ≤ Fintype.card J*A.card := calc
    _ ≤ ((univ : Finset J) ×ˢ A).card := by
      apply card_le_card_of_injOn charge
      · rintro ⟨v, i, j⟩ _
        exact mem_product.mpr ⟨mem_univ _, inA j⟩
      · rintro ⟨v, i, j⟩ hv ⟨w, i', k⟩ hw same
        change (i, anchor j) = (i', anchor k) at same
        obtain ⟨rfl, anchorEq⟩ := Prod.mk.inj same
        obtain ⟨_, ij, vi, vj⟩ := mem_filter.mp hv
        obtain ⟨_, ik, wi, wk⟩ := mem_filter.mp hw
        have vi' := (mem_filter.mp vi).2
        have wi' := (mem_filter.mp wi).2
        have xStep := anchorStep j (mem_filter.mp vj).2
        have yStep := anchorStep k (mem_filter.mp wk).2
        obtain ⟨vertexEq, indexEq⟩ := list_backward_collision free unique ij ik
          (outside i) (outside j) (outside k)
          ((mem_listBackwardTargets.mp vi').2.choose_spec.2.1)
          ((mem_listBackwardTargets.mp wi').2.choose_spec.2.1)
          xStep (anchorEq.symm ▸ yStep) (inA j)
          (mem_listBackwardTargets.mp vi').1 (mem_listBackwardTargets.mp wi').1
        exact congrArg₂ (fun a b => (a, i, b)) (Subtype.ext vertexEq) (Subtype.ext indexEq)
    _ = _ := by simp
  have cardMarks (i : J) : (marks i).card = (listBackwardTargets paths u h i.val).card := by
    rw [← card_image_of_injective (marks i) Subtype.val_injective]
    congr 1
    ext v
    constructor
    · rintro hv
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
      exact (mem_filter.mp hw).2
    · intro hv
      let w : S := ⟨v, mem_union_right _ (mem_listBackwardTargets.mp hv).1⟩
      exact mem_image.mpr ⟨w, mem_filter.mpr ⟨mem_attach _ _, hv⟩, rfl⟩
  have mass : (∑ i, (marks i).card) = listBackwardBaseIncidences paths u h x := by
    simp only [cardMarks]
    exact J.sum_coe_sort (fun i => (listBackwardTargets paths u h i).card)
  have bound := incidence_square marks _ cap
  rw [mass, Fintype.card_coe, Fintype.card_coe] at bound
  exact bound

theorem lemma35_list_backward_upper {paths : I → List V}
    (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (u : V) (h x : ℕ) (hx : 0 < x) :
    let n : ℝ := (listPredecessorSupport paths u h ∪ listSuccessorSupport paths u).card
    let p : ℝ := (listLargeBranchBases paths u h x).card
    let s : ℝ := (listPredecessorSupport paths u h).card
    (listBackwardBaseIncidences paths u h x : ℝ) ≤ n+Real.sqrt (2*n*(p*s)) := by
  simpa only [Nat.cast_mul] using sqrt_budget (lemma35_list_backward_incidence free unique u h x hx)


variable [Fintype V]

/-- All tuples in the sampled h-system, including every on-base right endpoint. -/
noncomputable def fullListBranchTuples (paths : I → List V) (base : I) (h : ℕ) : Finset (BranchTuple V I) := by
  classical
  exact univ.filter fun w =>
    InListBranchWindow paths base w.left h w.leftStart w.x ∧
    InListBranchWindow paths base w.right h w.rightStart w.y ∧ w.x ∉ paths base ∧
    ∃ m, ListIntersectionChain paths w.left m w.right w.x w.y

theorem mem_fullListBranchTuples {paths : I → List V} {base : I} {h : ℕ} {w : BranchTuple V I} :
    w ∈ fullListBranchTuples paths base h ↔
      InListBranchWindow paths base w.left h w.leftStart w.x ∧
      InListBranchWindow paths base w.right h w.rightStart w.y ∧ w.x ∉ paths base ∧
      ∃ m, ListIntersectionChain paths w.left m w.right w.x w.y := by
  classical
  simp [fullListBranchTuples]

theorem listBranchTuples_subset_full (paths : I → List V) (base : I) (h : ℕ) :
    listBranchTuples paths base h ⊆ fullListBranchTuples paths base h := by
  intro w hw
  obtain ⟨left, right, outside, _, middle⟩ := mem_listBranchTuples.mp hw
  exact mem_fullListBranchTuples.mpr ⟨left, right, outside, middle⟩

noncomputable def listFullOnBaseBranchTuples (paths : I → List V) (base : I) (h : ℕ) :
    Finset (BranchTuple V I) := by
  classical
  exact (fullListBranchTuples paths base h).filter fun w => w.y ∈ paths base

theorem fullListBranchTuples_partition (paths : I → List V) (base : I) (h : ℕ) :
    (fullListBranchTuples paths base h).card =
      (listFullOnBaseBranchTuples paths base h).card+(listOffBaseBranchTuples paths base h).card := by
  classical
  have same : (fullListBranchTuples paths base h).filter (fun w => w.y ∉ paths base) =
      listOffBaseBranchTuples paths base h := by
    ext w
    simp only [listOffBaseBranchTuples, mem_filter, mem_fullListBranchTuples, mem_listBranchTuples,
      QualifyingListBranchTuple]
    tauto
  rw [← same]
  exact (card_filter_add_card_filter_not (s := fullListBranchTuples paths base h)
    (fun w : BranchTuple V I => w.y ∈ paths base)).symm

/-- Each other path through an on-base vertex contributes a single start.
The base itself has at most h+1 starts. -/
theorem listBranchesThrough_on_base {paths : I → List V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    {b : I} {v : V} {h : ℕ} (onBase : v ∈ paths b) :
    (listBranchesThrough paths b h v).card ≤ (occurrences (fun i => (paths i).toFinset) v).card+h+1 := by
  classical
  let bs := listBranchesThrough paths b h v
  let own := bs.filter fun w => w.1 = b
  let other := listOtherBranchesThrough paths b h v
  have split : own.card+other.card = bs.card :=
    card_filter_add_card_filter_not (s := bs) (fun w : I × V => w.1 = b)
  have otherCount : other.card ≤ (occurrences (fun i => (paths i).toFinset) v).card :=
    listOtherBranchesThrough_card unique onBase
  let rank := (paths b).idxOf
  have ownCount : own.card ≤ h+1 := calc
    _ ≤ (range (h+1)).card := by
      apply card_le_card_of_injOn (fun w => rank v - rank w.2)
      · rintro ⟨i, u⟩ hi
        obtain ⟨hw, rfl⟩ := mem_filter.mp hi
        have close := (mem_listBranchesThrough.mp hw).2.2.2.2
        change rank v ≤ rank u + h at close
        apply mem_range.mpr
        change rank v - rank u < h+1
        omega
      · rintro ⟨i, u⟩ hu ⟨j, w⟩ hw eq
        obtain ⟨hu, rfl⟩ := mem_filter.mp hu
        obtain ⟨hw, rfl⟩ := mem_filter.mp hw
        obtain ⟨ub, _, _, early, _⟩ := mem_listBranchesThrough.mp hu
        obtain ⟨_, _, _, early', _⟩ := mem_listBranchesThrough.mp hw
        change rank u ≤ rank v at early
        change rank w ≤ rank v at early'
        change rank v - rank u = rank v - rank w at eq
        have r : rank u = rank w := by omega
        obtain rfl := (List.idxOf_inj ub).mp r
        rfl
    _ = _ := card_range _
  change bs.card ≤ _
  rw [← split]
  omega

private noncomputable def listFullOnBaseBucket (paths : I → List V) (b : I) (h x : ℕ) : Finset (BranchTuple V I) := by
  classical
  exact (listFullOnBaseBranchTuples paths b h).filter fun w =>
    x ≤ (listBranchesThrough paths b h w.x).card ∧ (listBranchesThrough paths b h w.x).card < 2*x

/-- Each important pair is charged by at most `2*x` left branches and `D+h+1` right branches. -/
theorem lemma35_list_full_on_base_count {paths : I → List V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (h x D : ℕ) (degree : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) :
    (∑ b, (listFullOnBaseBucket paths b h x).card) ≤
      (2*x*(D+h+1))*∑ u, (listImportantBaseIncidences paths u h x + listBackwardBaseIncidences paths u h x) := by
  classical
  let collected := (univ : Finset I).sigma fun b => listFullOnBaseBucket paths b h x
  let targets := (univ : Finset V).sigma fun u =>
    (listLargeBranchBases paths u h x).sigma fun b => listImportantTargets paths u h b ∪ listBackwardTargets paths u h b
  let charge (z : Σ _ : I, BranchTuple V I) : Σ _ : V, Σ _ : I, V :=
    ⟨z.2.x, z.1, z.2.y⟩
  have maps : Set.MapsTo charge (collected : Set _) targets := by
    rintro ⟨b, w⟩ hw
    obtain ⟨counted, lower, _⟩ := mem_filter.mp (mem_sigma.mp hw).2
    obtain ⟨counted, onBase⟩ := mem_filter.mp counted
    obtain ⟨left, _, outside, m, middle⟩ := mem_fullListBranchTuples.mp counted
    have near : w.leftStart ∈ listPredecessorSupport paths w.x h :=
      mem_listPredecessorSupport.mpr ⟨w.left,
        ⟨left.2.1, left.2.2.1, left.2.2.2.1.lt_of_ne (fun equal =>
          outside ((List.idxOf_inj left.2.1).mp equal ▸ left.1))⟩, left.2.2.2.2⟩
    have succ : w.y ∈ listSuccessorSupport paths w.x :=
      mem_listSuccessorSupport.mpr ⟨m, middle.middle_step⟩
    have different : w.leftStart ≠ w.y := by
      intro eq
      have shared := unique middle.left_ne_middle left.2.1
        (eq.symm ▸ middle.middle_step.2.1) middle.on_left middle.middle_step.1
      exact (listBefore_ne middle.middle_step) (shared.symm.trans eq)
    have belongs : w.y ∈ listImportantTargets paths w.x h b ∪ listBackwardTargets paths w.x h b := by
      rcases listBefore_total left.1 onBase different with forward | backward
      · exact mem_union_left _ (mem_listImportantTargets.mpr ⟨succ, w.leftStart, near, forward⟩)
      · exact mem_union_right _ (mem_listBackwardTargets.mpr ⟨succ, w.leftStart, near, backward⟩)
    exact mem_sigma.mpr ⟨mem_univ _, mem_sigma.mpr
      ⟨mem_filter.mpr ⟨mem_univ _, outside, (listBranchesThrough_card unique outside) ▸ lower⟩, belongs⟩⟩
  have fibers (z : Σ _ : V, Σ _ : I, V) :
      ((collected.filter fun a => charge a = z).card) ≤ 2*x*(D+h+1) := by
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
    have rightCount : (listBranchesThrough paths b h v).card ≤ D+h+1 := by
      have count := listBranchesThrough_on_base unique (h := h) (b := b) (hv ▸ (mem_filter.mp q).2)
      have cap := degree v
      omega
    let decode (a : Σ _ : I, BranchTuple V I) := ((a.2.left, a.2.leftStart), (a.2.right, a.2.rightStart))
    have cap : F.card ≤ (listBranchesThrough paths b h u ×ˢ listBranchesThrough paths b h v).card := by
      apply card_le_card_of_injOn decode
      · rintro ⟨i, w⟩ hw
        obtain ⟨hi, hu, hv⟩ := members hw
        change i = b at hi
        subst i
        obtain ⟨counted, _⟩ := mem_filter.mp (mem_filter.mp (mem_sigma.mp (mem_filter.mp hw).1).2).1
        have valid := mem_fullListBranchTuples.mp counted
        exact mem_product.mpr ⟨mem_listBranchesThrough.mpr (hu ▸ valid.1), mem_listBranchesThrough.mpr (hv ▸ valid.2.1)⟩
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
  have result : collected.card ≤ (2*x*(D+h+1))*targets.card := by
    rw [card_eq_sum_card_fiberwise maps]
    calc
      _ ≤ ∑ _ ∈ targets, (2*x*(D+h+1)) := sum_le_sum fun z _ => fibers z
      _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  have targetCap : targets.card ≤ ∑ u, (listImportantBaseIncidences paths u h x + listBackwardBaseIncidences paths u h x) := by
    simp only [targets, card_sigma, listImportantBaseIncidences, listBackwardBaseIncidences, ← sum_add_distrib]
    exact sum_le_sum fun u _ => sum_le_sum fun b _ => card_union_le _ _
  simpa only [collected, card_sigma] using result.trans (Nat.mul_le_mul_left _ targetCap)

/-- The dyadic number of full tuples with right endpoint on the base. -/
theorem lemma35_list_full_on_base_dyadic_count {paths : I → List V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (h D : ℕ) (degree : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D) :
    (∑ b, (listFullOnBaseBranchTuples paths b h).card) ≤
      ∑ j ∈ range (Nat.log 2 D+1),
        (2*(2^j)*(D+h+1))*∑ u,
          (listImportantBaseIncidences paths u h (2^j) + listBackwardBaseIncidences paths u h (2^j)) := by
  classical
  let J := range (Nat.log 2 D+1)
  have perBase (b : I) : (listFullOnBaseBranchTuples paths b h).card ≤
      ∑ j ∈ J, (listFullOnBaseBucket paths b h (2^j)).card := by
    let target := J.sigma fun j => listFullOnBaseBucket paths b h (2^j)
    have bound : (listFullOnBaseBranchTuples paths b h).card ≤ target.card := by
      apply card_le_card_of_injOn (fun w : BranchTuple V I =>
        (⟨Nat.log 2 (listBranchesThrough paths b h w.x).card, w⟩ : Σ _ : ℕ, BranchTuple V I))
      · intro w hw
        obtain ⟨counted, _⟩ := mem_filter.mp hw
        obtain ⟨start, _, outside, _, _⟩ := mem_fullListBranchTuples.mp counted
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
    _ ≤ ∑ b, ∑ j ∈ J, (listFullOnBaseBucket paths b h (2^j)).card :=
      sum_le_sum (fun b _ => perBase b)
    _ = ∑ j ∈ J, ∑ b, (listFullOnBaseBucket paths b h (2^j)).card := sum_comm
    _ ≤ _ := sum_le_sum fun j _ => lemma35_list_full_on_base_count unique h (2^j) D degree

end OnlineReachabilityPreservers
