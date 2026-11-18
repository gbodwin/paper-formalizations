import OnlineReachabilityPreservers.BranchingDegrees

/-! The source-restricted incidence and on-base branching counts in Lemma 35. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [LinearOrder I]

omit [LinearOrder I] in
private theorem source_removal {paths : I → Finset V} {source : I → V}
    (first : ∀ i, source i ∈ paths i ∧ ∀ v ∈ paths i, source i ≤ v)
    {i : I} {x : V} (mark : x ∈ (paths i).erase (source i)) : PathBefore paths i (source i) x := by
  obtain ⟨ne, hx⟩ := mem_erase.mp mark
  exact ⟨(first i).1, hx, ((first i).2 x hx).lt_of_ne ne.symm⟩

private theorem source_collision {paths : I → Finset V} {source : I → V}
    (free : HalfBridgeFree (PathBefore paths) 4)
    (first : ∀ i, source i ∈ paths i ∧ ∀ v ∈ paths i, source i ≤ v)
    {i j k : I} (hij : i < j) (hik : i < k) {x y : V}
    (xi : x ∈ (paths i).erase (source i)) (xj : x ∈ (paths j).erase (source j))
    (yi : y ∈ (paths i).erase (source i)) (yk : y ∈ (paths k).erase (source k))
    (eq : source j = source k) : x = y ∧ j = k := by
  have conflict {i j k : I} {x y : V} (hij : i < j) (hik : i < k) (hxy : x < y)
      (xi : x ∈ paths i) (yi : y ∈ paths i)
      (xj : PathBefore paths j (source j) x) (yk : PathBefore paths k (source k) y)
      (heq : source j = source k) : False := by
    by_cases hjk : j = k
    · subst k
      exact hxy.ne (path_intersection_unique (by decide) free hij.ne xi xj.2.1 yi yk.2.1)
    let bridge : Bridge (PathBefore paths) 1 :=
      orderedBridge ![source j, x, y] ![j, i] k (by
        intro a b he
        fin_cases a <;> fin_cases b
        · rfl
        · exact (hij.ne' he).elim
        · exact (hij.ne he).elim
        · rfl)
        (by intro a; fin_cases a; exacts [Ne.symm hjk, hik.ne'])
        (show PathBefore paths k (source j) y from heq.symm ▸ yk)
        (by
          intro a
          fin_cases a
          · exact xj
          · exact ⟨xi, yi, hxy⟩)
    exact free (by decide) bridge hik
  have earlier := (mem_erase.mp xi).2
  have later := (mem_erase.mp yi).2
  have xstep := source_removal first xj
  have ystep := source_removal first yk
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact (conflict hij hik hxy earlier later xstep ystep eq).elim
  · refine ⟨rfl, ?_⟩
    by_contra hjk
    have h := path_intersection_unique (by decide) free hjk xstep.1
      (show source j ∈ paths k from eq.symm ▸ ystep.1) xstep.2.1 ystep.2.1
    exact xstep.2.2.ne h
  · exact (conflict hik hij hyx later earlier ystep xstep eq.symm).elim

variable [Fintype V] [Fintype I]

/-- An arbitrary common-order half-4-bridge-free family with sources in S has
few non-source incidences. The count applies to induced path systems. -/
theorem source_restricted_square {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (S : Finset V) (source : I → V)
    (contained : ∀ i, source i ∈ S)
    (first : ∀ i, source i ∈ paths i ∧ ∀ v ∈ paths i, source i ≤ v) :
    let m := ∑ i, ((paths i).erase (source i)).card
    m^2 ≤ Fintype.card V*(m+2*(Fintype.card I*S.card)) := by
  let marks (i : I) := (paths i).erase (source i)
  let charge (z : V × I × I) := (z.2.1, source z.2.2)
  have bound : (collisions marks).card ≤ Fintype.card I*S.card := calc
    _ ≤ ((univ : Finset I) ×ˢ S).card := by
      apply card_le_card_of_injOn charge
      · rintro ⟨x, i, j⟩ _
        exact mem_product.mpr ⟨mem_univ _, contained j⟩
      · rintro ⟨x, i, j⟩ ha ⟨y, i', k⟩ hb eq
        change (i, source j) = (i', source k) at eq
        obtain ⟨rfl, e⟩ := Prod.mk.inj eq
        obtain ⟨_, hij, xi, xj⟩ := mem_filter.mp ha
        obtain ⟨_, hik, yi, yk⟩ := mem_filter.mp hb
        obtain ⟨rfl, rfl⟩ := source_collision free first hij hik xi xj yi yk e
        rfl
    _ = _ := by simp
  exact incidence_square marks _ bound


/-- Strict successors of u on any path through u. -/
def successorSupport (paths : I → Finset V) (u : V) : Finset V :=
  (occurrences paths u).biUnion fun i => (paths i).filter (u < ·)

omit [Fintype V] [LinearOrder I] in
theorem mem_successorSupport {paths : I → Finset V} {u v : V} :
    v ∈ successorSupport paths u ↔ ∃ i, u ∈ paths i ∧ v ∈ paths i ∧ u < v := by
  constructor
  · intro hv
    obtain ⟨i, hi, hv⟩ := mem_biUnion.mp hv
    exact ⟨i, mem_occurrences.mp hi, (mem_filter.mp hv).1, (mem_filter.mp hv).2⟩
  · rintro ⟨i, hu, hv, hlt⟩
    exact mem_biUnion.mpr ⟨i, mem_occurrences.mpr hu, mem_filter.mpr ⟨hv, hlt⟩⟩

omit [Fintype V] [LinearOrder I] in
theorem successorSupport_card (paths : I → Finset V) (u : V) (L : ℕ)
    (lengths : ∀ i, (paths i).card ≤ L) :
    (successorSupport paths u).card ≤ (occurrences paths u).card*L := by
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ _ ∈ occurrences paths u, L := sum_le_sum fun i _ => card_filter_le _ _ |>.trans (lengths i)
    _ = _ := by simp

/-- The incident pairs retained in the source-restricted family for a fixed off-base vertex. -/
def importantBaseIncidences (paths : I → Finset V) (u : V) (h x : ℕ) : ℕ :=
  ∑ b ∈ largeBranchBases paths u h x, (paths b ∩ successorSupport paths u).card

omit [Fintype V] in
/-- Lemma 35's incidence bound on the actual induced family. -/
theorem lemma35_important_incidence {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (u : V) (h x : ℕ) (hx : 0 < x) :
    let n := (predecessorSupport paths u h ∪ successorSupport paths u).card
    let p := (largeBranchBases paths u h x).card
    let s := (predecessorSupport paths u h).card
    let m := importantBaseIncidences paths u h x
    m^2 ≤ n*(m+2*(p*s)) := by
  dsimp only
  classical
  let A := predecessorSupport paths u h
  let B := successorSupport paths u
  let S := A ∪ B
  let J := largeBranchBases paths u h x
  let P := inducedPaths paths S J
  let sources : Finset S := S.attach.filter (fun w => w.val ∈ A)
  have predecessor (i : J) : ∃ w : S, w ∈ P i ∧ w.val ∈ A := by
    have hcount : x ≤ (paths i.val ∩ A).card := (mem_filter.mp i.2).2.2
    obtain ⟨w, hw⟩ := card_pos.mp (hx.trans_le hcount)
    obtain ⟨hp, ha⟩ := mem_inter.mp hw
    let q : S := ⟨w, mem_union_left _ ha⟩
    exact ⟨q, mem_filter.mpr ⟨mem_attach _ _, hp⟩, ha⟩
  have nonempty (i : J) : (P i).Nonempty := by
    obtain ⟨w, hw, _⟩ := predecessor i
    exact ⟨w, hw⟩
  let first (i : J) := (P i).min' (nonempty i)
  have first_min (i : J) : first i ∈ P i ∧ ∀ w ∈ P i, first i ≤ w :=
    ⟨min'_mem _ _, fun _ h => min'_le _ _ h⟩
  have first_lt (i : J) : (first i).val < u := by
    obtain ⟨w, hw, ha⟩ := predecessor i
    obtain ⟨j, _, _, hlt, _⟩ := mem_predecessorSupport.mp ha
    have h : (first i).val ≤ w.val := (first_min i).2 w hw
    exact h.trans_lt hlt
  have initial (i : J) : first i ∈ sources := by
    apply mem_filter.mpr
    refine ⟨mem_attach _ _, ?_⟩
    rcases mem_union.mp (first i).2 with ha | hb
    · exact ha
    · obtain ⟨j, _, _, hlt⟩ := mem_successorSupport.mp hb
      exact ((first_lt i).asymm hlt).elim
  have sCap : sources.card ≤ A.card :=
    card_le_card_of_injOn Subtype.val (fun _ hv => (mem_filter.mp hv).2)
      Subtype.val_injective.injOn
  let m' := ∑ i, ((P i).erase (first i)).card
  have marks (i : J) : (paths i.val ∩ B).card ≤ ((P i).erase (first i)).card := calc
    _ ≤ (((P i).erase (first i)).image (Subtype.val : S → V)).card := by
      apply card_le_card
      intro w hw
      obtain ⟨hp, hb⟩ := mem_inter.mp hw
      obtain ⟨j, _, _, hlt⟩ := mem_successorSupport.mp hb
      let q : S := ⟨w, mem_union_right _ hb⟩
      apply mem_image.mpr
      refine ⟨q, mem_erase.mpr ⟨?_, mem_filter.mpr ⟨mem_attach _ _, hp⟩⟩, rfl⟩
      intro eq
      exact (ne_of_lt ((first_lt i).trans hlt)) (congrArg Subtype.val eq).symm
    _ = _ := card_image_of_injective _ Subtype.val_injective
  let m := importantBaseIncidences paths u h x
  let q := J.card*A.card
  have sub : m ≤ m' := calc
    _ = ∑ i : J, (paths i.val ∩ B).card := by
      exact (J.sum_coe_sort (fun i => (paths i ∩ B).card)).symm
    _ ≤ _ := sum_le_sum fun i _ => marks i
  have hbound := source_restricted_square (free.induced S J) sources first initial first_min
  change m'^2 ≤ Fintype.card S*(m'+2*(Fintype.card J*sources.card)) at hbound
  rw [Fintype.card_coe, Fintype.card_coe] at hbound
  have larger : m'^2 ≤ S.card*(m'+2*q) := hbound.trans (by dsimp only [q]; gcongr)
  change m^2 ≤ S.card*(m+2*q)
  by_cases z : m ≤ S.card
  · rw [pow_two]
    exact (Nat.mul_le_mul_right m z).trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
  · have z' : 0 ≤ (m':ℤ)-(m:ℤ) := by omega
    have hS : 0 ≤ (m':ℤ)+(m:ℤ)-(S.card:ℤ) := by omega
    have h := mul_nonneg z' hS
    have real : (m':ℤ)^2 ≤ (S.card:ℤ)*((m':ℤ)+2*(q:ℤ)) := by exact_mod_cast larger
    have t : (m:ℤ)^2 ≤ (S.card:ℤ)*((m:ℤ)+2*(q:ℤ)) := by nlinarith only [h, real]
    exact_mod_cast t


omit [Fintype V] in
/-- The actual number of important pairs with a fixed off-base left endpoint. -/
theorem lemma35_important_upper {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (u : V) (h x : ℕ) (hx : 0 < x) :
    let n : ℝ := (predecessorSupport paths u h ∪ successorSupport paths u).card
    let p : ℝ := (largeBranchBases paths u h x).card
    let s : ℝ := (predecessorSupport paths u h).card
    (importantBaseIncidences paths u h x : ℝ) ≤ n+Real.sqrt (2*n*(p*s)) := by
  simpa only [Nat.cast_mul] using sqrt_budget (lemma35_important_incidence free u h x hx)

/-- At a vertex on the base, every other path branches from that vertex alone.
The base itself contributes at most h+1 possible starting positions. -/
theorem branchesThrough_on_base {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    {b : I} {v : V} {h : ℕ} (onBase : v ∈ paths b) :
    (branchesThrough paths b h v).card ≤ (occurrences paths v).card+(h+1) := by
  classical
  let bs := branchesThrough paths b h v
  let own := bs.filter fun w => w.1 = b
  let other := bs.filter fun w => w.1 ≠ b
  have split : own.card+other.card = bs.card :=
    card_filter_add_card_filter_not (s := bs) (fun w : I × V => w.1 = b)
  have unique {i : I} {u : V} (hi : (i, u) ∈ other) : u = v := by
    obtain ⟨hw, ne⟩ := mem_filter.mp hi
    obtain ⟨hub, hui, hvi, _, _⟩ := mem_branchesThrough.mp hw
    exact path_intersection_unique (by decide) free ne hui hub hvi onBase
  have otherCount : other.card ≤ (occurrences paths v).card := by
    apply card_le_card_of_injOn Prod.fst
    · rintro ⟨i, u⟩ hi
      exact mem_occurrences.mpr (mem_branchesThrough.mp (mem_filter.mp hi).1).2.2.1
    · rintro ⟨i, u⟩ hu ⟨j, w⟩ hw eq
      change i = j at eq
      subst j
      rw [unique hu, unique hw]
  let rank (u : V) := (predecessors (paths b) u).card
  have ownCount : own.card ≤ h+1 := calc
    _ ≤ (range (h+1)).card := by
      apply card_le_card_of_injOn (fun w => rank v - rank w.2)
      · rintro ⟨i, u⟩ hi
        obtain ⟨hw, rfl⟩ := mem_filter.mp hi
        have hnear := (mem_branchesThrough.mp hw).2.2.2.2
        apply mem_range.mpr
        change rank v ≤ rank u+h at hnear
        change rank v-rank u < h+1
        omega
      · rintro ⟨i, u⟩ hu ⟨j, w⟩ hw eq
        obtain ⟨hu, rfl⟩ := mem_filter.mp hu
        obtain ⟨hw, rfl⟩ := mem_filter.mp hw
        obtain ⟨hub, _, _, huv, _⟩ := mem_branchesThrough.mp hu
        obtain ⟨hwb, _, _, hwv, _⟩ := mem_branchesThrough.mp hw
        have ru : rank u ≤ rank v := predecessor_count_mono _ huv
        have rw' : rank w ≤ rank v := predecessor_count_mono _ hwv
        change rank v-rank u = rank v-rank w at eq
        have r : rank u = rank w := by omega
        obtain rfl := predecessor_count_injective _ hub hwb r
        rfl
    _ = _ := card_range _
  change bs.card ≤ _
  rw [← split]
  omega

/-- The on-base members of Q with left branching degree in [x, 2x). -/
noncomputable def onBaseBucket (paths : I → Finset V) (b : I) (h x : ℕ) : Finset (BranchTuple V I) := by
  classical
  exact (branchTuples paths b h).filter fun w =>
    w.y ∈ paths b ∧ x ≤ (branchesThrough paths b h w.x).card ∧ (branchesThrough paths b h w.x).card < 2*x

/-- The on-base tuple count in one bucket, summed over all bases. Important
pairs are charged by the two independent choices of branching windows. -/
theorem lemma35_on_base_count {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (h x D : ℕ) (degree : ∀ v, (occurrences paths v).card ≤ D) :
    (∑ b, (onBaseBucket paths b h x).card) ≤
      (2*x*(D+h+1))*∑ u, importantBaseIncidences paths u h x := by
  classical
  let collected := (univ : Finset I).sigma fun b => onBaseBucket paths b h x
  let targets := (univ : Finset V).sigma fun u =>
    (largeBranchBases paths u h x).sigma fun b => paths b ∩ successorSupport paths u
  let charge (z : Σ _ : I, BranchTuple V I) : Σ _ : V, Σ _ : I, V :=
    ⟨z.2.x, z.1, z.2.y⟩
  have maps : Set.MapsTo charge (collected : Set _) targets := by
    rintro ⟨b, w⟩ hw
    obtain ⟨counted, onBase, lower, _⟩ := mem_filter.mp (mem_sigma.mp hw).2
    obtain ⟨start, _, outside, m, middle⟩ := mem_branchTuples.mp counted
    apply mem_sigma.mpr
    refine ⟨mem_univ _, mem_sigma.mpr ⟨?_, mem_inter.mpr ⟨onBase, ?_⟩⟩⟩
    · exact mem_filter.mpr ⟨mem_univ _, outside, (branchesThrough_card free outside) ▸ lower⟩
    · exact mem_successorSupport.mpr ⟨m, middle.middle_step⟩
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
    have loc := members hw
    change b' = b ∧ w.x = u ∧ w.y = v at loc
    obtain ⟨hb, hu, hv⟩ := loc
    subst b'
    obtain ⟨_, hy, _, lt⟩ := mem_filter.mp (mem_sigma.mp (mem_filter.mp hw).1).2
    have leftCount : (branchesThrough paths b h u).card ≤ 2*x := (hu ▸ lt).le
    have rightCount : (branchesThrough paths b h v).card ≤ D+h+1 :=
      (branchesThrough_on_base free (hv ▸ hy)).trans (by have e := degree v; omega)
    let decode (a : Σ _ : I, BranchTuple V I) := ((a.2.left, a.2.leftStart), (a.2.right, a.2.rightStart))
    have leSize : F.card ≤ (branchesThrough paths b h u ×ˢ branchesThrough paths b h v).card := by
      apply card_le_card_of_injOn decode
      · rintro ⟨i, w⟩ hw
        have loc := members hw
        change i = b ∧ w.x = u ∧ w.y = v at loc
        obtain ⟨hi, hu, hv⟩ := loc
        subst i
        obtain ⟨subset, _, _, _⟩ := mem_filter.mp (mem_sigma.mp (mem_filter.mp hw).1).2
        have valid := mem_branchTuples.mp subset
        exact mem_product.mpr ⟨mem_branchesThrough.mpr (hu ▸ valid.1), mem_branchesThrough.mpr (hv ▸ valid.2.1)⟩
      · rintro ⟨a, ⟨l, r, ls, rs, u', v'⟩⟩ h₁ ⟨c, ⟨l', r', ls', rs', u'', v''⟩⟩ h₂ e
        have loc₁ := members h₁
        have loc₂ := members h₂
        change a = b ∧ u' = u ∧ v' = v at loc₁
        change c = b ∧ u'' = u ∧ v'' = v at loc₂
        obtain ⟨ha, hu', hv'⟩ := loc₁
        obtain ⟨hc, hu'', hv''⟩ := loc₂
        subst a
        subst c
        subst u'
        subst v'
        subst u''
        subst v''
        change ((l, ls), (r, rs)) = ((l', ls'), (r', rs')) at e
        simp only [Prod.mk.injEq] at e
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := e
        rfl
    exact leSize.trans (by rw [card_product]; exact Nat.mul_le_mul leftCount rightCount)
  have result : collected.card ≤ (2*x*(D+h+1))*targets.card := by
    rw [card_eq_sum_card_fiberwise maps]
    calc
      _ ≤ ∑ _ ∈ targets, 2*x*(D+h+1) := sum_le_sum fun z _ => fibers z
      _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  simpa only [collected, targets, card_sigma, importantBaseIncidences] using result


/-- The tuples in Q whose second endpoint is on the base, called Q₂. -/
noncomputable def onBaseBranchTuples (paths : I → Finset V) (b : I) (h : ℕ) :
    Finset (BranchTuple V I) := by
  classical
  exact (branchTuples paths b h).filter fun w => w.y ∈ paths b

theorem branchTuples_partition (paths : I → Finset V) (b : I) (h : ℕ) :
    (branchTuples paths b h).card =
      (onBaseBranchTuples paths b h).card+(offBaseBranchTuples paths b h).card := by
  classical
  exact (card_filter_add_card_filter_not (s := branchTuples paths b h)
    (fun w : BranchTuple V I => w.y ∈ paths b)).symm

/-- The dyadic sum in Lemma 35 before the estimates for the number of
important pairs are averaged. -/
theorem lemma35_on_base_dyadic_count {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (h D : ℕ) (degree : ∀ v, (occurrences paths v).card ≤ D) :
    (∑ b, (onBaseBranchTuples paths b h).card) ≤
      ∑ j ∈ range (Nat.log 2 D+1),
        (2*(2^j)*(D+h+1))*∑ u, importantBaseIncidences paths u h (2^j) := by
  classical
  let J := range (Nat.log 2 D+1)
  have perBase (b : I) : (onBaseBranchTuples paths b h).card ≤
      ∑ j ∈ J, (onBaseBucket paths b h (2^j)).card := by
    let target := J.sigma fun j => onBaseBucket paths b h (2^j)
    have bound : (onBaseBranchTuples paths b h).card ≤ target.card := by
      apply card_le_card_of_injOn (fun w : BranchTuple V I =>
        (⟨Nat.log 2 (branchesThrough paths b h w.x).card, w⟩ : Σ _ : ℕ, BranchTuple V I))
      · intro w hw
        obtain ⟨counted, onBase⟩ := mem_filter.mp hw
        obtain ⟨start, _, outside, _, _⟩ := mem_branchTuples.mp counted
        let d := (branchesThrough paths b h w.x).card
        have hd : 0 < d := card_pos.mpr ⟨(w.left, w.leftStart), mem_branchesThrough.mpr start⟩
        have cap : d ≤ D := (branchesThrough_le_degree free outside).trans (degree w.x)
        have j := Nat.lt_succ_of_le (Nat.log_mono_right (b := 2) cap)
        have lower := Nat.pow_log_le_self 2 hd.ne'
        have upper := Nat.lt_pow_succ_log_self (by decide : 1 < 2) d
        rw [Nat.pow_succ, Nat.mul_comm] at upper
        exact mem_sigma.mpr ⟨mem_range.mpr j, mem_filter.mpr ⟨counted, onBase, lower, upper⟩⟩
      · intro w _ z _ eq
        exact congrArg (fun a : Σ _ : ℕ, BranchTuple V I => a.2) eq
    simpa only [target, card_sigma] using bound
  calc
    _ ≤ ∑ b, ∑ j ∈ J, (onBaseBucket paths b h (2^j)).card :=
      sum_le_sum (fun b _ => perBase b)
    _ = ∑ j ∈ J, ∑ b, (onBaseBucket paths b h (2^j)).card := sum_comm
    _ ≤ _ := sum_le_sum (fun j _ => lemma35_on_base_count free h (2^j) D degree)

end OnlineReachabilityPreservers
