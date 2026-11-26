import OnlineReachabilityPreservers.FrozenClippingBudgets
import OnlineReachabilityPreservers.ReverseIntersectionCopies

/-! Keep the original rows and vertices by clipping their incidence counts. -/

namespace OnlineReachabilityPreservers

open Finset

local notation "Before" => SourceAudit.BeforeIn

/-- Count ordered pairs of rows sharing a vertex. After the first common
vertex in their earlier row, each further common vertex occupies a distinct
incidence for that earlier row and its unique later reverse partner. -/
theorem listDegree_square_sub_sum_le_halfThree {k n p : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k) :
    let d := fun v => (occurrences (fun i => (paths i).toFinset) v).card
    (∑ v, (d v*d v-d v)) ≤ p*p-p+2*(∑ i, (paths i).length) := by
  classical
  let Z (i : Fin p) := (paths i).toFinset
  let P := (univ : Finset (Fin p)).offDiag
  let common (q : Fin p × Fin p) := Z q.1 ∩ Z q.2
  let early (q : Fin p × Fin p) := min q.1 q.2
  let late (q : Fin p × Fin p) := max q.1 q.2
  let extra (q : Fin p × Fin p) := (common q).filter (fun v => ∃ u ∈ common q, Before paths (early q) u v)
  let incidences := (univ : Finset (Fin p)).sigma Z
  let extras := P.sigma extra
  have inEarly (q : Fin p × Fin p) {v : Fin n} (hv : v ∈ common q) : v ∈ Z (early q) := by
    obtain ⟨left,right⟩ := mem_inter.mp hv
    rcases le_total q.1 q.2 with le | le
    · simpa only [early,min_eq_left le] using left
    · simpa only [early,min_eq_right le] using right
  have inLate (q : Fin p × Fin p) {v : Fin n} (hv : v ∈ common q) : v ∈ Z (late q) := by
    obtain ⟨left,right⟩ := mem_inter.mp hv
    rcases le_total q.1 q.2 with le | le
    · simpa only [late,max_eq_right le] using right
    · simpa only [late,max_eq_left le] using left
  have orientation {q : Fin p × Fin p} (hq : q ∈ P) : early q < late q := by
    have unequal := (mem_offDiag.mp hq).2.2
    rcases lt_or_gt_of_ne unequal with forward | backward
    · simpa only [early,late,min_eq_left forward.le,max_eq_right forward.le] using forward
    · simpa only [early,late,min_eq_right backward.le,max_eq_left backward.le] using backward
  have reverse {q : Fin p × Fin p} {v : Fin n} (hq : q ∈ P) (hv : v ∈ extra q) :
      LaterReversePartner paths v (early q) (late q) := by
    obtain ⟨commonV,u,commonU,before⟩ := mem_filter.mp hv
    have ordered := orientation hq
    have laterU := List.mem_toFinset.mp (inLate q commonU)
    have laterV := List.mem_toFinset.mp (inLate q commonV)
    rcases listBefore_total laterU laterV (listBefore_ne before) with same | opposite
    · exact (no_parallel_list_steps free (by omega) ordered.ne before same).elim
    · exact ⟨ordered,u,before,opposite⟩
  let charge (entry : extras) : Bool × incidences :=
    (decide (entry.val.1.1 < entry.val.1.2),
      ⟨⟨early entry.val.1,entry.val.2⟩,mem_sigma.mpr
        ⟨mem_univ _,inEarly entry.val.1 (mem_filter.mp ((mem_sigma.mp entry.property).2)).1⟩⟩)
  have inject : Function.Injective charge := by
    intro X Y eq
    obtain ⟨⟨q,x⟩,qMem⟩ := X
    obtain ⟨⟨r,y⟩,rMem⟩ := Y
    have Xmem := mem_sigma.mp qMem
    have Ymem := mem_sigma.mp rMem
    have earlyEq : early q = early r := congrArg (fun e => e.2.val.1) eq
    have vertexEq : x = y := congrArg (fun e => e.2.val.2) eq
    have sign : decide (q.1 < q.2) = decide (r.1 < r.2) := congrArg Prod.fst eq
    have partnerX := reverse Xmem.1 Xmem.2
    have partnerY := reverse Ymem.1 Ymem.2
    rw [← vertexEq, ← earlyEq] at partnerY
    have lateEq := laterReversePartner_unique free three partnerX partnerY
    have samePair : q = r := by
      by_cases ordered : q.1 < q.2
      · have ordered' : r.1 < r.2 := of_decide_eq_true (sign.symm.trans (decide_eq_true ordered))
        exact Prod.ext
          (by simpa only [early,min_eq_left ordered.le,min_eq_left ordered'.le] using earlyEq)
          (by simpa only [late,max_eq_right ordered.le,max_eq_right ordered'.le] using lateEq)
      · have ordered' : ¬ r.1 < r.2 := of_decide_eq_false (sign.symm.trans (decide_eq_false ordered))
        have back := lt_of_le_of_ne (le_of_not_gt ordered) ((mem_offDiag.mp Xmem.1).2.2.symm)
        have back' := lt_of_le_of_ne (le_of_not_gt ordered') ((mem_offDiag.mp Ymem.1).2.2.symm)
        exact Prod.ext
          (by simpa only [late,max_eq_left back.le,max_eq_left back'.le] using lateEq)
          (by simpa only [early,min_eq_right back.le,min_eq_right back'.le] using earlyEq)
    subst r
    subst y
    rfl
  have extraCount : (∑ q ∈ P, (extra q).card) ≤ 2*(∑ i, (paths i).length) := by
    have bound := Fintype.card_le_of_injective charge inject
    simp only [Fintype.card_coe,Fintype.card_prod,Fintype.card_bool,extras,incidences,card_sigma,Z,
      List.toFinset_card_of_nodup (simple _)] at bound
    exact bound
  have overlap (q : Fin p × Fin p) : (common q).card ≤ (extra q).card+1 := by
    have subset : extra q ⊆ common q := filter_subset _ _
    have first : ((common q) \ (extra q)).card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      by_contra distinct
      obtain ⟨xCommon,xNot⟩ := mem_sdiff.mp hx
      obtain ⟨yCommon,yNot⟩ := mem_sdiff.mp hy
      rcases listBefore_total (List.mem_toFinset.mp (inEarly q xCommon))
          (List.mem_toFinset.mp (inEarly q yCommon)) distinct with xy | yx
      · exact yNot (mem_filter.mpr ⟨yCommon,x,xCommon,xy⟩)
      · exact xNot (mem_filter.mpr ⟨xCommon,y,yCommon,yx⟩)
    have exactCount := card_sdiff_add_card_eq_card subset
    omega
  have rows (v : Fin n) : (occurrences Z v).offDiag = P.filter (fun q => v ∈ common q) := by
    ext q
    simp only [mem_offDiag,mem_filter,mem_occurrences,P,mem_univ,true_and,common,mem_inter]
    tauto
  have same : (∑ v, ((occurrences Z v).offDiag).card) = ∑ q ∈ P, (common q).card := by
    simp_rw [rows,card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [← card_filter]
    congr 1
    ext v
    simp
  have Pcount : P.card = p*p-p := by simp only [P,offDiag_card,card_univ,Fintype.card_fin]
  simp only [← offDiag_card]
  change (∑ v, ((occurrences Z v).offDiag).card) ≤ _
  rw [same]
  calc
    _ ≤ ∑ q ∈ P, ((extra q).card+1) := sum_le_sum fun q _ => overlap q
    _ = (∑ q ∈ P, (extra q).card) + (p*p-p) := by rw [sum_add_distrib]; simp [Pcount]
    _ ≤ _ := by omega

private def firstRowsAt {n p : ℕ} (paths : Fin p → List (Fin n)) (D : ℕ) (v : Fin n) : Finset (Fin p) :=
  (((occurrences (fun i => (paths i).toFinset) v).sort).take D).toFinset

/-- Delete incidences beyond the degree cap, keeping the earliest rows at
each vertex. The surviving rows keep their original vertex labels. -/
def clipListDegrees {n p : ℕ} (paths : Fin p → List (Fin n)) (D : ℕ) (i : Fin p) : List (Fin n) :=
  (paths i).filter fun v => decide (i ∈ firstRowsAt paths D v)

theorem clipListDegrees_sublist {n p : ℕ} (paths : Fin p → List (Fin n)) (D : ℕ) (i : Fin p) :
    (clipListDegrees paths D i).Sublist (paths i) := List.filter_sublist

private theorem clipListDegrees_occurrences {n p : ℕ} (paths : Fin p → List (Fin n)) (D : ℕ) (v : Fin n) :
    occurrences (fun i => (clipListDegrees paths D i).toFinset) v = firstRowsAt paths D v := by
  ext i
  simp only [mem_occurrences,List.mem_toFinset,clipListDegrees,List.mem_filter,decide_eq_true_eq]
  refine ⟨And.right,fun found => ⟨?_,found⟩⟩
  have original : i ∈ occurrences (fun i => (paths i).toFinset) v :=
    (Finset.mem_sort _).mp (List.mem_of_mem_take (List.mem_toFinset.mp found))
  have present : v ∈ (paths i).toFinset := (mem_occurrences (marks := fun i => (paths i).toFinset)).mp original
  exact List.mem_toFinset.mp present

/-- Degree clipping gives the exact new degrees and accounts for each
lost incidence once. -/
theorem clipListDegrees_counts {n p : ℕ} (paths : Fin p → List (Fin n)) (D : ℕ)
    (simple : ∀ i, (paths i).Nodup) :
    let degree := fun v => (occurrences (fun i => (paths i).toFinset) v).card
    (∀ v, (occurrences (fun i => (clipListDegrees paths D i).toFinset) v).card = min D (degree v)) ∧
      (∑ i, (clipListDegrees paths D i).length) + (∑ v, (degree v-D)) = ∑ i, (paths i).length := by
  let degree := fun v => (occurrences (fun i => (paths i).toFinset) v).card
  have cap (v : Fin n) : (occurrences (fun i => (clipListDegrees paths D i).toFinset) v).card = min D (degree v) := by
    rw [clipListDegrees_occurrences]
    unfold firstRowsAt degree
    rw [List.toFinset_card_of_nodup ((sort_nodup _ _).take),List.length_take,length_sort]
  have whole : (∑ v, degree v) = ∑ i, (paths i).length := by
    rw [sum_occurrences]
    exact sum_congr rfl fun i _ => List.toFinset_card_of_nodup (simple i)
  have simpleClipped (i : Fin p) : (clipListDegrees paths D i).Nodup :=
    (clipListDegrees_sublist paths D i).nodup (simple i)
  have clipped : (∑ i, (clipListDegrees paths D i).length) = ∑ v, min D (degree v) := by
    rw [← sum_congr rfl (fun v _ => cap v),sum_occurrences]
    exact sum_congr rfl fun i _ => (List.toFinset_card_of_nodup (simpleClipped i)).symm
  refine ⟨cap,?_⟩
  rw [clipped,← whole,← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  change min D (degree v)+(degree v-D) = degree v
  omega

/-- Total incidence loss from capping each original degree at `D`. -/
def listDegreeExcess {n p : ℕ} (paths : Fin p → List (Fin n)) (D : ℕ) : ℕ :=
  ∑ v, ((occurrences (fun i => (paths i).toFinset) v).card-D)

private theorem length_degree_clipping_loss_bounds {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    (hn : 0 < n) (hp : 0 < p)
    (dense : 8*n ≤ ∑ i, (paths i).length) (long : 8*p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    let T := listLengthExcess paths (4*M/p)
    let Y := listDegreeExcess paths (4*M/n)
    488*T ≤ M*p ∧ 504*T ≤ M*n ∧ 1008*Y ≤ (p+16)*M ∧ 976*Y ≤ (n+16)*M := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let A := 4*L-2
  let T := listLengthExcess paths L
  let Y := listDegreeExcess paths D
  have mPos : 0 < M := hn.trans_le (by omega)
  have Dpos : 0 < D := (four_average_width hn (show n ≤ M by omega)).1
  have Lpos : 0 < L := (four_average_width hp (show p ≤ M by omega)).1
  obtain ⟨degreeWidth, degreeCapacity⟩ := dense_clipping_coefficient hn dense
  obtain ⟨rowWidth, rowCapacity⟩ := dense_clipping_coefficient hp long
  let B := 4*D-2
  change 126 ≤ A at rowWidth
  change 126 ≤ B at degreeWidth
  change 61*M ≤ 4*(A*p) at rowCapacity
  change 61*M ≤ 4*(B*n) at degreeCapacity
  have rowOverflow : A*T ≤ 2*(n*n-n) := listLengthExcess_mul_le_halfTwo paths simple free (by omega) Lpos
  have degreeOverflow : (4*D-2)*Y ≤ p*p-p+2*M := by
    have bound := listDegree_square_sub_sum_le_halfThree paths simple free three
    apply le_trans _ bound
    unfold Y listDegreeExcess
    rw [mul_sum]
    exact sum_le_sum fun _ _ => overflow_le_ordered_pairs Dpos
  have squares : 64*(n*n-n) ≤ M^2 := calc
    _ ≤ 64*(n*n) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = (8*n)^2 := by ring
    _ ≤ _ := Nat.pow_le_pow_left dense 2
  have rowCharge : 488*T ≤ M*p := by
    apply (Nat.mul_le_mul_left_iff (by positivity : 0 < 8*M)).mp
    calc
      _ = 64*(61*M*T) := by ring
      _ ≤ 64*(4*(A*p)*T) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ rowCapacity)
      _ = (256*p)*(A*T) := by ring
      _ ≤ (256*p)*(2*(n*n-n)) := Nat.mul_le_mul_left _ rowOverflow
      _ = (8*p)*(64*(n*n-n)) := by ring
      _ ≤ (8*p)*M^2 := Nat.mul_le_mul_left _ squares
      _ = _ := by ring
  have degreeCharge : 1008*Y ≤ (p+16)*M := by
    calc
      _ = 8*(126*Y) := by ring
      _ ≤ 8*((4*D-2)*Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ degreeWidth)
      _ ≤ 8*(p*p-p+2*M) := Nat.mul_le_mul_left _ degreeOverflow
      _ ≤ 8*(p*p+2*M) := Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.sub_le _ _) _)
      _ = (8*p)*p+16*M := by ring
      _ ≤ (M*p)+16*M := Nat.add_le_add_right (Nat.mul_le_mul_right _ long) _
      _ = _ := by ring
  have rowChargeByVertices : 504*T ≤ M*n := calc
    _ = 4*(126*T) := by ring
    _ ≤ 4*(A*T) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ rowWidth)
    _ ≤ 4*(2*(n*n-n)) := Nat.mul_le_mul_left _ rowOverflow
    _ ≤ 4*(2*(n*n)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    _ = (8*n)*n := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ dense
  have pSquares : 64*(p*p) ≤ M^2 := calc
    _ = (8*p)^2 := by ring
    _ ≤ _ := Nat.pow_le_pow_left long 2
  have nCharge : 128*n ≤ 16*M := calc
    _ = 16*(8*n) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 16 dense
  have degreeChargeByVertices : 976*Y ≤ (n+16)*M := by
    apply (Nat.mul_le_mul_left_iff mPos).mp
    calc
      _ = 16*(61*M*Y) := by ring
      _ ≤ 16*(4*(B*n)*Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ degreeCapacity)
      _ = (64*n)*(B*Y) := by ring
      _ ≤ (64*n)*(p*p-p+2*M) := Nat.mul_le_mul_left _ degreeOverflow
      _ ≤ (64*n)*(p*p+2*M) := Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.sub_le _ _) _)
      _ = n*(64*(p*p))+(128*n)*M := by ring
      _ ≤ n*M^2+(16*M)*M := Nat.add_le_add (Nat.mul_le_mul_left _ pSquares) (Nat.mul_le_mul_right _ nCharge)
      _ = _ := by ring
  exact ⟨rowCharge,rowChargeByVertices,degreeCharge,degreeChargeByVertices⟩

private theorem list_clipping_loss_small_budget {n p k : ℕ} (paths : Fin p → List (Fin n))
    (simple : ∀ i, (paths i).Nodup) (free : HalfBridgeFree (Before paths) k) (three : 3 ≤ k)
    (hn : 0 < n) (hp : 0 < p) (count : n ≤ 157 ∨ p ≤ 156)
    (dense : 8*n ≤ ∑ i, (paths i).length) (long : 8*p ≤ ∑ i, (paths i).length) :
    let M := ∑ i, (paths i).length
    104*(listLengthExcess paths (4*M/p)+listDegreeExcess paths (4*M/n)) ≤ 51*M := by
  let M := ∑ i, (paths i).length
  let T := listLengthExcess paths (4*M/p)
  let Y := listDegreeExcess paths (4*M/n)
  obtain ⟨rowP,rowN,degreeP,degreeN⟩ := length_degree_clipping_loss_bounds paths simple free three hn hp dense long
  change 488*T ≤ M*p at rowP
  change 504*T ≤ M*n at rowN
  change 1008*Y ≤ (p+16)*M at degreeP
  change 976*Y ≤ (n+16)*M at degreeN
  change 104*(T+Y) ≤ 51*M
  rcases count with vertex | row
  · have rowLimit := rowN.trans (Nat.mul_le_mul_left M vertex)
    have degreeLimit := degreeN.trans (Nat.mul_le_mul_right M (show n+16 ≤ 173 by omega))
    have rowTotal := Nat.mul_le_mul_left 976 rowLimit
    have degreeTotal := Nat.mul_le_mul_left 504 degreeLimit
    omega
  · have rowLimit := rowP.trans (Nat.mul_le_mul_left M row)
    have degreeLimit := degreeP.trans (Nat.mul_le_mul_right M (show p+16 ≤ 172 by omega))
    have rowTotal := Nat.mul_le_mul_left 1008 rowLimit
    have degreeTotal := Nat.mul_le_mul_left 488 degreeLimit
    omega

/-- Capping both dimensions by rowwise deletions preserves the chosen
bridge exclusion at every cutoff. The displayed loss suffices for
peeling at the original averages within both budgets. -/
theorem regularization_list_frozen_after_length_degree_clipping {half : Bool} {k n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length)
    (loss : let M := ∑ i, (paths i).length
      104*(listLengthExcess paths (4*M/p)+listDegreeExcess paths (4*M/n)) ≤ 51*M) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  let D := 4*M/n
  let L := 4*M/p
  let short (i : Fin p) := (paths i).take L
  let kept := clipListDegrees short D
  let smaller := fun v => (occurrences (fun i => (short i).toFinset) v).card
  have subShort (i : Fin p) : (short i).Sublist (paths i) := List.take_sublist _ _
  have sub (i : Fin p) : (kept i).Sublist (paths i) := (clipListDegrees_sublist short D i).trans (subShort i)
  have simpleKept (i : Fin p) : (kept i).Nodup := (sub i).nodup (simple i)
  have step (i : Fin p) (x y : Fin n) (h : Before kept i x y) : Before paths i x y :=
    listBefore_of_sublist (simple i) (sub i) h
  have legal : localOrderAdmissible half k kept := by
    cases half
    · intro j size
      exact ⟨fun b => (allowed size).false (b.mapPaths id Function.injective_id step)⟩
    · intro j size b earlier
      exact allowed size (b.mapPaths id Function.injective_id step) earlier
  have pathCap (i : Fin p) : (kept i).length ≤ L :=
    (clipListDegrees_sublist short D i).length_le.trans (by simp [short])
  obtain ⟨degreeCap,degreeLoss⟩ := clipListDegrees_counts short D (fun i => (subShort i).nodup (simple i))
  have pathLoss : (∑ i, (short i).length)+listLengthExcess paths L = M := by
    unfold M listLengthExcess
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [show (short i).length = min L (paths i).length from List.length_take]
    omega
  have degreeBudget : (∑ v, (smaller v-D)) ≤ listDegreeExcess paths D := by
    unfold listDegreeExcess
    apply sum_le_sum
    intro v _
    apply Nat.sub_le_sub_right _ D
    apply card_le_card
    intro i inside
    simp only [mem_occurrences,List.mem_toFinset] at inside ⊢
    exact (subShort i).subset inside
  change (∑ i, (kept i).length)+(∑ v, (smaller v-D)) = ∑ i, (short i).length at degreeLoss
  change 104*(listLengthExcess paths L+listDegreeExcess paths D) ≤ 51*M at loss
  have mass : (∑ i, (kept i).length) ≤ M := sum_le_sum (fun i _ => (sub i).length_le)
  refine regularization_list_frozen_after_caps_with_ratios_of_mass
    (retention := 104) (vNum := 1) (vDen := 1) (pNum := 1) (pDen := 1)
    kept simpleKept legal hn hp dense long (by decide) (by decide) (by decide) (by decide)
    (by simp) (by simp) pathCap (fun v => (degreeCap v).trans_le (min_le_left _ _)) mass ?_
  change 106*M ≤ 208*(∑ i, (kept i).length)
  omega

/-- With at most 157 vertices or at most 156 paths, attain the original caps and budgets at any
full or half cutoff of at least two. In the high-density branch at
cutoffs of at least three, clipping deletes incidences in the original rows. -/
theorem regularization_list_frozen_of_small_budget_all_cutoffs {half : Bool} {k n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) (count : n ≤ 157 ∨ p ≤ 156) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  let M := ∑ i, (paths i).length
  have free : HalfBridgeFree (Before paths) k := by
    cases half
    · exact (show BridgeFree (Before paths) k from allowed).halfFree
    · exact allowed
  by_cases low : M ≤ 8*max n p
  · obtain ⟨n', hn', p', hp', clean, cleanSimple, cleanFull, mass, upper, caps⟩ :=
      regularization_list_frozen_low_mass paths simple free two hn hp dense long low
    have legal : localOrderAdmissible half k clean := by cases half; exact cleanFull; exact cleanFull.halfFree
    exact ⟨n', hn', p', hp', clean, cleanSimple, legal, by omega, upper, caps⟩
  by_cases three : 3 ≤ k
  · have vDense : 8*n ≤ M := by have sides := le_max_left n p; omega
    have pDense : 8*p ≤ M := by have sides := le_max_right n p; omega
    exact regularization_list_frozen_after_length_degree_clipping paths simple allowed hn hp dense long
      (list_clipping_loss_small_budget paths simple free three hn hp count vDense pDense)
  · apply regularization_list_frozen_of_clipping_budgets paths simple allowed two (by omega) hn hp dense long
    by_cases small : p ≤ 227
    · exact Or.inl small
    · right
      have vertices : n ≤ 157 := count.resolve_right (by omega)
      have square : n*n ≤ 157*157 := Nat.mul_le_mul vertices vertices
      omega

/-- For at most 156 paths, attain the original caps and budgets at any
full or half cutoff of at least two. In the high-density branch at
cutoffs of at least three, clipping deletes incidences in the original rows. -/
theorem regularization_list_frozen_of_small_path_budget_all_cutoffs {half : Bool} {k n p : ℕ}
    (paths : Fin p → List (Fin n)) (simple : ∀ i, (paths i).Nodup)
    (allowed : localOrderAdmissible half k paths) (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p)
    (dense : n ≤ ∑ i, (paths i).length) (long : p ≤ ∑ i, (paths i).length) (count : p ≤ 156) :
    let M := ∑ i, (paths i).length
    ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
      (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
      M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  regularization_list_frozen_of_small_budget_all_cutoffs paths simple allowed two hn hp dense long (Or.inr count)

/-- The same budget regime gives original-average caps at the
unrestricted extremum. -/
theorem localOrderExtremal_frozen_of_small_budget_all_cutoffs (n p k : ℕ) (half : Bool)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (count : n ≤ 157 ∨ p ≤ 156) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean := by
  obtain ⟨paths, simple, allowed, maximal, dense, long⟩ := localOrderExtremal_isDense n p k half hn hp
  exact ⟨paths, simple, allowed, maximal,
    regularization_list_frozen_of_small_budget_all_cutoffs paths simple allowed two hn hp dense long count⟩

/-- The same path-count regime gives original-average caps at the
unrestricted extremum. -/
theorem localOrderExtremal_frozen_of_small_path_budget_all_cutoffs (n p k : ℕ) (half : Bool)
    (two : 2 ≤ k) (hn : 0 < n) (hp : 0 < p) (count : p ≤ 156) :
    ∃ paths : Fin p → List (Fin n), (∀ i, (paths i).Nodup) ∧ localOrderAdmissible half k paths ∧
      (∀ other : Fin p → List (Fin n), (∀ i, (other i).Nodup) → localOrderAdmissible half k other →
        (∑ i, (other i).length) ≤ ∑ i, (paths i).length) ∧
      let M := ∑ i, (paths i).length
      ∃ n' ≤ n, ∃ p' ≤ p, ∃ clean : Fin p' → List (Fin n'),
        (∀ i, (clean i).Nodup) ∧ localOrderAdmissible half k clean ∧
        M ≤ 104*(∑ i, (clean i).length) ∧ (∑ i, (clean i).length) ≤ M ∧ frozenListCaps n p M clean :=
  localOrderExtremal_frozen_of_small_budget_all_cutoffs n p k half two hn hp (Or.inr count)

end OnlineReachabilityPreservers
