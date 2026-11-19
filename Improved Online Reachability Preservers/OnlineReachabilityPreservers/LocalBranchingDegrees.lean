import OnlineReachabilityPreservers.BranchingDegrees
import OnlineReachabilityPreservers.LocalInducedPaths
import OnlineReachabilityPreservers.LocalOfflineCounting

/-! Branching degrees and predecessor subsystems in local path orders. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [LinearOrder I] [Fintype I]

local notation "ListBefore" => SourceAudit.BeforeIn

private def listPredecessorWindow (path : List V) (v : V) (h : ℕ) : Finset V :=
  path.toFinset.filter fun u => path.idxOf u < path.idxOf v ∧ path.idxOf v ≤ path.idxOf u + h

theorem listPredecessorWindow_card (path : List V) (v : V) (h : ℕ) :
    (listPredecessorWindow path v h).card ≤ h := by
  calc
    _ ≤ (range h).card := by
      apply card_le_card_of_injOn (fun u => path.idxOf v - path.idxOf u - 1)
      · intro u hu
        obtain ⟨_, early, close⟩ := mem_filter.mp hu
        exact mem_range.mpr (show path.idxOf v - path.idxOf u - 1 < h by omega)
      · intro x hx y hy equal
        obtain ⟨xm, xt, _⟩ := mem_filter.mp hx
        obtain ⟨_, yt, _⟩ := mem_filter.mp hy
        change path.idxOf v - path.idxOf x - 1 = path.idxOf v - path.idxOf y - 1 at equal
        exact (List.idxOf_inj (List.mem_toFinset.mp xm)).mp (by omega)
    _ = _ := card_range _

/-- The union of the preceding windows on paths through `v`. -/
def listPredecessorSupport (paths : I → List V) (v : V) (h : ℕ) : Finset V :=
  (occurrences (fun i => (paths i).toFinset) v).biUnion fun i => listPredecessorWindow (paths i) v h

omit [LinearOrder I] in
theorem mem_listPredecessorSupport {paths : I → List V} {v u : V} {h : ℕ} :
    u ∈ listPredecessorSupport paths v h ↔
      ∃ i, ListBefore paths i u v ∧ (paths i).idxOf v ≤ (paths i).idxOf u + h := by
  constructor
  · intro inside
    obtain ⟨i, hi, width⟩ := mem_biUnion.mp inside
    obtain ⟨ui, early, close⟩ := mem_filter.mp width
    have vi := (mem_occurrences (marks := fun j => (paths j).toFinset)).mp hi
    exact ⟨i, ⟨List.mem_toFinset.mp ui, List.mem_toFinset.mp vi, early⟩, close⟩
  · rintro ⟨i, ⟨ui, vi, early⟩, close⟩
    exact mem_biUnion.mpr ⟨i, mem_occurrences.mpr (List.mem_toFinset.mpr vi),
      mem_filter.mpr ⟨List.mem_toFinset.mpr ui, early, close⟩⟩

omit [LinearOrder I] in
theorem listPredecessorSupport_card (paths : I → List V) (v : V) (h : ℕ) :
    (listPredecessorSupport paths v h).card ≤ (occurrences (fun i => (paths i).toFinset) v).card * h := by
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ i ∈ occurrences (fun i => (paths i).toFinset) v, h :=
      sum_le_sum (fun i _ => listPredecessorWindow_card (paths i) v h)
    _ = _ := by simp

variable [Fintype V]

noncomputable def listBranchesThrough (paths : I → List V) (b : I) (h : ℕ) (v : V) : Finset (I × V) := by
  classical
  exact univ.filter fun w => InListBranchWindow paths b w.1 h w.2 v

omit [LinearOrder I] in
theorem mem_listBranchesThrough {paths : I → List V} {b : I} {h : ℕ} {v u : V} {i : I} :
    (i, u) ∈ listBranchesThrough paths b h v ↔ InListBranchWindow paths b i h u v := by
  classical
  simp [listBranchesThrough]

/-- Off the base, every branch starts at a distinct vertex in the near-predecessor support. -/
theorem listBranchesThrough_card {paths : I → List V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    {b : I} {v : V} {h : ℕ} (outside : v ∉ paths b) :
    (listBranchesThrough paths b h v).card = ((paths b).toFinset ∩ listPredecessorSupport paths v h).card := by
  apply card_bij (fun w _ => w.2)
  · rintro ⟨i, u⟩ hu
    obtain ⟨ub, ui, vi, after, close⟩ := mem_listBranchesThrough.mp hu
    have early : (paths i).idxOf u < (paths i).idxOf v := after.lt_of_ne fun equal =>
      outside (((List.idxOf_inj ui).mp equal) ▸ ub)
    exact mem_inter.mpr ⟨List.mem_toFinset.mpr ub, mem_listPredecessorSupport.mpr ⟨i, ⟨ui, vi, early⟩, close⟩⟩
  · rintro ⟨i, u⟩ hu ⟨j, w⟩ hw equal
    change u = w at equal
    subst w
    by_contra different
    obtain ⟨ub, ui, vi, _, _⟩ := mem_listBranchesThrough.mp hu
    obtain ⟨_, uj, vj, _, _⟩ := mem_listBranchesThrough.mp hw
    have ij : i ≠ j := fun e => different (by rw [e])
    exact outside (unique ij ui uj vi vj ▸ ub)
  · intro u hu
    obtain ⟨ub, has⟩ := mem_inter.mp hu
    obtain ⟨i, ⟨ui, vi, early⟩, close⟩ := mem_listPredecessorSupport.mp has
    exact ⟨(i, u), mem_listBranchesThrough.mpr ⟨List.mem_toFinset.mp ub, ui, vi, early.le, close⟩, rfl⟩

omit [LinearOrder I] in
/-- Off the base, any path through `v` contributes at most one branch. -/
theorem listBranchesThrough_le_degree {paths : I → List V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    {b : I} {v : V} {h : ℕ} (outside : v ∉ paths b) :
    (listBranchesThrough paths b h v).card ≤ (occurrences (fun i => (paths i).toFinset) v).card := by
  apply card_le_card_of_injOn Prod.fst
  · rintro ⟨i, u⟩ inside
    exact mem_occurrences.mpr (List.mem_toFinset.mpr (mem_listBranchesThrough.mp inside).2.2.1)
  · rintro ⟨i, u⟩ hu ⟨j, w⟩ hw equal
    change i = j at equal
    subst j
    have a := mem_listBranchesThrough.mp hu
    have c := mem_listBranchesThrough.mp hw
    have different : i ≠ b := fun e => outside (e ▸ a.2.2.1)
    obtain rfl := unique different a.2.1 a.1 c.2.1 c.1
    rfl

/-- Eligible base paths for a large branching degree at the fixed vertex. -/
def listLargeBranchBases (paths : I → List V) (v : V) (h x : ℕ) : Finset I :=
  univ.filter fun b => v ∉ paths b ∧ x ≤ ((paths b).toFinset ∩ listPredecessorSupport paths v h).card

noncomputable def listLargeBranchVertices (paths : I → List V) (b : I) (h x : ℕ) : Finset V := by
  classical
  exact univ.filter fun v => v ∉ paths b ∧ x ≤ (listBranchesThrough paths b h v).card

theorem list_sum_large_branches {paths : I → List V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (h x : ℕ) :
    (∑ b, (listLargeBranchVertices paths b h x).card) = ∑ v, (listLargeBranchBases paths v h x).card := by
  classical
  rw [← sum_occurrences]
  apply sum_congr rfl
  intro v _
  congr 1
  ext b
  simp only [occurrences, listLargeBranchVertices, listLargeBranchBases, mem_filter, mem_univ, true_and]
  exact and_congr_right fun hv => by rw [listBranchesThrough_card unique hv]

omit [LinearOrder I] [Fintype V] in
/-- Lemma 32's estimate using only the uniform degree cap. -/
theorem lemma32_list_degree_count (paths : I → List V) (v : V) (h x D : ℕ)
    (degrees : ∀ u, (occurrences (fun i => (paths i).toFinset) u).card ≤ D) :
    (listLargeBranchBases paths v h x).card*x ≤ (occurrences (fun i => (paths i).toFinset) v).card*h*D := by
  let J := listLargeBranchBases paths v h x
  let S := listPredecessorSupport paths v h
  let marks (i : I) := (paths i).toFinset
  calc
    _ = ∑ _ ∈ J, x := by simp [J]
    _ ≤ ∑ i ∈ J, (inducedPath marks S i).card := by
      apply sum_le_sum
      intro i hi
      rw [inducedPath_card]
      exact (mem_filter.mp hi).2.2
    _ ≤ ∑ i : I, (inducedPath marks S i).card :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ ≤ S.card*D := inducedPath_mass_le marks S D (fun u _ => degrees u)
    _ ≤ _ := Nat.mul_le_mul_right _ (listPredecessorSupport_card paths v h)

omit [LinearOrder I] in
private theorem list_branch_incidence_bound (paths : I → List V) (b : I) (h : ℕ) :
    (∑ v, (listBranchesThrough paths b h v).card) ≤
      ∑ u ∈ (paths b).toFinset, (occurrences (fun i => (paths i).toFinset) u).card*(h+1) := by
  classical
  let active (w : I × V) := if w.2 ∈ paths b ∧ w.2 ∈ paths w.1
    then listWindowVertices (paths w.1) w.2 h else ∅
  have atVertex (v : V) : listBranchesThrough paths b h v = occurrences active v := by
    ext ⟨i, u⟩
    constructor
    · intro hv
      obtain ⟨hb, hi, hv, after, close⟩ := mem_listBranchesThrough.mp hv
      apply mem_occurrences.mpr
      rw [show active (i, u) = listWindowVertices (paths i) u h by simp [active, hb, hi]]
      exact mem_filter.mpr ⟨List.mem_toFinset.mpr hv, after, close⟩
    · intro hv
      have used := (mem_occurrences (marks := active)).mp hv
      by_cases yes : u ∈ paths b ∧ u ∈ paths i
      · have inWindow : v ∈ listWindowVertices (paths i) u h := by simpa [active, yes] using used
        obtain ⟨present, after, nearby⟩ := mem_filter.mp inWindow
        exact mem_listBranchesThrough.mpr ⟨yes.1, yes.2, List.mem_toFinset.mp present, after, nearby⟩
      · simp [active, yes] at used
  simp only [atVertex, sum_occurrences]
  calc
    _ ≤ ∑ w : I × V, if w.2 ∈ paths b ∧ w.2 ∈ paths w.1 then h+1 else 0 := by
      apply sum_le_sum
      intro w _
      unfold active
      split
      · exact listWindowVertices_card (paths w.1) w.2 h
      · simp
    _ = ∑ u : V, ∑ i : I, if u ∈ paths b ∧ u ∈ paths i then h+1 else 0 := by
      rw [Fintype.sum_prod_type, sum_comm]
    _ = ∑ u : V, if u ∈ paths b then (occurrences (fun i => (paths i).toFinset) u).card*(h+1) else 0 := by
      apply sum_congr rfl
      intro u _
      by_cases hu : u ∈ paths b
      · simp only [hu, true_and, ite_true]
        rw [← sum_filter]
        simp [occurrences]
      · simp [hu]
    _ = _ := by
      rw [← sum_filter]
      congr 1
      ext u
      simp

omit [LinearOrder I] in
/-- The deterministic branching incidence cap of Lemma 33. -/
theorem lemma33_list_deterministic (paths : I → List V) (b : I) (h x : ℕ) :
    (listLargeBranchVertices paths b h x).card*x ≤
      ∑ u ∈ (paths b).toFinset, (occurrences (fun i => (paths i).toFinset) u).card*(h+1) := by
  classical
  calc
    _ = ∑ _ ∈ listLargeBranchVertices paths b h x, x := by simp
    _ ≤ ∑ v ∈ listLargeBranchVertices paths b h x, (listBranchesThrough paths b h v).card :=
      sum_le_sum fun _ hv => (mem_filter.mp hv).2.2
    _ ≤ ∑ v, (listBranchesThrough paths b h v).card :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ ≤ _ := list_branch_incidence_bound paths b h

/-- The size envelope assumed on each restricted list subfamily. -/
def ListInducedSizeBound (paths : I → List V) (C a b : ℝ) : Prop :=
  ∀ (S : Finset V) (J : Finset I),
    let n : ℝ := S.card
    let p : ℝ := J.card
    (∑ i : J, ((restrictListPaths paths S J i).length : ℝ)) ≤
      C*max n (max (n^a*p^(2-2*a)) (max (n^(2-2*b)*p^b) p))

omit [LinearOrder I] [Fintype V] in
/-- The inductive bound for large branches uses the actual restricted lists. -/
theorem lemma32_list_extremal_count {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (v : V) (h x : ℕ) {C a b : ℝ} (hC : 0 < C) (hx : C < (x : ℝ))
    (ha : 1/2 < a) (hb : b < 1) (prior : ListInducedSizeBound paths C a b) :
    let n : ℝ := (listPredecessorSupport paths v h).card
    ((listLargeBranchBases paths v h x).card : ℝ) ≤
      C*n/x + (C*n^a/x)^(1/(2*a-1)) + (C*n^(2-2*b)/x)^(1/(1-b)) := by
  let S := listPredecessorSupport paths v h
  let J := listLargeBranchBases paths v h x
  have natural : J.card*x ≤ ∑ i : J, (restrictListPaths paths S J i).length := by
    calc
      _ = ∑ _ : J, x := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro i _
        change x ≤ (restrictListPath (paths i.val) S).length
        rw [restrictListPath_length (simple i.val)]
        exact (mem_filter.mp i.property).2.2
  have lower : ((J.card : ℕ) : ℝ) * x ≤ ∑ i : J, ((restrictListPaths paths S J i).length : ℝ) := by
    exact_mod_cast natural
  exact count_from_size_envelope (by positivity) (by positivity) hC hx ha hb (lower.trans (prior S J))

/-- The uniform branching estimate in Lemma 33 for local path orders. -/
theorem lemma33_list_expected_count {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (D h x : ℕ) {C a b : ℝ} (hp : 0 < Fintype.card I) (hC : 0 < C) (hx : C < (x : ℝ))
    (ha : 1/2 < a) (hb : b < 1) (degrees : ∀ v, (occurrences (fun i => (paths i).toFinset) v).card ≤ D)
    (prior : ListInducedSizeBound paths C a b) :
    let z : ℝ := (D : ℝ)*h
    (∑ i, ((listLargeBranchVertices paths i h x).card : ℝ)) / (Fintype.card I : ℝ) ≤
      (Fintype.card V : ℝ) *
        (C*z/x + (C*z^a/x)^(1/(2*a-1)) + (C*z^(2-2*b)/x)^(1/(1-b))) / (Fintype.card I : ℝ) := by
  let z : ℝ := (D : ℝ)*h
  have both : (∑ i, ((listLargeBranchVertices paths i h x).card : ℝ)) =
      ∑ v, ((listLargeBranchBases paths v h x).card : ℝ) := by exact_mod_cast list_sum_large_branches unique h x
  rw [both]
  apply div_le_div_of_nonneg_right _ (show (0 : ℝ) ≤ Fintype.card I from (Nat.cast_pos.mpr hp).le)
  let envelope := C*z/x + (C*z^a/x)^(1/(2*a-1)) + (C*z^(2-2*b)/x)^(1/(1-b))
  calc
    _ ≤ ∑ _ : V, envelope := by
      apply sum_le_sum
      intro v _
      have size : ((listPredecessorSupport paths v h).card : ℝ) ≤ z := by
        change ((listPredecessorSupport paths v h).card : ℝ) ≤ (D : ℝ)*h
        exact_mod_cast (listPredecessorSupport_card paths v h).trans (Nat.mul_le_mul_right h (degrees v))
      refine (lemma32_list_extremal_count simple v h x hC hx ha hb prior).trans ?_
      have h1 : 0 ≤ 1/(2*a-1) := one_div_nonneg.mpr (by linarith)
      have h2 : 0 ≤ 1/(1-b) := one_div_nonneg.mpr (by linarith)
      dsimp only [envelope]
      gcongr
      linarith
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- The off-base tuple count is bounded by the squared branching weights of middle paths. -/
theorem lemma34_list_weighted_path_bound (paths : I → List V) (b : I) (h : ℕ) :
    (listOffBaseBranchTuples paths b h).card ≤
      ∑ i, (∑ v ∈ (paths i).toFinset \ (paths b).toFinset, (listBranchesThrough paths b h v).card)^2 := by
  classical
  let incidence (i : I) := ((paths i).toFinset \ (paths b).toFinset).sigma (listBranchesThrough paths b h)
  let tupleOf (w : (Σ _ : V, I × V) × (Σ _ : V, I × V)) : BranchTuple V I :=
    ⟨w.1.2.1, w.2.2.1, w.1.2.2, w.2.2.2, w.1.1, w.2.1⟩
  let candidates (i : I) := (incidence i ×ˢ incidence i).image tupleOf
  have sub : listOffBaseBranchTuples paths b h ⊆ univ.biUnion candidates := by
    intro w hw
    obtain ⟨hq, outside_y⟩ := mem_filter.mp hw
    obtain ⟨left, right, outside_x, _, i, mid⟩ := mem_listBranchTuples.mp hq
    have hx : Sigma.mk w.x (w.left, w.leftStart) ∈ incidence i := mem_sigma.mpr
      ⟨mem_sdiff.mpr ⟨List.mem_toFinset.mpr mid.middle_step.1, fun on => outside_x (List.mem_toFinset.mp on)⟩,
        mem_listBranchesThrough.mpr left⟩
    have hy : Sigma.mk w.y (w.right, w.rightStart) ∈ incidence i := mem_sigma.mpr
      ⟨mem_sdiff.mpr ⟨List.mem_toFinset.mpr mid.middle_step.2.1, fun on => outside_y (List.mem_toFinset.mp on)⟩,
        mem_listBranchesThrough.mpr right⟩
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_image.mpr
      ⟨(⟨w.x, (w.left, w.leftStart)⟩, ⟨w.y, (w.right, w.rightStart)⟩),
        mem_product.mpr ⟨hx, hy⟩, by cases w; rfl⟩⟩
  apply (card_le_card sub).trans
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro i _
  exact card_image_le.trans (by rw [card_product, card_sigma, pow_two])

end OnlineReachabilityPreservers
