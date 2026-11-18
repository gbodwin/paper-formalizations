import OnlineReachabilityPreservers.ClosePairs
import OnlineReachabilityPreservers.SecondMoment

/-! Predecessor subsystems and large branching degrees, Appendix A. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]

private def precedingWindow (s : Finset V) (v : V) (h : ℕ) : Finset V :=
  s.filter fun u => u < v ∧ (predecessors s v).card ≤ (predecessors s u).card + h

omit [Fintype V] in
private theorem precedingWindow_card (s : Finset V) (v : V) (h : ℕ) :
    (precedingWindow s v h).card ≤ h := by
  let rank (u : V) := (predecessors s u).card
  have hr {u : V} (hu : u ∈ precedingWindow s v h) : rank u < rank v :=
    predecessor_count_strict (mem_filter.mp hu).1 (mem_filter.mp hu).2.1
  calc
    _ ≤ (range h).card := by
      apply card_le_card_of_injOn (fun u => rank v - rank u - 1)
      · intro u hu
        have hx : rank v ≤ rank u + h := (mem_filter.mp hu).2.2
        have ht := hr hu
        apply mem_range.mpr
        change rank v - rank u - 1 < h
        omega
      · intro u hu z hz eq
        change rank v - rank u - 1 = rank v - rank z - 1 at eq
        have hu' := hr hu
        have hz' := hr hz
        exact predecessor_count_injective s (mem_filter.mp hu).1 (mem_filter.mp hz).1
          (show rank u = rank z by omega)
    _ = _ := card_range h

/-- The vertices in the preceding h positions on all paths through v. -/
def predecessorSupport (paths : I → Finset V) (v : V) (h : ℕ) : Finset V :=
  (occurrences paths v).biUnion fun i => precedingWindow (paths i) v h

omit [Fintype V] [LinearOrder I] in
theorem mem_predecessorSupport {paths : I → Finset V} {v u : V} {h : ℕ} :
    u ∈ predecessorSupport paths v h ↔
      ∃ i, v ∈ paths i ∧ u ∈ paths i ∧ u < v ∧
        (predecessors (paths i) v).card ≤ (predecessors (paths i) u).card + h := by
  constructor
  · intro hu
    obtain ⟨i, hi, hm⟩ := mem_biUnion.mp hu
    obtain ⟨hu, hv, hr⟩ := mem_filter.mp hm
    exact ⟨i, (mem_filter.mp hi).2, hu, hv, hr⟩
  · rintro ⟨i, hv, hu, hlt, hr⟩
    exact mem_biUnion.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hv⟩, mem_filter.mpr ⟨hu, hlt, hr⟩⟩

omit [Fintype V] [LinearOrder I] in
theorem predecessorSupport_card (paths : I → Finset V) (v : V) (h : ℕ) :
    (predecessorSupport paths v h).card ≤ (occurrences paths v).card * h := by
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ i ∈ occurrences paths v, h := sum_le_sum fun i _ => precedingWindow_card (paths i) v h
    _ = _ := by simp

noncomputable def branchesThrough (paths : I → Finset V) (b : I) (h : ℕ) (v : V) :
    Finset (I × V) := by
  classical
  exact univ.filter fun w => InBranchWindow paths b w.1 h w.2 v

omit [LinearOrder I] in
private theorem mem_branchesThrough {paths : I → Finset V} {b : I} {h : ℕ} {v : V} {i : I} {u : V} :
    (i, u) ∈ branchesThrough paths b h v ↔ InBranchWindow paths b i h u v := by
  classical
  simp [branchesThrough]

/-- Off the base, each branch through v gives a distinct predecessor on the base. -/
theorem branchesThrough_card {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    {b : I} {v : V} {h : ℕ} (outside : v ∉ paths b) :
    (branchesThrough paths b h v).card = (paths b ∩ predecessorSupport paths v h).card := by
  apply card_bij (fun w _ => w.2)
  · rintro ⟨i, u⟩ hu
    obtain ⟨hub, hui, hvi, huv, near⟩ := mem_branchesThrough.mp hu
    exact mem_inter.mpr ⟨hub, mem_predecessorSupport.mpr
      ⟨i, hvi, hui, huv.lt_of_ne (fun eq => outside (eq ▸ hub)), near⟩⟩
  · rintro ⟨i, u⟩ hu ⟨j, w⟩ hw eq
    change u = w at eq
    subst w
    by_contra hne
    obtain ⟨hub, hui, hvi, _, _⟩ := mem_branchesThrough.mp hu
    obtain ⟨_, huj, hvj, _, _⟩ := mem_branchesThrough.mp hw
    have hij : i ≠ j := fun e => hne (by rw [e])
    exact outside ((path_intersection_unique (by decide) free hij hui huj hvi hvj) ▸ hub)
  · intro u hu
    obtain ⟨hub, hp⟩ := mem_inter.mp hu
    obtain ⟨i, hvi, hui, hlt, near⟩ := mem_predecessorSupport.mp hp
    exact ⟨(i, u), mem_branchesThrough.mpr ⟨hub, hui, hvi, hlt.le, near⟩, rfl⟩

/-- Base paths off v whose intersection with its predecessor subsystem has at least x vertices. -/
def largeBranchBases (paths : I → Finset V) (v : V) (h x : ℕ) : Finset I :=
  univ.filter fun b => v ∉ paths b ∧ x ≤ (paths b ∩ predecessorSupport paths v h).card

noncomputable def largeBranchVertices (paths : I → Finset V) (b : I) (h x : ℕ) : Finset V := by
  classical
  exact univ.filter fun v => v ∉ paths b ∧ x ≤ (branchesThrough paths b h v).card

/-- Sum the large branching-degree counts over the base paths. -/
theorem lemma33_sum_large_branches {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (h x : ℕ) :
    (∑ b, (largeBranchVertices paths b h x).card) = ∑ v, (largeBranchBases paths v h x).card := by
  classical
  rw [← sum_occurrences]
  apply sum_congr rfl
  intro v _
  congr 1
  ext b
  simp only [occurrences, largeBranchVertices, largeBranchBases, mem_filter, mem_univ, true_and]
  exact and_congr_right fun hv => by rw [branchesThrough_card free hv]

omit [Fintype V] [LinearOrder I] [Fintype I] in
private theorem incidence_on_support (paths : I → Finset V) (J : Finset I) (S : Finset V) :
    (∑ i ∈ J, (paths i ∩ S).card) = ∑ v ∈ S, (J.filter fun i => v ∈ paths i).card := by
  simp only [card_eq_sum_ones, sum_filter]
  calc
    _ = ∑ i ∈ J, ∑ v ∈ S, if v ∈ paths i then 1 else 0 := by
      apply sum_congr rfl
      intro i _
      rw [← sum_filter, ← card_eq_sum_ones, ← card_eq_sum_ones]
      congr 1
      ext v
      simp [and_comm]
    _ = _ := sum_comm

omit [Fintype V] [LinearOrder I] in
/-- The maximum-degree bound for the first count in Lemma 32. -/
theorem lemma32_degree_count (paths : I → Finset V) (v : V) (h x D : ℕ)
    (degree_cap : ∀ u, (occurrences paths u).card ≤ D) :
    (largeBranchBases paths v h x).card*x ≤ (occurrences paths v).card*h*D := by
  let J := largeBranchBases paths v h x
  let S := predecessorSupport paths v h
  calc
    _ = ∑ _ ∈ J, x := by simp [J]
    _ ≤ ∑ i ∈ J, (paths i ∩ S).card := sum_le_sum fun i hi => (mem_filter.mp hi).2.2
    _ = ∑ u ∈ S, (J.filter fun i => u ∈ paths i).card := incidence_on_support _ _ _
    _ ≤ ∑ _ ∈ S, D := sum_le_sum fun u _ =>
      (card_le_card (fun i hi => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩)).trans (degree_cap u)
    _ = S.card*D := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (predecessorSupport_card paths v h)

omit [LinearOrder I] in
private theorem branch_incidence_bound (paths : I → Finset V) (b : I) (h : ℕ) :
    (∑ v, (branchesThrough paths b h v).card) ≤ ∑ u ∈ paths b, (occurrences paths u).card*(h+1) := by
  classical
  let active (w : I × V) := if w.2 ∈ paths b ∧ w.2 ∈ paths w.1
    then verticesInWindow (paths w.1) w.2 h else ∅
  have atVertex (v : V) : branchesThrough paths b h v = occurrences active v := by
    ext ⟨i, u⟩
    constructor
    · intro hv
      obtain ⟨hb, hi, hv, hle, near⟩ := mem_branchesThrough.mp hv
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      rw [show active (i, u) = verticesInWindow (paths i) u h by simp [active, hb, hi]]
      exact mem_filter.mpr ⟨hv, hle, near⟩
    · intro hv
      have hactive : v ∈ active (i, u) := (mem_filter.mp hv).2
      by_cases hs : u ∈ paths b ∧ u ∈ paths i
      · have hwin : v ∈ verticesInWindow (paths i) u h := by simpa [active, hs] using hactive
        obtain ⟨hv, hle, near⟩ := mem_filter.mp hwin
        exact mem_branchesThrough.mpr ⟨hs.1, hs.2, hv, hle, near⟩
      · simp [active, hs] at hactive
  simp only [atVertex, sum_occurrences]
  calc
    _ ≤ ∑ w : I × V, if w.2 ∈ paths b ∧ w.2 ∈ paths w.1 then h+1 else 0 := by
      apply sum_le_sum
      intro w _
      unfold active
      split
      · exact window_card (paths w.1) w.2 h
      · simp
    _ = ∑ u : V, ∑ i : I, if u ∈ paths b ∧ u ∈ paths i then h+1 else 0 := by
      rw [Fintype.sum_prod_type, sum_comm]
    _ = ∑ u : V, if u ∈ paths b then (occurrences paths u).card*(h+1) else 0 := by
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
      ext
      simp

omit [LinearOrder I] in
/-- Deterministic incidence bound in Lemma 33 before taking an expectation. -/
theorem lemma33_deterministic (paths : I → Finset V) (b : I) (h x : ℕ) :
    (largeBranchVertices paths b h x).card*x ≤ ∑ u ∈ paths b, (occurrences paths u).card*(h+1) := by
  classical
  calc
    _ = ∑ _ ∈ largeBranchVertices paths b h x, x := by simp
    _ ≤ ∑ v ∈ largeBranchVertices paths b h x, (branchesThrough paths b h v).card :=
      sum_le_sum fun _ hv => (mem_filter.mp hv).2.2
    _ ≤ ∑ v, (branchesThrough paths b h v).card :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ ≤ _ := branch_incidence_bound paths b h

/-- A path restricted to a smaller vertex set in its inherited order. -/
def inducedPath (paths : I → Finset V) (S : Finset V) (i : I) : Finset S :=
  S.attach.filter fun v => v.val ∈ paths i

/-- Restrict the vertices to S and the path indices to J, in their inherited orders. -/
def inducedPaths (paths : I → Finset V) (S : Finset V) (J : Finset I) (i : J) : Finset S :=
  inducedPath paths S i.val

omit [Fintype V] [Fintype I] in
theorem HalfBridgeFree.induced_vertices {paths : I → Finset V} {size : ℕ}
    (free : HalfBridgeFree (PathBefore paths) size) (S : Finset V) :
    HalfBridgeFree (PathBefore (inducedPath paths S)) size := by
  intro k hk b earlier
  let old : Bridge (PathBefore paths) k :=
    b.mapVertices Subtype.val Subtype.val_injective fun _ _ _ h =>
      ⟨(mem_filter.mp h.1).2, (mem_filter.mp h.2.1).2, h.2.2⟩
  exact free hk old earlier

omit [Fintype V] [Fintype I] in
theorem HalfBridgeFree.induced {paths : I → Finset V} {size : ℕ}
    (free : HalfBridgeFree (PathBefore paths) size) (S : Finset V) (J : Finset I) :
    HalfBridgeFree (PathBefore (inducedPaths paths S J)) size :=
  (free.induced_vertices S).restrict_paths J

omit [Fintype V] [LinearOrder I] [Fintype I] in
theorem inducedPath_card (paths : I → Finset V) (S : Finset V) (i : I) :
    (inducedPath paths S i).card = (paths i ∩ S).card := by
  have eq : (inducedPath paths S i).image Subtype.val = paths i ∩ S := by
    ext u
    constructor
    · intro hu
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
      exact mem_inter.mpr ⟨(mem_filter.mp hv).2, v.2⟩
    · intro hu
      obtain ⟨hi, hs⟩ := mem_inter.mp hu
      exact mem_image.mpr ⟨⟨u, hs⟩, mem_filter.mpr ⟨mem_attach _ _, hi⟩, rfl⟩
  rw [← eq, card_image_of_injective _ Subtype.val_injective]

omit [Fintype V] [LinearOrder I] [Fintype I] in
theorem inducedPaths_card (paths : I → Finset V) (S : Finset V) {J : Finset I} (i : J) :
    (inducedPaths paths S J i).card = (paths i.val ∩ S).card :=
  inducedPath_card paths S i.val

omit [Fintype V] [LinearOrder I] in
/-- The lower incidence count for applying the inductive extremal bound in Lemma 32. -/
theorem lemma32_induced_incidence (paths : I → Finset V) (v : V) (h x : ℕ) :
    let J := largeBranchBases paths v h x
    let S := predecessorSupport paths v h
    J.card*x ≤ ∑ i : J, (inducedPaths paths S J i).card := by
  calc
    _ = ∑ _ : largeBranchBases paths v h x, x := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      rw [inducedPaths_card]
      exact (mem_filter.mp i.2).2.2

/-- The inductive incidence bound on restrictions to a vertex set and path subfamily. -/
def InducedSizeBound (paths : I → Finset V) (C a b : ℝ) : Prop :=
  ∀ (S : Finset V) (J : Finset I), HalfBridgeFree (PathBefore (inducedPaths paths S J)) 4 →
    let n : ℝ := S.card
    let p : ℝ := J.card
    (∑ i : J, ((inducedPaths paths S J i).card : ℝ)) ≤
      C*max n (max (n^a*p^(2-2*a)) (max (n^(2-2*b)*p^b) p))

private theorem count_from_power {m x A r : ℝ} (hm : 0 < m) (hx : 0 < x) (hr : r < 1)
    (bound : m*x ≤ A*m^r) : m ≤ (A/x)^(1/(1-r)) := by
  have power : m^(1-r) ≤ A/x := by
    apply (le_div_iff₀ hx).mpr
    rw [Real.rpow_sub hm, Real.rpow_one, div_mul_eq_mul_div,
      div_le_iff₀ (Real.rpow_pos_of_pos hm _)]
    exact bound
  have e : 0 < 1-r := sub_pos.mpr hr
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hm.le _) power (one_div_pos.mpr e).le
  rw [← Real.rpow_mul hm.le, mul_one_div, div_self e.ne', Real.rpow_one] at hp
  exact hp

/-- Solve the incidence-size envelope for the number of paths of length at least x. -/
theorem count_from_size_envelope {m n x C a b : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hC : 0 < C) (hx : C < x) (ha : 1/2 < a) (hb : b < 1)
    (bound : m*x ≤ C*max n (max (n^a*m^(2-2*a)) (max (n^(2-2*b)*m^b) m))) :
    m ≤ C*n/x + (C*n^a/x)^(1/(2*a-1)) + (C*n^(2-2*b)/x)^(1/(1-b)) := by
  have hx' := hC.trans hx
  have t₀ : 0 ≤ C*n/x := by positivity
  have t₁ : 0 ≤ (C*n^a/x)^(1/(2*a-1)) := by positivity
  have t₂ : 0 ≤ (C*n^(2-2*b)/x)^(1/(1-b)) := by positivity
  rcases hm.eq_or_lt with eq | hm
  · rw [← eq]
    positivity
  simp_rw [mul_max_of_nonneg _ _ hC.le] at bound
  rcases le_max_iff.mp bound with h₀ | bound
  · have h := (le_div_iff₀ hx').mpr h₀
    linarith only [h, t₁, t₂]
  rcases le_max_iff.mp bound with h₁ | bound
  · have h := count_from_power hm hx' (show 2-2*a < 1 by linarith)
      (show m*x ≤ (C*n^a)*m^(2-2*a) by simpa only [mul_assoc] using h₁)
    rw [show 1-(2-2*a) = 2*a-1 by ring] at h
    linarith only [h, t₀, t₂]
  rcases le_max_iff.mp bound with h₂ | h₃
  · have h := count_from_power hm hx' hb
      (show m*x ≤ (C*n^(2-2*b))*m^b by simpa only [mul_assoc] using h₂)
    linarith only [h, t₀, t₁]
  · have h : C*m < m*x := by
      simpa only [mul_comm C m] using mul_lt_mul_of_pos_left hx hm
    exact (not_lt_of_ge h₃ h).elim

omit [Fintype V] in
/-- The extremal part of Lemma 32, using the bound on the actual induced predecessor system. -/
theorem lemma32_extremal_count {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (v : V) (h x : ℕ) {C a b : ℝ} (hC : 0 < C) (hx : C < (x : ℝ))
    (ha : 1/2 < a) (hb : b < 1)
    (input : InducedSizeBound paths C a b) :
    let n : ℝ := (predecessorSupport paths v h).card
    ((largeBranchBases paths v h x).card : ℝ) ≤
      C*n/x + (C*n^a/x)^(1/(2*a-1)) + (C*n^(2-2*b)/x)^(1/(1-b)) := by
  let S := predecessorSupport paths v h
  let J := largeBranchBases paths v h x
  have low : ((J.card : ℕ) : ℝ) * x ≤ ∑ i : J, ((inducedPaths paths S J i).card : ℝ) := by
    exact_mod_cast lemma32_induced_incidence paths v h x
  exact count_from_size_envelope (by positivity) (by positivity) hC hx ha hb
    (low.trans (input S J (free.induced S J)))

/-- Uniformly averaging over the base paths is a finite double count. -/
theorem lemma33_uniform_average {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (h x : ℕ) (hp : 0 < Fintype.card I) {B : ℝ}
    (count : ∀ v, ((largeBranchBases paths v h x).card : ℝ) ≤ B) :
    (∑ b, ((largeBranchVertices paths b h x).card : ℝ)) / (Fintype.card I : ℝ) ≤
      (Fintype.card V : ℝ)*B / (Fintype.card I : ℝ) := by
  have eql : (∑ b, ((largeBranchVertices paths b h x).card : ℝ)) =
      ∑ v, ((largeBranchBases paths v h x).card : ℝ) := by
    exact_mod_cast lemma33_sum_large_branches free h x
  rw [eql]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ _ : V, B := sum_le_sum fun v _ => count v
    _ = _ := by simp

/-- Lemma 33's expected count in terms of the uniform degree and inductive size bounds. -/
theorem lemma33_expected_count {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (D h x : ℕ) {C a b : ℝ} (hp : 0 < Fintype.card I) (hC : 0 < C) (hx : C < (x : ℝ))
    (ha : 1/2 < a) (hb : b < 1) (degree_cap : ∀ v, (occurrences paths v).card ≤ D)
    (input : InducedSizeBound paths C a b) :
    let z : ℝ := (D : ℝ)*h
    (∑ i, ((largeBranchVertices paths i h x).card : ℝ)) / (Fintype.card I : ℝ) ≤
      (Fintype.card V : ℝ) *
        (C*z/x + (C*z^a/x)^(1/(2*a-1)) + (C*z^(2-2*b)/x)^(1/(1-b))) / (Fintype.card I : ℝ) := by
  let z : ℝ := (D : ℝ)*h
  apply lemma33_uniform_average free h x hp
  intro v
  have small : ((predecessorSupport paths v h).card : ℝ) ≤ z := by
    change ((predecessorSupport paths v h).card : ℝ) ≤ (D : ℝ)*h
    exact_mod_cast (predecessorSupport_card paths v h).trans (Nat.mul_le_mul_right h (degree_cap v))
  have lower := lemma32_extremal_count free v h x hC hx ha hb input
  refine lower.trans ?_
  have h1 : 0 ≤ 1/(2*a-1) := by
    apply one_div_nonneg.mpr
    linarith
  have h2 : 0 ≤ 1/(1-b) := by
    apply one_div_nonneg.mpr
    linarith
  gcongr
  linarith

/-- The tuples with both endpoints off the base path, called Q₁ in Appendix A. -/
noncomputable def offBaseBranchTuples (paths : I → Finset V) (b : I) (h : ℕ) : Finset (BranchTuple V I) :=
  (branchTuples paths b h).filter fun w => w.y ∉ paths b

/-- The first upper bound on Q₁ in Lemma 34, summing over middle paths. -/
theorem lemma34_weighted_path_bound (paths : I → Finset V) (b : I) (h : ℕ) :
    (offBaseBranchTuples paths b h).card ≤
      ∑ i, (∑ v ∈ paths i \ paths b, (branchesThrough paths b h v).card)^2 := by
  classical
  let incidence (i : I) := (paths i \ paths b).sigma (branchesThrough paths b h)
  let tupleOf (w : (Σ _ : V, I × V) × (Σ _ : V, I × V)) : BranchTuple V I :=
    ⟨w.1.2.1, w.2.2.1, w.1.2.2, w.2.2.2, w.1.1, w.2.1⟩
  let candidates (i : I) := (incidence i ×ˢ incidence i).image tupleOf
  have sub : offBaseBranchTuples paths b h ⊆ univ.biUnion candidates := by
    intro w hw
    obtain ⟨hq, outside_y⟩ := mem_filter.mp hw
    obtain ⟨left, right, outside_x, i, mid⟩ := mem_branchTuples.mp hq
    have hx : Sigma.mk w.x (w.left, w.leftStart) ∈ incidence i :=
      mem_sigma.mpr ⟨mem_sdiff.mpr ⟨mid.middle_step.1, outside_x⟩, mem_branchesThrough.mpr left⟩
    have hy : Sigma.mk w.y (w.right, w.rightStart) ∈ incidence i :=
      mem_sigma.mpr ⟨mem_sdiff.mpr ⟨mid.middle_step.2.1, outside_y⟩, mem_branchesThrough.mpr right⟩
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_image.mpr
      ⟨(⟨w.x, (w.left, w.leftStart)⟩, ⟨w.y, (w.right, w.rightStart)⟩),
        mem_product.mpr ⟨hx, hy⟩, by cases w; rfl⟩⟩
  apply (card_le_card sub).trans
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro i _
  exact card_image_le.trans (by rw [card_product, card_sigma, pow_two])

omit [LinearOrder V] [Fintype V] in
private theorem weighted_dyadic_square (S : Finset V) (D : V → ℕ) (L : ℕ)
    (covers : ∀ v ∈ S, Nat.log 2 (D v) < L) :
    (∑ v ∈ S, D v)^2 ≤ 4*L * ∑ j ∈ range L,
      (2^j)^2 * (S.filter fun v => 0 < D v ∧ Nat.log 2 (D v) = j).card^2 := by
  let positive := S.filter fun v => 0 < D v
  let part (j : ℕ) := positive.filter fun v => Nat.log 2 (D v) = j
  let upper (j : ℕ) := 2^j * (part j).card
  have splitSum : (∑ v ∈ S, D v) = ∑ j ∈ range L, ∑ v ∈ part j, D v := calc
    _ = ∑ v ∈ positive, D v := by
      dsimp only [positive]
      rw [sum_filter]
      apply sum_congr rfl
      intro v _
      by_cases hv : 0 < D v
      · simp [hv]
      · simp [Nat.eq_zero_of_not_pos hv]
    _ = _ := (sum_fiberwise_of_maps_to
      (fun v hv => mem_range.mpr (covers v (mem_filter.mp hv).1)) D).symm
  have hpart (j : ℕ) : (∑ v ∈ part j, D v) ≤ 2 * upper j := calc
    _ ≤ ∑ _ ∈ part j, 2*2^j := by
      apply sum_le_sum
      intro v hv
      have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (D v)
      rw [(mem_filter.mp hv).2, Nat.pow_succ, Nat.mul_comm] at h
      exact h.le
    _ = _ := by simp [upper, mul_comm, mul_assoc]
  have bound : (∑ v ∈ S, D v) ≤ 2*∑ j ∈ range L, upper j := by
    rw [splitSum, mul_sum]
    exact sum_le_sum fun j _ => hpart j
  have CS := sum_mul_sq_le_sq_mul_sq (R := ℕ) (range L) (fun _ => 1) upper
  have hsq : (∑ j ∈ range L, upper j)^2 ≤ L * ∑ j ∈ range L, (upper j)^2 := by
    simpa using CS
  calc
    _ ≤ (2*∑ j ∈ range L, upper j)^2 := Nat.pow_le_pow_left bound _
    _ = 4*(∑ j ∈ range L, upper j)^2 := by ring
    _ ≤ 4*(L * ∑ j ∈ range L, (upper j)^2) := Nat.mul_le_mul_left _ hsq
    _ = _ := by
      rw [← mul_assoc]
      congr 1
      apply sum_congr rfl
      intro j _
      simp only [upper, part, positive, filter_filter, mul_pow]

/-- The off-base dyadic sets whose restricted path moments occur in Lemma 34. -/
noncomputable def degreeBucket (paths : I → Finset V) (b : I) (h j : ℕ) : Finset V := by
  classical
  exact (univ \ paths b).filter fun v =>
    0 < (branchesThrough paths b h v).card ∧ Nat.log 2 (branchesThrough paths b h v).card = j

omit [LinearOrder I] in
theorem degreeBucket_subset_large (paths : I → Finset V) (b : I) (h j : ℕ) :
    degreeBucket paths b h j ⊆ largeBranchVertices paths b h (2^j) := by
  intro v hv
  obtain ⟨hb, hp, hl⟩ := mem_filter.mp hv
  have hpow := Nat.pow_log_le_self 2 hp.ne'
  rw [hl] at hpow
  exact mem_filter.mpr ⟨mem_univ _, (mem_sdiff.mp hb).2, hpow⟩

/-- A finite version of the dyadic Cauchy–Schwarz step in Lemma 34. -/
theorem lemma34_dyadic_moment {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (b : I) (h : ℕ) :
    let L := Nat.log 2 (Fintype.card V) + 1
    (offBaseBranchTuples paths b h).card ≤
      4*L * ∑ j ∈ range L, (2^j)^2 * ∑ i, (paths i ∩ degreeBucket paths b h j).card^2 := by
  classical
  let L := Nat.log 2 (Fintype.card V) + 1
  let D (v : V) := (branchesThrough paths b h v).card
  have covers (i : I) (v : V) (hv : v ∈ paths i \ paths b) : Nat.log 2 (D v) < L := by
    have d_eq : D v = (paths b ∩ predecessorSupport paths v h).card :=
      branchesThrough_card free (mem_sdiff.mp hv).2
    rw [d_eq]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (card_le_univ _))
  have same (i : I) (j : ℕ) :
      ((paths i \ paths b).filter fun v => 0 < D v ∧ Nat.log 2 (D v) = j) =
        paths i ∩ degreeBucket paths b h j := by
    ext v
    simp only [degreeBucket, mem_filter, mem_sdiff, mem_inter, mem_univ, true_and, D]
    tauto
  refine (lemma34_weighted_path_bound paths b h).trans ?_
  calc
    _ ≤ ∑ i : I, 4*L * ∑ j ∈ range L, (2^j)^2 * (paths i ∩ degreeBucket paths b h j).card^2 := by
      apply sum_le_sum
      intro i _
      have h := weighted_dyadic_square (paths i \ paths b) D L (covers i)
      simp only [same] at h
      exact h
    _ = _ := by
      rw [← mul_sum, sum_comm]
      simp only [mul_sum, L]

omit [Fintype V] in
/-- The second-moment estimate on any nonempty sampled vertex set.
The restricted system inherits the bridge condition and the incidence budget. -/
theorem sampled_vertex_moment {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (S : Finset V) (hS : 0 < S.card) (D : ℕ) (hD : 0 < D) {L C a b : ℝ}
    (hL : 0 < L) (hC : 0 < C) (ha₀ : 1/2 ≤ a) (ha₁ : a < 3/4) (hb₀ : 1/2 < b) (hb₁ : b ≤ 1)
    (cap : ∀ i, ((paths i).card : ℝ) ≤ L)
    (degree_cap : ∀ u ∈ S, (occurrences paths u).card ≤ D)
    (input : InducedSizeBound paths C a b) :
    let n : ℝ := S.card
    let d : ℝ := D
    (∑ i, ((paths i ∩ S).card : ℝ)^2) ≤
      2*C*n*(L+d) +
      (1/(3-4*a)+1)*C^(1/(2-2*a))*n^(3/2 : ℝ)*d^((3-4*a)/(2-2*a)) +
      (1/(2*b-1)+1)*C^(1/b)*n^(1/b)*d^((2*b-1)/b) := by
  let restricted := inducedPath paths S
  have eqCard : Fintype.card S = S.card := by simp
  have hcap (i : I) : ((restricted i).card : ℝ) ≤ L := by
    change ((inducedPath paths S i).card : ℝ) ≤ L
    rw [inducedPath_card]
    have smaller : ((paths i ∩ S).card : ℝ) ≤ (paths i).card := by
      exact_mod_cast card_le_card (inter_subset_left : paths i ∩ S ⊆ paths i)
    exact smaller.trans (cap i)
  have htotal : (∑ i, (restricted i).card) ≤ S.card*D := calc
    _ = ∑ u ∈ S, (occurrences paths u).card := by
      simpa only [restricted, inducedPath_card, occurrences] using incidence_on_support paths univ S
    _ ≤ ∑ _ ∈ S, D := sum_le_sum fun u hu => degree_cap u hu
    _ = _ := by simp
  have htotalR : (∑ i, ((restricted i).card : ℝ)) ≤ (Fintype.card S : ℝ) * D := by
    rw [eqCard]
    exact_mod_cast htotal
  have moment := lemma31_acyclic_moment restricted (free.induced_vertices S)
    (show 0 < Fintype.card S by simpa only [eqCard] using hS) (show (0 : ℝ) < D by exact_mod_cast hD)
    hL hC ha₀ ha₁ hb₀ hb₁ hcap htotalR (by
      intro J _
      have h := input S J (free.induced S J)
      change (∑ i : J, ((restricted i.val).card : ℝ)) ≤ _ at h
      have sum_eq : (∑ i : J, ((restricted i.val).card : ℝ)) =
          ∑ i ∈ J, ((restricted i).card : ℝ) :=
        J.sum_coe_sort (fun i : I => ((restricted i).card : ℝ))
      rw [sum_eq] at h
      simpa only [eqCard] using h)
  simpa only [restricted, inducedPath_card, eqCard] using moment

end OnlineReachabilityPreservers
