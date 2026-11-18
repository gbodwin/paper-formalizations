import OnlineReachabilityPreservers.PairwiseInitial

/-! The finite close-pair count used in Appendix A.3. -/

namespace OnlineReachabilityPreservers

open Finset

variable {A : Type*}

private def orderedPairs (s : Finset A) (left : A → ℕ) : Finset (A × A) :=
  (s ×ˢ s).filter (fun z => left z.1 < left z.2)

private theorem orderedPairs_card {s : Finset A} {left : A → ℕ} (hinj : Set.InjOn left s) :
    (orderedPairs s left).card = s.card.choose 2 := by
  rw [← card_image_of_injOn hinj, ← card_product_filter_lt]
  apply card_bij (fun z _ => (left z.1, left z.2))
  · intro z hz
    obtain ⟨hz, hlt⟩ := mem_filter.mp hz
    obtain ⟨h1, h2⟩ := mem_product.mp hz
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_image_of_mem _ h1, mem_image_of_mem _ h2⟩, hlt⟩
  · intro x hx y hy eq
    obtain ⟨hx1, hx2⟩ := mem_product.mp (mem_filter.mp hx).1
    obtain ⟨hy1, hy2⟩ := mem_product.mp (mem_filter.mp hy).1
    exact Prod.ext
      (hinj hx1 hy1 (congrArg Prod.fst eq))
      (hinj hx2 hy2 (congrArg Prod.snd eq))
  · rintro ⟨a, b⟩ hz
    obtain ⟨hm, hlt⟩ := mem_filter.mp hz
    obtain ⟨ha, hb⟩ := mem_product.mp hm
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hb
    exact ⟨(x, y), mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hlt⟩, rfl⟩

/-- Two pairs of positions with a strictly increasing left position, a
nondecreasing right position, and each displacement at most `h`. -/
def nearbyPairs (s : Finset A) (left right : A → ℕ) (h : ℕ) : Finset (A × A) :=
  (s ×ˢ s).filter fun z => left z.1 < left z.2 ∧ right z.1 ≤ right z.2 ∧
    left z.2 ≤ left z.1 + h ∧ right z.2 ≤ right z.1 + h

/-- A finite lower bound on the close pairs in two monotone lists of positions.
Partition the position sums into intervals of width `h+1` and count within each. -/
theorem nearbyPairs_lower (s : Finset A) (left right : A → ℕ) (L R h : ℕ)
    (left_injective : Set.InjOn left s)
    (right_mono : ∀ a ∈ s, ∀ b ∈ s, left a < left b → right a ≤ right b)
    (in_range : ∀ a ∈ s, left a ≤ L ∧ right a ≤ R) :
    (h + 1) * s.card^2 ≤ (L + R + h + 1) * (s.card + 2 * (nearbyPairs s left right h).card) := by
  classical
  let key (a : A) := (left a + right a) / (h + 1)
  let z := (L + R) / (h + 1) + 1
  let bucket (i : ℕ) := s.filter fun a => key a = i
  let pairsIn (i : ℕ) := orderedPairs (bucket i) left
  have maps : ∀ a ∈ s, key a ∈ range z := by
    intro a ha
    obtain ⟨hl, hr⟩ := in_range a ha
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.add_le_add hl hr)))
  have total : s.card = ∑ i ∈ range z, (bucket i).card :=
    card_eq_sum_card_fiberwise maps
  have close_of_pair {c : A × A} {i : ℕ} (hc : c ∈ pairsIn i) : c ∈ nearbyPairs s left right h := by
    obtain ⟨hp, hlt⟩ := mem_filter.mp hc
    obtain ⟨ha, hb⟩ := mem_product.mp hp
    obtain ⟨ha, hi⟩ := mem_filter.mp ha
    obtain ⟨hb, hj⟩ := mem_filter.mp hb
    have hright := right_mono _ ha _ hb hlt
    have hkey : (left c.1 + right c.1) / (h + 1) = (left c.2 + right c.2) / (h + 1) :=
      hi.trans hj.symm
    have eqA := Nat.mod_add_div (left c.1 + right c.1) (h + 1)
    have eqB := Nat.mod_add_div (left c.2 + right c.2) (h + 1)
    rw [← hkey] at eqB
    have hmod : (left c.2 + right c.2) % (h + 1) < h + 1 := Nat.mod_lt _ (Nat.succ_pos h)
    have hsum : left c.2 + right c.2 ≤ left c.1 + right c.1 + h := by omega
    exact mem_filter.mpr ⟨mem_product.mpr ⟨ha, hb⟩, hlt, hright, by omega, by omega⟩
  have hpair : ∑ i ∈ range z, (bucket i).card.choose 2 ≤ (nearbyPairs s left right h).card := by
    have count (i : ℕ) : (pairsIn i).card = (bucket i).card.choose 2 :=
      orderedPairs_card (fun _ ha _ hb eq => left_injective (mem_filter.mp ha).1 (mem_filter.mp hb).1 eq)
    simp_rw [← count]
    have disj : ((range z : Finset ℕ) : Set ℕ).PairwiseDisjoint pairsIn := by
      intro i _ j _ hne
      apply disjoint_left.mpr
      intro c hi hj
      have e : key c.1 = i := (mem_filter.mp (mem_product.mp (mem_filter.mp hi).1).1).2
      have e' : key c.1 = j := (mem_filter.mp (mem_product.mp (mem_filter.mp hj).1).1).2
      exact hne (e.symm.trans e')
    rw [← card_biUnion disj]
    exact card_le_card fun _ hc => by
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hc
      exact close_of_pair hi
  have hCS : s.card^2 ≤ z * ∑ i ∈ range z, (bucket i).card^2 := by
    rw [total]
    simpa using sum_mul_sq_le_sq_mul_sq (R := ℕ) (range z) (fun _ => 1) (fun i => (bucket i).card)
  have squares : ∑ i ∈ range z, (bucket i).card^2 =
      s.card + 2 * ∑ i ∈ range z, (bucket i).card.choose 2 := by
    simp only [square_choose, sum_add_distrib, mul_sum, ← total]
  have hz : (h + 1) * z ≤ L + R + h + 1 := calc
    _ = ((L + R) / (h + 1)) * (h + 1) + (h + 1) := by unfold z; ring
    _ ≤ _ := by have := Nat.div_mul_le_self (L + R) (h + 1); omega
  rw [squares] at hCS
  calc
    _ ≤ (h + 1) * (z * (s.card + 2 * ∑ i ∈ range z, (bucket i).card.choose 2)) :=
      Nat.mul_le_mul_left _ hCS
    _ = ((h + 1) * z) * (s.card + 2 * ∑ i ∈ range z, (bucket i).card.choose 2) := by
      rw [mul_assoc]
    _ ≤ _ := by gcongr

variable {V I : Type*} [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]

private def leftRank (paths : I → Finset V) (l : I) (w : I × V × V) : ℕ :=
  (predecessors (paths l) w.2.1).card

private def rightRank (paths : I → Finset V) (r : I) (w : I × V × V) : ℕ :=
  (predecessors (paths r) w.2.2).card

/-- Close pairs in a fiber of Definition 3, in increasing order of their left intersection. -/
noncomputable def closeWitnessPairs (paths : I → Finset V) (l r : I) (h : ℕ) :
    Finset ((I × V × V) × (I × V × V)) :=
  nearbyPairs (rWitnesses paths l r) (leftRank paths l) (rightRank paths r) h

theorem lemma28_fiber_lower {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (l r : I) (h : ℕ) :
    (h + 1) * (rWitnesses paths l r).card^2 ≤
      ((paths l).card + (paths r).card + h + 1) *
        ((rWitnesses paths l r).card + 2 * (closeWitnessPairs paths l r h).card) := by
  apply nearbyPairs_lower
  · intro a ha b hb he
    exact rWitnesses_left_injective free l r ha hb (predecessor_count_injective _
      (mem_rWitnesses.mp ha).on_left (mem_rWitnesses.mp hb).on_left he)
  · intro a ha b hb hlt
    have lt : a.2.1 < b.2.1 := lt_of_not_ge
      (fun ge => hlt.not_ge (predecessor_count_mono (paths l) ge))
    exact predecessor_count_mono _ (lemma24_right_monotone free (mem_rWitnesses.mp ha)
      (mem_rWitnesses.mp hb) lt)
  · intro w _
    exact ⟨card_filter_le _ _, card_filter_le _ _⟩

/-- A branch records its starting intersection on the base path and the subsequent vertex. -/
def InBranchWindow (paths : I → Finset V) (base branch : I) (h : ℕ) (start x : V) : Prop :=
  start ∈ paths base ∧ start ∈ paths branch ∧ x ∈ paths branch ∧ start ≤ x ∧
    (predecessors (paths branch) x).card ≤ (predecessors (paths branch) start).card + h

/-- An element of the sampled set Q, with the two branching paths identified by their starts. -/
structure BranchTuple (V I : Type*) where
  left : I
  right : I
  leftStart : V
  rightStart : V
  x : V
  y : V
  deriving Fintype

/-- The two windows and a middle path witness a tuple counted by Q. -/
def QualifyingBranchTuple (paths : I → Finset V) (base : I) (h : ℕ)
    (w : BranchTuple V I) : Prop :=
  InBranchWindow paths base w.left h w.leftStart w.x ∧
    InBranchWindow paths base w.right h w.rightStart w.y ∧ w.x ∉ paths base ∧
    ∃ m, IntersectionChain paths w.left m w.right w.x w.y

noncomputable def branchTuples (paths : I → Finset V) (base : I) (h : ℕ) :
    Finset (BranchTuple V I) := by
  classical
  exact univ.filter (QualifyingBranchTuple paths base h)

theorem mem_branchTuples {paths : I → Finset V} {base : I} {h : ℕ} {w : BranchTuple V I} :
    w ∈ branchTuples paths base h ↔ QualifyingBranchTuple paths base h w := by
  classical
  simp [branchTuples]

/-- A close pair charges a tuple to the earlier middle path in intersection order as base.
The positions and branching paths determine the later middle path by Lemma 24. -/
theorem lemma28_charge {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (h : ℕ) :
    (∑ lr : I × I, (closeWitnessPairs paths lr.1 lr.2 h).card) ≤
      ∑ base : I, (branchTuples paths base h).card := by
  classical
  let pairs := (univ : Finset (I × I)).sigma fun lr => closeWitnessPairs paths lr.1 lr.2 h
  let collected := (univ : Finset I).sigma fun base => branchTuples paths base h
  let charge : (Σ _ : I × I, (I × V × V) × (I × V × V)) → Σ _ : I, BranchTuple V I
    | ⟨⟨l, r⟩, ⟨b, u, v⟩, ⟨_, x, y⟩⟩ => ⟨b, ⟨l, r, u, v, x, y⟩⟩
  have bound : pairs.card ≤ collected.card := by
    apply card_le_card_of_injOn charge
    · rintro ⟨⟨l, r⟩, ⟨b, u, v⟩, ⟨m, x, y⟩⟩ hw
      have hclose : ((b, u, v), (m, x, y)) ∈ closeWitnessPairs paths l r h := (mem_sigma.mp hw).2
      obtain ⟨hp, hlt, _, hd1, hd2⟩ := mem_filter.mp hclose
      obtain ⟨hb, hm⟩ := mem_product.mp hp
      have base := mem_rWitnesses.mp hb
      have later := mem_rWitnesses.mp hm
      have ux : u < x := lt_of_not_ge (fun ge => hlt.not_ge (predecessor_count_mono (paths l) ge))
      have vy : v ≤ y := lemma24_right_monotone free base later ux
      have outside : x ∉ paths b := by
        intro hx
        exact ux.ne (path_intersection_unique (by decide) free base.left_ne_middle
          base.on_left base.middle_step.1 later.on_left hx)
      apply mem_sigma.mpr
      exact ⟨mem_univ _, mem_branchTuples.mpr
        ⟨⟨base.middle_step.1, base.on_left, later.on_left, ux.le, hd1⟩,
         ⟨base.middle_step.2.1, base.on_right, later.on_right, vy, hd2⟩,
         outside, ⟨m, later⟩⟩⟩
    · rintro ⟨⟨l, r⟩, ⟨b, u, v⟩, ⟨m, x, y⟩⟩ hw
        ⟨⟨l', r'⟩, ⟨b', u', v'⟩, ⟨m', x', y'⟩⟩ hw' eq
      have eb : b = b' := congrArg Sigma.fst eq
      have ew : (⟨l, r, u, v, x, y⟩ : BranchTuple V I) = ⟨l', r', u', v', x', y'⟩ :=
        congrArg (fun z : Σ _ : I, BranchTuple V I => z.2) eq
      subst b'
      cases ew
      have left : ((b, u, v), (m, x, y)) ∈ closeWitnessPairs paths l r h := (mem_sigma.mp hw).2
      have right : ((b, u, v), (m', x, y)) ∈ closeWitnessPairs paths l r h := (mem_sigma.mp hw').2
      have h1 := mem_rWitnesses.mp (mem_product.mp (mem_filter.mp left).1).2
      have h2 := mem_rWitnesses.mp (mem_product.mp (mem_filter.mp right).1).2
      obtain rfl := lemma24_left_injective free h1 h2
      rfl
  simpa only [pairs, collected, card_sigma] using bound

/-- Lemma 28 before absorbing the linear fiber term. Expectations over a uniformly
sampled base path use the sum of these Q counts divided by the number of paths. -/
theorem lemma28_branch_lower {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (L h : ℕ) (length : ∀ i, (paths i).card ≤ L) :
    (h + 1) * (∑ lr : I × I, (rWitnesses paths lr.1 lr.2).card^2) ≤
      (2*L + h + 1) * ((rChains paths).card + 2 * ∑ base : I, (branchTuples paths base h).card) := by
  rw [mul_sum]
  calc
    _ ≤ ∑ lr : I × I, (2*L + h + 1) *
        ((rWitnesses paths lr.1 lr.2).card + 2 * (closeWitnessPairs paths lr.1 lr.2 h).card) := by
      apply sum_le_sum
      intro lr _
      exact (lemma28_fiber_lower free lr.1 lr.2 h).trans
        (Nat.mul_le_mul_right _ (by have := length lr.1; have := length lr.2; omega))
    _ = (2*L + h + 1) * ((rChains paths).card +
        2 * ∑ lr : I × I, (closeWitnessPairs paths lr.1 lr.2 h).card) := by
      rw [← mul_sum, sum_add_distrib, ← mul_sum, rChains_card]
    _ ≤ _ := by gcongr; exact lemma28_charge free h

theorem rChains_square_le (paths : I → Finset V) :
    (rChains paths).card^2 ≤ Fintype.card I^2 *
      ∑ lr : I × I, (rWitnesses paths lr.1 lr.2).card^2 := by
  rw [rChains_card]
  have hc := sum_mul_sq_le_sq_mul_sq (R := ℕ) (univ : Finset (I × I)) (fun _ => 1)
    (fun lr => (rWitnesses paths lr.1 lr.2).card)
  simpa [Fintype.card_prod, pow_two] using hc

/-- A finite density condition under which the second moment controls the sampled Q count. -/
theorem lemma28_branch_lower_dense {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (L h : ℕ) (length : ∀ i, (paths i).card ≤ L) (hp : 0 < Fintype.card I)
    (dense : 2 * (2*L + h + 1) * (Fintype.card I)^2 ≤ (h + 1) * (rChains paths).card) :
    (h + 1) * (∑ lr : I × I, (rWitnesses paths lr.1 lr.2).card^2) ≤
      4 * (2*L + h + 1) * ∑ base : I, (branchTuples paths base h).card := by
  let r := (rChains paths).card
  let a := 2*L + h + 1
  let p := Fintype.card I
  let q := ∑ base : I, (branchTuples paths base h).card
  let m := ∑ lr : I × I, (rWitnesses paths lr.1 lr.2).card^2
  have basic : (h + 1) * m ≤ a * (r + 2*q) := lemma28_branch_lower free L h length
  have hCS : r^2 ≤ p^2 * m := rChains_square_le paths
  have linear : 2*a*r ≤ (h + 1)*m := by
    apply Nat.le_of_mul_le_mul_right (c := p^2) _ (Nat.pow_pos hp)
    have hd := Nat.mul_le_mul_right r dense
    have hs := Nat.mul_le_mul_left (h + 1) hCS
    change (2*a*p^2)*r ≤ ((h + 1)*r)*r at hd
    nlinarith only [hd, hs]
  change (h + 1) * m ≤ 4*a*q
  nlinarith only [basic, linear]

private theorem window_size_budget {L h p M : ℕ}
    (length : L*p ≤ 4*M) (window : h*p ≤ M) (long : 8*p ≤ M) :
    (2*L+h+1)*p ≤ 10*M := by
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  omega

/-- The incidence lower count supplies the density condition of Lemma 28.
The length and threshold inequalities use the average path length m/p
and average vertex degree m/n with denominators cleared. -/
theorem lemma28_from_incidence {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (L h : ℕ) (length : ∀ i, (paths i).card ≤ L)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (hdense : 16 * Fintype.card V ≤ ∑ i, (paths i).card)
    (hlong : 8 * Fintype.card I ≤ ∑ i, (paths i).card)
    (avg_length : L * Fintype.card I ≤ 4 * ∑ i, (paths i).card)
    (window_le_avg : h * Fintype.card I ≤ ∑ i, (paths i).card)
    (window_large : 40960 * (Fintype.card V)^2 * (Fintype.card I)^2 ≤
      (h + 1) * (∑ i, (paths i).card)^3) :
    (h + 1) * (∑ lr : I × I, (rWitnesses paths lr.1 lr.2).card^2) ≤
      4 * (2*L + h + 1) * ∑ base : I, (branchTuples paths base h).card := by
  apply lemma28_branch_lower_dense free L h length hp
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).card
  let a := 2*L + h + 1
  have ha : a*p ≤ 10*M := window_size_budget avg_length window_le_avg hlong
  have lower : M^4 ≤ 2048 * n^2 * p * (rChains paths).card :=
    lemma26_chain_lower paths hn hp hdense hlong
  apply Nat.le_of_mul_le_mul_right (c := 2048*n^2*p) _ (by positivity)
  have h1 := Nat.mul_le_mul_right (4096*n^2*p^2) ha
  have h2 := Nat.mul_le_mul_right M window_large
  have h3 := Nat.mul_le_mul_left (h + 1) lower
  change (40960*n^2*p^2) * M ≤ ((h + 1)*M^3) * M at h2
  change (2*a*p^2) * (2048*n^2*p) ≤ ((h+1)*(rChains paths).card) * (2048*n^2*p)
  nlinarith only [h1, h2, h3]

/-- The lower bound on the uniform mean grows linearly with the
window parameter. The statement clears the mean and average denominators. -/
theorem lemma28_scaled_mean_lower {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (L h : ℕ) (length : ∀ i, (paths i).card ≤ L)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (hdense : 16 * Fintype.card V ≤ ∑ i, (paths i).card)
    (hlong : 8 * Fintype.card I ≤ ∑ i, (paths i).card)
    (avg_length : L * Fintype.card I ≤ 4 * ∑ i, (paths i).card)
    (window_le_avg : h * Fintype.card I ≤ ∑ i, (paths i).card)
    (window_large : 40960 * (Fintype.card V)^2 * (Fintype.card I)^2 ≤
      (h + 1) * (∑ i, (paths i).card)^3) :
    (h+1)*(∑ i, (paths i).card)^7 ≤
      (40*2048^2)*(Fintype.card V)^4*(Fintype.card I)^3*
      ∑ base : I, (branchTuples paths base h).card := by
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).card
  let a := 2*L+h+1
  let R := (rChains paths).card
  let S := ∑ lr : I × I, (rWitnesses paths lr.1 lr.2).card^2
  let Q := ∑ base : I, (branchTuples paths base h).card
  have hM : 0 < M := (Nat.mul_pos (by decide) hp).trans_le hlong
  have lower : M^4 ≤ 2048*n^2*p*R := lemma26_chain_lower paths hn hp hdense hlong
  have close : (h+1)*S ≤ 4*a*Q :=
    lemma28_from_incidence free L h length hn hp hdense hlong avg_length window_le_avg window_large
  have hwindow : a*p ≤ 10*M := window_size_budget avg_length window_le_avg hlong
  have square : M^8 ≤ 2048^2*n^4*p^4*S := calc
    M^8 = (M^4)^2 := by ring
    _ ≤ (2048*n^2*p*R)^2 := Nat.pow_le_pow_left lower 2
    _ = (2048^2*n^4*p^2)*R^2 := by ring
    _ ≤ (2048^2*n^4*p^2)*(p^2*S) := Nat.mul_le_mul_left _ (rChains_square_le paths)
    _ = _ := by ring
  change (h+1)*M^7 ≤ (40*2048^2)*n^4*p^3*Q
  apply Nat.le_of_mul_le_mul_right (c := M*p) _ (Nat.mul_pos hM hp)
  calc
    _ = ((h+1)*p)*M^8 := by ring
    _ ≤ ((h+1)*p)*(2048^2*n^4*p^4*S) := Nat.mul_le_mul_left _ square
    _ = (2048^2*n^4*p^5)*((h+1)*S) := by ring
    _ ≤ (2048^2*n^4*p^5)*(4*a*Q) := Nat.mul_le_mul_left _ close
    _ = (4*2048^2*n^4*p^4*Q)*(a*p) := by ring
    _ ≤ (4*2048^2*n^4*p^4*Q)*(10*M) := Nat.mul_le_mul_left _ hwindow
    _ = _ := by ring

/-- The uniform mean of the qualifying tuple counts controls the squared product
of the average length and degree, with denominators cleared. -/
theorem lemma28_mean_lower {paths : I → Finset V} (free : HalfBridgeFree (PathBefore paths) 4)
    (L h : ℕ) (length : ∀ i, (paths i).card ≤ L)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (hdense : 16 * Fintype.card V ≤ ∑ i, (paths i).card)
    (hlong : 8 * Fintype.card I ≤ ∑ i, (paths i).card)
    (avg_length : L * Fintype.card I ≤ 4 * ∑ i, (paths i).card)
    (window_le_avg : h * Fintype.card I ≤ ∑ i, (paths i).card)
    (window_large : 40960 * (Fintype.card V)^2 * (Fintype.card I)^2 ≤
      (h + 1) * (∑ i, (paths i).card)^3) :
    (∑ i, (paths i).card)^4 ≤ 4096 * (Fintype.card V)^2 * Fintype.card I *
      ∑ base : I, (branchTuples paths base h).card := by
  let n := Fintype.card V
  let p := Fintype.card I
  let M := ∑ i, (paths i).card
  let Q := ∑ base : I, (branchTuples paths base h).card
  have scaled := lemma28_scaled_mean_lower free L h length hn hp hdense hlong avg_length
    window_le_avg window_large
  change M^4 ≤ 4096*n^2*p*Q
  apply Nat.le_of_mul_le_mul_right (c := 40960*n^2*p^2) _ (by positivity)
  calc
    _ = (40960*n^2*p^2)*M^4 := by ring
    _ ≤ ((h+1)*M^3)*M^4 := Nat.mul_le_mul_right _ window_large
    _ = (h+1)*M^7 := by ring
    _ ≤ (40*2048^2)*n^4*p^3*Q := scaled
    _ = _ := by ring

omit [Fintype V] [Fintype I] in
/-- Off the base path, a vertex has at most one branching path in a full bridge-free system. -/
theorem branchWindow_unique {paths : I → Finset V} (free : BridgeFree (PathBefore paths) 4)
    {b l r : I} {u v x : V} {h : ℕ} (outside : x ∉ paths b)
    (hu : InBranchWindow paths b l h u x) (hv : InBranchWindow paths b r h v x) : l = r ∧ u = v := by
  obtain ⟨hub, hul, hxl, hux, _⟩ := hu
  obtain ⟨hvb, hvr, hxr, hvx, _⟩ := hv
  have hlb : l ≠ b := fun eq => outside (eq ▸ hxl)
  have hrb : r ≠ b := fun eq => outside (eq ▸ hxr)
  have hux' : u < x := hux.lt_of_ne (fun eq => outside (eq ▸ hub))
  have hvx' : v < x := hvx.lt_of_ne (fun eq => outside (eq ▸ hvb))
  by_cases eq : l = r
  · subst r
    exact ⟨rfl, path_intersection_unique (by decide) free.halfFree hlb hul hub hvr hvb⟩
  · rcases lt_trichotomy u v with huv | rfl | hvu
    · exact (free.no_three (by decide) hrb.symm hlb eq
        ⟨hub, hvb, huv⟩ ⟨hvr, hxr, hvx'⟩ ⟨hul, hxl, hux'⟩).elim
    · exact (hux'.ne (path_intersection_unique (by decide) free.halfFree eq hul hvr hxl hxr)).elim
    · exact (free.no_three (by decide) hlb.symm hrb (fun he => eq he.symm)
        ⟨hvb, hub, hvu⟩ ⟨hul, hxl, hux'⟩ ⟨hvr, hxr, hvx'⟩).elim

omit [Fintype V] [Fintype I] in
private theorem right_off_base {paths : I → Finset V} (free : BridgeFree (PathBefore paths) 4)
    {b : I} {h : ℕ} {w : BranchTuple V I} (hw : QualifyingBranchTuple paths b h w) :
    w.y ∉ paths b := by
  obtain ⟨start, _, hx, m, mid⟩ := hw
  obtain ⟨hsb, hsl, hxl, hle, _⟩ := start
  intro hy
  have hlt : w.leftStart < w.x := hle.lt_of_ne (fun eq => hx (eq ▸ hsb))
  have hbl : b ≠ w.left := fun eq => hx (eq.symm ▸ hxl)
  have hbm : b ≠ m := fun eq => hx (eq.symm ▸ mid.middle_step.1)
  exact free.no_three (by decide) mid.left_ne_middle hbl hbm ⟨hsl, hxl, hlt⟩
    mid.middle_step ⟨hsb, hy, hlt.trans mid.middle_step.2.2⟩

/-- Vertices at offsets from zero to h on a path after a specified start. -/
def verticesInWindow (s : Finset V) (start : V) (h : ℕ) : Finset V :=
  s.filter fun x => start ≤ x ∧ (predecessors s x).card ≤ (predecessors s start).card + h

omit [Fintype V] in
theorem window_card (s : Finset V) (start : V) (h : ℕ) :
    (verticesInWindow s start h).card ≤ h + 1 := by
  let rank (x : V) := (predecessors s x).card
  calc
    _ ≤ (range (h + 1)).card := by
      apply card_le_card_of_injOn (fun x => rank x - rank start)
      · intro x hx
        have hx' : rank x ≤ rank start + h := (mem_filter.mp hx).2.2
        apply mem_range.mpr
        change rank x - rank start < h + 1
        omega
      · intro x hx y hy eq
        change rank x - rank start = rank y - rank start at eq
        have hxs : rank start ≤ rank x := predecessor_count_mono s (mem_filter.mp hx).2.1
        have hys : rank start ≤ rank y := predecessor_count_mono s (mem_filter.mp hy).2.1
        exact predecessor_count_injective s (mem_filter.mp hx).1 (mem_filter.mp hy).1
          (show rank x = rank y by omega)
    _ = _ := card_range _

/-- Vertices in at least one sampled branching path. -/
def branchSupport (paths : I → Finset V) (b : I) (h : ℕ) : Finset V :=
  (paths b).biUnion fun u => (occurrences paths u).biUnion fun i => verticesInWindow (paths i) u h

omit [Fintype V] [LinearOrder I] in
theorem mem_branchSupport {paths : I → Finset V} {b : I} {h : ℕ} {x : V} :
    x ∈ branchSupport paths b h ↔ ∃ i u, InBranchWindow paths b i h u x := by
  constructor
  · intro hx
    obtain ⟨u, hu, hm⟩ := mem_biUnion.mp hx
    obtain ⟨i, hi, hw⟩ := mem_biUnion.mp hm
    obtain ⟨hxi, hle, hnear⟩ := mem_filter.mp hw
    exact ⟨i, u, hu, (mem_filter.mp hi).2, hxi, hle, hnear⟩
  · rintro ⟨i, u, hu, hi, hx, hle, hnear⟩
    exact mem_biUnion.mpr ⟨u, hu, mem_biUnion.mpr
      ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩, mem_filter.mpr ⟨hx, hle, hnear⟩⟩⟩

omit [Fintype V] [LinearOrder I] in
/-- The sampled vertices are bounded by h+1 times the incidences on the base path. -/
theorem branchSupport_card (paths : I → Finset V) (b : I) (h : ℕ) :
    (branchSupport paths b h).card ≤ ∑ u ∈ paths b, (occurrences paths u).card * (h + 1) := by
  apply card_biUnion_le.trans
  apply sum_le_sum
  intro u _
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ i ∈ occurrences paths u, (h + 1) := sum_le_sum fun i _ => window_card (paths i) u h
    _ = _ := by simp

/-- The combinatorial step of Lemma 41. The Q tuples inject into the ordered
vertex pairs of the paths restricted to the sampled subsystem. -/
theorem lemma41_branch_count {paths : I → Finset V} (free : BridgeFree (PathBefore paths) 4)
    (b : I) (h : ℕ) :
    (branchTuples paths b h).card ≤ ∑ i, (paths i ∩ branchSupport paths b h).card.choose 2 := by
  classical
  let support (i : I) := paths i ∩ branchSupport paths b h
  let covered (i : I) := (support i ×ˢ support i).filter fun p => p.1 < p.2
  let endpoints (w : BranchTuple V I) := (w.x, w.y)
  have bound : (branchTuples paths b h).card ≤ (univ.biUnion covered).card := by
    apply card_le_card_of_injOn endpoints
    · intro w hw
      obtain ⟨a, c, _, m, mid⟩ := mem_branchTuples.mp hw
      have hx : w.x ∈ branchSupport paths b h := mem_branchSupport.mpr ⟨_, _, a⟩
      have hy : w.y ∈ branchSupport paths b h := mem_branchSupport.mpr ⟨_, _, c⟩
      exact mem_biUnion.mpr ⟨m, mem_univ _, mem_filter.mpr
        ⟨mem_product.mpr ⟨mem_inter.mpr ⟨mid.middle_step.1, hx⟩,
                         mem_inter.mpr ⟨mid.middle_step.2.1, hy⟩⟩, mid.middle_step.2.2⟩⟩
    · rintro ⟨l, r, u, v, x, y⟩ hw ⟨l', r', u', v', x', y'⟩ hw' eq
      change (x, y) = (x', y') at eq
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
      have a := mem_branchTuples.mp hw
      have c := mem_branchTuples.mp hw'
      obtain ⟨rfl, rfl⟩ := branchWindow_unique free a.2.2.1 a.1 c.1
      obtain ⟨rfl, rfl⟩ := branchWindow_unique free (right_off_base free a) a.2.1 c.2.1
      rfl
  refine bound.trans (card_biUnion_le.trans ?_)
  exact sum_le_sum (fun i _ => (card_product_filter_lt (s := support i)).le)

end OnlineReachabilityPreservers
