import OnlineReachabilityPreservers.ClosePairs
import OnlineReachabilityPreservers.GeneralInitial

/-! Close-pair charges for paths with local orders and unique intersections. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]

local notation "ListBefore" => SourceAudit.BeforeIn

/-- A fiber of Definition 3 with the left and right meeting vertices. -/
noncomputable def listRWitnesses (paths : I → List V) (l r : I) : Finset (I × V × V) := by
  classical
  exact univ.filter fun w => ListIntersectionChain paths l w.1 r w.2.1 w.2.2

theorem mem_listRWitnesses {paths : I → List V} {l r : I} {w : I × V × V} :
    w ∈ listRWitnesses paths l r ↔ ListIntersectionChain paths l w.1 r w.2.1 w.2.2 := by
  classical
  simp [listRWitnesses]

private theorem listRChains_card (paths : I → List V) :
    (listRChains paths).card = ∑ lr : I × I, (listRWitnesses paths lr.1 lr.2).card := by
  classical
  let fibers := (univ : Finset (I × I)).biUnion
    (fun lr => (listRWitnesses paths lr.1 lr.2).image (Prod.mk lr))
  have equal : listRChains paths = fibers := by
    ext ⟨lr, w⟩
    simp [fibers, mem_listRWitnesses, mem_listRChains]
  rw [equal, card_biUnion]
  · apply sum_congr rfl
    intro lr _
    exact card_image_of_injective _ fun _ _ he => congrArg Prod.snd he
  · intro lr _ lr' _ different
    apply disjoint_left.mpr
    intro w a b
    obtain ⟨_, _, rfl⟩ := mem_image.mp a
    obtain ⟨_, _, eq⟩ := mem_image.mp b
    exact different (congrArg Prod.fst eq).symm

private def listLeftRank (paths : I → List V) (l : I) (w : I × V × V) : ℕ :=
  (paths l).idxOf w.2.1

private def listRightRank (paths : I → List V) (r : I) (w : I × V × V) : ℕ :=
  (paths r).idxOf w.2.2

/-- Close positions measured on the two outer paths separately. -/
noncomputable def listCloseWitnessPairs (paths : I → List V) (l r : I) (h : ℕ) :
    Finset ((I × V × V) × (I × V × V)) :=
  nearbyPairs (listRWitnesses paths l r) (listLeftRank paths l) (listRightRank paths r) h

omit [Fintype V] [Fintype I] in
private theorem listWitnesses_distinct_middles {paths : I → List V} {l r : I} {a b : I × V × V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (one : ListIntersectionChain paths l a.1 r a.2.1 a.2.2)
    (two : ListIntersectionChain paths l b.1 r b.2.1 b.2.2)
    (order : listLeftRank paths l a < listLeftRank paths l b) : a.1 ≠ b.1 := by
  intro equal
  have meet := unique one.left_ne_middle one.on_left one.middle_step.1 two.on_left
    (equal.symm ▸ two.middle_step.1)
  exact order.ne (congrArg (paths l).idxOf meet)

/-- The position-counting inequality of Lemma 28 for locally ordered lists. -/
theorem lemma28_list_fiber_lower {paths : I → List V} (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (l r : I) (h : ℕ) :
    (h + 1) * (listRWitnesses paths l r).card^2 ≤
      ((paths l).length + (paths r).length + h + 1) *
        ((listRWitnesses paths l r).card + 2 * (listCloseWitnessPairs paths l r h).card) := by
  apply nearbyPairs_lower
  · rintro ⟨a, xa, ya⟩ ha ⟨b, xb, yb⟩ hb equal
    have one := mem_listRWitnesses.mp ha
    have two := mem_listRWitnesses.mp hb
    have sameX : xa = xb := (List.idxOf_inj one.on_left).mp equal
    subst xb
    have sameMiddle : a = b := lemma24_list_left_injective free one two
    subst b
    have sameY : ya = yb := unique one.right_earlier.ne one.on_right one.middle_step.2.1
      two.on_right two.middle_step.2.1
    subst yb
    rfl
  · intro a ha b hb earlier
    have one := mem_listRWitnesses.mp ha
    have two := mem_listRWitnesses.mp hb
    exact lemma24_list_right_monotone free (listWitnesses_distinct_middles unique one two earlier)
      one two ⟨one.on_left, two.on_left, earlier⟩
  · intro w hw
    have on := mem_listRWitnesses.mp hw
    exact ⟨(List.idxOf_lt_length_of_mem on.on_left).le, (List.idxOf_lt_length_of_mem on.on_right).le⟩

/-- A branch uses the forward window on its own path, starting at the intersection with the base. -/
def InListBranchWindow (paths : I → List V) (base branch : I) (h : ℕ) (start x : V) : Prop :=
  start ∈ paths base ∧ start ∈ paths branch ∧ x ∈ paths branch ∧
    (paths branch).idxOf start ≤ (paths branch).idxOf x ∧
    (paths branch).idxOf x ≤ (paths branch).idxOf start + h

/-- Retain an on-base right endpoint when the left start precedes it on the
base. The close-pair charges all satisfy this condition. -/
def QualifyingListBranchTuple (paths : I → List V) (base : I) (h : ℕ) (w : BranchTuple V I) : Prop :=
  InListBranchWindow paths base w.left h w.leftStart w.x ∧
    InListBranchWindow paths base w.right h w.rightStart w.y ∧ w.x ∉ paths base ∧
    (w.y ∈ paths base → w.right ≠ base ∧ ListBefore paths base w.leftStart w.y) ∧
    ∃ m, ListIntersectionChain paths w.left m w.right w.x w.y

noncomputable def listBranchTuples (paths : I → List V) (base : I) (h : ℕ) : Finset (BranchTuple V I) := by
  classical
  exact univ.filter (QualifyingListBranchTuple paths base h)

theorem mem_listBranchTuples {paths : I → List V} {base : I} {h : ℕ} {w : BranchTuple V I} :
    w ∈ listBranchTuples paths base h ↔ QualifyingListBranchTuple paths base h w := by
  classical
  simp [listBranchTuples]

/-- The tuples needed in Appendix B have both endpoints off the base. -/
noncomputable def listOffBaseBranchTuples (paths : I → List V) (base : I) (h : ℕ) : Finset (BranchTuple V I) := by
  classical
  exact (listBranchTuples paths base h).filter (fun w => w.y ∉ paths base)

private def listChargeTuple (l r : I) (a b : I × V × V) : BranchTuple V I :=
  ⟨l, r, a.2.1, a.2.2, b.2.1, b.2.2⟩

private theorem listClosePair_qualifies {paths : I → List V}
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    {l r : I} {a b : I × V × V} {h : ℕ} (near : (a, b) ∈ listCloseWitnessPairs paths l r h) :
    QualifyingListBranchTuple paths a.1 h (listChargeTuple l r a b) := by
  obtain ⟨both, left, right, dx, dy⟩ := mem_filter.mp near
  have one := mem_listRWitnesses.mp (mem_product.mp both).1
  have two := mem_listRWitnesses.mp (mem_product.mp both).2
  have outside : b.2.1 ∉ paths a.1 := by
    intro on
    have equal := unique one.left_ne_middle one.on_left one.middle_step.1 two.on_left on
    exact left.ne (congrArg (paths l).idxOf equal)
  refine ⟨⟨one.middle_step.1, one.on_left, two.on_left, left.le, dx⟩,
    ⟨one.middle_step.2.1, one.on_right, two.on_right, right, dy⟩, outside, ?_, ⟨b.1, two⟩⟩
  intro on
  have equal := unique one.right_earlier.ne one.on_right one.middle_step.2.1 two.on_right on
  refine ⟨one.right_earlier.ne, ?_⟩
  change a.2.2 = b.2.2 at equal
  change ListBefore paths a.1 a.2.1 b.2.2
  rw [← equal]
  exact one.middle_step

private theorem listClosePair_off_base {paths : I → List V} (free : BridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    {l r : I} {a b : I × V × V} {h : ℕ} (near : (a, b) ∈ listCloseWitnessPairs paths l r h) :
    b.2.2 ∉ paths a.1 := by
  intro on
  obtain ⟨both, left, _⟩ := mem_filter.mp near
  have one := mem_listRWitnesses.mp (mem_product.mp both).1
  have two := mem_listRWitnesses.mp (mem_product.mp both).2
  have strict := lemma24_list_right_strict free (listWitnesses_distinct_middles unique one two left)
    one two ⟨one.on_left, two.on_left, left⟩
  exact (listBefore_ne strict) (unique one.right_earlier.ne one.on_right one.middle_step.2.1 two.on_right on)

private theorem listClosePair_charge {paths : I → List V} (free : HalfBridgeFree (ListBefore paths) 4)
    (h : ℕ) (Q : I → Finset (BranchTuple V I))
    (accept : ∀ {l r a b}, (a, b) ∈ listCloseWitnessPairs paths l r h → listChargeTuple l r a b ∈ Q a.1) :
    (∑ lr : I × I, (listCloseWitnessPairs paths lr.1 lr.2 h).card) ≤ ∑ b, (Q b).card := by
  classical
  let incoming := (univ : Finset (I × I)).sigma fun lr => listCloseWitnessPairs paths lr.1 lr.2 h
  let outgoing := (univ : Finset I).sigma Q
  let charge : (Σ _ : I × I, (I × V × V) × (I × V × V)) → Σ _ : I, BranchTuple V I :=
    fun z => ⟨z.2.1.1, listChargeTuple z.1.1 z.1.2 z.2.1 z.2.2⟩
  have cap : incoming.card ≤ outgoing.card := by
    apply card_le_card_of_injOn charge
    · intro z hz
      exact mem_sigma.mpr ⟨mem_univ _, accept (mem_sigma.mp hz).2⟩
    · rintro ⟨⟨l, r⟩, ⟨b, u, v⟩, ⟨m, x, y⟩⟩ one
        ⟨⟨l', r'⟩, ⟨b', u', v'⟩, ⟨m', x', y'⟩⟩ two equal
      have base : b = b' := congrArg Sigma.fst equal
      have tuple : (⟨l, r, u, v, x, y⟩ : BranchTuple V I) = ⟨l', r', u', v', x', y'⟩ :=
        congrArg (fun z : Σ _ : I, BranchTuple V I => z.2) equal
      subst b'
      cases tuple
      have h₁ : ((b, u, v), (m, x, y)) ∈ listCloseWitnessPairs paths l r h := (mem_sigma.mp one).2
      have h₂ : ((b, u, v), (m', x, y)) ∈ listCloseWitnessPairs paths l r h := (mem_sigma.mp two).2
      have a := mem_listRWitnesses.mp (mem_product.mp (mem_filter.mp h₁).1).2
      have b := mem_listRWitnesses.mp (mem_product.mp (mem_filter.mp h₂).1).2
      have equal : m = m' := lemma24_list_left_injective free a b
      subst m'
      rfl
  simpa only [incoming, outgoing, card_sigma] using cap

/-- All close pairs contribute to the filtered online count. -/
theorem lemma28_list_charge {paths : I → List V} (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (h : ℕ) : (∑ lr : I × I, (listCloseWitnessPairs paths lr.1 lr.2 h).card) ≤
      ∑ b, (listBranchTuples paths b h).card :=
  listClosePair_charge free h _ (fun pair => mem_listBranchTuples.mpr (listClosePair_qualifies unique pair))

/-- With full bridge-freeness, all close pairs contribute off the base. -/
theorem lemma28_list_off_base_charge {paths : I → List V} (free : BridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (h : ℕ) : (∑ lr : I × I, (listCloseWitnessPairs paths lr.1 lr.2 h).card) ≤
      ∑ b, (listOffBaseBranchTuples paths b h).card := by
  classical
  apply listClosePair_charge free.halfFree h
  intro l r a b pair
  exact mem_filter.mpr ⟨mem_listBranchTuples.mpr (listClosePair_qualifies unique pair),
    listClosePair_off_base free unique pair⟩

private theorem lemma28_list_lower_of_count {paths : I → List V} (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (L h Q : ℕ) (length : ∀ i, (paths i).length ≤ L)
    (count : (∑ lr : I × I, (listCloseWitnessPairs paths lr.1 lr.2 h).card) ≤ Q) :
    (h + 1) * (∑ lr : I × I, (listRWitnesses paths lr.1 lr.2).card^2) ≤
      (2 * L + h + 1) * ((listRChains paths).card + 2 * Q) := by
  rw [mul_sum]
  calc
    _ ≤ ∑ lr : I × I, (2 * L + h + 1) *
        ((listRWitnesses paths lr.1 lr.2).card + 2 * (listCloseWitnessPairs paths lr.1 lr.2 h).card) := by
      apply sum_le_sum
      intro lr _
      exact (lemma28_list_fiber_lower free unique lr.1 lr.2 h).trans
        (Nat.mul_le_mul_right _ (by have := length lr.1; have := length lr.2; omega))
    _ = (2 * L + h + 1) * ((listRChains paths).card + 2 *
        ∑ lr : I × I, (listCloseWitnessPairs paths lr.1 lr.2 h).card) := by
      rw [← mul_sum, sum_add_distrib, ← mul_sum, listRChains_card]
    _ ≤ _ := by gcongr

/-- Lemma 28's lower comparison for the online tuples in local path orders. -/
theorem lemma28_list_lower {paths : I → List V} (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (L h : ℕ) (length : ∀ i, (paths i).length ≤ L) :
    (h + 1) * (∑ lr : I × I, (listRWitnesses paths lr.1 lr.2).card^2) ≤
      (2 * L + h + 1) * ((listRChains paths).card + 2 * ∑ b, (listBranchTuples paths b h).card) :=
  lemma28_list_lower_of_count free unique L h _ length (lemma28_list_charge free unique h)

/-- The same comparison for the offline tuples with both endpoints off the base. -/
theorem lemma28_list_off_base_lower {paths : I → List V} (free : BridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (L h : ℕ) (length : ∀ i, (paths i).length ≤ L) :
    (h + 1) * (∑ lr : I × I, (listRWitnesses paths lr.1 lr.2).card^2) ≤
      (2 * L + h + 1) * ((listRChains paths).card + 2 * ∑ b, (listOffBaseBranchTuples paths b h).card) :=
  lemma28_list_lower_of_count free.halfFree unique L h _ length (lemma28_list_off_base_charge free unique h)

private theorem listRChains_square_le (paths : I → List V) :
    (listRChains paths).card^2 ≤ Fintype.card I^2 *
      ∑ lr : I × I, (listRWitnesses paths lr.1 lr.2).card^2 := by
  rw [listRChains_card]
  have bound := sum_mul_sq_le_sq_mul_sq (R := ℕ) (univ : Finset (I × I)) (fun _ => 1)
    (fun lr => (listRWitnesses paths lr.1 lr.2).card)
  simpa [Fintype.card_prod, pow_two] using bound

private theorem scaled_list_branching_count (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (L h Q : ℕ) (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (hdense : 16 * Fintype.card V ≤ ∑ i, (paths i).length)
    (hlong : 8 * Fintype.card I ≤ ∑ i, (paths i).length)
    (avg_length : L * Fintype.card I ≤ 4 * ∑ i, (paths i).length)
    (window_le_avg : h * Fintype.card I ≤ ∑ i, (paths i).length)
    (window_large : 40960 * (Fintype.card V)^2 * (Fintype.card I)^2 ≤
      (h + 1) * (∑ i, (paths i).length)^3)
    (close : (h + 1) * (∑ lr : I × I, (listRWitnesses paths lr.1 lr.2).card^2) ≤
      (2 * L + h + 1) * ((listRChains paths).card + 2 * Q)) :
    (h+1)*(∑ i, (paths i).length)^7 ≤ (40*2048^2)*(Fintype.card V)^4*(Fintype.card I)^3*Q := by
  have window : (2 * L + h + 1) * Fintype.card I ≤ 10 * ∑ i, (paths i).length := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
    omega
  exact scaled_branching_count hn hp ((Nat.mul_pos (by decide) hp).trans_le hlong)
    (lemma26_list_chain_lower paths simple hn hp hdense hlong) (listRChains_square_le paths)
    close window window_large

/-- The scaled lower count for the locally ordered online system. -/
theorem lemma28_list_scaled_mean_lower {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (L h : ℕ) (length : ∀ i, (paths i).length ≤ L)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (hdense : 16 * Fintype.card V ≤ ∑ i, (paths i).length)
    (hlong : 8 * Fintype.card I ≤ ∑ i, (paths i).length)
    (avg_length : L * Fintype.card I ≤ 4 * ∑ i, (paths i).length)
    (window_le_avg : h * Fintype.card I ≤ ∑ i, (paths i).length)
    (window_large : 40960 * (Fintype.card V)^2 * (Fintype.card I)^2 ≤
      (h + 1) * (∑ i, (paths i).length)^3) :
    (h+1)*(∑ i, (paths i).length)^7 ≤
      (40*2048^2)*(Fintype.card V)^4*(Fintype.card I)^3*∑ b, (listBranchTuples paths b h).card :=
  scaled_list_branching_count paths simple L h _ hn hp hdense hlong avg_length window_le_avg window_large
    (lemma28_list_lower free unique L h length)

/-- The scaled lower count for the locally ordered offline system. -/
theorem lemma28_list_off_base_mean_lower {paths : I → List V} (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (ListBefore paths) 4)
    (unique : ∀ {i j x y}, i ≠ j → x ∈ paths i → x ∈ paths j → y ∈ paths i → y ∈ paths j → x = y)
    (L h : ℕ) (length : ∀ i, (paths i).length ≤ L)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (hdense : 16 * Fintype.card V ≤ ∑ i, (paths i).length)
    (hlong : 8 * Fintype.card I ≤ ∑ i, (paths i).length)
    (avg_length : L * Fintype.card I ≤ 4 * ∑ i, (paths i).length)
    (window_le_avg : h * Fintype.card I ≤ ∑ i, (paths i).length)
    (window_large : 40960 * (Fintype.card V)^2 * (Fintype.card I)^2 ≤
      (h + 1) * (∑ i, (paths i).length)^3) :
    (h+1)*(∑ i, (paths i).length)^7 ≤
      (40*2048^2)*(Fintype.card V)^4*(Fintype.card I)^3*∑ b, (listOffBaseBranchTuples paths b h).card :=
  scaled_list_branching_count paths simple L h _ hn hp hdense hlong avg_length window_le_avg window_large
    (lemma28_list_off_base_lower free unique L h length)

end OnlineReachabilityPreservers
