import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Log
import OnlineReachabilityPreservers.SteinerTreeRounding

/-! Exact finite ancestor thresholds for integral capacity tiers. -/

namespace OnlineReachabilityPreservers

open Finset

/-- Round a positive integer capacity up to a power of two. Zero stays zero. -/
def dyadicCapacity (units : ℕ) : ℕ :=
  if units = 0 then 0 else 2 ^ (units.log2 + 1)

theorem dyadicCapacity_bounds (units : ℕ) :
    units ≤ dyadicCapacity units ∧ dyadicCapacity units ≤ 2 * units := by
  by_cases zero : units = 0
  · simp [dyadicCapacity, zero]
  · simp only [dyadicCapacity, zero, ↓reduceIte]
    exact ⟨Nat.lt_log2_self.le, by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ (Nat.log2_self_le zero)⟩

theorem dyadicCapacity_mono : Monotone dyadicCapacity := by
  intro a b le
  by_cases zero : a = 0
  · simp [dyadicCapacity, zero]
  have pos : b ≠ 0 := (Nat.pos_of_ne_zero zero).ne' ∘ fun hb => Nat.eq_zero_of_le_zero (hb ▸ le)
  simp only [dyadicCapacity, zero, pos, ↓reduceIte]
  exact Nat.pow_le_pow_right (by decide)
    (Nat.succ_le_succ (by simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right le (b := 2)))

section History

variable {V : Type*} [DecidableEq V] [Fintype V] {height : ℕ}

private theorem historyAncestors_nonempty (v : HeightNode V height) : (historyAncestors v).Nonempty :=
  ⟨v, mem_historyAncestors.mpr List.prefix_rfl⟩

omit [DecidableEq V] [Fintype V] in
private theorem historyParent_prefix (v : HeightNode V height) : (heightParent v).val <+: v.val :=
  List.dropLast_prefix v.val

omit [DecidableEq V] [Fintype V] in
private theorem heightRoot_of_nil {v : HeightNode V height} (nil : v.val = []) : v = heightRoot :=
  Subtype.ext nil

omit [DecidableEq V] [Fintype V] in
private theorem heightParent_shorter {v : HeightNode V height} (ne : v ≠ heightRoot) :
    (heightParent v).val.length < v.val.length := by
  have pos : 0 < v.val.length := List.length_pos_of_ne_nil (fun empty => ne (heightRoot_of_nil empty))
  change v.val.dropLast.length < v.val.length
  rw [List.length_dropLast]
  omega

theorem historyAncestors_parent (v : HeightNode V height) :
    historyAncestors v = insert v (historyAncestors (heightParent v)) := by
  ext u
  simp only [mem_historyAncestors, mem_insert]
  refine ⟨fun h => ?_, fun h => h.elim (fun e => e.symm ▸ List.prefix_rfl)
    (fun p => p.trans (historyParent_prefix v))⟩
  by_cases equal : u = v
  · exact Or.inl equal
  · apply Or.inr
    change _ <+: v.val.dropLast
    rw [List.dropLast_eq_take, List.prefix_take_iff]
    have shorter : u.val.length < v.val.length :=
      lt_of_le_of_ne h.length_le (fun lengths => equal (Subtype.ext (h.eq_of_length_le lengths.ge)))
    exact ⟨h, Nat.le_sub_one_of_lt shorter⟩

private theorem historyAncestors_root :
    historyAncestors (heightRoot : HeightNode V height) = {heightRoot} := by
  ext u
  exact ⟨fun hu => mem_singleton.mpr (heightRoot_of_nil (List.prefix_nil.mp (mem_historyAncestors.mp hu))),
    fun hu => mem_historyAncestors.mpr (by rw [mem_singleton.mp hu])⟩

def rootCappedCapacity (tier : ℕ) (units : HeightNode V height → ℕ) (v : HeightNode V height) : ℕ :=
  if v = heightRoot then 2 ^ tier else min (2 ^ tier) (dyadicCapacity (units v))

/-- The ancestor minimum makes the capacities nonincreasing with depth. -/
def historyCapacityUnits (tier : ℕ) (units : HeightNode V height → ℕ) (v : HeightNode V height) : ℕ :=
  (historyAncestors v).inf' (historyAncestors_nonempty v) (rootCappedCapacity tier units)

theorem historyCapacityUnits_root (tier : ℕ) (units : HeightNode V height → ℕ) :
    historyCapacityUnits tier units heightRoot = 2 ^ tier := by
  unfold historyCapacityUnits
  simp [historyAncestors_root, rootCappedCapacity]

theorem historyCapacityUnits_le (tier : ℕ) (units : HeightNode V height → ℕ)
    {u v : HeightNode V height} (ancestor : u.val <+: v.val) :
    historyCapacityUnits tier units v ≤ rootCappedCapacity tier units u :=
  inf'_le _ (mem_historyAncestors.mpr ancestor)

theorem historyCapacityUnits_ancestor (tier : ℕ) (units : HeightNode V height → ℕ)
    {u v : HeightNode V height} (ancestor : u.val <+: v.val) :
    historyCapacityUnits tier units v ≤ historyCapacityUnits tier units u := by
  apply le_inf'
  intro a ha
  exact historyCapacityUnits_le tier units ((mem_historyAncestors.mp ha).trans ancestor)

theorem historyCapacityUnits_bounded (tier : ℕ) (units : HeightNode V height → ℕ) (v : HeightNode V height) :
    historyCapacityUnits tier units v ≤ 2 ^ tier := by
  have := historyCapacityUnits_le tier units (u := heightRoot) (v := v) List.nil_prefix
  simpa [rootCappedCapacity] using this

private theorem historyCapacityUnits_power (tier : ℕ) (units : HeightNode V height → ℕ)
    (v : HeightNode V height) :
    historyCapacityUnits tier units v = 0 ∨ ∃ k ≤ tier, historyCapacityUnits tier units v = 2 ^ k := by
  apply inf'_mem {a | a = 0 ∨ ∃ k ≤ tier, a = 2 ^ k}
  · intro a ha b hb
    rcases min_choice a b with eq | eq
    · exact eq.symm ▸ ha
    · exact eq.symm ▸ hb
  · intro a _
    change rootCappedCapacity tier units a = 0 ∨ ∃ k ≤ tier, rootCappedCapacity tier units a = 2 ^ k
    by_cases root : a = heightRoot
    · exact Or.inr ⟨tier, le_rfl, by simp [rootCappedCapacity, root]⟩
    · simp only [rootCappedCapacity, root, ↓reduceIte]
      by_cases zero : units a = 0
      · exact Or.inl (by simp [dyadicCapacity, zero])
      · simp only [dyadicCapacity, zero, ↓reduceIte]
        by_cases le : tier ≤ (units a).log2 + 1
        · exact Or.inr ⟨tier, le_rfl, min_eq_left (Nat.pow_le_pow_right (by decide) le)⟩
        · have lt := Nat.lt_of_not_ge le
          exact Or.inr ⟨_, lt.le, min_eq_right (Nat.pow_le_pow_right (by decide) lt.le)⟩

theorem historyCapacityUnits_mono (tier : ℕ) {units more : HeightNode V height → ℕ}
    (order : units ≤ more) : historyCapacityUnits tier units ≤ historyCapacityUnits tier more := by
  intro v
  apply le_inf'
  intro u hu
  have below := historyCapacityUnits_le tier units (mem_historyAncestors.mp hu)
  apply below.trans
  unfold rootCappedCapacity
  split
  · exact le_rfl
  · exact min_le_min_left _ (dyadicCapacity_mono (order u))

/-- Use an integer cutoff whose success probability is the ratio to the
parent's capacity. All positive denominators divide the sample size. -/
def historyCutoff (sampleTier tier : ℕ) (units : HeightNode V height → ℕ)
    (v : HeightNode V height) : ℕ :=
  if v = heightRoot then 2 ^ sampleTier else
    2 ^ sampleTier * historyCapacityUnits tier units v / historyCapacityUnits tier units (heightParent v)

theorem historyCutoff_bounded (sampleTier tier : ℕ) (units : HeightNode V height → ℕ)
    (v : HeightNode V height) :
    historyCutoff sampleTier tier units v ≤ 2 ^ sampleTier := by
  unfold historyCutoff
  split
  · exact le_rfl
  · let parent := historyCapacityUnits tier units (heightParent v)
    have le := historyCapacityUnits_ancestor tier units (historyParent_prefix v)
    change 2 ^ sampleTier * historyCapacityUnits tier units v / parent ≤ 2 ^ sampleTier
    by_cases zero : parent = 0
    · simp [zero]
    · calc
        _ ≤ (2 ^ sampleTier * parent) / parent :=
          Nat.div_le_div_right (Nat.mul_le_mul_left _ le)
        _ = _ := Nat.mul_div_cancel _ (Nat.pos_of_ne_zero zero)

private theorem historyCutoff_ratio {sampleTier tier : ℕ} (tierLe : tier ≤ sampleTier)
    (units : HeightNode V height → ℕ) {v : HeightNode V height} (ne : v ≠ heightRoot)
    (positive : 0 < historyCapacityUnits tier units (heightParent v)) :
    (historyCutoff sampleTier tier units v : ℝ) / ((2 ^ sampleTier : ℕ) : ℝ) =
      (historyCapacityUnits tier units v : ℝ) / (historyCapacityUnits tier units (heightParent v) : ℝ) := by
  let m : ℕ := 2 ^ sampleTier
  let parent := historyCapacityUnits tier units (heightParent v)
  let cap := historyCapacityUnits tier units v
  have mPos : 0 < (m : ℝ) := Nat.cast_pos.mpr (by dsimp [m]; positivity)
  have parentPos : 0 < (parent : ℝ) := Nat.cast_pos.mpr positive
  have div : parent ∣ m := by
    rcases historyCapacityUnits_power tier units (heightParent v) with zero | ⟨k, hk, eq⟩
    · exact ((Nat.ne_of_gt positive) zero).elim
    · change historyCapacityUnits tier units (heightParent v) ∣ _
      rw [eq]
      exact Nat.pow_dvd_pow _ (hk.trans tierLe)
  have exactDiv : m * cap / parent * parent = m * cap :=
    Nat.div_mul_cancel (dvd_mul_of_dvd_left div _)
  have eq : ((m * cap / parent : ℕ) : ℝ) * (parent : ℝ) = (m : ℝ) * (cap : ℝ) := by
    exact_mod_cast exactDiv
  simp only [historyCutoff, ne, ↓reduceIte]
  change (((m * cap / parent : ℕ) : ℝ) / (m : ℝ)) = (cap : ℝ) / (parent : ℝ)
  exact (div_eq_div_iff mPos.ne' parentPos.ne').mpr (by simpa only [mul_comm (cap : ℝ)] using eq)

theorem historyCap_dyadic {sampleTier tier : ℕ} (tierLe : tier ≤ sampleTier)
    (units : HeightNode V height → ℕ) (v : HeightNode V height) :
    historyCap (2 ^ sampleTier) (historyCutoff sampleTier tier units) v =
      (historyCapacityUnits tier units v : ℝ) / ((2 ^ tier : ℕ) : ℝ) := by
  let m : ℕ := 2 ^ sampleTier
  let cutoff := historyCutoff sampleTier tier units
  let capacity := historyCapacityUnits tier units
  have mPos : 0 < m := by dsimp [m]; positivity
  have mNe : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr mPos).ne'
  have tierNe : (((2 ^ tier : ℕ) : ℝ)) ≠ 0 := by positivity
  have product (u : HeightNode V height) : historyCap m cutoff u =
      ∏ a ∈ historyAncestors u, (cutoff a : ℝ) / m :=
    thresholdPathsEvent_probability mPos cutoff _ (fun a _ => historyCutoff_bounded _ _ _ _)
  have all (k : ℕ) : ∀ u : HeightNode V height, u.val.length = k →
      historyCap m cutoff u = (capacity u : ℝ) / ((2 ^ tier : ℕ) : ℝ) := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro u len
      by_cases root : u = heightRoot
      · subst u
        rw [product, historyAncestors_root, prod_singleton]
        simp [cutoff, historyCutoff, ← show m = 2 ^ sampleTier from rfl,
          mNe, capacity, historyCapacityUnits_root]
      · have outside : u ∉ historyAncestors (heightParent u) := by
          intro member
          exact (not_le_of_gt (heightParent_shorter root)) (mem_historyAncestors.mp member).length_le
        have shorter : (heightParent u).val.length < k := len ▸ heightParent_shorter root
        have recurse := ih _ shorter (heightParent u) rfl
        rw [product, historyAncestors_parent u, prod_insert outside, ← product, recurse]
        by_cases zero : capacity (heightParent u) = 0
        · have childZero : capacity u = 0 := Nat.eq_zero_of_le_zero (zero ▸
            historyCapacityUnits_ancestor tier units (historyParent_prefix u))
          simp [zero, childZero]
        · have positive : 0 < capacity (heightParent u) := Nat.pos_of_ne_zero zero
          have castNe : (capacity (heightParent u) : ℝ) ≠ 0 := (Nat.cast_pos.mpr positive).ne'
          rw [historyCutoff_ratio tierLe units root positive]
          dsimp only [capacity] at castNe ⊢
          field_simp [castNe, tierNe]
  exact all _ v rfl

/-- Capacity-dominated integral descendant sums imply the conditional
tree-rounding success probability. -/
theorem dyadicHistory_group_probability {sampleTier tier supply : ℕ} (tierLe : tier ≤ sampleTier)
    (tierBound : 2 ^ tier ≤ supply)
    (units leaves : HeightNode V height → ℕ)
    (total : ∑ b, leaves b = supply)
    (dominated : ∀ u : HeightNode V height, u ≠ heightRoot →
      (∑ b ∈ univ.filter (fun b : HeightNode V height => u.val <+: b.val), leaves b) ≤ units u) :
    let cutoff := historyCutoff sampleTier tier units
    let terminals := univ.filter (fun a : HeightNode V height => 0 < leaves a)
    1 / (height + 1 : ℝ) ≤
      finiteProbability (terminals.biUnion (selectedHistoryEvent (2 ^ sampleTier) cutoff)) := by
  let terminals := univ.filter (fun a : HeightNode V height => 0 < leaves a)
  let mass := fun a : HeightNode V height => (leaves a : ℝ) / supply
  let below := fun u : HeightNode V height => univ.filter (fun b : HeightNode V height => u.val <+: b.val)
  have supplyPos : (0 : ℝ) < supply := Nat.cast_pos.mpr ((by positivity : 0 < 2 ^ tier).trans_le tierBound)
  have tierPos : (0 : ℝ) < ((2 ^ tier : ℕ) : ℝ) := by positivity
  have noZero (s : Finset (HeightNode V height)) :
      (∑ b ∈ s.filter (fun b => 0 < leaves b), leaves b) = ∑ b ∈ s, leaves b := by
    rw [Finset.sum_filter]
    apply sum_congr rfl
    intro b _
    split
    · rfl
    · omega
  apply selectedHistory_group_probability (by positivity) (historyCutoff sampleTier tier units)
    (historyCutoff_bounded _ _ _) terminals mass
  · intro a positive
    exact div_pos (Nat.cast_pos.mpr (mem_filter.mp positive).2) supplyPos
  · unfold mass
    rw [← Finset.sum_div, ← Nat.cast_sum, noZero, total, div_self supplyPos.ne']
  · intro u
    change (∑ b ∈ terminals.filter (fun b => u.val <+: b.val), (leaves b : ℝ) / supply) ≤ _
    have reorder : terminals.filter (fun b => u.val <+: b.val) =
        (below u).filter (fun b => 0 < leaves b) := by
      ext a
      simp [terminals, below, and_comm]
    rw [reorder, ← Finset.sum_div, ← Nat.cast_sum, noZero, historyCap_dyadic tierLe]
    apply (div_le_div_iff₀ supplyPos tierPos).mpr
    have sumSupply : (∑ b ∈ below u, leaves b) ≤ supply :=
      (sum_le_sum_of_subset (subset_univ _) (f := leaves)).trans_eq total
    have num : (∑ b ∈ below u, leaves b) * 2 ^ tier ≤ supply * historyCapacityUnits tier units u := by
      apply inf'_mem {c | (∑ b ∈ below u, leaves b) * 2 ^ tier ≤ supply * c}
      · intro x hx y hy
        rcases min_choice x y with eq | eq
        · exact eq.symm ▸ hx
        · exact eq.symm ▸ hy
      intro a inside
      change (∑ b ∈ below u, leaves b) * 2 ^ tier ≤ supply * rootCappedCapacity tier units a
      have anc := mem_historyAncestors.mp inside
      by_cases root : a = heightRoot
      · simp only [rootCappedCapacity, root, ↓reduceIte]
        exact Nat.mul_le_mul_right _ sumSupply
      · simp only [rootCappedCapacity, root, ↓reduceIte, mul_min]
        refine le_min (Nat.mul_le_mul_right _ sumSupply) ?_
        have sub : below u ⊆ below a :=
          fun b hb => mem_filter.mpr ⟨mem_univ _, anc.trans (mem_filter.mp hb).2⟩
        have left := ((sum_le_sum_of_subset sub (f := leaves)).trans (dominated a root)).trans
          (dyadicCapacity_bounds (units a)).1
        simpa only [Nat.mul_comm (dyadicCapacity (units a)) supply] using Nat.mul_le_mul left tierBound
    simpa only [mul_comm (supply : ℝ)] using (show
      ((∑ b ∈ below u, leaves b : ℕ) : ℝ) * ((2 ^ tier : ℕ) : ℝ) ≤
        (supply : ℝ) * (historyCapacityUnits tier units u : ℝ) from by exact_mod_cast num)

end History

end OnlineReachabilityPreservers
