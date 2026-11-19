import OnlineReachabilityPreservers.OppositeIntersectionPruning
import OnlineReachabilityPreservers.PairwiseInitial

/-! The initial Appendix A incidence bound with arbitrary local path orders. -/

namespace OnlineReachabilityPreservers

open Finset

variable {V I : Type*} [LinearOrder V] [Fintype V] [LinearOrder I] [Fintype I]

local notation "ListBefore" => SourceAudit.BeforeIn

/-- Witnesses of intersection chains, recording both meeting vertices. -/
noncomputable def listRChains (paths : I → List V) : Finset ((I × I) × (I × V × V)) := by
  classical
  exact univ.filter fun w => ListIntersectionChain paths w.1.1 w.2.1 w.1.2 w.2.2.1 w.2.2.2

theorem mem_listRChains {paths : I → List V} {w : (I × I) × (I × V × V)} :
    w ∈ listRChains paths ↔ ListIntersectionChain paths w.1.1 w.2.1 w.1.2 w.2.2.1 w.2.2.2 := by
  classical
  simp [listRChains]

/-- The path triples of Definition 3. A middle path is counted once
for its two outer paths when it has at least one witness. -/
noncomputable def listRTriples (paths : I → List V) : Finset ((I × I) × I) := by
  classical
  exact univ.biUnion fun lr : I × I => (listRMiddles paths lr.1 lr.2).image (Prod.mk lr)

omit [Fintype V] in
theorem mem_listRTriples {paths : I → List V} {l m r : I} :
    ((l, r), m) ∈ listRTriples paths ↔ ∃ x y, ListIntersectionChain paths l m r x y := by
  classical
  simp [listRTriples, listRMiddles]

omit [Fintype V] in
/-- The upper count from Lemma 24 uses the fibers of distinct middle paths. -/
theorem listRTriples_upper {paths : I → List V} (free : HalfBridgeFree (ListBefore paths) 4) :
    (listRTriples paths).card ≤ Fintype.card I * ∑ i, (paths i).length := by
  classical
  have size : (listRTriples paths).card = ∑ lr : I × I, (listRMiddles paths lr.1 lr.2).card := by
    unfold listRTriples
    rw [card_biUnion]
    · apply sum_congr rfl
      intro lr _
      exact card_image_of_injective _ fun _ _ equal => congrArg Prod.snd equal
    · intro lr _ lr' _ different
      apply disjoint_left.mpr
      intro w a b
      obtain ⟨_, _, rfl⟩ := mem_image.mp a
      obtain ⟨_, _, equal⟩ := mem_image.mp b
      exact different (congrArg Prod.fst equal).symm
  rw [size]
  calc
    _ ≤ ∑ lr : I × I, (paths lr.1).length :=
      sum_le_sum fun lr _ => lemma24_list_fiber_card free lr.1 lr.2
    _ = _ := by rw [Fintype.sum_prod_type]; simp [mul_sum]

/-- The Lemma 26 incidence lower bound in local list orders. This counts
witnesses. They represent distinct path triples when intersections are unique. -/
theorem lemma26_list_chain_lower (paths : I → List V) (simple : ∀ i, (paths i).Nodup)
    (hn : 0 < Fintype.card V) (hp : 0 < Fintype.card I)
    (hdense : 16 * Fintype.card V ≤ ∑ i, (paths i).length)
    (hlong : 8 * Fintype.card I ≤ ∑ i, (paths i).length) :
    (∑ i, (paths i).length)^4 ≤ 2048 * (Fintype.card V)^2 * Fintype.card I * (listRChains paths).card := by
  let marks (i : I) := (paths i).toFinset
  let position (i : I) (v : V) := (paths i).idxOf v
  have length (i : I) : (marks i).card = (paths i).length := List.toFinset_card_of_nodup (simple i)
  have injective (i : I) : Set.InjOn (position i) (marks i) := by
    intro x hx y _ equal
    exact (List.idxOf_inj (List.mem_toFinset.mp hx)).mp equal
  have lower := lemma26_ranked_chain_lower marks position injective (listRChains paths)
    (fun lm lr earlier left right mx my order => mem_listRChains.mpr
      ⟨lm, lr, earlier, List.mem_toFinset.mp left, List.mem_toFinset.mp right,
        List.mem_toFinset.mp mx, List.mem_toFinset.mp my, order⟩)
    hn hp (by simpa only [length] using hdense) (by simpa only [length] using hlong)
  simpa only [length] using lower

/-- Remove opposite intersections before counting witnesses, then forget
the witnesses. This proves the Lemma 26 lower bound for distinct path
triples in the original locally ordered simple paths. -/
theorem lemma26_list_triple_lower {p : ℕ} (paths : Fin p → List V) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) 4) (hn : 0 < Fintype.card V) (hp : 0 < p)
    (hdense : 32 * Fintype.card V ≤ ∑ i, (paths i).length)
    (hlong : 16 * p ≤ ∑ i, (paths i).length) :
    (∑ i, (paths i).length)^4 ≤ 32768 * (Fintype.card V)^2 * p * (listRTriples paths).card := by
  let n := Fintype.card V
  let mass := ∑ i, (paths i).length
  let kept := removeOppositeIntersections paths
  let m := ∑ i, (kept i).length
  have half : mass ≤ 2 * m := removeOppositeIntersections_mass simple free (by decide)
  have simpleKept (i : Fin p) : (kept i).Nodup :=
    (removeOppositeIntersections_sublist paths i).nodup (simple i)
  have lower : m^4 ≤ 2048 * n^2 * p * (listRChains kept).card := by
    simpa only [Fintype.card_fin] using lemma26_list_chain_lower kept simpleKept hn
      (by simpa only [Fintype.card_fin] using hp) (by change 16 * n ≤ m; omega)
      (by rw [Fintype.card_fin]; change 8 * p ≤ m; omega)
  have retainedCount : (listRChains kept).card ≤ (listRTriples paths).card := by
    apply card_le_card_of_injOn (fun w => (w.1, w.2.1))
    · rintro ⟨⟨l, r⟩, middle, x, y⟩ selected
      have chain := mem_listRChains.mp selected
      exact mem_listRTriples.mpr ⟨x, y, chain.left_ne_middle, chain.left_ne_right, chain.right_earlier,
        (removeOppositeIntersections_sublist paths l).subset chain.on_left,
        (removeOppositeIntersections_sublist paths r).subset chain.on_right,
        removeOppositeIntersections_before simple chain.middle_step⟩
    · rintro ⟨⟨l, r⟩, middle, x, y⟩ a ⟨⟨l', r'⟩, middle', x', y'⟩ b equal
      cases equal
      have one := mem_listRChains.mp a
      have two := mem_listRChains.mp b
      have sameX := removeOppositeIntersections_unique simple free (by decide) one.left_ne_middle
        one.on_left one.middle_step.1 two.on_left two.middle_step.1
      have sameY := removeOppositeIntersections_unique simple free (by decide) one.right_earlier.ne
        one.on_right one.middle_step.2.1 two.on_right two.middle_step.2.1
      change x = x' at sameX
      change y = y' at sameY
      subst x' y'
      rfl
  change mass^4 ≤ 32768 * n^2 * p * (listRTriples paths).card
  calc
    _ ≤ (2*m)^4 := Nat.pow_le_pow_left half 4
    _ = 16 * m^4 := by ring
    _ ≤ 16 * (2048 * n^2 * p * (listRChains kept).card) := Nat.mul_le_mul_left _ lower
    _ ≤ 16 * (2048 * n^2 * p * (listRTriples paths).card) := by gcongr
    _ = _ := by ring

/-- Exact finite form of Lemma 27 for arbitrary ordered families of simple paths. -/
theorem lemma27_list {p : ℕ} (paths : Fin p → List V) (simple : ∀ i, (paths i).Nodup)
    (free : HalfBridgeFree (ListBefore paths) 4) :
    let n := Fintype.card V
    let mass := ∑ i, (paths i).length
    mass ≤ 32 * n ∨ mass ≤ 16 * p ∨ mass^3 ≤ 32768 * (n * p)^2 := by
  dsimp only
  let n := Fintype.card V
  let mass := ∑ i, (paths i).length
  by_cases dense : mass ≤ 32 * n
  · exact Or.inl dense
  by_cases long : mass ≤ 16 * p
  · exact Or.inr (Or.inl long)
  have bounded : mass ≤ p * n := by
    calc
      _ = ∑ i : Fin p, (paths i).toFinset.card := by
        simp only [mass, List.toFinset_card_of_nodup (simple _)]
      _ ≤ ∑ _ : Fin p, n := sum_le_sum (fun _ _ => card_le_univ _)
      _ = _ := by simp
  have posn : 0 < n := Nat.pos_of_ne_zero (by intro zero; rw [zero, mul_zero] at bounded; omega)
  have posp : 0 < p := Nat.pos_of_ne_zero (by intro zero; rw [zero, zero_mul] at bounded; omega)
  have positive : 0 < mass := by omega
  have lower := lemma26_list_triple_lower paths simple free posn posp (by omega) (by omega)
  have upper : (listRTriples paths).card ≤ p * mass := by
    simpa only [Fintype.card_fin] using listRTriples_upper free
  have both : mass^4 ≤ 32768 * n^2 * p * (p * mass) := lower.trans (Nat.mul_le_mul_left _ upper)
  refine Or.inr (Or.inr (Nat.le_of_mul_le_mul_right ?_ positive))
  convert both using 1 <;> ring

/-- The same initial bound for full-bridge-free path systems. -/
theorem lemma27_list_full {p : ℕ} (paths : Fin p → List V) (simple : ∀ i, (paths i).Nodup)
    (free : BridgeFree (ListBefore paths) 4) :
    let n := Fintype.card V
    let mass := ∑ i, (paths i).length
    mass ≤ 32 * n ∨ mass ≤ 16 * p ∨ mass^3 ≤ 32768 * (n * p)^2 :=
  lemma27_list paths simple free.halfFree

end OnlineReachabilityPreservers
