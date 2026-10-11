import SlackSparsification.PathEdges
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-! Integer prefix/suffix bookkeeping. Choosing missing-edge order statistics
makes overlap and the zero-edge purchase regime explicit. -/
namespace SlackSparsification
open Finset SimpleGraph
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The rank of a selected missing-edge index is exactly the number of
smaller indices. -/
theorem card_before_order_index (I : Finset ℕ) (j : Fin I.card) :
    (I.filter fun i => i < I.orderEmbOfFin rfl j).card = j.val := by
  let e := I.orderEmbOfFin rfl
  have he : I.filter (fun i => i < e j) = (Iio j).image e := by
    ext i
    constructor
    · intro hi
      obtain ⟨hiI, hij⟩ := mem_filter.mp hi
      have hir : i ∈ (univ : Finset (Fin I.card)).image e := by
        simpa [e] using hiI
      obtain ⟨k, _, hki⟩ := mem_image.mp hir
      refine mem_image.mpr ⟨k, mem_Iio.mpr ?_, hki⟩
      exact e.lt_iff_lt.mp (hki.symm ▸ hij)
    · intro hi
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hi
      exact mem_filter.mpr ⟨I.orderEmbOfFin_mem rfl k, e.strictMono (mem_Iio.mp hk)⟩
  rw [he, card_image_of_injective _ e.injective, Fin.card_Iio]

theorem card_through_order_index (I : Finset ℕ) (j : Fin I.card) :
    (I.filter fun i => i ≤ I.orderEmbOfFin rfl j).card = j.val + 1 := by
  let a := I.orderEmbOfFin rfl j
  have ha : a ∈ I := I.orderEmbOfFin_mem rfl j
  have he : I.filter (fun i => i ≤ a) = insert a (I.filter fun i => i < a) := by
    ext i
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨hi, hle⟩
      rcases lt_or_eq_of_le hle with hlt | rfl
      · exact Or.inr ⟨hi, hlt⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hi, hlt⟩)
      · exact ⟨ha, le_rfl⟩
      · exact ⟨hi, hlt.le⟩
  rw [he, card_insert_of_notMem (by simp)]
  exact congrArg (· + 1) (card_before_order_index I j)

theorem card_after_order_index (I : Finset ℕ) (j : Fin I.card) :
    (I.filter fun i => I.orderEmbOfFin rfl j < i).card = I.card - (j.val + 1) := by
  have he : I.filter (fun i => I.orderEmbOfFin rfl j < i) =
      I \ (I.filter fun i => i ≤ I.orderEmbOfFin rfl j) := by
    ext i
    by_cases hi : i ∈ I <;> simp [hi, not_le, not_lt]
  rw [he, card_sdiff_of_subset (filter_subset _ _), card_through_order_index]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact missing-index bookkeeping for a prefix. -/
theorem missingIndices_take {G : SimpleGraph V} {s t : V}
    (H : SimpleGraph V) (p : G.Walk s t) (a : ℕ) (ha : a ≤ p.length) :
    missingIndices H (p.take a) = (missingIndices H p).filter (· < a) := by
  ext i
  simp only [missingIndices, mem_filter, mem_range, Walk.take_length,
    Nat.min_eq_left ha]
  constructor
  · rintro ⟨hi, hm⟩
    refine ⟨⟨by omega, ?_⟩, hi⟩
    simpa only [Walk.take_getVert, Nat.min_eq_right (show i ≤ a by omega),
      Nat.min_eq_right (show i + 1 ≤ a by omega)] using hm
  · rintro ⟨⟨_, hm⟩, hi⟩
    refine ⟨hi, ?_⟩
    simpa only [Walk.take_getVert, Nat.min_eq_right (show i ≤ a by omega),
      Nat.min_eq_right (show i + 1 ≤ a by omega)] using hm

/-- A suffix's missing steps inject into the original missing steps at or
after its start index. -/
theorem missingIndices_drop_card {G : SimpleGraph V} {s t : V}
    (H : SimpleGraph V) (p : G.Walk s t) (b : ℕ) :
    (missingIndices H (p.drop b)).card ≤ ((missingIndices H p).filter (b ≤ ·)).card := by
  apply card_le_card_of_injOn (fun i => b + i)
  · intro i hi
    dsimp only at *
    obtain ⟨hi, hm⟩ := mem_filter.mp hi
    have hil : i < p.length - b := by simpa using mem_range.mp hi
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, by omega⟩
    simpa only [Walk.drop_getVert, Nat.add_assoc] using hm
  · intro i _ j _ hij
    dsimp only at hij
    omega

/-- A shortest walk's selected vertices, including its final vertex, have
at most three neighbors per external vertex. -/
theorem path_vertex_neighborhood_count (G H : SimpleGraph V) (hHG : H ≤ G)
    {s t : V} (p : G.Walk s t) (hp : p.length = G.dist s t)
    (I : Finset ℕ) (hI : ∀ i ∈ I, i ≤ p.length) (d : ℕ)
    (hd : ∀ i ∈ I, d ≤ H.degree (p.getVert i)) :
    d * I.card ≤ 3 * (I.biUnion fun i => H.neighborFinset (p.getVert i)).card := by
  let N := fun i => H.neighborFinset (p.getVert i)
  let U := I.biUnion N
  have hN : ∀ i ∈ I, N i ⊆ U := by
    intro i hi v hv
    exact mem_biUnion.mpr ⟨i, hi, hv⟩
  have hsum := sum_hits U I N hN
  have hover : ∀ y ∈ U, (hits I N y).card ≤ 3 := by
    intro y _
    apply card_le_three_of_span
    intro i hi j hj hij
    obtain ⟨hiI, hiH⟩ := mem_filter.mp hi
    obtain ⟨hjI, hjH⟩ := mem_filter.mp hj
    exact neighbors_span_two G p hp y i j hij (hI j hjI)
      (hHG (by simpa [N] using hiH)) (hHG (by simpa [N] using hjH))
  calc
    _ = ∑ _ ∈ I, d := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ I, (N i).card := sum_le_sum (fun i hi => by simpa [N] using hd i hi)
    _ = ∑ y ∈ U, (hits I N y).card := hsum.symm
    _ ≤ ∑ _ ∈ U, 3 := sum_le_sum hover
    _ = _ := by simp [U, N, Nat.mul_comm]

/-- Prefix and suffix cutoff indices straddle at least one unbought missing
edge whenever there are more than 2m missing edges. -/
theorem ordered_missing_cuts (I : Finset ℕ) (m : ℕ) (hm : 2 * m < I.card) :
    ∃ a b, a ∈ I ∧ b ∈ I ∧ a ≤ b ∧
      (I.filter (· < a)).card = m ∧ (I.filter (b < ·)).card = m ∧
      (I.filter (· ≤ a)).card = m + 1 ∧ (I.filter (b ≤ ·)).card = m + 1 := by
  let j : Fin I.card := ⟨m, by omega⟩
  let k : Fin I.card := ⟨I.card - (m + 1), by omega⟩
  let a := I.orderEmbOfFin rfl j
  let b := I.orderEmbOfFin rfl k
  have hab : a ≤ b := (I.orderEmbOfFin rfl).monotone (by change m ≤ I.card - (m + 1); omega)
  have ha := card_before_order_index I j
  have hb := card_after_order_index I k
  have ha' := card_through_order_index I j
  have hbc := card_before_order_index I k
  have he : I.filter (b ≤ ·) = I \ (I.filter (· < b)) := by
    ext i
    by_cases hi : i ∈ I <;> simp [hi, not_le, not_lt]
  refine ⟨a, b, I.orderEmbOfFin_mem rfl j, I.orderEmbOfFin_mem rfl k, hab, ha, ?_, ha', ?_⟩
  · change (I.filter (b < ·)).card = m
    change (I.filter (b < ·)).card = I.card - (I.card - (m + 1) + 1) at hb
    omega
  · rw [he, card_sdiff_of_subset (filter_subset _ _), hbc]
    dsimp [k]
    omega

end SlackSparsification
