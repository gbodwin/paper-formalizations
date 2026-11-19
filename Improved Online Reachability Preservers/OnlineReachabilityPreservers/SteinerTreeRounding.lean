import Mathlib.Algebra.Order.BigOperators.Expect
import OnlineReachabilityPreservers.SteinerFiniteSampling
import OnlineReachabilityPreservers.SteinerHeightTree

/-! The finite probability calculation for rounding a group in a rooted tree. -/

namespace OnlineReachabilityPreservers

open Finset
open scoped BigOperators

section Uniform

variable {Ω : Type*} [Fintype Ω]

private noncomputable def eventIndicator [DecidableEq Ω] (event : Finset Ω) (ω : Ω) : ℝ :=
  if ω ∈ event then 1 else 0

private theorem expect_eventIndicator [DecidableEq Ω] (event : Finset Ω) :
    (𝔼 ω, eventIndicator event ω) = finiteProbability event := by
  rw [Finset.expect_eq_sum_div_card]
  simp [eventIndicator, finiteProbability]

/-- A nonzero estimator with mean one and second moment at most B succeeds
with probability at least 1/B. -/
private theorem finiteProbability_of_moments [DecidableEq Ω]
    (event : Finset Ω) (Y : Ω → ℝ) {B : ℝ} (pos : 0 < B)
    (support : ∀ ω ∉ event, Y ω = 0)
    (mean : (𝔼 ω, Y ω) = 1) (second : (𝔼 ω, Y ω ^ 2) ≤ B) :
    1 / B ≤ finiteProbability event := by
  have both (ω : Ω) : Y ω * eventIndicator event ω = Y ω := by
    by_cases mem : ω ∈ event <;> simp [eventIndicator, mem, support]
  have square (ω : Ω) : eventIndicator event ω ^ 2 = eventIndicator event ω := by
    by_cases mem : ω ∈ event <;> simp [eventIndicator, mem]
  have cauchy := Finset.expect_mul_sq_le_sq_mul_sq (univ : Finset Ω) Y (eventIndicator event)
  simp_rw [both, square, mean, expect_eventIndicator, one_pow] at cauchy
  have nonnegative : 0 ≤ finiteProbability event := by unfold finiteProbability; positivity
  exact (div_le_iff₀ pos).mpr (by
    rw [mul_comm]
    exact cauchy.trans (mul_le_mul_of_nonneg_right second nonnegative))

variable {A : Type*}

/-- A weighted moment bound for the union of a finite family of events.
The weights sum to one. The pairwise hypothesis uses the second moment
contribution conditional on the first event. -/
private theorem finiteProbability_biUnion_of_overlap [DecidableEq Ω] (terminals : Finset A)
    (event : A → Finset Ω) (mass : A → ℝ) {B : ℝ} (pos : 0 < B)
    (nonneg : ∀ a ∈ terminals, 0 ≤ mass a)
    (total : ∑ a ∈ terminals, mass a = 1)
    (marginal : ∀ a ∈ terminals, 0 < finiteProbability (event a))
    (overlap : ∀ a ∈ terminals,
      (∑ b ∈ terminals, mass b * (finiteProbability (event a ∩ event b) /
        (finiteProbability (event a) * finiteProbability (event b)))) ≤ B) :
    1 / B ≤ finiteProbability (terminals.biUnion event) := by
  let coeff := fun a => mass a / finiteProbability (event a)
  let Y := fun ω => ∑ a ∈ terminals, coeff a * eventIndicator (event a) ω
  have supported (ω : Ω) (out : ω ∉ terminals.biUnion event) : Y ω = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have absent : ω ∉ event a := fun h => out (mem_biUnion.mpr ⟨a, ha, h⟩)
    simp [eventIndicator, absent]
  have mean : (𝔼 ω, Y ω) = 1 := by
    simp only [Y, Finset.expect_sum_comm, mul_comm (coeff _)]
    rw [← total]
    apply sum_congr rfl
    intro a ha
    rw [← Finset.expect_mul (univ : Finset Ω) (eventIndicator (event a)) (coeff a),
      expect_eventIndicator]
    exact mul_div_cancel₀ _ (marginal a ha).ne'
  have productIndicator (a b : A) (ω : Ω) :
      (coeff a * eventIndicator (event a) ω) * (coeff b * eventIndicator (event b) ω) =
        eventIndicator (event a ∩ event b) ω * (coeff a * coeff b) := by
    by_cases ha : ω ∈ event a <;> by_cases hb : ω ∈ event b <;> simp [eventIndicator, ha, hb]
  have second : (𝔼 ω, Y ω ^ 2) ≤ B := by
    simp only [Y, pow_two, Finset.sum_mul, Finset.mul_sum,
      Finset.expect_sum_comm, productIndicator]
    calc
      _ = ∑ a ∈ terminals, mass a *
          (∑ b ∈ terminals, mass b * (finiteProbability (event a ∩ event b) /
            (finiteProbability (event a) * finiteProbability (event b)))) := by
        simp only [Finset.mul_sum]
        apply sum_congr rfl
        intro a _
        apply sum_congr rfl
        intro b _
        rw [← Finset.expect_mul (univ : Finset Ω) (eventIndicator (event b ∩ event a)) (coeff b * coeff a),
          expect_eventIndicator, inter_comm (event b) (event a)]
        simp only [coeff, div_eq_mul_inv, mul_inv]
        ring
      _ ≤ ∑ a ∈ terminals, mass a * B :=
        sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (overlap a ha) (nonneg a ha)
      _ = B := by rw [← Finset.sum_mul, total, one_mul]
  exact finiteProbability_of_moments _ Y pos supported mean second

end Uniform

section History

variable {V : Type*} [DecidableEq V] [Fintype V] {height : ℕ}

/-- All prefixes of a history, including its root and itself. -/
def historyAncestors (node : HeightNode V height) : Finset (HeightNode V height) :=
  univ.filter fun a => a.val <+: node.val

@[simp]
theorem mem_historyAncestors {a node : HeightNode V height} :
    a ∈ historyAncestors node ↔ a.val <+: node.val := by simp [historyAncestors]

theorem historyAncestors_card_le (node : HeightNode V height) :
    (historyAncestors node).card ≤ height + 1 := by
  let ancestors := historyAncestors node
  have unique (a) (ha : a ∈ ancestors) (b) (hb : b ∈ ancestors)
      (same : a.val.length = b.val.length) : a = b := by
    apply Subtype.ext
    rw [List.prefix_iff_eq_take.mp (mem_historyAncestors.mp ha),
      List.prefix_iff_eq_take.mp (mem_historyAncestors.mp hb)]
    congr
  have inside : ancestors.image (fun a => a.val.length) ⊆ range (height + 1) := by
    intro k hk
    obtain ⟨a, _, rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (Nat.lt_succ_of_le a.2)
  rw [← card_image_of_injOn unique, ← card_range (height + 1)]
  exact card_le_card inside

def historyCommon (a b : HeightNode V height) : HeightNode V height :=
  ⟨commonListPrefix a.val b.val,
    ((prefix_commonListPrefix_iff _ _ _).mp List.prefix_rfl).1.length_le.trans a.2⟩

theorem historyAncestors_common (a b : HeightNode V height) :
    historyAncestors (historyCommon a b) = historyAncestors a ∩ historyAncestors b := by
  ext v
  simp only [mem_historyAncestors, mem_inter, historyCommon, prefix_commonListPrefix_iff]

/-- Selection of a history is the conjunction of the independent tests
on its ancestor chain. -/
abbrev historySample (V : Type*) (height m : ℕ) := HeightNode V height → Fin m

noncomputable def selectedHistoryEvent (m : ℕ) (cutoff : HeightNode V height → ℕ)
    (node : HeightNode V height) : Finset (historySample V height m) :=
  thresholdPathsEvent m cutoff (historyAncestors node)

noncomputable def historyCap (m : ℕ) (cutoff : HeightNode V height → ℕ)
    (node : HeightNode V height) : ℝ :=
  finiteProbability (selectedHistoryEvent m cutoff node)

private theorem historyCap_nonneg (m : ℕ) (cutoff : HeightNode V height → ℕ)
    (node : HeightNode V height) : 0 ≤ historyCap m cutoff node := by
  unfold historyCap finiteProbability
  positivity

private theorem historyCap_pair {m : ℕ} (positive : 0 < m)
    (cutoff : HeightNode V height → ℕ) (bounded : ∀ u, cutoff u ≤ m)
    (a b : HeightNode V height) :
    finiteProbability (selectedHistoryEvent m cutoff a ∩ selectedHistoryEvent m cutoff b) *
      historyCap m cutoff (historyCommon a b) = historyCap m cutoff a * historyCap m cutoff b := by
  unfold historyCap selectedHistoryEvent
  rw [← thresholdPathsEvent_union, historyAncestors_common]
  simp only [thresholdPathsEvent_probability positive cutoff _ (fun i _ => bounded i)]
  exact prod_union_inter

/-- A unit terminal flow bounded by the rooted marginals is hit with
probability at least 1/(height+1). Each node may provide its own
independent threshold. -/
theorem selectedHistory_group_probability {m : ℕ} (positive : 0 < m)
    (cutoff : HeightNode V height → ℕ) (bounded : ∀ u, cutoff u ≤ m)
    (terminals : Finset (HeightNode V height)) (mass : HeightNode V height → ℝ)
    (support : ∀ a ∈ terminals, 0 < mass a)
    (total : ∑ a ∈ terminals, mass a = 1)
    (dominated : ∀ u, (∑ a ∈ terminals.filter (fun a => u.val <+: a.val), mass a) ≤ historyCap m cutoff u) :
    1 / (height + 1 : ℝ) ≤ finiteProbability (terminals.biUnion (selectedHistoryEvent m cutoff)) := by
  classical
  let cap := historyCap m cutoff
  have capPos {a u} (ha : a ∈ terminals) (ancestor : u ∈ historyAncestors a) : 0 < cap u := by
    have present : a ∈ terminals.filter (fun a => u.val <+: a.val) :=
      mem_filter.mpr ⟨ha, mem_historyAncestors.mp ancestor⟩
    have below := single_le_sum (f := mass) (fun b hb => (support b (mem_filter.mp hb).1).le) present
    exact (support a ha).trans_le (below.trans (dominated u))
  apply finiteProbability_biUnion_of_overlap terminals (selectedHistoryEvent m cutoff) mass
    (by positivity) (fun a ha => (support a ha).le) total
  · intro a ha
    exact capPos ha (mem_historyAncestors.mpr List.prefix_rfl)
  · intro a ha
    let ancestors := historyAncestors a
    have overlap (b) (hb : b ∈ terminals) :
        (finiteProbability (selectedHistoryEvent m cutoff a ∩ selectedHistoryEvent m cutoff b) /
          (cap a * cap b)) = 1 / cap (historyCommon a b) := by
      have left := capPos ha (mem_historyAncestors.mpr List.prefix_rfl)
      have right := capPos hb (mem_historyAncestors.mpr List.prefix_rfl)
      have common : historyCommon a b ∈ ancestors := by
        exact mem_inter.mp ((historyAncestors_common a b) ▸
          (mem_historyAncestors.mpr List.prefix_rfl : historyCommon a b ∈ historyAncestors (historyCommon a b))) |>.1
      have nonzero := (capPos ha common).ne'
      apply (div_eq_div_iff (mul_ne_zero left.ne' right.ne') nonzero).mpr
      simpa only [one_mul] using historyCap_pair positive cutoff bounded a b
    let contribution := fun (u b : HeightNode V height) =>
      if u.val <+: b.val then mass b / cap u else 0
    calc
      _ ≤ ∑ b ∈ terminals, ∑ u ∈ ancestors, contribution u b := by
        apply sum_le_sum
        intro b hb
        rw [show finiteProbability (selectedHistoryEvent m cutoff a) = cap a from rfl,
          show finiteProbability (selectedHistoryEvent m cutoff b) = cap b from rfl,
          overlap b hb, mul_one_div]
        have common : historyCommon a b ∈ historyAncestors a ∩ historyAncestors b := by
          rw [← historyAncestors_common]
          exact mem_historyAncestors.mpr List.prefix_rfl
        have part := single_le_sum (f := fun u => contribution u b) (s := ancestors)
          (fun u _ => by
            unfold contribution
            split
            · exact div_nonneg (support b hb).le (historyCap_nonneg m cutoff u)
            · exact le_rfl) (mem_inter.mp common).1
        simpa [contribution, mem_historyAncestors.mp (mem_inter.mp common).2] using part
      _ = ∑ u ∈ ancestors, ∑ b ∈ terminals, contribution u b := sum_comm
      _ ≤ ∑ _ ∈ ancestors, (1 : ℝ) := by
        apply sum_le_sum
        intro u hu
        rw [show (∑ b ∈ terminals, contribution u b) =
            ∑ b ∈ terminals.filter (fun b => u.val <+: b.val), mass b / cap u by
          rw [sum_filter]]
        rw [← Finset.sum_div]
        exact (div_le_iff₀ (capPos ha hu)).mpr (by simpa only [one_mul] using dominated u)
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast historyAncestors_card_le a

end History

end OnlineReachabilityPreservers
