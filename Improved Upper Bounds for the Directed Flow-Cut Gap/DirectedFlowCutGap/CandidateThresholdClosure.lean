import DirectedFlowCutGap.CandidateGridRounding
import DirectedFlowCutGap.MinimumClosureProblem

/-!
# Exact threshold-bit encoding of integer difference constraints

A forced level-zero bit is retained for every coordinate. This makes negative
bounds sound even when the source potential is zero. An implication whose target
would exceed L forbids its source bit. The finite network has polynomial size;
this module does not supply an algorithm for finding its minimum closure.
-/
namespace DirectedFlowCutGap.CandidateThresholdClosure

open scoped BigOperators
open CandidateGridRounding.DifferenceSystem MinimumClosureProblem

variable {I : Type*} [Fintype I] [DecidableEq I] {L : ℕ}

abbrev Node (I : Type*) (L : ℕ) := I × Fin (L + 1)

/-- A fully integer, decidable version of the bounded feasible-point predicate. -/
def IntFeasible (S : CandidateGridRounding.DifferenceSystem I L) (q : GridPoint I L) : Prop :=
  (∀ i, S.lower i ≤ q i ∧ q i ≤ S.upper i) ∧
    ∀ i j, ((q i : ℕ) : ℤ) - (q j : ℕ) ≤ S.bound i j

omit [Fintype I] [DecidableEq I] in
theorem intFeasible_iff (S : CandidateGridRounding.DifferenceSystem I L) (q : GridPoint I L) :
    IntFeasible S q ↔ S.Feasible (gridValue q) := by
  unfold IntFeasible CandidateGridRounding.DifferenceSystem.Feasible gridValue
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      constructor
      · exact_mod_cast (h.1 i).1
      · exact_mod_cast (h.1 i).2
    · intro i j
      exact_mod_cast h.2 i j
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      constructor
      · exact_mod_cast (h.1 i).1
      · exact_mod_cast (h.1 i).2
    · intro i j
      exact_mod_cast h.2 i j

/-- Select precisely the initial interval of levels below each potential. -/
def encode (q : GridPoint I L) : Finset (Node I L) :=
  Finset.univ.filter fun a => a.2 ≤ q a.1

omit [DecidableEq I] in
@[simp] theorem mem_encode (q : GridPoint I L) (a : Node I L) :
    a ∈ encode q ↔ a.2 ≤ q a.1 := by simp [encode]

/-- Required bits encode lower bounds (including level zero). Forbidden bits
encode upper bounds and overflowing difference implications. -/
def problem (S : CandidateGridRounding.DifferenceSystem I L) (c : I → ℤ) : Problem (Node I L) where
  required := Finset.univ.filter fun a => a.2 ≤ S.lower a.1
  forbidden := Finset.univ.filter fun a => S.upper a.1 < a.2 ∨
    ∃ j, (L : ℤ) < ((a.2 : ℕ) : ℤ) - S.bound a.1 j
  arcs := Finset.univ.filter fun e =>
    (e.1.1 = e.2.1 ∧ e.2.2 ≤ e.1.2) ∨
      ((e.2.2 : ℕ) : ℤ) = ((e.1.2 : ℕ) : ℤ) - S.bound e.1.1 e.2.1
  cost := fun a => if a.2 = 0 then 0 else c a.1

@[simp] theorem mem_required (S : CandidateGridRounding.DifferenceSystem I L)
    (c : I → ℤ) (a : Node I L) :
    a ∈ (problem S c).required ↔ a.2 ≤ S.lower a.1 := by simp [problem]

@[simp] theorem mem_forbidden (S : CandidateGridRounding.DifferenceSystem I L)
    (c : I → ℤ) (a : Node I L) :
    a ∈ (problem S c).forbidden ↔ S.upper a.1 < a.2 ∨
      ∃ j, (L : ℤ) < ((a.2 : ℕ) : ℤ) - S.bound a.1 j := by simp [problem]

@[simp] theorem mem_arcs (S : CandidateGridRounding.DifferenceSystem I L)
    (c : I → ℤ) (a b : Node I L) :
    (a, b) ∈ (problem S c).arcs ↔
      (a.1 = b.1 ∧ b.2 ≤ a.2) ∨
        ((b.2 : ℕ) : ℤ) = ((a.2 : ℕ) : ℤ) - S.bound a.1 b.1 := by simp [problem]

/-- Every integer feasible point gives a valid finite closure. -/
theorem encode_closed (S : CandidateGridRounding.DifferenceSystem I L) (c : I → ℤ)
    {q : GridPoint I L} (hq : IntFeasible S q) : (problem S c).IsClosed (encode q) := by
  refine ⟨?_, Finset.disjoint_left.mpr ?_, ?_⟩
  · intro a ha
    exact (mem_encode q a).mpr (((mem_required S c a).mp ha).trans (hq.1 a.1).1)
  · intro a ha hf
    have haq := (mem_encode q a).mp ha
    rcases (mem_forbidden S c a).mp hf with hupper | ⟨j, hover⟩
    · exact (not_lt_of_ge (haq.trans (hq.1 a.1).2)) hupper
    · have hdiff := hq.2 a.1 j
      have hlevel : ((a.2 : ℕ) : ℤ) ≤ (q a.1 : ℕ) := by exact_mod_cast haq
      have hqL : ((q j : ℕ) : ℤ) ≤ L := by exact_mod_cast Nat.le_of_lt_succ (q j).isLt
      omega
  · intro a b hab ha
    have haq := (mem_encode q a).mp ha
    apply (mem_encode q b).mpr
    rcases (mem_arcs S c a b).mp hab with ⟨hcoord, hlevel⟩ | hshift
    · rw [hcoord] at haq
      exact hlevel.trans haq
    · have hdiff := hq.2 a.1 b.1
      have hlevel : ((a.2 : ℕ) : ℤ) ≤ (q a.1 : ℕ) := by exact_mod_cast haq
      have hresult : ((b.2 : ℕ) : ℤ) ≤ (q b.1 : ℕ) := by omega
      exact_mod_cast hresult

/-- A closed encoding satisfies every original integer difference constraint,
including negative bounds and the level-zero case. -/
theorem intFeasible_of_encode_closed (S : CandidateGridRounding.DifferenceSystem I L)
    (c : I → ℤ) {q : GridPoint I L} (hq : (problem S c).IsClosed (encode q)) :
    IntFeasible S q := by
  have hself (i : I) : (i, q i) ∈ encode q := by simp
  have hnot (i : I) : (i, q i) ∉ (problem S c).forbidden :=
    fun h => Finset.disjoint_left.mp hq.avoids_forbidden (hself i) h
  refine ⟨?_, ?_⟩
  · intro i
    constructor
    · exact (mem_encode q (i, S.lower i)).mp
        (hq.contains_required (by simp))
    · by_contra h
      exact hnot i ((mem_forbidden S c (i, q i)).mpr (Or.inl (lt_of_not_ge h)))
  · intro i j
    let z : ℤ := ((q i : ℕ) : ℤ) - S.bound i j
    have hzL : z ≤ (L : ℤ) := by
      by_contra h
      exact hnot i ((mem_forbidden S c (i, q i)).mpr (Or.inr ⟨j, lt_of_not_ge h⟩))
    by_cases hz : z ≤ 0
    · have hq₀ : (0 : ℤ) ≤ (q j : ℕ) := Int.natCast_nonneg _
      dsimp [z] at hz
      omega
    · have hz₀ : 0 ≤ z := (lt_of_not_ge hz).le
      let k : Fin (L + 1) := ⟨z.toNat, by
        have h := Int.toNat_le_toNat hzL
        simp only [Int.toNat_natCast] at h
        omega⟩
      have hk : ((k : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz₀
      have harc : ((i, q i), (j, k)) ∈ (problem S c).arcs :=
        (mem_arcs S c _ _).mpr (Or.inr hk)
      have hkj := (mem_encode q (j, k)).mp (hq.follows_arcs _ _ harc (hself i))
      have hkj' : ((k : ℕ) : ℤ) ≤ (q j : ℕ) := by exact_mod_cast hkj
      dsimp [z] at hk
      omega

theorem encode_closed_iff (S : CandidateGridRounding.DifferenceSystem I L) (c : I → ℤ)
    (q : GridPoint I L) : (problem S c).IsClosed (encode q) ↔ IntFeasible S q :=
  ⟨intFeasible_of_encode_closed S c, encode_closed S c⟩

/-- The selected levels of one coordinate. -/
def levels (T : Finset (Node I L)) (i : I) : Finset (Fin (L + 1)) :=
  Finset.univ.filter fun k => (i, k) ∈ T

omit [Fintype I] in
@[simp] theorem mem_levels (T : Finset (Node I L)) (i : I) (k : Fin (L + 1)) :
    k ∈ levels T i ↔ (i, k) ∈ T := by simp [levels]

theorem levels_nonempty (S : CandidateGridRounding.DifferenceSystem I L) (c : I → ℤ)
    (T : Finset (Node I L)) (hT : (problem S c).IsClosed T) (i : I) :
    (levels T i).Nonempty := by
  refine ⟨0, (mem_levels T i 0).mpr (hT.contains_required ?_)⟩
  simp

/-- Decode by the maximum selected level, whose existence follows from the
required level-zero bit. -/
def decode (S : CandidateGridRounding.DifferenceSystem I L) (c : I → ℤ)
    (T : Finset (Node I L)) (hT : (problem S c).IsClosed T) : GridPoint I L :=
  fun i => (levels T i).max' (levels_nonempty S c T hT i)

/-- Every feasible closure is precisely an initial-interval threshold encoding. -/
theorem encode_decode (S : CandidateGridRounding.DifferenceSystem I L) (c : I → ℤ)
    (T : Finset (Node I L)) (hT : (problem S c).IsClosed T) :
    encode (decode S c T hT) = T := by
  ext ⟨i, k⟩
  rw [mem_encode]
  constructor
  · intro hk
    have hmax : (i, decode S c T hT i) ∈ T :=
      (mem_levels T i _).mp ((levels T i).max'_mem (levels_nonempty S c T hT i))
    apply hT.follows_arcs (i, decode S c T hT i) (i, k) _ hmax
    exact (mem_arcs S c _ _).mpr (Or.inl ⟨rfl, hk⟩)
  · intro hk
    exact (levels T i).le_max' k ((mem_levels T i k).mpr hk)

theorem decode_feasible (S : CandidateGridRounding.DifferenceSystem I L) (c : I → ℤ)
    (T : Finset (Node I L)) (hT : (problem S c).IsClosed T) :
    IntFeasible S (decode S c T hT) := by
  apply (encode_closed_iff S c _).mp
  simpa only [encode_decode S c T hT] using hT


/-- The integer objective of the original potential assignment. -/
def integerObjective (c : I → ℤ) (q : GridPoint I L) : ℤ :=
  ∑ i, c i * (q i : ℕ)

theorem sum_threshold_cost (q : Fin (L + 1)) (c : ℤ) :
    (∑ k : Fin (L + 1), if k ≤ q then (if k = 0 then 0 else c) else 0) =
      c * (q : ℕ) := by
  have hset : (Finset.univ.filter fun k : Fin (L + 1) => k ≤ q ∧ k ≠ 0) =
      (Finset.Iic q).erase 0 := by
    ext k
    simp [and_comm]
  calc
    _ = ∑ _k ∈ Finset.univ.filter (fun k : Fin (L + 1) => k ≤ q ∧ k ≠ 0), c := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k ≤ q <;> by_cases hk₀ : k = 0 <;> simp [hk, hk₀]
    _ = c * (q : ℕ) := by
      rw [hset]
      simp [Finset.card_erase_of_mem (show (0 : Fin (L + 1)) ∈ Finset.Iic q by simp),
        mul_comm]

/-- Every positive threshold contributes its coordinate cost exactly once. -/
theorem objective_encode (S : CandidateGridRounding.DifferenceSystem I L) (c : I → ℤ)
    (q : GridPoint I L) : (problem S c).objective (encode q) = integerObjective c q := by
  unfold Problem.objective encode
  rw [Finset.sum_filter]
  change (∑ a : Node I L, if a.2 ≤ q a.1 then
    (if a.2 = 0 then 0 else c a.1) else 0) = ∑ i, c i * (q i : ℕ)
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun i _ => sum_threshold_cost (q i) (c i))

theorem objective_decode (S : CandidateGridRounding.DifferenceSystem I L) (c : I → ℤ)
    (T : Finset (Node I L)) (hT : (problem S c).IsClosed T) :
    (problem S c).objective T = integerObjective c (decode S c T hT) := by
  rw [← objective_encode S c, encode_decode]

omit [DecidableEq I] in
/-- The signed threshold cost agrees exactly with the real linear objective. -/
theorem integerObjective_coe (c : I → ℤ) (q : GridPoint I L) :
    (integerObjective c q : ℝ) =
      CandidateGridRounding.DifferenceSystem.objective (fun i => (c i : ℝ)) (gridValue q) := by
  simp [integerObjective, CandidateGridRounding.DifferenceSystem.objective, gridValue]

/-- A genuine closure optimality certificate transfers to the integer problem.
This is a reduction theorem; it does not assert that an algorithm found the
certificate. -/
theorem transfer_minimality (S : CandidateGridRounding.DifferenceSystem I L) (c : I → ℤ)
    (T : Finset (Node I L)) (hT : (problem S c).IsClosed T)
    (hmin : ∀ U, (problem S c).IsClosed U →
      (problem S c).objective T ≤ (problem S c).objective U) :
    ∀ q, IntFeasible S q → integerObjective c (decode S c T hT) ≤ integerObjective c q := by
  intro q hq
  rw [← objective_decode S c T hT, ← objective_encode S c q]
  exact hmin (encode q) (encode_closed S c hq)

omit [DecidableEq I] in
/-- The threshold domain and its explicit arc list have polynomial size. -/
theorem card_node : Fintype.card (Node I L) = Fintype.card I * (L + 1) := by
  simp [Node]

theorem card_arcs_le (S : CandidateGridRounding.DifferenceSystem I L) (c : I → ℤ) :
    (problem S c).arcs.card ≤ (Fintype.card I * (L + 1)) ^ 2 := by
  simpa [Fintype.card_prod, card_node, pow_two] using (problem S c).arcs.card_le_univ


/-- A useful finite-capacity budget for uniformly bounded integer costs. -/
theorem absolute_cost_le (S : CandidateGridRounding.DifferenceSystem I L)
    (c : I → ℤ) (K : ℕ) (hK : ∀ i, (c i).natAbs ≤ K) :
    (∑ a : Node I L, ((problem S c).cost a).natAbs) ≤
      Fintype.card I * (L + 1) * K := by
  calc
    _ ≤ ∑ _a : Node I L, K := by
      apply Finset.sum_le_sum
      intro a _
      dsimp [problem]
      split_ifs
      · simp
      · exact hK a.1
    _ = _ := by simp

end DirectedFlowCutGap.CandidateThresholdClosure
