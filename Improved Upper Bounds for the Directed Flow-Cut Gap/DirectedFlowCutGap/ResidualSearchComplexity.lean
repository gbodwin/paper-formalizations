import DirectedFlowCutGap.ResidualPathSearch

/-!
# Search-query accounting for actual integral augmentation

`runWithSearchCost` executes the same augmentation recurrence as `run`, retaining
the predicate-test counters of the searches it actually performs. Its first
projection is proved equal to `run (finiteResidualSearch ...)`. The bound is
`k (2 n^3 + n)` equality/adjacency tests for `k` iterations and `n` vertices.

This is a search-query bound. It excludes flow-update arithmetic, the evaluation
cost of functional flow amounts, vertex comparison implementations, final cut
conversion, and integer bit complexity. An iteration budget equal to a general
integer cut capacity is pseudo-polynomial, not polynomial in its binary length.
Applications must separately bound that capacity (and the omitted costs).
-/
namespace DirectedFlowCutGap.IntegralNetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {c : Capacity V} {s t : V}

/-- Actual augmentation with the counters returned by each executed search. -/
def runWithSearchCost (E : ResidualSearch.Enumeration V) (initial : Flow c s t) :
    ℕ → Flow c s t × ℕ
  | 0 => (initial, 0)
  | k + 1 =>
      let a := runWithSearchCost E initial k
      let b := finiteResidualSearchWithCost E a.1
      ((match b.1 with
        | .found p => a.1.augment p
        | .stopped _ => a.1), a.2 + b.2)

/-- Counting does not replace the actual flow computation with a cost surrogate. -/
theorem runWithSearchCost_flow (E : ResidualSearch.Enumeration V)
    (initial : Flow c s t) (k : ℕ) :
    (runWithSearchCost E initial k).1 = run (finiteResidualSearch E c s t) initial k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [run_succ, ← ih]
      simp only [runWithSearchCost, Flow.step, finiteResidualSearch]
      cases (finiteResidualSearchWithCost E (runWithSearchCost E initial k).1).1 <;> rfl

/-- Every counted search query belongs to an actual executed search. -/
theorem runWithSearchCost_bound (E : ResidualSearch.Enumeration V)
    (initial : Flow c s t) (k : ℕ) :
    (runWithSearchCost E initial k).2 ≤ k * (2 * (Fintype.card V)^3 + Fintype.card V) := by
  induction k with
  | zero => simp [runWithSearchCost]
  | succ k ih =>
      have h := finiteResidualSearchWithCost_bound E (runWithSearchCost E initial k).1
      change (runWithSearchCost E initial k).2 +
        (finiteResidualSearchWithCost E (runWithSearchCost E initial k).1).2 ≤ _
      calc
        _ ≤ k * (2 * (Fintype.card V)^3 + Fintype.card V) +
            (2 * (Fintype.card V)^3 + Fintype.card V) := Nat.add_le_add ih h
        _ = _ := by ring

/-- The tracked computation stops by the same concrete separating-cut budget. -/
theorem runWithSearchCost_stopped (E : ResidualSearch.Enumeration V)
    (X : Finset V) (hs : s ∈ X) (ht : t ∉ X) :
    ¬Nonempty (SimplePath
      (runWithSearchCost E (Flow.zero c s t) (cutCapacity c X)).1.residual s t) := by
  rw [runWithSearchCost_flow]
  exact run_stopped_at_cut_budget (finiteResidualSearch E c s t) X hs ht

/-- The output flow and the explicit computed cut have equal value/capacity. -/
theorem runWithSearchCost_certificate (E : ResidualSearch.Enumeration V)
    (X : Finset V) (hs : s ∈ X) (ht : t ∉ X) :
    let r := runWithSearchCost E (Flow.zero c s t) (cutCapacity c X)
    s ∈ finiteResidualCut E r.1 ∧ t ∉ finiteResidualCut E r.1 ∧
      r.1.value = (cutCapacity c (finiteResidualCut E r.1) : ℤ) ∧
      (∀ g : Flow c s t, g.value ≤ r.1.value) ∧
      (∀ Y : Finset V, s ∈ Y → t ∉ Y →
        cutCapacity c (finiteResidualCut E r.1) ≤ cutCapacity c Y) ∧
      r.2 ≤ cutCapacity c X * (2 * (Fintype.card V)^3 + Fintype.card V) := by
  have h := finiteResidualCut_certificate E _ (runWithSearchCost_stopped (c := c) E X hs ht)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
    runWithSearchCost_bound E _ _⟩

end DirectedFlowCutGap.IntegralNetworkFlow
