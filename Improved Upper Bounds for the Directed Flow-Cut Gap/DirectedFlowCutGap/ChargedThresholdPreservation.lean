import DirectedFlowCutGap.ChargedEdgeThresholdDemands
import DirectedFlowCutGap.RationalPrunedEdgeFamily

namespace DirectedFlowCutGap.ChargedThresholdPreservation

open BinaryFractionalWalkOracle (Adjacency shortest)
open BinaryRational (StoredBounded)
open IntegralNetworkFlow
open RationalEdgeThresholds (Weights cost)
open RationalExactEdgeOracle (Edge)

variable {n : ℕ}

private theorem far_value (A : Adjacency n) (w : Weights n) (p : Edge n) :
    (ChargedEdgeThresholdDemands.far A w p).1 = RationalEdgeThresholds.far A w p := by
  unfold ChargedEdgeThresholdDemands.far RationalEdgeThresholds.far
  dsimp only
  cases (shortest (ResidualSearch.Enumeration.fin n) A (cost w) p.1 p.2).1 <;> rfl

private def pair (A : Adjacency n) (w q : Weights n) (p : Edge n) : Bool × ℕ :=
  let original := ChargedEdgeThresholdDemands.far A w p
  if original.1 then
    let modified := ChargedEdgeThresholdDemands.far A q p
    (modified.1,original.2+modified.2+6)
  else (true,original.2+4)

private theorem pair_spec (A : Adjacency n) (w q : Weights n) (p : Edge n) :
    (pair A w q p).1 = true ↔ (RationalEdgeThresholds.far A w p = true →
      RationalEdgeThresholds.far A q p = true) := by
  unfold pair
  dsimp only
  by_cases h : RationalEdgeThresholds.far A w p = true
  · have actual : (ChargedEdgeThresholdDemands.far A w p).1 = true := (far_value A w p).trans h
    rw [ite_eq_left actual]
    simp [far_value,h]
  · have actual : ¬ (ChargedEdgeThresholdDemands.far A w p).1 = true := by simpa only [far_value] using h
    simp [ite_eq_right actual,h]

private def pairBudget (n B C : ℕ) : ℕ :=
  ChargedEdgeThresholdDemands.pairBudget n B + ChargedEdgeThresholdDemands.pairBudget n C + 6

private theorem pair_paid (A : Adjacency n) (w q : Weights n) {B C : ℕ}
    (oldFits : ∀ s t : Fin n, StoredBounded w[s.val][t.val] B)
    (newFits : ∀ s t : Fin n, StoredBounded q[s.val][t.val] C) (p : Edge n) :
    (pair A w q p).2 ≤ pairBudget n B C := by
  have old := ChargedEdgeThresholdDemands.far_paid A w oldFits p
  have new := ChargedEdgeThresholdDemands.far_paid A q newFits p
  unfold pair pairBudget
  dsimp only
  split <;> omega

private def scan (A : Adjacency n) (w q : Weights n) : List (Edge n) → Bool × ℕ
  | [] => (true,1)
  | p::ps =>
    let here := pair A w q p
    if here.1 then
      let rest := scan A w q ps
      (rest.1,here.2+rest.2+4)
    else (false,here.2+4)

private theorem scan_spec (A : Adjacency n) (w q : Weights n) (ps : List (Edge n)) :
    (scan A w q ps).1 = true ↔ ∀ p ∈ ps, RationalEdgeThresholds.far A w p = true →
      RationalEdgeThresholds.far A q p = true := by
  induction ps with
  | nil => simp [scan]
  | cons p ps ih =>
    rw [List.forall_mem_cons,← pair_spec,← ih,scan]
    by_cases h : (pair A w q p).1 = true <;> simp [h]

private theorem scan_paid (A : Adjacency n) (w q : Weights n) {B C : ℕ}
    (oldFits : ∀ s t : Fin n, StoredBounded w[s.val][t.val] B)
    (newFits : ∀ s t : Fin n, StoredBounded q[s.val][t.val] C) (ps : List (Edge n)) :
    (scan A w q ps).2 ≤ ps.length*(pairBudget n B C+4)+1 := by
  induction ps with
  | nil => simp [scan]
  | cons p ps ih =>
    have here := pair_paid A w q oldFits newFits p
    rw [scan,List.length_cons,Nat.add_mul,Nat.one_mul]
    dsimp only
    split <;> omega

private def allPairs (n : ℕ) : List (Edge n) :=
  (List.finRange n).flatMap fun s => (List.finRange n).map fun t => (s,t)

/-- Check the old threshold demands against proposed weights. Skip the
second path search for close pairs and stop at the first lost demand. -/
def check (A : Adjacency n) (w q : Weights n) : Bool × ℕ :=
  let result := scan A w q (allPairs n)
  (result.1,result.2+12*n*n+10*n+5)

theorem check_value (A : Adjacency n) (w q : Weights n) :
    (check A w q).1 = RationalPrunedEdgeFamily.preserves A w q := by
  apply Bool.eq_iff_iff.mpr
  change (scan A w q (allPairs n)).1 = true ↔
    decide (RationalEdgeThresholds.demands A w ⊆ RationalEdgeThresholds.demands A q) = true
  rw [scan_spec,decide_eq_true_eq]
  constructor
  · intro yes p member
    have source := List.mem_filter.mp member
    exact List.mem_filter.mpr ⟨source.1,yes p source.1 source.2⟩
  · intro yes p present old
    exact (List.mem_filter.mp (yes (List.mem_filter.mpr ⟨present,old⟩))).2

def budget (n B C : ℕ) : ℕ := n*n*(pairBudget n B C+4)+1+12*n*n+10*n+5

theorem check_paid (A : Adjacency n) (w q : Weights n) {B C : ℕ}
    (oldFits : ∀ s t : Fin n, StoredBounded w[s.val][t.val] B)
    (newFits : ∀ s t : Fin n, StoredBounded q[s.val][t.val] C) :
    (check A w q).2 ≤ budget n B C := by
  have h := scan_paid A w q oldFits newFits (allPairs n)
  have size : (allPairs n).length = n*n := by simp [allPairs,List.length_flatMap]
  rw [size] at h
  unfold check budget
  dsimp only
  omega

end DirectedFlowCutGap.ChargedThresholdPreservation
