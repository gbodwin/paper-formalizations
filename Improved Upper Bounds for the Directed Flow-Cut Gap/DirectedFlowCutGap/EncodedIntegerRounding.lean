import DirectedFlowCutGap.RetainedCandidateSolver
import DirectedFlowCutGap.RetainedFairBitLaw

/-!
# Executable integer rounding at all thresholds

The hard branch builds the concrete closure dictionary and original-demand
mask. It runs the retained controller at its analyzed natural-number
parameters. The other branches produce a mask directly. The finite tree can
be lowered to a bounded literal-fair-bit computation.
-/

namespace DirectedFlowCutGap.EncodedIntegerRounding

open scoped NNReal
open FiniteDrawTrees RetainedGridState IntegerEpochParameters IntegerAdaptiveExecution

private theorem make_order (n L : ℕ) :
    (CandidateEnumeration.make n L).base.enumeration.vertices = List.finRange n :=
  CandidateEnumeration.fin_vertices n

private def hardTree {n : ℕ} (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    FiniteDrawTrees.Tree (Flags n) :=
  let F := CandidateEnumeration.make n L
  let G := RetainedCandidateSolver.graph adjacency
  let Q := RetainedCandidateSolver.optimizer
    (demands := remainingSet (RetainedDemandMask.compute G F.base.enumeration L))
    adjacency F (make_order n L) hL
  let initial := RetainedDemandMask.initial G F.base.enumeration L hL
  let C := integerCutOracle (G := G) hL F.base.enumeration
  map (fun out => out.result.cache.state.data.cut)
    (RetainedDrawTrees.runTree Q hL C (restart n) (fuel n + 1) (fuel n + 1) initial)

/-- The dictionary and shortest-path mask are constructed only in the hard branch. -/
def tree {n : ℕ} (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    FiniteDrawTrees.Tree (Flags n) :=
  if L ≤ n then
    if 64 * cap n ≤ L ∧ n ≤ L ^ 3 then hardTree adjacency L hL
    else .pure (Vector.replicate n true)
  else .pure (Vector.replicate n false)

def drawBound (n : ℕ) : ℕ := (fuel n + 1) * (2 * n * n)

theorem tree_within {n : ℕ} (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    Within (drawBound n) (tree adjacency L hL) := by
  unfold tree
  split_ifs
  · unfold hardTree
    exact within_map (RetainedDrawTrees.runTree_within ..) _
  · exact .pure _ _
  · exact .pure _ _

theorem tree_widths {n : ℕ} (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    LazyFairBitTrees.WidthsLE (RetainedDrawTrees.sampleWidth n L) (tree adjacency L hL) := by
  unfold tree
  split_ifs
  · unfold hardTree
    exact LazyFairBitTrees.widths_map (RetainedDrawTrees.runTree_widths ..) _
  · exact .pure _
  · exact .pure _

def bitTree {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    FiniteDrawTrees.Tree (Flags n) :=
  LazyFairBitTrees.lower T (tree adjacency L hL)

theorem bitTree_binary {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    LazyFairBitTrees.Binary (bitTree T adjacency L hL) :=
  LazyFairBitTrees.lower_binary T _

theorem bitTree_within {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    Within (drawBound n * T * RetainedDrawTrees.sampleWidth n L) (bitTree T adjacency L hL) :=
  LazyFairBitTrees.lower_within (tree_within adjacency L hL) (tree_widths adjacency L hL) T

private theorem hardLaw_eq {n : ℕ} (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    (ideal (hardTree adjacency L hL)).map cutSet =
      IntegerClosureAsymptotic.coreLaw (RetainedCandidateSolver.graph adjacency) L hL
        (CandidateEnumeration.make n L).network.enumeration := by
  let : NeZero L := ⟨hL.ne'⟩
  let F := CandidateEnumeration.make n L
  let G := RetainedCandidateSolver.graph adjacency
  let mask := RetainedDemandMask.compute G F.base.enumeration L
  let Q := RetainedCandidateSolver.optimizer (demands := remainingSet mask)
    adjacency F (make_order n L) hL
  let C := integerCutOracle (G := G) hL F.base.enumeration
  let initial := RetainedDemandMask.initial G F.base.enumeration L hL
  have hr := RetainedFairBitLaw.runTree_law Q hL C (restart n) (fuel n + 1) (fuel n + 1) initial
  have hQ := RetainedCandidateSolver.optimizer_eq (demands := remainingSet mask)
    adjacency F (make_order n L) hL
  simp only [hardTree, ideal, law_map, PMF.map_comp]
  refine (congrArg (fun p => p.map (fun out => cutSet out.result.cache.state.data.cut)) hr).trans ?_
  rw [show Q = _ from hQ]
  exact RetainedClosureLaw.computedLaw_eq_coreLaw (G := G) hL F.base.enumeration F.network.enumeration

/-- Ideal law of the actual executable dispatcher, with the same dictionary
order in execution and in the closure-selected analysis. -/
theorem law_eq {n : ℕ} (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L) :
    (ideal (tree adjacency L hL)).map cutSet =
      IntegerClosureAsymptotic.allRegimeLaw (RetainedCandidateSolver.graph adjacency) L hL
        (CandidateEnumeration.make n L).network.enumeration := by
  simp only [tree, IntegerClosureAsymptotic.allRegimeLaw, Fintype.card_fin]
  split_ifs
  · exact hardLaw_eq adjacency L hL
  · change (PMF.pure (Vector.replicate n true)).map cutSet = _
    rw [PMF.pure_map]
    simp [cutSet]
  · change (PMF.pure (Vector.replicate n false)).map cutSet = _
    rw [PMF.pure_map]
    simp [cutSet]

theorem support_valid {n : ℕ} (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L)
    {mask : Flags n} (hm : mask ∈ (ideal (tree adjacency L hL)).support) :
    IsIntegralCut (RetainedCandidateSolver.graph adjacency) (cutSet mask)
      (CandidateSchedule.unweightedDemands (RetainedCandidateSolver.graph adjacency) (L : ℝ≥0) :
        Set (Pair n)) := by
  have hc := (PMF.mem_support_map_iff cutSet (ideal (tree adjacency L hL)) (cutSet mask)).2
    ⟨mask, hm, rfl⟩
  rw [law_eq] at hc
  exact IntegerClosureAsymptotic.allRegimeLaw_valid _ L hL _ hc

theorem bit_support_valid {n : ℕ} (T : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L)
    {mask : Flags n} (hm : mask ∈ (ideal (bitTree T adjacency L hL)).support) :
    IsIntegralCut (RetainedCandidateSolver.graph adjacency) (cutSet mask)
      (CandidateSchedule.unweightedDemands (RetainedCandidateSolver.graph adjacency) (L : ℝ≥0) :
        Set (Pair n)) :=
  support_valid adjacency L hL
    (LazyFairBitTrees.lowered_support_subset_ideal T (tree adjacency L hL) hm)

theorem expected_size_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (adjacency : PairFlags n) (L : ℕ) (hL : 0 < L),
        FiniteAmplification.expectedCost ((ideal (tree adjacency L hL)).map cutSet)
          (fun X => (X.card : ℝ)) ≤ C * (n : ℝ) ^ ε * AdaptiveCost.sizeFactor (Fin n) (L : ℝ≥0) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := IntegerClosureAsymptotic.allRegimeLaw_expected_uniform ε hε
  refine ⟨C, hC, ?_⟩
  intro n adjacency L hL
  rw [law_eq]
  simpa only [Fintype.card_fin] using hb (Fin n) (RetainedCandidateSolver.graph adjacency) L hL
    (CandidateEnumeration.make n L).network.enumeration

end DirectedFlowCutGap.EncodedIntegerRounding
