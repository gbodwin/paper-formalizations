import DirectedFlowCutGap.RetainedGridState

/-!
# Computing the original threshold-demand mask

Unit integer shortest paths determine the original unweighted demands. The
comparison preserves infinity, so disconnected pairs have exactly their
mathematical demand semantics. The computed Boolean mask is the runtime index
of the initial retained code; the distance equality is an erased certificate.
-/
namespace DirectedFlowCutGap.RetainedDemandMask

open scoped NNReal ENNReal
open RetainedGridState

variable {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj]

/-- One executed integer shortest-path call and threshold test per pair. -/
def compute (EV : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin n))
    (L : ℕ) : PairFlags n :=
  Vector.ofFn fun s => Vector.ofFn fun t =>
    decide ((L : WithTop ℕ) ≤ (IntegerLevelCuts.vertexDistance EV G (fun _ => 1) s t).1)

theorem compute_correct (EV : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin n))
    (L : ℕ) : remainingSet (compute G EV L) = CandidateSchedule.unweightedDemands G (L : ℝ≥0) := by
  ext p
  simp only [mem_remainingSet, compute, flag, Vector.getElem_ofFn, decide_eq_true_eq,
    CandidateSchedule.unweightedDemands, Finset.mem_filter, Finset.mem_univ, true_and]
  have hd := IntegerLevelCuts.vertexDistance_correct EV G (fun _ => 1) 1 p.1 p.2
  simp only [Nat.cast_one, div_one] at hd
  rw [← hd]
  cases (IntegerLevelCuts.vertexDistance EV G (fun _ => 1) p.1 p.2).1 using WithTop.recTopCoe with
  | top => simp
  | coe d => simp [IntegerShortestPaths.scaled]

/-- The actual executable initial state, with computed original-demand mask. -/
def initial (EV : IntegralNetworkFlow.ResidualSearch.Enumeration (Fin n))
    (L : ℕ) (hL : 0 < L) : Code G (remainingSet (compute G EV L)) L :=
  initialMaskedCode G (by exact_mod_cast (show 1 ≤ L by omega))
    (compute G EV L) (compute_correct G EV L)

end DirectedFlowCutGap.RetainedDemandMask
