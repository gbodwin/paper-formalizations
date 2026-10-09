import DirectedFlowCutGap.LazyFairBitTrees
import DirectedFlowCutGap.RetainedClosureLaw

/-!
# Finite-draw trees for the actual retained controller

The controller is instantiated directly with the compositional FiniteDrawTrees.Tree monad.
Permutation and cell tapes are generated in their actual order. Each possible
state, including states reached through bounded-rejection defaults, has at
most n² active labels, so an epoch needs at most 2n² primitive draws.
Only the finite cut is used for output-event comparisons; logged controller
results themselves contain unbounded natural counters.
-/
namespace DirectedFlowCutGap.RetainedDrawTrees
open scoped NNReal ENNReal BigOperators
open FiniteDrawTrees LazyFairBitTrees RetainedGridState IntegerAdaptiveExecution

/-- The same shrinking bounds as the checked permutation tape interpreter. -/
def permutation : (m : ℕ) → FiniteDrawTrees.Tree (FinitePermutationSampler.Tape m)
  | 0 => .pure ()
  | m+1 => FiniteDrawTrees.bind (pick (m+1) (by omega))
      (fun j => FiniteDrawTrees.map (fun t => (j,t)) (permutation m))

def cells (L : ℕ) (hL : 0 < L) : (m : ℕ) → FiniteDrawTrees.Tree (FiniteGridSampler.Cells L m)
  | 0 => .pure ()
  | m+1 => FiniteDrawTrees.bind (pick L hL) (fun j => FiniteDrawTrees.map (fun t => (j,t)) (cells L hL m))

def tape (L : ℕ) (hL : 0 < L) (m : ℕ) :
    FiniteDrawTrees.Tree (FinitePermutationSampler.Tape m × FiniteGridSampler.Cells L m) :=
  FiniteDrawTrees.bind (permutation m) (fun p => FiniteDrawTrees.map (fun c => (p,c)) (cells L hL m))

theorem permutation_within (m : ℕ) : Within m (permutation m) := by
  induction m with
  | zero => exact .pure 0 ()
  | succ m ih =>
      change Within (m+1) (FiniteDrawTrees.bind (pick (m+1) (by omega))
        (fun j => FiniteDrawTrees.map (fun t : FinitePermutationSampler.Tape m => (j,t)) (permutation m)))
      simpa only [Nat.add_comm] using
        within_bind (within_pick (m+1) (by omega)) _
          (fun j => within_map ih (fun t => (j,t)))

theorem cells_within (L : ℕ) (hL : 0 < L) (m : ℕ) : Within m (cells L hL m) := by
  induction m with
  | zero => exact .pure 0 ()
  | succ m ih =>
      change Within (m+1) (FiniteDrawTrees.bind (pick L hL)
        (fun j => FiniteDrawTrees.map (fun t : FiniteGridSampler.Cells L m => (j,t)) (cells L hL m)))
      simpa only [Nat.add_comm] using
        within_bind (within_pick L hL) _ (fun j => within_map ih (fun t => (j,t)))

theorem tape_within (L : ℕ) (hL : 0 < L) (m : ℕ) : Within (2*m) (tape L hL m) := by
  simpa only [tape, two_mul] using
    within_bind (permutation_within m) _ (fun p => within_map (cells_within L hL m) (fun c => (p,c)))

theorem permutation_widths {m w : ℕ} (h : FairBitWords.width m ≤ w) :
    WidthsLE w (permutation m) := by
  induction m with
  | zero => exact .pure ()
  | succ m ih =>
      apply widths_bind (WidthsLE.draw h (fun j => .pure j))
      intro j
      exact widths_map (ih ((width_mono (by omega : m ≤ m+1)).trans h)) _

theorem cells_widths (L : ℕ) (hL : 0 < L) {w : ℕ}
    (h : FairBitWords.width L ≤ w) (m : ℕ) : WidthsLE w (cells L hL m) := by
  induction m with
  | zero => exact .pure ()
  | succ m ih => exact widths_bind (.draw h (fun j => .pure j)) _ (fun j => widths_map ih _)

theorem tape_widths (L : ℕ) (hL : 0 < L) {m w : ℕ}
    (hm : FairBitWords.width m ≤ w) (h : FairBitWords.width L ≤ w) :
    WidthsLE w (tape L hL m) :=
  widths_bind (permutation_widths hm) _ (fun _ => widths_map (cells_widths L hL h m) _)

def sampleTape {n L : ℕ} (hL : 0 < L) (a : PairFlags n) :
    FiniteDrawTrees.Tree (RetainedTapeInput.Tape L a) :=
  tape L hL (Fintype.card ↥(remainingSet a))

theorem active_card_le {n : ℕ} (a : PairFlags n) :
    Fintype.card ↥(remainingSet a) ≤ n*n := by
  rw [Fintype.card_coe]
  exact (Finset.card_le_univ _).trans_eq (by simp [Pair])

theorem sampleTape_within {n L : ℕ} (hL : 0 < L) (a : PairFlags n) :
    Within (2*n*n) (sampleTape hL a) := by
  apply within_mono (tape_within L hL _)
  have h := Nat.mul_le_mul_left 2 (active_card_le a)
  simpa only [Nat.mul_assoc] using h

def sampleWidth (n L : ℕ) : ℕ := FairBitWords.width (max (n*n) L)

theorem sampleTape_widths {n L : ℕ} (hL : 0 < L) (a : PairFlags n) :
    WidthsLE (sampleWidth n L) (sampleTape hL a) := by
  apply tape_widths
  · exact width_mono ((active_card_le a).trans (le_max_left _ _))
  · exact width_mono (le_max_right _ _)

section Controller
variable {n L : ℕ} {G : Digraph (Fin n)} {D : Finset (Pair n)}
variable {selector : FlexibleCandidateSchedule.FamilyProvider G D (L : ℝ≥0) → Prop}
variable {H : ∃ P, selector P}

def executeTree (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (c : Cache H) : FiniteDrawTrees.Tree (RetainedSampledExecution.LoggedResult H) :=
  RetainedSampledExecution.executeSampled (sampleTape hL) Q hL C R restartFuel epochs c

def runTree (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (s : Code G D L) : FiniteDrawTrees.Tree (RetainedSampledExecution.LoggedResult H) :=
  RetainedSampledExecution.runSampled (sampleTape hL) Q hL C R restartFuel epochs s

theorem executeTree_within (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (c : Cache H) :
    Within (epochs*(2*n*n)) (executeTree Q hL C R restartFuel epochs c) := by
  induction epochs generalizing c with
  | zero => exact .pure _ _
  | succ epochs ih =>
      unfold executeTree
      rw [RetainedSampledExecution.executeSampled]
      split
      · exact .pure _ _
      · rw [show (epochs+1)*(2*n*n) = 2*n*n + epochs*(2*n*n) by ring]
        apply within_bind (sampleTape_within hL _)
        intro t
        exact within_map (ih _) _

theorem runTree_within (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (s : Code G D L) :
    Within (epochs*(2*n*n)) (runTree Q hL C R restartFuel epochs s) := by
  exact within_map (executeTree_within Q hL C R restartFuel epochs _) _

theorem executeTree_widths (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (c : Cache H) :
    WidthsLE (sampleWidth n L) (executeTree Q hL C R restartFuel epochs c) := by
  induction epochs generalizing c with
  | zero => exact .pure _
  | succ epochs ih =>
      unfold executeTree
      rw [RetainedSampledExecution.executeSampled]
      split
      · exact .pure _
      · exact widths_bind (sampleTape_widths hL _) _ (fun t => widths_map (ih _) _)

theorem runTree_widths (Q : Optimizer H) (hL : 0 < L) (C : CutOracle G L hL)
    (R restartFuel epochs : ℕ) (s : Code G D L) :
    WidthsLE (sampleWidth n L) (runTree Q hL C R restartFuel epochs s) :=
  widths_map (executeTree_widths Q hL C R restartFuel epochs _) _

end Controller

noncomputable section

theorem permutation_law (m : ℕ) : ideal (permutation m) = FinitePermutationSampler.tapePMF m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change law uniformDraw (FiniteDrawTrees.bind (pick (m+1) (by omega))
        (fun j => FiniteDrawTrees.map (fun t : FinitePermutationSampler.Tape m => (j,t)) (permutation m))) =
        FinitePermutationSampler.independent (PMF.uniformOfFintype (Fin (m+1))) (FinitePermutationSampler.tapePMF m)
      rw [law_bind, law_pick]
      simp_rw [law_map]
      change (uniformDraw (m+1) _).bind (fun j => (ideal (permutation m)).map (fun t => (j,t))) = _
      rw [ih]
      rfl

theorem cells_law (L : ℕ) (hL : 0 < L) [NeZero L] (m : ℕ) :
    ideal (cells L hL m) = FiniteGridSampler.cellsPMF L m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change law uniformDraw (FiniteDrawTrees.bind (pick L hL)
        (fun j => FiniteDrawTrees.map (fun t : FiniteGridSampler.Cells L m => (j,t)) (cells L hL m))) =
        FinitePermutationSampler.independent (PMF.uniformOfFintype (Fin L)) (FiniteGridSampler.cellsPMF L m)
      rw [law_bind, law_pick]
      simp_rw [law_map]
      change (uniformDraw L hL).bind (fun j => (ideal (cells L hL m)).map (fun t => (j,t))) = _
      rw [ih]
      rfl

theorem tape_law (L : ℕ) (hL : 0 < L) [NeZero L] (m : ℕ) :
    ideal (tape L hL m) = FiniteGridSampler.tapePMF m L := by
  simp only [tape, ideal, law_bind, law_map]
  change (ideal (permutation m)).bind (fun p => (ideal (cells L hL m)).map (fun c => (p,c))) = _
  rw [permutation_law, cells_law]
  rfl

theorem sampleTape_law {n L : ℕ} (hL : 0 < L) [NeZero L] (a : PairFlags n) :
    ideal (sampleTape hL a) = RetainedExecutionLaw.sampleTape a := tape_law L hL _

end
end DirectedFlowCutGap.RetainedDrawTrees
