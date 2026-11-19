import DirectedFlowCutGap.OriginalGraphControllerProgram
import DirectedFlowCutGap.RetainedClosureLaw
import DirectedFlowCutGap.RetainedFairBitLaw
import DirectedFlowCutGap.ChargedCutSelection

/-! Connect the physical controller's literal tape to the established cut law. -/

namespace DirectedFlowCutGap.OriginalGraphControllerLaw
open scoped NNReal
open BinaryArithmetic RetainedGridState IntegralNetworkFlow FiniteDrawTrees
open EpochScanData (Graph optimizer cacheOf)
open InitialGraphContexts (enumeration)
open PhysicalControllerInitializer (initialCode)
open CandidateEnumeration (Network)
open IntegerEpochParameters (restart fuel)

private theorem map_twice {A B C : Type} (f : A→B) (g : B→C) (t : FiniteDrawTrees.Tree A) :
    map g (map f t)=map (fun x=>g (f x)) t := by
  induction t with
  | pure a => rfl
  | draw n h next ih =>
    exact congrArg (FiniteDrawTrees.Tree.draw n h) (funext ih)

private theorem lower_map (T : ℕ) {A B : Type} (f : A→B) (t : FiniteDrawTrees.Tree A) :
    LazyFairBitTrees.lower T (map f t)=map f (LazyFairBitTrees.lower T t) := by
  change LazyFairBitTrees.lower T (t >>= fun a => .pure (f a))=_
  rw [ChargedCutSelection.lower_bind]
  rfl

variable {n L : ℕ} {adj : PairFlags n}

noncomputable abbrev sourceCode (positive : 0<L) := initialCode adj positive
noncomputable abbrev ratio (n : ℕ) := (restart n).bits
abbrev epochs (n : ℕ) := fuel n+1

noncomputable abbrev codeTree (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) :=
  ControllerTapeModel.tree positive E (ratio n) (epochs n) (epochs n) (sourceCode (adj:=adj) positive)

noncomputable abbrev cutTree (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) :=
  map (fun s => cutSet s.data.cut) (codeTree (adj:=adj) positive E)

theorem cutTree_eq (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) :
    cutTree (adj:=adj) positive E =
      RetainedFairBitLaw.cutTree (optimizer positive E) positive (integerCutOracle (G:=Graph adj) positive (enumeration n))
        (restart n) (epochs n) (epochs n) (sourceCode (adj:=adj) positive) := by
  let s := sourceCode (adj:=adj) positive
  let Q := optimizer (adj:=adj) (demands:=remainingSet s.data.remaining) positive E
  let C := integerCutOracle (G:=Graph adj) positive (enumeration n)
  let t := RetainedDrawTrees.executeTree Q positive C (restart n) (epochs n) (epochs n) (cacheOf positive E s)
  have oracle : EpochScanData.cutOracle adj positive=C := EncodedRoundingInput.cutOracle_eq (enumeration n) adj positive
  have exactTree := ControllerTapeModel.tree_exact positive E (ratio n) (epochs n) (epochs n) s
  rw [oracle,show value (ratio n)=restart n from value_bits _] at exactTree
  change map (fun x => cutSet x.data.cut) (ControllerTapeModel.tree positive E (ratio n) (epochs n) (epochs n) s) =
    RetainedFairBitLaw.cutTree Q positive C (restart n) (epochs n) (epochs n) s
  rw [exactTree]
  change map (fun x => cutSet x.data.cut) (map (fun out => out.result.cache.state) t) = _
  have runEq : RetainedDrawTrees.runTree Q positive C (restart n) (epochs n) (epochs n) s =
      map (fun out => { out with
        result := { out.result with work := (IntegerAdaptiveExecution.refreshWork s).add out.result.work } }) t := rfl
  change _ = map (fun out => cutSet out.result.cache.state.data.cut)
    (RetainedDrawTrees.runTree Q positive C (restart n) (epochs n) (epochs n) s)
  rw [runEq,map_twice,map_twice]

def readBound (n L trials : ℕ) : ℕ :=
  (epochs n*(2*n*n))*trials*RetainedDrawTrees.sampleWidth n L

noncomputable def cutRun (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L))
    (trials : ℕ) (tape : Bits) : Option (Finset (Fin n)) :=
  (ControllerTapeModel.run positive E (ratio n) trials (epochs n) (epochs n) (sourceCode (adj:=adj) positive) tape).map
    (fun x => cutSet x.1.data.cut)

theorem cutRun_eq (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (trials : ℕ) (tape : Bits) :
    cutRun (adj:=adj) positive E trials tape =
      (EncodedSolverBits.run
        (RetainedFairBitLaw.bitTree trials (optimizer positive E) positive
          (integerCutOracle (G:=Graph adj) positive (enumeration n)) (restart n) (epochs n) (epochs n)
          (sourceCode (adj:=adj) positive)) tape).map Prod.fst := by
  rw [RetainedFairBitLaw.bitTree,← cutTree_eq,cutTree,lower_map,EncodedSolverBits.run_map]
  simp only [cutRun,ControllerTapeModel.run,Option.map_map,Function.comp_def]

theorem codeTree_within (positive : 0 < L) (E : ResidualSearch.Enumeration (Network n L)) :
    Within (epochs n * (2 * n * n)) (codeTree (adj:=adj) positive E) := by
  unfold codeTree
  rw [ControllerTapeModel.tree_exact]
  exact within_map (RetainedDrawTrees.executeTree_within _ _ _ _ _ _ _) _

theorem codeTree_widths (positive : 0 < L) (E : ResidualSearch.Enumeration (Network n L)) :
    LazyFairBitTrees.WidthsLE (RetainedDrawTrees.sampleWidth n L) (codeTree (adj:=adj) positive E) := by
  unfold codeTree
  rw [ControllerTapeModel.tree_exact]
  exact LazyFairBitTrees.widths_map (RetainedDrawTrees.executeTree_widths _ _ _ _ _ _ _) _

theorem tape_complete (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (trials : ℕ)
    (tape : Bits) (enough : readBound n L trials≤tape.length) :
    ∃ out reads,
      ControllerTapeModel.run positive E (ratio n) trials (epochs n) (epochs n) (sourceCode (adj:=adj) positive) tape=
        some (out,(tape.drop reads,reads)) ∧ reads≤readBound n L trials := by
  rw [ControllerTapeModel.run]
  exact EncodedSolverBits.complete (LazyFairBitTrees.lower_within
    (codeTree_within (adj:=adj) positive E) (codeTree_widths (adj:=adj) positive E) trials)
    (LazyFairBitTrees.lower_binary trials _) tape enough

theorem literal_law (positive : 0<L) (E : ResidualSearch.Enumeration (Network n L)) (trials : ℕ) :
    (EncodedSolverBits.fairTape (readBound n L trials)).map (cutRun (adj:=adj) positive E trials) =
      (ideal (LazyFairBitTrees.lower trials (cutTree (adj:=adj) positive E))).map some := by
  rw [cutTree_eq, show cutRun (adj:=adj) positive E trials = _ from
    funext fun tape => cutRun_eq positive E trials tape]
  exact EncodedSolverBits.run_fairTape (RetainedFairBitLaw.bitTree_within _ _ _ _ _ _ _ _)
    (RetainedFairBitLaw.bitTree_binary _ _ _ _ _ _ _ _)

theorem ideal_law (positive : 0<L) [NeZero L] (E : ResidualSearch.Enumeration (Network n L)) :
    ideal (cutTree (adj:=adj) positive E) = IntegerClosureAsymptotic.coreLaw (Graph adj) L positive E := by
  rw [cutTree_eq,RetainedFairBitLaw.cutTree_law]
  let Q := optimizer (adj:=adj) (demands:=remainingSet (sourceCode (adj:=adj) positive).data.remaining) positive E
  let C := integerCutOracle (G:=Graph adj) positive (enumeration n)
  let s := sourceCode (adj:=adj) positive
  change RetainedExecutionLaw.outputLaw Q positive C (restart n) (epochs n) (epochs n) s = _
  rw [← RetainedExecutionLaw.sampledRunLaw_output Q positive C (restart n) (epochs n) (epochs n) s]
  exact RetainedClosureLaw.computedLaw_eq_coreLaw (G:=Graph adj) positive (enumeration n) E

theorem cut_support_valid (positive : 0<L) [NeZero L] (E : ResidualSearch.Enumeration (Network n L))
    (trials : ℕ) {X : Finset (Fin n)}
    (returned : X∈(ideal (LazyFairBitTrees.lower trials (cutTree (adj:=adj) positive E))).support) :
    IsIntegralCut (Graph adj) X (CandidateSchedule.unweightedDemands (Graph adj) (L : ℝ≥0) : Set (Pair n)) := by
  have h := LazyFairBitTrees.lowered_support_subset_ideal trials (cutTree (adj:=adj) positive E) returned
  rw [ideal_law] at h
  exact IntegerClosureAsymptotic.coreLaw_valid (Graph adj) L positive E h

theorem cut_event_le (positive : 0<L) [NeZero L] (E : ResidualSearch.Enumeration (Network n L))
    (trials : ℕ) (event : Finset (Fin n)→Prop) :
    FiniteAmplification.probability (ideal (LazyFairBitTrees.lower trials (cutTree (adj:=adj) positive E))) event ≤
      FiniteAmplification.probability (IntegerClosureAsymptotic.coreLaw (Graph adj) L positive E) event+
        ((epochs n*(2*n*n) : ℕ) : ℝ)*((1 : ℝ)/2)^trials := by
  have within : Within (epochs n * (2 * n * n)) (cutTree (adj:=adj) positive E) :=
    within_map (codeTree_within positive E) (fun out => cutSet out.data.cut)
  have h := LazyFairBitTrees.lowered_event_le within trials event
  rw [ideal_law] at h
  exact h

end DirectedFlowCutGap.OriginalGraphControllerLaw
