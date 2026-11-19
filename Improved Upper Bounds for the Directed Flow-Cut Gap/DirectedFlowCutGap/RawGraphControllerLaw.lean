import DirectedFlowCutGap.RawGraphControllerProgram

/-! The distribution obtained by running the fixed machine on a fair tape. -/

namespace DirectedFlowCutGap.RawGraphControllerLaw

open scoped NNReal
open BinaryArithmetic ImmutableReferenceSimulation FiniteDrawTrees IntegralNetworkFlow RetainedGridState
open RawGraphControllerProgram (instructionBound)
open OriginalGraphControllerLaw (cutTree cutRun readBound ratio epochs)
open CandidateEnumeration (Node Network)

def readCut {n : ℕ} (word : Bits) : Finset (Fin n) :=
  Finset.univ.filter fun v => word[v.val]?.getD false = true

theorem readCut_flags {n : ℕ} (flags : Flags n) : readCut flags.toList = cutSet flags := by
  ext v
  have h : v.val<flags.toList.length := by simpa only [Vector.length_toList] using v.isLt
  simp only [readCut,cutSet,Finset.mem_filter,Finset.mem_univ,true_and,List.getElem?_eq_getElem h,
    Option.getD_some,Vector.getElem_toList]

def run {n : ℕ} (L H : ℕ) (trialWord : Bits) (input : BitState 26704) : Option (Finset (Fin n)) := do
  let (out,_) ← GuardedReferenceExecution.execute RawGraphControllerProgram.program
    (instructionBound n L H trialWord+1) input 0
  let cut ← PhysicalCoverReader.readWord (eraseState out).heap (eraseState out).registers.d
  pure (readCut cut)

structure Input {n L : ℕ} (adj : PairFlags n) (trialWord : Bits) (H A : ℕ) (state : BitState 26704) : Prop where
  bounded : state.Bounded H A
  entry : state.pc=0
  quiet : state.stack=[]
  dense : (eraseState state).next=(eraseState state).heap.length
  graph : InitialGraphContexts.Input (L:=L) (eraseState state).heap (eraseState state).registers.a adj
  trials : BooleanTableRead.BoolList (eraseState state).heap (eraseState state).registers.b trialWord

theorem Input.with_tape {n L H A : ℕ} {adj : PairFlags n} {trialWord : Bits} {state : BitState 26704}
    (data : Input (L:=L) adj trialWord H A state) (tape : Bits) :
    Input (L:=L) adj trialWord H A { state with source := tape } :=
  ⟨data.bounded,data.entry,data.quiet,data.dense,data.graph,data.trials⟩

set_option maxHeartbeats 1200000 in
theorem run_eq {n L H A : ℕ} {adj : PairFlags n} {trialWord : Bits} (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (input : BitState 26704) (data : Input (L:=L) adj trialWord H A input) :
    run L H trialWord input = cutRun (adj:=adj) positive E (value trialWord) input.source := by
  have observed := RawGraphControllerProgram.guarded_cut positive EN E input
    data.bounded data.entry data.quiet data.dense data.graph data.trials
  cases model : ControllerTapeModel.run positive E (ratio n) (value trialWord) (epochs n) (epochs n)
    (PhysicalControllerInitializer.initialCode adj positive) input.source with
  | none =>
    rw [model] at observed
    simp [run,OriginalGraphControllerLaw.cutRun,model,observed]
  | some result =>
    rcases result with ⟨last,rest,reads⟩
    rw [model] at observed
    obtain ⟨out,paid,guarded,cut,_,_,_,_,_⟩ := observed
    simp [run,OriginalGraphControllerLaw.cutRun,model,guarded,cut,readCut_flags]

theorem fairTape_law {n L H A : ℕ} {adj : PairFlags n} {trialWord : Bits} (positive : 0<L)
    (EN : ResidualSearch.Enumeration (Node n L)) (E : ResidualSearch.Enumeration (Network n L))
    (input : BitState 26704) (data : Input (L:=L) adj trialWord H A input) :
    (EncodedSolverBits.fairTape (readBound n L (value trialWord))).map
      (fun tape => run L H trialWord { input with source := tape }) =
      (ideal (LazyFairBitTrees.lower (value trialWord) (cutTree (adj:=adj) positive E))).map some := by
  have equality : (fun tape => run (n:=n) L H trialWord { input with source := tape }) =
      cutRun (adj:=adj) positive E (value trialWord) := by
    funext tape
    exact run_eq positive EN E _ (data.with_tape tape)
  rw [equality]
  exact OriginalGraphControllerLaw.literal_law positive E (value trialWord)

end DirectedFlowCutGap.RawGraphControllerLaw
