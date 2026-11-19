import DirectedFlowCutGap.RawGraphInputStore
import DirectedFlowCutGap.EncodedIntegerRounding
import DirectedFlowCutGap.EncodedEpochParameters
import DirectedFlowCutGap.PhysicalCoverAccess
import DirectedFlowCutGap.BinaryNaturalView

/-! Execute all three cutoff regimes and transport the actual output and tape. -/

namespace DirectedFlowCutGap.PhysicalIntegerRounding

open BinaryArithmetic FiniteDrawTrees RetainedGridState ImmutableReferenceSimulation
open IntegerEpochParameters (restart fuel cap)
open OriginalGraphControllerLaw (codeTree projectTree_eq projectRun_eq ratio epochs sourceCode)
open RawGraphControllerProgram (instructionBound chargeBound)
open RawGraphInputStore (prepare cells)
open IntegralNetworkFlow

structure Result (n : ℕ) where
  mask : Flags n
  suffix : Bits
  paid : ℕ

def Result.observe {n : ℕ} (r : Result n) : Flags n × Bits := (r.mask,r.suffix)

def fromWord (n : ℕ) (word : Bits) : Flags n :=
  let bits := word.toArray
  Vector.ofFn (fun v : Fin n => bits[v.val]?.getD false)

private theorem fromWord_exact {n : ℕ} (mask : Flags n) : fromWord n mask.toList=mask := by
  apply Vector.ext
  intro i hi
  have h : i < mask.toList.length := by simpa only [Vector.length_toList] using hi
  simp only [fromWord,Vector.getElem_ofFn,List.getElem?_toArray,List.getElem?_eq_getElem h,
    Option.getD_some,Vector.getElem_toList]

structure BoundaryWords where
  dimension : Bits
  level : Bits
  trials : Bits
  paid : ℕ

def boundaryWords (n L T : ℕ) : BoundaryWords :=
  let dimension := BinaryNaturalView.encode n
  let level := BinaryNaturalView.encode L
  let trials := BinaryNaturalView.encode T
  ⟨dimension.1,level.1,trials.1,dimension.2+level.2+trials.2+24*(n+1)^3+12⟩

@[simp] theorem boundary_dimension (n L T : ℕ) : (boundaryWords n L T).dimension=n.bits :=
  BinaryNaturalView.encode_bits _

@[simp] theorem boundary_level (n L T : ℕ) : (boundaryWords n L T).level=L.bits :=
  BinaryNaturalView.encode_bits _

@[simp] theorem boundary_trials (n L T : ℕ) : (boundaryWords n L T).trials=T.bits :=
  BinaryNaturalView.encode_bits _

def maskCopyCharge (n length : ℕ) : ℕ := 16*(n+length+1)^2

def hardRun {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (tape : Bits) : Option (Result n) :=
  let words := boundaryWords n L T
  let matrix := GraphRelaxationRefinement.matrix adj
  let H := cells matrix words.dimension words.level words.trials
  let entry := prepare matrix words.dimension words.level words.trials tape
  do
    let (out,paid) ← GuardedReferenceExecution.execute RawGraphControllerProgram.program
      (instructionBound n L (H+1) words.trials+1) entry.1 0
    let observed := PhysicalCoverAccess.readWord out.heap out.registers.d
    let mask ← observed.1
    pure ⟨fromWord n mask,out.source,entry.2+paid+observed.2+words.paid+maskCopyCharge n mask.length⟩

private noncomputable abbrev maskTree {n L : ℕ} (adj : PairFlags n) (positive : 0<L) :=
  map (fun s => s.data.cut)
    (codeTree (adj:=adj) positive (CandidateEnumeration.make n L).network.enumeration)

private theorem hard_observe {n L : ℕ} (T : ℕ) (adj : PairFlags n) (positive : 0<L) (tape : Bits) :
    (hardRun T adj L tape).map Result.observe =
      (EncodedSolverBits.run (LazyFairBitTrees.lower T (maskTree adj positive)) tape).map
        (fun (mask,(rest,_)) => (mask,rest)) := by
  let F := CandidateEnumeration.make n L
  let E := F.network.enumeration
  let EN := F.nodes.enumeration
  let matrix := GraphRelaxationRefinement.matrix adj
  let H := cells matrix n.bits L.bits T.bits
  let input := prepare matrix n.bits L.bits T.bits tape
  obtain ⟨data,_⟩ := RawGraphInputStore.prepare_spec (L:=L) adj T.bits tape
  have physical := RawGraphControllerProgram.guarded_cut positive EN E input.1
    data.bounded data.entry data.quiet data.dense data.graph data.trials
  rw [value_bits,show input.1.source=tape from rfl] at physical
  have law := projectRun_eq (adj:=adj) id positive E T tape
  change EncodedSolverBits.run (LazyFairBitTrees.lower T (maskTree adj positive)) tape = _ at law
  rw [law]
  cases model : ControllerTapeModel.run positive E (ratio n) T (epochs n) (epochs n) (sourceCode (adj:=adj) positive) tape with
  | none =>
    rw [model] at physical
    simp [hardRun,matrix,input,physical]
  | some answer =>
    rcases answer with ⟨out,rest,reads⟩
    rw [model] at physical
    obtain ⟨native,paid,done,mask,tail,_,_,_,_⟩ := physical
    dsimp only [input,matrix] at done
    have observed : (PhysicalCoverAccess.readWord native.heap native.registers.d).1 =
        some out.data.cut.toList := (PhysicalCoverAccess.readWord_value _ _).trans mask
    simp [hardRun,done,observed,Result.observe,fromWord_exact,tail]

set_option maxHeartbeats 1100000 in
private theorem tree_hard {n L : ℕ} (adj : PairFlags n) (positive : 0<L) (inside : L≤n)
    (constraints : 64*cap n≤L ∧ n≤L^3) :
    EncodedIntegerRounding.tree adj L positive=maskTree adj positive := by
  let F := CandidateEnumeration.make n L
  let E := F.network.enumeration
  let mask := RetainedDemandMask.compute (RetainedCandidateSolver.graph adj) F.base.enumeration L
  let start := RetainedDemandMask.initial (RetainedCandidateSolver.graph adj) F.base.enumeration L positive
  let Q := RetainedCandidateSolver.makeOptimizer (demands:=remainingSet mask) adj L positive
  have opt := RetainedCandidateSolver.makeOptimizer_eq (demands:=remainingSet mask) adj L positive
  rw [EncodedIntegerRounding.tree,ite_eq_left inside,ite_eq_left constraints]
  rw [show maskTree adj positive = _ from projectTree_eq (adj:=adj) id positive E]
  change map (fun out => out.result.cache.state.data.cut)
      (RetainedDrawTrees.runTree Q positive
        (integerCutOracle (G:=RetainedCandidateSolver.graph adj) positive F.base.enumeration)
          (restart n) (epochs n) (epochs n) start) =
    map (fun out => out.result.cache.state.data.cut)
      (RetainedDrawTrees.runTree (EpochScanData.optimizer positive E) positive
        (integerCutOracle (G:=EpochScanData.Graph adj) positive (InitialGraphContexts.enumeration n))
          (restart n) (epochs n) (epochs n) (sourceCode (adj:=adj) positive))
  have replace := congrArg (fun solver => map (fun out => out.result.cache.state.data.cut)
    (RetainedDrawTrees.runTree solver positive
      (integerCutOracle (G:=RetainedCandidateSolver.graph adj) positive F.base.enumeration)
        (restart n) (epochs n) (epochs n) start)) opt
  let reference (EV : ResidualSearch.Enumeration (Fin n)) :=
    let initial := RetainedDemandMask.initial (RetainedCandidateSolver.graph adj) EV L positive
    map (fun out => out.result.cache.state.data.cut) (RetainedDrawTrees.runTree
      (tabulatedOptimizer positive EV E) positive (integerCutOracle (G:=RetainedCandidateSolver.graph adj) positive EV)
      (restart n) (epochs n) (epochs n) initial)
  have injective : Function.Injective (ResidualSearch.Enumeration.vertices (V:=Fin n)) := by
    intro a b h
    cases a
    cases b
    cases h
    rfl
  have exactOrder : F.base.enumeration=InitialGraphContexts.enumeration n := injective
    (CandidateEnumeration.fin_order n)
  exact replace.trans (congrArg reference exactOrder)

/-- The cutoff gate uses the existing charged arithmetic parameter calculation.
The heavy physical controller runs only when the level is at most the graph size. -/
def run {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (tape : Bits) : Option (Result n) :=
  let p := EncodedEpochParameters.compute n
  let work := p.work+2*n+10
  if L≤n then
    if 64*p.cap≤L ∧ n≤L^3 then
      (hardRun T adj L tape).map (fun result => { result with paid := work+result.paid })
    else some ⟨Vector.replicate n true,tape,work⟩
  else some ⟨Vector.replicate n false,tape,work⟩

theorem run_observe {n : ℕ} (T : ℕ) (adj : PairFlags n) (L : ℕ) (positive : 0<L) (tape : Bits) :
    (run T adj L tape).map Result.observe =
      (EncodedSolverBits.run (EncodedIntegerRounding.bitTree T adj L positive) tape).map
        (fun (mask,(rest,_)) => (mask,rest)) := by
  by_cases inside : L≤n
  · by_cases constraints : 64*cap n≤L ∧ n≤L^3
    · simp only [run,EncodedEpochParameters.compute_cap,ite_eq_left inside,ite_eq_left constraints,Option.map_map,EncodedIntegerRounding.bitTree]
      rw [tree_hard adj positive inside constraints]
      exact hard_observe T adj positive tape
    · simp only [run,EncodedEpochParameters.compute_cap,ite_eq_left inside,ite_eq_right constraints,
        EncodedIntegerRounding.bitTree,EncodedIntegerRounding.tree]
      rfl
  · simp only [run,ite_eq_right inside,EncodedIntegerRounding.bitTree,EncodedIntegerRounding.tree]
    rfl

end DirectedFlowCutGap.PhysicalIntegerRounding
