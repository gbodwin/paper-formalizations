import DirectedFlowCutGap.PhysicalVertexSampling
import DirectedFlowCutGap.BinaryAmplificationPreparation
import DirectedFlowCutGap.ChargedVertexModes

/-! Original vertex input, actual fractional computation, repeated fair tape and binary selection. -/

namespace DirectedFlowCutGap.PhysicalAmplifiedVertexSolver

open BinaryArithmetic FiniteDrawTrees EncodedVertexSolver EncodedVertexAmplification
open LiteralTapeComposition (execute execute_map execute_bind)
open PhysicalVertexSampling (Runner fromPlan fromPlanWith fromPlan_observe)

def samples {A : Type} (one : Bits → Option ((A × ℕ) × Bits)) :
    (k : ℕ) → Bits → Option ((Fin k → A × ℕ) × Bits)
  | 0,tape => some (Fin.elim0,tape)
  | k+1,tape => (one tape).bind fun (first,rest) =>
      (samples one k rest).map fun (later,suffix) => (Fin.cons first later,suffix)

theorem samples_observe {A : Type} (one : Bits → Option ((A × ℕ) × Bits))
    (T k : ℕ) (tree : FiniteDrawTrees.Tree A)
    (observes : ∀ tape, (one tape).map (fun ((a,_),tail) => (a,tail))=execute T tree tape)
    (tape : Bits) :
    (samples one k tape).map (fun (all,rest) => ((fun i => (all i).1),rest)) =
      execute T (EncodedAmplification.samples tree k) tape := by
  induction k generalizing tape with
  | zero =>
    have same : (fun i : Fin 0 => (Fin.elim0 i : A × ℕ).1) = Fin.elim0 := funext (fun i => i.elim0)
    simp only [samples,Option.map_some,EncodedAmplification.samples,LiteralTapeComposition.execute_pure,same]
  | succ k ih =>
    change (samples one (k+1) tape).map (fun (all,rest) => ((fun i => (all i).1),rest)) =
      execute T (tree >>= fun a => map (Fin.cons (α:=fun _ => A) a)
        (EncodedAmplification.samples tree k)) tape
    rw [execute_bind,← observes]
    cases first : one tape with
    | none => simp [samples,first]
    | some answer =>
      rcases answer with ⟨⟨a,paid⟩,rest⟩
      rw [samples,first]
      simp only [Option.bind_some,Option.map_some,execute_map,← ih]
      cases more : samples one k rest with
      | none => rfl
      | some other =>
        rcases other with ⟨later,suffix⟩
        simp only [Option.map_some]
        have eq : (fun i => (Fin.cons (α:=fun _ => A × ℕ) (a,paid) later i).1) = Fin.cons (α:=fun _ => A) a (fun i => (later i).1) := by
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        rw [eq]

structure Result (n : ℕ) where
  output : Output n
  suffix : Bits
  dispatch : ℕ
  readback : ℕ
  roundingAndSelection : ℕ

def Result.observe {n : ℕ} (r : Result n) : Output n × Bits := (r.output,r.suffix)

def run {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : Runner n)
    (roundBound extra confidence : ℕ) (tape : Bits) : Option (Result n) :=
  (PhysicalSourceReadback.run D).bind fun (plan,dispatch,readback) =>
    let setup := BinaryAmplificationPreparation.prepare D.costs roundBound extra confidence
    (samples (fromPlanWith D setup.costs round setup.trials plan) (extra+1) tape).map fun (cuts,rest) =>
      let (winner,paid) := ChargedAmplification.select D.costs extra cuts
      ⟨winner,rest,dispatch,readback,paid+setup.paid⟩

set_option maxHeartbeats 1600000 in
theorem run_observe {n : ℕ} (D : BinaryFractionalGuesses.Input n) (round : Runner n) (model : Rounding n)
    (roundBound extra confidence : ℕ) (tape : Bits)
    (refines : ∀ T input bits, (round T input bits).map PhysicalIntegerRounding.Result.observe =
      execute T (model input) bits) :
    (run D round roundBound extra confidence tape).map Result.observe =
      (EncodedSolverBits.run (boundedBitTree roundBound extra confidence (BinaryFractionalGuesses.decodeInput D) model)
        tape).map (fun (out,(rest,_)) => (out,rest)) := by
  obtain ⟨paid,lookup,source,_,_⟩ := PhysicalSourceReadback.run_eq D
  let plan := PhysicalCoverReader.plan (BinaryFractionalGuesses.solveInput D).1
  let G := BinaryFractionalGuesses.decodeInput D
  let base := PhysicalVertexSolver.treeFromPlan G model plan
  let T := ChargedPhysicalVertexSolver.trialLimit G roundBound extra confidence
  let sampled := samples (fromPlan D round T plan) (extra+1) tape
  have obs := samples_observe (fromPlan D round T plan) T (extra+1) base
    (fromPlan_observe D round model T (refines T) plan) tape
  have selected : boundedBitTree roundBound extra confidence G model = LazyFairBitTrees.lower T
      (EncodedAmplification.selectedTree (codePrice G) base extra) := by
    simp only [boundedBitTree,boundedFromOutput,EncodedAmplification.bitTree,ChargedPhysicalVertexSolver.trialLimit,
      base,plan,PhysicalVertexSolver.treeFromPlan_eq,BinaryFractionalGuesses.solveInput_refines,T,G]
  rw [selected]
  change (run D round roundBound extra confidence tape).map Result.observe =
    execute T (EncodedAmplification.selectedTree (codePrice G) base extra) tape
  rw [EncodedAmplification.selectedTree,execute_map,← obs]
  have native : run D round roundBound extra confidence tape = sampled.map fun (cuts,rest) =>
      ⟨(ChargedAmplification.select D.costs extra cuts).1,rest,paid,lookup,
        (ChargedAmplification.select D.costs extra cuts).2+
          (BinaryAmplificationPreparation.prepare D.costs roundBound extra confidence).paid⟩ := by
    simp only [run,source,Option.bind_some,sampled,T,G,plan,fromPlan,
      BinaryAmplificationPreparation.costs_value,BinaryAmplificationPreparation.trials_value D]
  rw [native]
  change (sampled.map _).map Result.observe = (sampled.map _).map _
  cases h : sampled with
  | none => rfl
  | some answer =>
    rcases answer with ⟨cuts,rest⟩
    change some ((ChargedAmplification.select D.costs extra cuts).1,rest) =
      some (EncodedAmplification.minimum (codePrice G) extra (fun i => (cuts i).1),rest)
    have eq := (BinaryCutPriceSelection.minimum_refines _ _
      (BinaryCutPriceSelection.cutScore_decodes D) extra (fun i => (cuts i).1)).1
    rw [show (ChargedAmplification.select D.costs extra cuts).1 =
      (BinaryCutPriceSelection.minimum (BinaryCutPriceSelection.cutScore D.costs) extra (fun i => (cuts i).1)).value from rfl,
      eq]

def vertex {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits) : Option (Result n) :=
  let e := confidenceExponent n κ
  run D (match mode with | .mass => PhysicalVertexRounding.weighted | .size => PhysicalVertexRounding.size)
    (roundDrawBound n) e (e+1) tape

theorem vertex_observe {n : ℕ} (κ : ℕ) (mode : ChargedVertexModes.Mode) (D : BinaryFractionalGuesses.Input n)
    (tape : Bits) :
    (vertex κ mode D tape).map Result.observe =
      (EncodedSolverBits.run (polynomialBitTree κ (BinaryFractionalGuesses.decodeInput D) (ChargedVertexModes.round n mode)) tape).map
        (fun (out,(rest,_)) => (out,rest)) := by
  cases mode with
  | mass => exact run_observe D _ _ _ _ _ tape PhysicalVertexRounding.weighted_observe
  | size => exact run_observe D _ _ _ _ _ tape PhysicalVertexRounding.size_observe

end DirectedFlowCutGap.PhysicalAmplifiedVertexSolver
