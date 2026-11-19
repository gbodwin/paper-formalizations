import DirectedFlowCutGap.PhysicalAmplifiedEdgeSolver
import DirectedFlowCutGap.RandomizedEdgeFamilyParameters

/-! Run the verified adaptive edge family using the physical edge solver at each request. -/

namespace DirectedFlowCutGap.PhysicalEdgeFamily

open BinaryArithmetic FiniteDrawTrees RandomizedEdgeFamily
open RationalWeakFamily RationalEdgeDecomposition CheckedMWHistory
open scoped NNRat ENNReal

abbrev State (n : ℕ) := History (Edge n)

structure Result (n : ℕ) where
  history : Option (State n)
  suffix : Bits
  dispatch : ℕ
  readback : ℕ
  roundingAndSelection : ℕ

def Result.observe {n : ℕ} (r : Result n) : Option (State n) × Bits := (r.history,r.suffix)

def Result.add {n : ℕ} (first later : Result n) : Result n :=
  { later with
    dispatch := first.dispatch+later.dispatch
    readback := first.readback+later.readback
    roundingAndSelection := first.roundingAndSelection+later.roundingAndSelection }

def stepWith {n : ℕ} (D : Input n) (demands : List (Edge n)) (s : State n) (tape : Bits) : Option (Result n) :=
  let cost := penalizedCosts (adjusted D) D.factor s.costs
  let query : EncodedEdgeLineInput.Input n := ⟨D.adjacency,demands,
    Vector.ofFn fun s => Vector.ofFn fun t => RawNonnegativeRational.Code.ofNNRat (cost (s,t))⟩
  (PhysicalAmplifiedEdgeSolver.run D.confidence query .mass tape).map fun round =>
    let next := (CheckedEdgeOracle.check query (allowance D s.costs) round.output).map
      (advance (floored D) D.factor (scale n) s)
    ⟨next,round.suffix,round.dispatch,round.readback,round.roundingAndSelection⟩

def step {n : ℕ} (D : Input n) (s : State n) (tape : Bits) : Option (Result n) :=
  stepWith D (RationalEdgeThresholds.demands D.adjacency D.weights) s tape

theorem step_observe {n : ℕ} (D : Input n) (s : State n) (tape : Bits) :
    (step D s tape).map Result.observe =
      (EncodedSolverBits.run (RandomizedEdgeFamily.step D s) tape).map
        (fun (out,(rest,_)) => (out,rest)) := by
  let query := request D (penalizedCosts (adjusted D) D.factor s.costs)
  let transform := fun out => (CheckedEdgeOracle.check query (allowance D s.costs) out).map
    (advance (floored D) D.factor (scale n) s)
  have observe := PhysicalAmplifiedEdgeSolver.run_observe D.confidence query .mass tape
  have folded : RandomizedEdgeFamily.step D s =
    map (Option.map (advance (floored D) D.factor (scale n) s))
      (map (CheckedEdgeOracle.check query (allowance D s.costs))
        (EncodedEdgeSolver.bitTree D.confidence query EncodedEdgeSolver.massMode)) := rfl
  rw [folded,EncodedSolverBits.run_map,EncodedSolverBits.run_map]
  have hstep : (step D s tape).map Result.observe =
      ((PhysicalAmplifiedEdgeSolver.run D.confidence query .mass tape).map PhysicalAmplifiedEdgeSolver.EdgeResult.observe).map
        (fun (out,rest) => (transform out,rest)) := by
    simp only [step,stepWith,query,request,Option.map_map,Function.comp_def,Result.observe,PhysicalAmplifiedEdgeSolver.EdgeResult.observe,transform]
  rw [hstep,observe]
  simp only [PhysicalAmplifiedEdgeSolver.model,Option.map_map,Function.comp_def,transform]

def runStages {n : ℕ} (one : State n → Bits → Option (Result n)) : ℕ → Option (State n) → Bits → Option (Result n)
  | 0,s,tape => some ⟨s,tape,0,0,0⟩
  | _+1,none,tape => some ⟨none,tape,0,0,0⟩
  | k+1,some s,tape => (one s tape).bind fun first =>
    (runStages one k first.history first.suffix).map first.add

def stages {n : ℕ} (D : Input n) : ℕ → Option (State n) → Bits → Option (Result n) := runStages (step D)

theorem stages_observe {n : ℕ} (D : Input n) (k : ℕ) (s : Option (State n)) (tape : Bits) :
    (stages D k s tape).map Result.observe =
      (EncodedSolverBits.run (AdaptiveOracleFailure.tree (RandomizedEdgeFamily.step D) k s) tape).map
        (fun (out,(rest,_)) => (out,rest)) := by
  induction k generalizing s tape with
  | zero => rfl
  | succ k ih =>
    cases s with
    | none => rfl
    | some s =>
      change (stages D (k+1) (some s) tape).map Result.observe =
        (EncodedSolverBits.run (RandomizedEdgeFamily.step D s >>= AdaptiveOracleFailure.tree (RandomizedEdgeFamily.step D) k)
          tape).map (fun (out,(rest,_)) => (out,rest))
      rw [EncodedSolverBits.run_bind_observe,← step_observe]
      cases first : step D s tape with
      | none => simp [stages,runStages,first]
      | some r =>
        simp only [show stages D (k+1) (some s) tape = (step D s tape).bind (fun first =>
          (stages D k first.history first.suffix).map first.add) from rfl,
          first,Option.bind_some,Option.map_some,Result.observe,← ih]
        cases stages D k r.history r.suffix <;> rfl

def run {n : ℕ} (D : Input n) (tape : Bits) : Option (Result n) :=
  stages D (rounds D) (some initial) tape

theorem run_observe {n : ℕ} (D : Input n) (tape : Bits) :
    (run D tape).map Result.observe =
      (EncodedSolverBits.run (build D) tape).map (fun (out,(rest,_)) => (out,rest)) :=
  stages_observe D (rounds D) (some initial) tape

theorem fairTape_law {n B : ℕ} (positive : 0<n) (D : Input n) (factor : 1≤D.factor)
    (width : InputFits D B) :
    (EncodedSolverBits.fairTape (readBudget n B D.confidence)).map (fun tape => (run D tape).map Result.history) =
      (ideal (build D)).map some := by
  have h : (fun tape => (run D tape).map Result.history) =
      (fun tape => (EncodedSolverBits.run (build D) tape).map Prod.fst) := by
    funext tape
    have e := congrArg (Option.map Prod.fst) (run_observe D tape)
    simpa only [Option.map_map,Function.comp_def,Result.observe] using e
  rw [h]
  exact EncodedSolverBits.run_fairTape (within_build positive D factor width) (build_binary D)

def family {n : ℕ} (D : Input n) (tape : Bits) : Option (Result n) :=
  if originalTotal D.adjacency D.weights<1 then
    some ⟨some ⟨fun _ => 1,List.replicate (rounds D) ∅⟩,tape,0,0,0⟩
  else run D tape

theorem family_observe {n : ℕ} (D : Input n) (tape : Bits) :
    (family D tape).map Result.observe =
      (EncodedSolverBits.run (familyTree D) tape).map (fun (out,(rest,_)) => (out,rest)) := by
  by_cases small : originalTotal D.adjacency D.weights<1
  · simp only [family,familyTree,ite_eq_left small]
    rfl
  · simp only [family,familyTree,ite_eq_right small]
    exact run_observe D tape

/-- The actual encoded edge calls inherit the paper's confidence, horizon,
and original-weight frequency bound. The unread bits remain observable. -/
theorem calibrated_physical (ε : ℝ) (positive : 0<ε) :
    ∃ k M : ℕ, 0<k ∧ 0<M ∧
      ∀ (n : ℕ), 2≤n → ∀ (adj : BinaryFractionalWalkOracle.Adjacency n)
        (w : RationalEdgeThresholds.Weights n) (κ : ℕ),
        let D := calibratedParameters k M κ adj w
        let budget := readBudget n (inputWidth D) D.confidence
        ((EncodedSolverBits.fairTape budget).map (fun tape => ((family D tape).map Result.history).join)) none ≤
          ENNReal.ofReal ((n : ℝ)^(-(κ : ℝ))) ∧
        ∀ tape : Bits, budget≤tape.length →
          ∃ out used, family D tape=some out ∧ out.suffix=tape.drop used ∧ used≤budget ∧
            ∀ s, out.history=some s → s.cuts.length=rounds D ∧ (∀ X∈s.cuts, Good adj w X) ∧
              ∀ e, (occurrences s e : ℝ)/(s.cuts.length : ℝ) ≤
                8*(originalWeight adj w e : ℝ)*(8*(M : ℝ)*(n : ℝ)^ε*(originalTotal adj w : ℝ)^(1/2 : ℝ)) := by
  obtain ⟨k,M,hk,hM,law⟩ := calibrated_families ε positive
  refine ⟨k,M,hk,hM,?_⟩
  intro n large adj w κ
  dsimp only
  let D := calibratedParameters k M κ adj w
  obtain ⟨chance,complete⟩ := law n large adj w κ
  constructor
  · have eq : (fun tape => ((family D tape).map Result.history).join) =
        (fun tape => ((EncodedSolverBits.run (familyTree D) tape).map Prod.fst).join) := by
      funext tape
      have h := congrArg (fun r => (r.map Prod.fst).join) (family_observe D tape)
      simpa only [Option.map_map,Function.comp_def,Result.observe] using h
    rw [eq]
    exact chance
  · intro tape enough
    obtain ⟨hist,used,exactRun,usedBound,good⟩ := complete tape enough
    have obs := family_observe D tape
    rw [exactRun] at obs
    cases actual : family D tape with
    | none => simp [actual] at obs
    | some out =>
      have equal : out.observe=(hist,tape.drop used) := by simpa only [actual,Option.map_some,Option.some.injEq] using obs
      refine ⟨out,used,rfl,congrArg Prod.snd equal,usedBound,?_⟩
      intro s selected
      exact good s ((congrArg Prod.fst equal).symm.trans selected)

end DirectedFlowCutGap.PhysicalEdgeFamily
