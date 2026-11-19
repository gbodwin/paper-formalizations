import DirectedFlowCutGap.BinaryEdgeFamilyControls
import DirectedFlowCutGap.BinaryEdgeFamilyState
import DirectedFlowCutGap.PhysicalBinaryEdgeWire
import DirectedFlowCutGap.PhysicalEdgeFamily

/-! The adaptive runner keeps each checked price row and calls the binary
edge solver with exactly the original adaptive query on each literal tape. -/

namespace DirectedFlowCutGap.PhysicalBinaryEdgeFamily

open scoped NNRat ENNReal
open BinaryArithmetic FiniteDrawTrees RandomizedEdgeFamily
open RationalEdgeDecomposition BinaryEdgeFamilyArithmetic BinaryEdgeFamilyState

structure Result (n : ℕ) where
  history : Option (State n)
  suffix : Bits
  dispatch : ℕ
  readback : ℕ
  roundingAndSelection : ℕ
  arithmetic : ℕ

def Result.observe {n : ℕ} (r : Result n) : Option (RationalWeakFamily.History (Edge n)) × Bits :=
  (r.history.map State.observe,r.suffix)

def Result.add {n : ℕ} (first later : Result n) : Result n :=
  { later with
    dispatch := first.dispatch+later.dispatch
    readback := first.readback+later.readback
    roundingAndSelection := first.roundingAndSelection+later.roundingAndSelection
    arithmetic := first.arithmetic+later.arithmetic }

def Result.total {n : ℕ} (r : Result n) : ℕ :=
  r.dispatch+r.readback+r.roundingAndSelection+r.arithmetic

def finishStep {n : ℕ} (p : Preparation n) (s : State n) (q : Query n)
    (r : PhysicalAmplifiedEdgeSolver.EdgeResult n) : Result n :=
  let a := check q r.output
  let next := a.1.map (advance p s)
  ⟨next.map Prod.fst,r.suffix,r.dispatch,r.readback,r.roundingAndSelection,
    q.paid+a.2+(next.map Prod.snd).getD 0+12⟩

def step {n : ℕ} (D : Input n) (p : Preparation n) (demands : List (Edge n)) (s : State n) (tape : Bits) :
    Option (Result n) :=
  let q := query D p demands s
  (PhysicalAmplifiedBinaryEdge.run D.confidence q.input .mass tape).map (finishStep p s q)

theorem step_canonical {n : ℕ} (D : Input n) (p : Preparation n) (demands : List (Edge n))
    (s : State n) (h : s.Canonical) (tape : Bits) {r : Result n} (ran : step D p demands s tape=some r) :
    ∀ next ∈ r.history, next.Canonical := by
  let q := query D p demands s
  obtain ⟨round,_,rfl⟩ := Option.map_eq_some_iff.mp ran
  intro out mem
  change out ∈ ((check q round.output).1.map (advance p s)).map Prod.fst at mem
  cases tag : (check q round.output).1 with
  | none => simp [tag] at mem
  | some mask =>
    simp only [tag,Option.map_some,Option.mem_some_iff] at mem
    rw [← mem]
    exact advance_canonical p s mask h

private theorem checked_observe {n : ℕ} (D : Input n) (s : State n) (h : s.Canonical)
    (answer : EncodedEdgeSolver.Output n) :
    let d := RationalEdgeThresholds.demands D.adjacency D.weights
    let q := query D (prepare D).1 d s
    ((check q answer).1.map (advance (prepare D).1 s)).map (fun a => a.1.observe) =
      (CheckedEdgeOracle.check (request D (RationalWeakFamily.penalizedCosts (adjusted D) D.factor s.observe.costs))
        (allowance D s.observe.costs) answer).map (CheckedMWHistory.advance (floored D) D.factor (scale n) s.observe) := by
  dsimp only
  rw [← query_request D s h,← check_value _ _ (query_limit D _ s) answer]
  simp only [Option.map_map,Function.comp_def,advance_observe]

theorem step_observe {n : ℕ} (D : Input n) (s : State n) (h : s.Canonical) (tape : Bits) :
    (step D (prepare D).1 (RationalEdgeThresholds.demands D.adjacency D.weights) s tape).map Result.observe =
      (EncodedSolverBits.run (RandomizedEdgeFamily.step D s.observe) tape).map (fun (out,(rest,_)) => (out,rest)) := by
  let d := RationalEdgeThresholds.demands D.adjacency D.weights
  let p := (prepare D).1
  let q := query D p d s
  let Q := request D (RationalWeakFamily.penalizedCosts (adjusted D) D.factor s.observe.costs)
  let call := PhysicalAmplifiedBinaryEdge.run D.confidence q.input .mass tape
  let finish := fun out => (CheckedEdgeOracle.check Q (allowance D s.observe.costs) out).map
    (CheckedMWHistory.advance (floored D) D.factor (scale n) s.observe)
  have inputEq : q.input=Q := query_request D s h
  have law := PhysicalAmplifiedBinaryEdge.run_observe D.confidence q.input .mass tape
  change call.map PhysicalAmplifiedEdgeSolver.EdgeResult.observe = _ at law
  rw [inputEq] at law
  have model : RandomizedEdgeFamily.step D s.observe =
      map (Option.map (CheckedMWHistory.advance (floored D) D.factor (scale n) s.observe))
        (map (CheckedEdgeOracle.check Q (allowance D s.observe.costs))
          (EncodedEdgeSolver.bitTree D.confidence Q EncodedEdgeSolver.massMode)) := rfl
  rw [model,EncodedSolverBits.run_map,EncodedSolverBits.run_map]
  have join : (step D p d s tape).map Result.observe =
      (call.map PhysicalAmplifiedEdgeSolver.EdgeResult.observe).map (fun (out,rest) => (finish out,rest)) := by
    change (call.map (finishStep p s q)).map Result.observe = _
    simp only [Option.map_map,Function.comp_def,finishStep,Result.observe,PhysicalAmplifiedEdgeSolver.EdgeResult.observe]
    apply congrArg (fun f => call.map f)
    funext a
    have same := checked_observe D s h a.output
    change ((check q a.output).1.map (advance p s)).map (fun x => x.1.observe) = finish a.output at same
    simp only [Option.map_map,Function.comp_def] at same
    rw [same]
  rw [show step D (prepare D).1 (RationalEdgeThresholds.demands D.adjacency D.weights) s tape=step D p d s tape from rfl,
    join,law]
  simp only [PhysicalAmplifiedEdgeSolver.model,Option.map_map,Function.comp_def,finish]

def stages {n : ℕ} (one : State n → Bits → Option (Result n)) : ℕ → Option (State n) → Bits → Option (Result n)
  | 0,s,tape => some ⟨s,tape,0,0,0,0⟩
  | _+1,none,tape => some ⟨none,tape,0,0,0,0⟩
  | k+1,some s,tape => (one s tape).bind fun first =>
    (stages one k first.history first.suffix).map first.add

theorem stages_observe {n : ℕ} (D : Input n) (k : ℕ) (state : Option (State n))
    (h : ∀ s ∈ state, s.Canonical) (tape : Bits) :
    let call := step D (prepare D).1 (RationalEdgeThresholds.demands D.adjacency D.weights)
    (stages call k state tape).map Result.observe =
      (EncodedSolverBits.run (AdaptiveOracleFailure.tree (RandomizedEdgeFamily.step D) k (state.map State.observe)) tape).map
        (fun (out,(rest,_)) => (out,rest)) := by
  dsimp only
  induction k generalizing state tape with
  | zero => rfl
  | succ k ih =>
    cases state with
    | none => rfl
    | some s =>
      let call := step D (prepare D).1 (RationalEdgeThresholds.demands D.adjacency D.weights)
      have hs := h s (by simp)
      change (stages call (k+1) (some s) tape).map Result.observe =
        (EncodedSolverBits.run (RandomizedEdgeFamily.step D s.observe >>=
          AdaptiveOracleFailure.tree (RandomizedEdgeFamily.step D) k) tape).map (fun (out,(rest,_)) => (out,rest))
      rw [EncodedSolverBits.run_bind_observe,← step_observe D s hs]
      change (stages call (k+1) (some s) tape).map Result.observe =
        ((call s tape).map Result.observe).bind _
      cases ran : call s tape with
      | none => simp only [stages,ran,Option.bind_none,Option.map_none]
      | some first =>
        have live := step_canonical D (prepare D).1 (RationalEdgeThresholds.demands D.adjacency D.weights) s hs tape ran
        have next := ih first.history live first.suffix
        simp only [stages,ran,Option.bind_some,Option.map_some,Result.observe,← next]
        cases stages call k first.history first.suffix <;> rfl

def runPrepared {n : ℕ} (D : Input n) (p : Preparation n × ℕ) (control : BinaryEdgeFamilyControls.Controls)
    (tape : Bits) : Option (Result n) :=
  if control.small then
    some ⟨some { initial n with cuts := List.replicate control.horizon ∅ },tape,0,0,0,
      p.2+control.paid+8*control.horizon+12⟩
  else
    let demands := ChargedEdgeThresholdDemands.demands D.adjacency D.weights
    (stages (step D p.1 demands.1) control.horizon (some (initial n)) tape).map
      (fun r => { r with arithmetic := p.2+control.paid+demands.2+r.arithmetic+12 })

def run {n : ℕ} (D : Input n) (tape : Bits) : Option (Result n) :=
  let p := prepare D
  runPrepared D p (BinaryEdgeFamilyControls.compute n p.1.total) tape

theorem run_observe {n : ℕ} (D : Input n) (tape : Bits) :
    (run D tape).map Result.observe =
      (EncodedSolverBits.run (familyTree D) tape).map (fun (out,(rest,_)) => (out,rest)) := by
  have horizon : (BinaryEdgeFamilyControls.compute n (prepare D).1.total).horizon=rounds D := by
    simp only [BinaryEdgeFamilyControls.compute_horizon,prepare_total,rounds]
  have small : (BinaryEdgeFamilyControls.compute n (prepare D).1.total).small=true ↔
      originalTotal D.adjacency D.weights<1 := by
    simp only [BinaryEdgeFamilyControls.compute_small,prepare_total]
  by_cases h : originalTotal D.adjacency D.weights<1
  · have take := small.mpr h
    have legacy := PhysicalEdgeFamily.family_observe D tape
    rw [← legacy]
    simp only [run,runPrepared,PhysicalEdgeFamily.family,ite_eq_left take,ite_eq_left h,Option.map_some,horizon,Result.observe,
      State.observe,initial,BinaryEdgeFamilyArithmetic.read,Vector.getElem_replicate,RawNonnegativeRational.Code.value_one,
      PhysicalEdgeFamily.Result.observe]
  · have take := fun eq => h (small.mp eq)
    let call := step D (prepare D).1 (RationalEdgeThresholds.demands D.adjacency D.weights)
    have init : ∀ s ∈ some (initial n), s.Canonical := fun s mem =>
      (Option.mem_some_iff.mp mem).symm ▸ initial_canonical n
    have law := stages_observe D (rounds D) (some (initial n)) init tape
    have obs : (run D tape).map Result.observe = (stages call (rounds D) (some (initial n)) tape).map Result.observe := by
      simp only [run,runPrepared,ite_eq_right take,horizon,ChargedEdgeThresholdDemands.demands_value,Option.map_map,
        Function.comp_def,Result.observe,call]
      rfl
    rw [obs,familyTree,ite_eq_right h]
    simpa only [Option.map_some,initial_observe,RandomizedEdgeFamily.build,call] using law

/-- The actual binary calls and retained price updates inherit the calibrated
confidence, horizon, and per-edge original-weight frequency guarantee. -/
theorem calibrated_physical (ε : ℝ) (positive : 0<ε) :
    ∃ k M : ℕ, 0<k ∧ 0<M ∧
      ∀ (n : ℕ), 2≤n → ∀ (adj : BinaryFractionalWalkOracle.Adjacency n)
        (w : RationalEdgeThresholds.Weights n) (κ : ℕ),
        let D := calibratedParameters k M κ adj w
        let budget := readBudget n (inputWidth D) D.confidence
        ((EncodedSolverBits.fairTape budget).map (fun tape => ((run D tape).map (fun r => r.observe.1)).join)) none ≤
          ENNReal.ofReal ((n : ℝ)^(-(κ : ℝ))) ∧
        ∀ tape : Bits, budget≤tape.length →
          ∃ out used, run D tape=some out ∧ out.suffix=tape.drop used ∧ used≤budget ∧
            ∀ s, out.history=some s → s.cuts.length=rounds D ∧ (∀ X∈s.cuts, Good adj w X) ∧
              ∀ e, (CheckedMWHistory.occurrences s.observe e : ℝ)/(s.cuts.length : ℝ) ≤
                8*(originalWeight adj w e : ℝ)*(8*(M : ℝ)*(n : ℝ)^ε*(originalTotal adj w : ℝ)^(1/2 : ℝ)) := by
  obtain ⟨k,M,hk,hM,law⟩ := calibrated_families ε positive
  refine ⟨k,M,hk,hM,?_⟩
  intro n large adj w κ
  dsimp only
  let D := calibratedParameters k M κ adj w
  obtain ⟨chance,complete⟩ := law n large adj w κ
  constructor
  · have eq : (fun tape => ((run D tape).map (fun r => r.observe.1)).join) =
        (fun tape => ((EncodedSolverBits.run (familyTree D) tape).map Prod.fst).join) := by
      funext tape
      have h := congrArg (fun r => (r.map Prod.fst).join) (run_observe D tape)
      simpa only [Option.map_map,Function.comp_def] using h
    rw [eq]
    exact chance
  · intro tape enough
    obtain ⟨hist,used,exactRun,usedBound,good⟩ := complete tape enough
    have obs := run_observe D tape
    rw [exactRun] at obs
    cases actual : run D tape with
    | none => simp [actual] at obs
    | some out =>
      have equal : out.observe=(hist,tape.drop used) :=
        by simpa only [actual,Option.map_some,Option.some.injEq] using obs
      refine ⟨out,used,rfl,congrArg Prod.snd equal,usedBound,?_⟩
      intro s selected
      have history : out.history.map State.observe=hist := congrArg Prod.fst equal
      rw [selected,Option.map_some] at history
      exact good s.observe history.symm

end DirectedFlowCutGap.PhysicalBinaryEdgeFamily
