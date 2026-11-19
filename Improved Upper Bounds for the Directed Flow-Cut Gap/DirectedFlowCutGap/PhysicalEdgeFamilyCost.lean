import DirectedFlowCutGap.PhysicalEdgeCostEnvelope
import DirectedFlowCutGap.PhysicalEdgeFamily
import DirectedFlowCutGap.AdaptiveWidthEnvelope

/-! Recorded edge solver charges along the reached adaptive histories. -/

namespace DirectedFlowCutGap.PhysicalEdgeFamilyCost

open scoped NNRat
open BinaryArithmetic FiniteDrawTrees Polynomial
open RandomizedEdgeFamily RationalWeakFamily CheckedMWHistory
open PhysicalEdgeFamily (Result State)
open PhysicalIntegerRoundingCost (eval_mono)

abbrev paid {n : ℕ} (r : Result n) : ℕ := r.dispatch+r.readback+r.roundingAndSelection

private theorem step_progress {n : ℕ} (positive : 0<n) (D : Input n) (factor : 1 ≤ D.factor)
    (s : State n) (hs : Invariant (floored D) D.factor (scale n) (keep D) s)
    (tape : Bits) {r : Result n} {next : State n} (actual : PhysicalEdgeFamily.step D s tape = some r)
    (more : r.history=some next) :
    Invariant (floored D) D.factor (scale n) (keep D) next ∧ next.cuts.length=s.cuts.length+1 := by
  have consistent := PhysicalEdgeFamily.step_observe D s tape
  rw [actual] at consistent
  cases idealRun : EncodedSolverBits.run (RandomizedEdgeFamily.step D s) tape with
  | none => simp [idealRun] at consistent
  | some x =>
    rcases x with ⟨h,rest,t⟩
    simp only [idealRun,Option.map_some,Option.some.injEq,Prod.mk.injEq,Result.observe] at consistent
    have acc := EncodedSolverBits.run_support (step_binary D s) idealRun
    rw [← consistent.1,more] at acc
    exact step_good positive D (zero_lt_one.trans_le factor) s next hs acc

private theorem step_paid {n B : ℕ} (p : Polynomial ℕ)
    (runBound : ∀ {n B : ℕ} (κ : ℕ) (D : EncodedEdgeLineInput.Input n)
      (mode : ChargedVertexModes.Mode) (tape : Bits), 1 ≤ B →
      (∀ u v : Fin n, (D.costs[u.val][v.val]).num.size ≤ B ∧ (D.costs[u.val][v.val]).den.size ≤ B) →
      ∀ {out : PhysicalAmplifiedEdgeSolver.EdgeResult n},
        PhysicalAmplifiedEdgeSolver.run κ D mode tape = some out →
          out.dispatch+out.readback+out.roundingAndSelection ≤ p.eval (n+D.demands.length+B+κ))
    (D : Input n) (width : InputFits D B) (s : State n)
    (hs : Invariant (floored D) D.factor (scale n) (keep D) s) (hT : s.cuts.length ≤ roundBudget n B)
    (tape : Bits) {r : Result n} (actual : PhysicalEdgeFamily.step D s tape=some r) :
    paid r ≤ p.eval (n+n*n+fieldBudget n B+D.confidence) := by
  let query := request D (penalizedCosts (adjusted D) D.factor s.costs)
  simp only [PhysicalEdgeFamily.step,PhysicalEdgeFamily.stepWith] at actual
  change ((PhysicalAmplifiedEdgeSolver.run D.confidence query .mass tape).map _)=some r at actual
  cases executed : PhysicalAmplifiedEdgeSolver.run D.confidence query .mass tape with
  | none => simp [executed] at actual
  | some out =>
    simp only [executed,Option.map_some,Option.some.injEq] at actual
    have positive : 1 ≤ fieldBudget n B := by unfold fieldBudget; dsimp only; omega
    have calls : query.demands.length ≤ n*n := by
      unfold query request RationalEdgeThresholds.demands
      dsimp only
      apply (List.length_filter_le ..).trans
      simp [List.length_flatMap]
    have cost := runBound D.confidence query .mass tape positive (step_query_width D width s hs hT) executed
    rw [← actual]
    exact cost.trans (eval_mono p (by omega))

private theorem stages_paid {n : ℕ} (D : Input n) (limit cap : ℕ)
    (stepBound : ∀ s : State n, Invariant (floored D) D.factor (scale n) (keep D) s → s.cuts.length ≤ limit →
      ∀ tape r, PhysicalEdgeFamily.step D s tape=some r → paid r ≤ cap)
    (positive : 0<n) (factor : 1 ≤ D.factor) (k : ℕ) (s : Option (State n)) (tape : Bits)
    (invariant : ∀ a ∈ s, Invariant (floored D) D.factor (scale n) (keep D) a ∧ a.cuts.length+k ≤ limit)
    {r : Result n} (actual : PhysicalEdgeFamily.stages D k s tape = some r) : paid r ≤ k*cap := by
  induction k generalizing s tape r with
  | zero =>
    simp only [PhysicalEdgeFamily.stages,PhysicalEdgeFamily.runStages,Option.some.injEq] at actual
    rw [← actual]
    simp
  | succ k ih =>
    cases s with
    | none =>
      simp only [PhysicalEdgeFamily.stages,PhysicalEdgeFamily.runStages,Option.some.injEq] at actual
      rw [← actual]
      exact Nat.zero_le _
    | some s =>
      have old := invariant s (by simp)
      change ((PhysicalEdgeFamily.step D s tape).bind fun first =>
        (PhysicalEdgeFamily.stages D k first.history first.suffix).map first.add)=some r at actual
      cases first : PhysicalEdgeFamily.step D s tape with
      | none => simp [first] at actual
      | some out =>
        cases later : PhysicalEdgeFamily.stages D k out.history out.suffix with
        | none => simp [first,later] at actual
        | some rest =>
          simp only [first,later,Option.bind_some,Option.map_some,Option.some.injEq] at actual
          have thisCost := stepBound s old.1 (by omega) tape out first
          have tailCost := ih out.history out.suffix (fun a mem => by
            have ⟨kept, length⟩ := step_progress positive D factor s old.1 tape first (Option.mem_def.mp mem)
            exact ⟨kept,by omega⟩) later
          rw [← actual]
          change out.dispatch+rest.dispatch+(out.readback+rest.readback)+
            (out.roundingAndSelection+rest.roundingAndSelection) ≤ (k+1)*cap
          rw [Nat.add_mul,Nat.one_mul]
          simp only [paid] at thisCost tailCost
          omega

noncomputable def paidPolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  let A := X+X+C 2
  let horizon := C 2*X*(C 2*X+X*X*(X+1)+C 3)+1
  let price := (C 3*A+1)*horizon
  let fields := price+A+X*X*(price+A+1)+C 2
  horizon*p.comp (X+X*X+fields+X)

theorem family_polynomial : ∃ p : Polynomial ℕ, ∀ {n B : ℕ}, 0<n → ∀ (D : Input n),
    1 ≤ D.factor → InputFits D B → ∀ tape r, PhysicalEdgeFamily.family D tape = some r →
      paid r ≤ p.eval (n+B+D.confidence) := by
  obtain ⟨p,hp⟩ := PhysicalEdgeCostEnvelope.edge_polynomial
  refine ⟨paidPolynomial p,?_⟩
  intro n B positive D factor width tape r actual
  let x := n+B+D.confidence
  have hn : n ≤ x := by dsimp only [x]; omega
  have hB : B ≤ x := by dsimp only [x]; omega
  have hc : D.confidence ≤ x := by dsimp only [x]; omega
  have horizon := rounds_le D width
  have totalBound : (roundBudget n B)*p.eval (n+n*n+fieldBudget n B+D.confidence) ≤ (paidPolynomial p).eval x := by
    simp only [paidPolynomial,eval_mul,eval_add,eval_C,eval_X,eval_one,eval_comp]
    unfold fieldBudget priceBudget arithmeticWidth roundBudget
    apply Nat.mul_le_mul
    · gcongr
    · apply eval_mono
      dsimp only
      gcongr
  by_cases small : RationalEdgeDecomposition.originalTotal D.adjacency D.weights<1
  · simp only [PhysicalEdgeFamily.family,ite_eq_left small,Option.some.injEq] at actual
    rw [← actual]
    exact Nat.zero_le _
  · rw [PhysicalEdgeFamily.family,ite_eq_right small] at actual
    have state : ∀ a ∈ some (initial : State n),
        Invariant (floored D) D.factor (scale n) (keep D) a ∧ a.cuts.length+rounds D ≤ roundBudget n B := by
      intro a mem
      rw [← Option.mem_some_iff.mp mem]
      exact ⟨initial_invariant _ _ _ _,by simpa only [initial,List.length_nil,Nat.zero_add] using horizon⟩
    have work := stages_paid D (roundBudget n B) (p.eval (n+n*n+fieldBudget n B+D.confidence))
      (fun s hs len bits _ ran => step_paid p hp D width s hs len bits ran)
      positive factor (rounds D) (some initial) tape state actual
    exact (work.trans (Nat.mul_le_mul_right _ horizon)).trans totalBound

theorem calibrated_polynomial {k : ℕ} (positive : 0<k) (M : ℕ) (multiplier : 0<M) :
    ∃ p : Polynomial ℕ, ∀ {n B : ℕ}, 0<n → ∀ (κ : ℕ)
      (adj : BinaryFractionalWalkOracle.Adjacency n) (w : RationalEdgeThresholds.Weights n),
      AdaptiveWidthEnvelope.StoredWeights w B → ∀ tape r,
      PhysicalEdgeFamily.family (calibratedParameters k M κ adj w) tape=some r →
        paid r ≤ p.eval (n+B+κ) := by
  obtain ⟨p,hp⟩ := family_polynomial
  let W : Polynomial ℕ := X+(C M.size+X+X*X*(X+1)+C 3)
  let S := X+(C 2*X*(C 2*X+X*X*(W+1)+C 3)+1)
  refine ⟨p.comp (X+W+S),?_⟩
  intro n B size κ adj w stored tape r actual
  let D := calibratedParameters k M κ adj w
  let x := n+B+κ
  have hn : n ≤ x := by dsimp only [x]; omega
  have hb : B ≤ x := by dsimp only [x]; omega
  have hk : κ ≤ x := by dsimp only [x]; omega
  have width : AdaptiveWidthEnvelope.width n B M ≤ W.eval x := by
    apply max_le
    · simp only [W,eval_add,eval_mul,eval_X,eval_C,eval_one]
      omega
    · simp only [W,eval_add,eval_mul,eval_X,eval_C,eval_one]
      exact (show M.size+n+n*n*(B+1)+3 ≤ M.size+x+x*x*(x+1)+3 by gcongr).trans (Nat.le_add_left _ _)
  have confidence : D.confidence ≤ S.eval x := by
    apply (AdaptiveWidthEnvelope.calibrated_confidence positive M κ adj w stored).trans
    unfold AdaptiveWidthEnvelope.confidence roundBudget
    simp only [S,eval_add,eval_mul,eval_X,eval_C,eval_one]
    gcongr
  have work := hp size D (parameters_factor_ge_one multiplier adj w)
    (AdaptiveWidthEnvelope.calibrated_fits positive M κ adj w stored) tape r actual
  rw [eval_comp]
  apply work.trans (eval_mono p ?_)
  simp only [eval_add,eval_X]
  gcongr

end DirectedFlowCutGap.PhysicalEdgeFamilyCost
